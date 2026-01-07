//! # Instance Processing Happening _Before_ It's Being Passed To The Actual Solver

use std::{
    cmp,
    ffi::OsString,
    fmt, fs, io,
    path::{Path, PathBuf},
};

use anyhow::Context;
use rustsat::{
    encodings::{CollectClauses, cert::CollectClauses as CollectCertClauses, pb},
    instances::{ManageVars, ReindexVars, fio},
    types::{Clause, Lit, RsHashMap, constraints::PbConstraint},
};

use crate::types::{
    FileContent, HardSoftClause, Instance, Objective, Parsed, Reindexer, VarManager,
};

#[derive(Copy, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "clap", derive(clap::ValueEnum))]
pub enum FileFormat {
    /// Infer the file format from the file extension. `.mcnf`, `.bicnf`,
    /// `.cnf`, `.wcnf` or `.dimacs` are all interpreted as DIMACS files and
    /// `.opb` as an OPB file. All file extensions can also be prepended with
    /// `.bz2` or `.gz` if compression is used.
    Infer,
    /// A DIMACS MCNF file
    Dimacs,
    /// A multi-objective OPB file
    Opb,
}

impl fmt::Display for FileFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FileFormat::Infer => write!(f, "infer"),
            FileFormat::Dimacs => write!(f, "dimacs"),
            FileFormat::Opb => write!(f, "opb"),
        }
    }
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

#[derive(Debug, thiserror::Error, Clone)]
#[error("Cannot infer file format from extension {0:?} or first characters of file")]
pub struct UnknownFileType(OsString);

pub fn parse<P: AsRef<Path>>(
    inst_path: P,
    file_format: FileFormat,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<Parsed> {
    let inst_path = inst_path.as_ref();
    let mut reader = fio::open_compressed_uncompressed_read(inst_path)?;
    match file_format {
        FileFormat::Infer => {
            if let Some(ext) = inst_path.extension() {
                let path_without_compr = inst_path.with_extension("");
                if let Some(ext) = if is_one_of!(ext, "gz", "bz2", "xz") {
                    // Strip compression extension
                    path_without_compr.extension()
                } else {
                    Some(ext)
                } {
                    if is_one_of!(ext, "mcnf", "bicnf", "wcnf", "cnf", "dimacs") {
                        tracing::info!(target: "file_format", determined = "MCNF", extension = ?ext);
                        return clausal(reader);
                    } else if is_one_of!(ext, "opb", "mopb", "pbmo") {
                        tracing::info!(target: "file_format", determined = "OPB", extension = ?ext);
                        return pseudo_boolean(reader, opb_opts);
                    }
                }
            }
            // automatically detect filtype from first couple of characters
            let buf = reader.fill_buf()?;
            for &char in buf {
                if char.is_ascii_whitespace() {
                    continue;
                }
                if char == b'c' || char == b'h' || char == b'o' {
                    tracing::info!(target: "file_format", determined = "MCNF", first_char = %char::from(char));
                    return clausal(reader);
                }
                if char == b'*' || char == b'm' || char == b'-' || char.is_ascii_digit() {
                    tracing::info!(target: "file_format", determined = "OPB", first_char = %char::from(char));
                    return clausal(reader);
                }
            }
            todo!()
        }
        FileFormat::Dimacs => clausal(reader),
        FileFormat::Opb => pseudo_boolean(reader, opb_opts),
    }
}

/// Processes a clausal input file, and optionally dumps an OPB file of the constraints for VeriPB
/// to use as input
fn clausal<R: io::BufRead>(reader: R) -> anyhow::Result<Parsed> {
    let parser = fio::dimacs::Parser::<fio::dimacs::Mcnf, _>::new(reader);
    let mut vm = VarManager::default();
    let mut n_objectives = 0;
    let mut clauses = vec![];
    for data in parser {
        match data? {
            fio::dimacs::McnfData::HardClause(clause) => {
                for lit in &clause {
                    vm.mark_used(lit.var());
                }
                clauses.push(HardSoftClause::Hard(clause));
            }
            fio::dimacs::McnfData::SoftClause {
                obj_idx,
                weight,
                clause,
            } => {
                for lit in &clause {
                    vm.mark_used(lit.var());
                }
                clauses.push(HardSoftClause::Soft {
                    obj_idx: obj_idx - 1,
                    weight,
                    clause,
                });
                n_objectives = cmp::max(obj_idx, n_objectives);
            }
            fio::dimacs::McnfData::Comment(_) => (),
        }
    }
    vm.mark_max_orig_var();
    Ok(Parsed {
        content: FileContent::Mcnf {
            clauses,
            n_objectives,
        },
        vm,
    })
}

/// Processes a PB input file, and optionally dumps an OPB file where the objectives have been
/// stripped for VeriPB to use as input
fn pseudo_boolean<R: io::BufRead>(
    reader: R,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<Parsed> {
    let parser = fio::opb::Parser::new(reader, opb_opts);
    let mut vm = VarManager::default();
    let mut constraints = vec![];
    let mut objectives = vec![];
    for data in parser {
        match data? {
            fio::opb::Data::Constr(pb_constraint) => {
                for (lit, _) in &pb_constraint {
                    vm.mark_used(lit.var());
                }
                constraints.push(pb_constraint);
            }
            fio::opb::Data::Obj(fio::opb::Objective {
                sense,
                terms,
                mut offset,
            }) => {
                let mut deduplicated = RsHashMap::default();
                let mut coeff_sum = 0;
                for (coeff, lit) in terms {
                    let lit = match sense {
                        fio::opb::ObjectiveSense::Minimize => lit,
                        fio::opb::ObjectiveSense::Maximize => !lit,
                    };
                    coeff_sum += coeff;
                    vm.mark_used(lit.var());
                    if let Some(weight) = deduplicated.get_mut(&lit) {
                        *weight += coeff;
                    } else {
                        if let Some(weight) = deduplicated.get_mut(&!lit) {
                            if *weight > coeff {
                                *weight -= coeff;
                            } else {
                                let weight = *weight;
                                deduplicated.remove(&!lit);
                                offset += isize::try_from(weight)
                                    .expect("cannot handle coefficients larger than `isize::MAX`");
                                if weight < coeff {
                                    deduplicated.insert(lit, coeff - weight);
                                }
                            }
                        } else {
                            deduplicated.insert(lit, coeff);
                        }
                    }
                }
                match sense {
                    fio::opb::ObjectiveSense::Minimize => {
                        objectives.push((deduplicated, offset, false));
                    }
                    fio::opb::ObjectiveSense::Maximize => {
                        let coeff_sum = isize::try_from(coeff_sum).context(
                            "overflow when converting maximization objective to minimization",
                        )?;
                        objectives.push((deduplicated, offset + coeff_sum, false));
                    }
                }
            }
            fio::opb::Data::Cmt(_) => (),
        }
    }
    vm.mark_max_orig_var();
    Ok(Parsed {
        content: FileContent::Mopb {
            constraints,
            objectives,
        },
        vm,
    })
}

#[cfg(feature = "maxpre")]
fn constraints_to_clausal(
    constraints: Vec<PbConstraint>,
    vm: &mut VarManager,
) -> Result<rustsat::instances::Cnf, rustsat::OutOfMemory> {
    use rustsat::{encodings::pb::default_encode_pb_constraint, instances::Cnf};

    let mut cnf = Cnf::new();
    for constr in constraints {
        default_encode_pb_constraint(constr, &mut cnf, vm)?;
    }
    Ok(cnf)
}

#[cfg(feature = "maxpre")]
pub fn max_pre(
    parsed: Parsed,
    techniques: &str,
    reindexing: bool,
) -> Result<(maxpre::MaxPre, Instance), rustsat::OutOfMemory> {
    use maxpre::PreproClauses;
    let Parsed {
        constraints,
        objs,
        mut vm,
        ..
    } = parsed;
    let cnf = constraints_to_clausal(constraints, &mut vm)?;
    let mut prepro = maxpre::MaxPre::new(
        cnf,
        objs.into_iter().map(|o| o.into_soft_cls()).collect(),
        !reindexing,
    );
    prepro.preprocess(techniques, 0, 1e9);
    let (cnf, objs) = prepro.prepro_instance();
    let objs: Vec<_> = objs
        .into_iter()
        .enumerate()
        .map(|(idx, (softs, offset))| {
            Objective::new(
                softs.into_iter().map(|(cl, w)| {
                    debug_assert_eq!(cl.len(), 1);
                    (!cl[0], w)
                }),
                offset,
                idx,
            )
        })
        .collect();
    let max_var = cnf.iter().fold(rustsat::types::Var::new(0), |max, cl| {
        cl.iter().fold(max, |max, l| std::cmp::max(max, l.var()))
    });
    let vm = VarManager::new(max_var, max_var);
    Ok((
        prepro,
        Instance {
            clauses: cnf.into_iter().map(|cl| (cl, None)).collect(),
            objs,
            vm,
        },
    ))
}

struct Collector(Vec<(Clause, Option<pigeons::AbsConstraintId>)>);

impl CollectClauses for Collector {
    fn n_clauses(&self) -> usize {
        self.0.len()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        self.0.extend(cl_iter.into_iter().map(|cl| (cl, None)));
        Ok(())
    }
}

impl CollectCertClauses for Collector {
    fn extend_cert_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = (Clause, pigeons::AbsConstraintId)>,
    {
        self.0
            .extend(cl_iter.into_iter().map(|(cl, id)| (cl, Some(id))));
        Ok(())
    }
}

pub fn normalize(
    parsed: Parsed,
    proof_paths: &Option<(PathBuf, Option<PathBuf>)>,
) -> anyhow::Result<(Option<pigeons::Proof<io::BufWriter<fs::File>>>, Instance)> {
    let mut proof = None;
    let mut collector = Collector(vec![]);
    let objectives: Vec<_>;
    let Parsed {
        content, mut vm, ..
    } = parsed;
    match content {
        FileContent::Mcnf {
            clauses,
            n_objectives,
        } => {
            let mut blits = RsHashMap::default();
            let mut objs = vec![(RsHashMap::<Lit, usize>::default(), 0); n_objectives];
            let mut id = if proof_paths.is_some() {
                Some(pigeons::AbsConstraintId::new(1))
            } else {
                None
            };
            for clause in clauses {
                match clause {
                    HardSoftClause::Hard(clause) => {
                        if let Some(id) = &mut id {
                            collector.add_cert_clause(clause, *id)?;
                            *id += 1;
                        } else {
                            collector.add_clause(clause)?;
                        }
                    }
                    HardSoftClause::Soft {
                        obj_idx,
                        weight,
                        mut clause,
                    } => {
                        let (obj, offset) = &mut objs[obj_idx];
                        let blit = if clause.is_empty() {
                            *offset += isize::try_from(weight)
                                .expect("cannot handle coefficients larger than `isize::MAX`");
                            continue;
                        } else if clause.len() == 1 {
                            !clause[0]
                        } else if let Some(blit) = blits.get(&clause) {
                            *blit
                        } else {
                            let blit = vm.new_lit();
                            blits.insert(clause.clone(), blit);
                            blit
                        };
                        if let Some(coeff) = obj.get_mut(&blit) {
                            *coeff += weight;
                        } else {
                            if let Some(coeff) = obj.get_mut(&!blit) {
                                if *coeff > weight {
                                    *coeff -= weight;
                                } else {
                                    let coeff = *coeff;
                                    obj.remove(&!blit);
                                    *offset += isize::try_from(coeff).expect(
                                        "cannot handle coefficients larger than `isize::MAX`",
                                    );
                                    if coeff < weight {
                                        obj.insert(blit, coeff - weight);
                                    }
                                }
                            } else {
                                obj.insert(blit, weight);
                            }
                        }
                        if clause.len() > 1 {
                            clause.add(blit);
                            if let Some(id) = &mut id {
                                collector.add_cert_clause(clause, *id)?;
                                *id += 1;
                            } else {
                                collector.add_clause(clause)?;
                            }
                        }
                    }
                }
            }
            objectives = objs
                .into_iter()
                .enumerate()
                .map(|(obj_idx, (terms, offset))| Objective::new(terms, offset, obj_idx, false))
                .collect();
            if let Some((proof_path, veripb_input_path)) = proof_paths {
                if let Some(veripb_input_path) = veripb_input_path {
                    // dump constraints into OPB file for VeriPB to read
                    let mut writer = io::BufWriter::new(fs::File::create(veripb_input_path)?);
                    let iter = collector
                        .0
                        .iter()
                        .map(|(c, _)| fio::opb::FileLine::<Option<_>>::Clause(c.clone()));
                    fio::opb::write_opb_lines(&mut writer, iter, fio::opb::Options::default())?;
                }

                proof = Some(crate::algs::proofs::init_proof(
                    io::BufWriter::new(fs::File::create(proof_path)?),
                    collector.0.len(),
                    &objectives,
                )?);
            }
        }
        FileContent::Mopb {
            constraints,
            objectives: parsed_objs,
        } => {
            objectives = parsed_objs
                .into_iter()
                .enumerate()
                .map(|(obj_idx, (terms, offset, negated))| {
                    Objective::new(terms, offset, obj_idx, negated)
                })
                .collect();

            if let Some((proof_path, veripb_input_path)) = proof_paths {
                let n_constraints = constraints.iter().fold(0, |s, c| {
                    if matches!(c, PbConstraint::Eq(_)) {
                        s + 2
                    } else {
                        s + 1
                    }
                });

                if let Some(veripb_input_path) = veripb_input_path {
                    // dump constraints into OPB file for VeriPB to read
                    let mut writer = io::BufWriter::new(fs::File::create(veripb_input_path)?);
                    let iter = constraints
                        .iter()
                        .map(|c| fio::opb::FileLine::<Option<_>>::Pb(c.clone()));
                    fio::opb::write_opb_lines(&mut writer, iter, fio::opb::Options::default())?;
                }

                let mut the_proof = crate::algs::proofs::init_proof(
                    io::BufWriter::new(fs::File::create(proof_path)?),
                    n_constraints,
                    &objectives,
                )?;

                let mut id = pigeons::AbsConstraintId::new(1);
                for constr in constraints {
                    let eq = matches!(constr, PbConstraint::Eq(_));
                    pb::cert::default_encode_pb_constraint(
                        (constr, id),
                        &mut collector,
                        &mut vm,
                        &mut the_proof,
                    )?;
                    id += 1 + usize::from(eq);
                }

                #[cfg(feature = "verbose-proofs")]
                the_proof.comment(&"end OPB translation")?;
                proof = Some(the_proof);
            } else {
                for constr in constraints {
                    pb::default_encode_pb_constraint(constr, &mut collector, &mut vm)?;
                }
            }
        }
    }
    vm.mark_max_enc_var();
    Ok((
        proof,
        Instance {
            clauses: collector.0,
            objectives,
            vm,
        },
    ))
}

pub fn reindexing(inst: Instance) -> (Reindexer, Instance) {
    let Instance {
        mut clauses,
        objectives: mut objs,
        vm,
        ..
    } = inst;
    let mut reindexer = Reindexer::new(vm.max_orig_var());
    for obj in &mut objs {
        let new_obj = Objective::new(
            obj.iter().map(|(l, w)| (reindexer.reindex_lit(l), w)),
            obj.offset(),
            obj.idx(),
            false,
        );
        *obj = new_obj;
    }
    for (cl, _) in &mut clauses {
        for l in cl {
            *l = reindexer.reindex_lit(*l);
        }
    }
    let max_var = reindexer.max_var().unwrap();
    let vm = VarManager::new(max_var, max_var);
    (
        reindexer,
        Instance {
            clauses,
            objectives: objs,
            vm,
        },
    )
}
