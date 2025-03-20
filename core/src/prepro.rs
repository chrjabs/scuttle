//! # Instance Processing Happening _Before_ It's Being Passed To The Actual Solver

use std::{
    cmp,
    ffi::OsString,
    fmt, fs, io,
    path::{Path, PathBuf},
};

use maxpre::{MaxPre, PreproClauses};
use rustsat::{
    encodings::{
        pb::{self, default_encode_pb_constraint},
        CollectCertClauses, CollectClauses,
    },
    instances::{fio, Cnf, ManageVars, MultiOptInstance, Objective as RsObjective, ReindexVars},
    types::{constraints::PbConstraint, Clause, Lit, RsHashMap, Var},
};

use crate::types::{Instance, Objective, Parsed, Reindexer, VarManager};

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

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
pub enum Error {
    #[error("Cannot infer file format from extension {0:?}")]
    UnknownFileExtension(OsString),
    #[error("To infer the file format, the file needs to have a file extension")]
    NoFileExtension,
}

pub fn parse<P: AsRef<Path>>(
    inst_path: P,
    file_format: FileFormat,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<Parsed> {
    let inst_path = inst_path.as_ref();
    match file_format {
        FileFormat::Infer => {
            if let Some(ext) = inst_path.extension() {
                let path_without_compr = inst_path.with_extension("");
                let ext = if is_one_of!(ext, "gz", "bz2", "xz") {
                    // Strip compression extension
                    match path_without_compr.extension() {
                        Some(ext) => ext,
                        None => anyhow::bail!(Error::NoFileExtension),
                    }
                } else {
                    ext
                };
                if is_one_of!(ext, "mcnf", "bicnf", "wcnf", "cnf", "dimacs") {
                    clausal(inst_path)
                } else if is_one_of!(ext, "opb", "mopb", "pbmo") {
                    pseudo_boolean(inst_path, opb_opts)
                } else {
                    anyhow::bail!(Error::UnknownFileExtension(OsString::from(ext)))
                }
            } else {
                anyhow::bail!(Error::NoFileExtension)
            }
        }
        FileFormat::Dimacs => clausal(inst_path),
        FileFormat::Opb => pseudo_boolean(inst_path, opb_opts),
    }
}

/// Processes a clausal input file, and optionally dumps an OPB file of the constraints for VeriPB
/// to use as input
fn clausal<P: AsRef<Path>>(input_path: P) -> anyhow::Result<Parsed> {
    let (mut constr, objs) =
        MultiOptInstance::<VarManager>::from_dimacs_path(input_path)?.decompose();
    constr.var_manager_mut().mark_max_orig_var();
    debug_assert_eq!(
        constr.n_pbs(),
        0,
        "parsing should not convert constraint types yet"
    );
    debug_assert_eq!(
        constr.n_cards(),
        0,
        "parsing should not convert constraint types yet"
    );
    let (constraints, vm) = constr.into_pbs();
    Ok(Parsed {
        constraints,
        objs,
        vm,
    })
}

/// Processes a PB input file, and optionally dumps an OPB file where the objectives have been
/// stripped for VeriPB to use as input
fn pseudo_boolean<P: AsRef<Path>>(
    input_path: P,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<Parsed> {
    let (mut constr, objs) =
        MultiOptInstance::<VarManager>::from_opb_path(input_path, opb_opts)?.decompose();
    constr.var_manager_mut().mark_max_orig_var();
    debug_assert_eq!(
        constr.n_clauses(),
        0,
        "parsing should not convert constraint types yet"
    );
    debug_assert_eq!(
        constr.n_cards(),
        0,
        "parsing should not convert constraint types yet"
    );
    let (constraints, vm) = constr.into_pbs();
    Ok(Parsed {
        constraints,
        objs,
        vm,
    })
}

fn constraints_to_clausal(
    constraints: Vec<PbConstraint>,
    vm: &mut VarManager,
) -> Result<Cnf, rustsat::OutOfMemory> {
    let mut cnf = Cnf::new();
    for constr in constraints {
        default_encode_pb_constraint(constr, &mut cnf, vm)?;
    }
    Ok(cnf)
}

pub fn max_pre(
    parsed: Parsed,
    techniques: &str,
    reindexing: bool,
) -> Result<(MaxPre, Instance), rustsat::OutOfMemory> {
    let Parsed {
        constraints,
        objs,
        mut vm,
        ..
    } = parsed;
    let cnf = constraints_to_clausal(constraints, &mut vm)?;
    let mut prepro = MaxPre::new(
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
    let max_var = cnf.iter().fold(Var::new(0), |max, cl| {
        cl.iter().fold(max, |max, l| cmp::max(max, l.var()))
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

pub fn to_clausal(
    parsed: Parsed,
    proof_paths: &Option<(PathBuf, Option<PathBuf>)>,
) -> anyhow::Result<(Option<pigeons::Proof<io::BufWriter<fs::File>>>, Instance)> {
    let Parsed {
        mut constraints,
        objs,
        mut vm,
        ..
    } = parsed;
    let mut blits = RsHashMap::default();
    // NOTE: soft clause to objective conversion is not certified
    let objs: Vec<_> = objs
        .into_iter()
        .enumerate()
        .map(|(idx, o)| process_objective(o, idx, &mut constraints, &mut blits, &mut vm))
        .collect();
    let mut proof = None;
    // (certified) PB -> CNF conversion
    let mut collector = Collector(vec![]);
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
            &objs,
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
    vm.mark_max_enc_var();
    Ok((
        proof,
        Instance {
            clauses: collector.0,
            objs,
            vm,
        },
    ))
}

fn process_objective<VM: ManageVars>(
    obj: RsObjective,
    idx: usize,
    constrs: &mut Vec<PbConstraint>,
    blits: &mut RsHashMap<Clause, Lit>,
    vm: &mut VM,
) -> Objective {
    let (soft_cls, offset) = obj.into_soft_cls();
    Objective::new(
        soft_cls.into_iter().map(|(mut cl, w)| {
            debug_assert!(cl.len() > 0);
            if cl.len() == 1 {
                return (!cl[0], w);
            }
            if let Some(&blit) = blits.get(&cl) {
                return (blit, w);
            }
            let blit = vm.new_var().pos_lit();
            // Save blit in case same soft clause reappears
            // TODO: find way to not have to clone the clause here
            blits.insert(cl.clone(), blit);
            // Relax clause and add it to the CNF
            cl.add(blit);
            constrs.push(cl.into());
            (blit, w)
        }),
        offset,
        idx,
    )
}

pub fn reindexing(inst: Instance) -> (Reindexer, Instance) {
    let Instance {
        mut clauses,
        mut objs,
        vm,
        ..
    } = inst;
    let mut reindexer = Reindexer::new(vm.max_orig_var());
    for obj in &mut objs {
        let new_obj = Objective::new(
            obj.iter().map(|(l, w)| (reindexer.reindex_lit(l), w)),
            obj.offset(),
            obj.idx(),
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
    (reindexer, Instance { clauses, objs, vm })
}
