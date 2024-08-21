//! # Instance Processing Happening _Before_ It's Being Passed To The Actual Solver

use std::{cmp, ffi::OsString, fmt, path::Path};

use maxpre::{MaxPre, PreproClauses};
use rustsat::{
    encodings::CollectClauses,
    instances::{fio, ManageVars, MultiOptInstance, Objective, ReindexVars},
    types::{Clause, Lit, RsHashMap, Var},
};

use crate::types::{Instance, Parsed, Reindexer, VarManager};

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
    let inst: MultiOptInstance<VarManager> = match file_format {
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
                    MultiOptInstance::from_dimacs_path(inst_path)?
                } else if is_one_of!(ext, "opb", "mopb", "pbmo") {
                    MultiOptInstance::from_opb_path(inst_path, opb_opts)?
                } else {
                    anyhow::bail!(Error::UnknownFileExtension(OsString::from(ext)))
                }
            } else {
                anyhow::bail!(Error::NoFileExtension)
            }
        }
        FileFormat::Dimacs => MultiOptInstance::from_dimacs_path(inst_path)?,
        FileFormat::Opb => MultiOptInstance::from_opb_path(inst_path, opb_opts)?,
    };
    // FIXME: make sure constraint order is preserved
    let (mut constr, objs) = inst.decompose();
    constr.var_manager_mut().mark_max_orig_var();
    let (cnf, mut vm) = constr.into_cnf();
    vm.mark_max_enc_var();
    Ok(Parsed { cnf, objs, vm })
}

pub fn max_pre(parsed: Parsed, techniques: &str, reindexing: bool) -> (MaxPre, Instance) {
    let Parsed { cnf, objs, .. } = parsed;
    let mut prepro = MaxPre::new(
        cnf,
        objs.into_iter().map(|o| o.into_soft_cls()).collect(),
        !reindexing,
    );
    prepro.preprocess(techniques, 0, 1e9);
    let (cnf, objs) = prepro.prepro_instance();
    let objs: Vec<(Vec<_>, _)> = objs
        .into_iter()
        .map(|(softs, offset)| {
            (
                softs
                    .into_iter()
                    .map(|(cl, w)| {
                        debug_assert_eq!(cl.len(), 1);
                        (!cl[0], w)
                    })
                    .collect(),
                offset,
            )
        })
        .collect();
    let max_var = cnf.iter().fold(Var::new(0), |max, cl| {
        cl.iter().fold(max, |max, l| cmp::max(max, l.var()))
    });
    let vm = VarManager::new(max_var, max_var);
    (prepro, Instance { cnf, objs, vm })
}

pub fn handle_soft_clauses(parsed: Parsed) -> Instance {
    let Parsed {
        mut cnf,
        objs,
        mut vm,
    } = parsed;
    let mut blits = RsHashMap::default();
    let objs: Vec<_> = objs
        .into_iter()
        .map(|o| process_objective(o, &mut cnf, &mut blits, &mut vm))
        .collect();
    vm.mark_max_enc_var();
    Instance { cnf, objs, vm }
}

fn process_objective<Col: CollectClauses, VM: ManageVars>(
    obj: Objective,
    col: &mut Col,
    blits: &mut RsHashMap<Clause, Lit>,
    vm: &mut VM,
) -> (Vec<(Lit, usize)>, isize) {
    let (soft_cls, offset) = obj.into_soft_cls();
    let mut soft_lits = Vec::new();
    for (mut cl, w) in soft_cls.into_iter() {
        debug_assert!(cl.len() > 0);
        if cl.len() == 1 {
            soft_lits.push((!cl[0], w));
            continue;
        }
        if let Some(&blit) = blits.get(&cl) {
            soft_lits.push((blit, w));
            continue;
        }
        let blit = vm.new_var().pos_lit();
        // Save blit in case same soft clause reappears
        // TODO: find way to not have to clone the clause here
        blits.insert(cl.clone(), blit);
        soft_lits.push((blit, w));
        // Relax clause and add it to the CNF
        cl.add(blit);
        col.add_clause(cl).unwrap();
    }
    (soft_lits, offset)
}

pub fn reindexing(inst: Instance) -> (Reindexer, Instance) {
    let Instance {
        mut cnf,
        mut objs,
        vm,
        ..
    } = inst;
    let mut reindexer = Reindexer::new(vm.max_orig_var());
    for (softs, _) in &mut objs {
        for (l, _) in softs {
            *l = reindexer.reindex_lit(*l);
        }
    }
    for cl in &mut cnf {
        for l in cl {
            *l = reindexer.reindex_lit(*l);
        }
    }
    let max_var = reindexer.max_var().unwrap();
    let vm = VarManager::new(max_var, max_var);
    (reindexer, Instance { cnf, objs, vm })
}
