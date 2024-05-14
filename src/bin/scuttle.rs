use std::{ffi::OsString, path::PathBuf, thread};

use maxpre::{MaxPre, PreproClauses, PreproMultiOpt};
use rustsat::{
    encodings::{card, pb},
    instances::{
        fio, BasicVarManager, ManageVars, MultiOptInstance, ReindexVars, ReindexingVarManager,
    },
    types::{Assignment, Clause},
};
use rustsat_cadical::CaDiCaL;
#[cfg(feature = "div-con")]
use scuttle::solver::divcon::SeqDivCon;
use scuttle::{
    self,
    cli::{Algorithm, CardEncoding, Cli, FileFormat, PbEncoding},
    solver::CoreBoost,
    BiOptSat, LowerBounding, MaybeTerminatedError, PMinimal, Solve,
};

/// The SAT solver used
type Oracle = CaDiCaL<'static, 'static>;

/// P-Minimal instantiation used
type PMin<VM> = PMinimal<pb::DbGte, card::DbTotalizer, VM, fn(Assignment) -> Clause, Oracle>;
/// BiOptSat Instantiation used
type Bos<PBE, CE, VM> = BiOptSat<PBE, CE, VM, fn(Assignment) -> Clause, Oracle>;
/// Lower-bounding instantiation used
type Lb<VM> = LowerBounding<pb::DbGte, card::DbTotalizer, VM, fn(Assignment) -> Clause, Oracle>;
#[cfg(feature = "div-con")]
/// Divide and Conquer prototype used
type Dc<VM> = SeqDivCon<VM, Oracle, fn(Assignment) -> Clause>;

fn main() -> anyhow::Result<()> {
    let cli = Cli::init();

    match sub_main(&cli) {
        MaybeTerminatedError::Done(_) => (),
        MaybeTerminatedError::Terminated(term) => cli.log_termination(&term)?,
        MaybeTerminatedError::Error(err) => cli.error(&format!("{err}"))?,
    };

    Ok(())
}

fn sub_main(cli: &Cli) -> MaybeTerminatedError {
    cli.print_header()?;
    cli.print_solver_config()?;

    cli.info(&format!("solving instance {:?}", cli.inst_path))?;

    let inst = parse_instance(cli.inst_path.clone(), cli.file_format, cli.opb_options)?;

    // MaxPre Preprocessing
    let (prepro, inst) = if cli.preprocessing {
        let mut prepro = <MaxPre as PreproMultiOpt>::new(inst, !cli.maxpre_reindexing);
        prepro.preprocess(&cli.maxpre_techniques, 0, 1e9);
        let inst = PreproMultiOpt::prepro_instance(&mut prepro);
        (Some(prepro), inst)
    } else {
        (None, inst)
    };

    // Reindexing
    let (inst, reindexer) = if cli.reindexing {
        let reindexer = ReindexingVarManager::default();
        let (inst, reindexer) = inst
            .reindex(reindexer)
            .change_var_manager(|vm| BasicVarManager::from_next_free(vm.max_var().unwrap() + 1));
        (inst, Some(reindexer))
    } else {
        (inst, None)
    };

    // TODO: make sure configuration is also set after reset
    let oracle = {
        let mut o = Oracle::default();
        o.set_configuration(cli.cadical_config).unwrap();
        o
    };

    match cli.alg {
        Algorithm::PMinimal(opts, ref cb_opts) => {
            let mut solver = PMin::new_default_blocking(inst, oracle, opts)?;
            setup_cli_interaction(&mut solver, cli)?;
            let cont = if let Some(cb_opts) = cb_opts {
                solver.core_boost(cb_opts.clone())?
            } else {
                true
            };
            if cont {
                solver.solve(cli.limits)?;
            }
            post_solve(&mut solver, cli, prepro, reindexer).into()
        }
        Algorithm::BiOptSat(opts, pb_enc, card_enc, ref cb_opts) => {
            if inst.n_objectives() != 2 {
                cli.error("the bioptsat algorithm can only be run on bi-objective problems")?;
                return MaybeTerminatedError::Error(anyhow::anyhow!(Error::InvalidInstance));
            }
            if cb_opts.is_some() && (pb_enc != PbEncoding::Gte || card_enc != CardEncoding::Tot) {
                cli.error("core boosting is only implemented for the GTE and Totalizer encodings")?;
                return MaybeTerminatedError::Error(anyhow::anyhow!(Error::InvalidConfig));
            }
            match pb_enc {
                PbEncoding::Gte => match card_enc {
                    CardEncoding::Tot => {
                        type S<VM> = Bos<pb::DbGte, card::DbTotalizer, VM>;
                        let mut solver = S::new_default_blocking(inst, oracle, opts)?;
                        setup_cli_interaction(&mut solver, cli)?;
                        let cont = if let Some(cb_opts) = cb_opts {
                            solver.core_boost(cb_opts.clone())?
                        } else {
                            true
                        };
                        if cont {
                            solver.solve(cli.limits)?;
                        }
                        post_solve(&mut solver, cli, prepro, reindexer).into()
                    }
                },
                PbEncoding::Dpw => match card_enc {
                    CardEncoding::Tot => {
                        type S<VM> = Bos<pb::DynamicPolyWatchdog, card::DbTotalizer, VM>;
                        let mut solver = S::new_default_blocking(inst, oracle, opts)?;
                        setup_cli_interaction(&mut solver, cli)?;
                        solver.solve(cli.limits)?;
                        post_solve(&mut solver, cli, prepro, reindexer).into()
                    }
                },
            }
        }
        Algorithm::LowerBounding(opts, ref cb_opts) => {
            let mut solver = Lb::new_default_blocking(inst, oracle, opts)?;
            setup_cli_interaction(&mut solver, cli)?;
            let cont = if let Some(cb_opts) = cb_opts {
                solver.core_boost(cb_opts.clone())?
            } else {
                true
            };
            if cont {
                solver.solve(cli.limits)?;
            }
            post_solve(&mut solver, cli, prepro, reindexer).into()
        }
        #[cfg(feature = "div-con")]
        Algorithm::DivCon(ref opts) => {
            let mut solver = Dc::new_default_blocking(inst, oracle, opts.clone())?;
            setup_cli_interaction(&mut solver, cli)?;
            solver.solve(cli.limits)?;
            post_solve(&mut solver, cli, prepro, reindexer).into()
        }
    }
}

fn setup_cli_interaction<S: Solve>(solver: &mut S, cli: &Cli) -> anyhow::Result<()> {
    // Set up signal handling
    let mut interrupter = solver.interrupter();
    let mut signals = signal_hook::iterator::Signals::new([
        signal_hook::consts::SIGTERM,
        signal_hook::consts::SIGINT,
        signal_hook::consts::SIGXCPU,
        signal_hook::consts::SIGABRT,
    ])?;
    // Thread for catching incoming signals
    thread::spawn(move || {
        for _ in signals.forever() {
            interrupter.interrupt();
        }
    });

    solver.attach_logger(cli.new_cli_logger());
    Ok(())
}

fn post_solve<S: Solve>(
    solver: &mut S,
    cli: &Cli,
    mut prepro: Option<MaxPre>,
    reindexer: Option<ReindexingVarManager>,
) -> anyhow::Result<()> {
    cli.info("finished solving the instance")?;

    let pareto_front = solver.pareto_front();

    // Reverse reindexing
    let pareto_front = if let Some(reindexer) = reindexer {
        let reverse = |l| reindexer.reverse_lit(l);
        pareto_front.convert_solutions(&mut |s| s.into_iter().filter_map(reverse).collect())
    } else {
        pareto_front
    };

    // Solution reconstruction
    let pareto_front = if let Some(ref mut prepro) = prepro {
        pareto_front.convert_solutions(&mut |s| prepro.reconstruct(s))
    } else {
        pareto_front
    };

    cli.print_pareto_front(pareto_front)?;

    let (stats, ostats, estats) = solver.all_stats();
    cli.print_stats(stats)?;
    // Get extended stats for solver that supports stats
    if let Some(stats) = ostats {
        cli.print_oracle_stats(stats)?;
    }
    if let Some(stats) = estats {
        cli.print_encoding_stats(stats)?;
    }
    if let Some(prepro) = prepro {
        cli.print_maxpre_stats(prepro.stats())?;
    }

    Ok(())
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn parse_instance(
    inst_path: PathBuf,
    file_format: FileFormat,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<MultiOptInstance> {
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
                Ok(
                    if is_one_of!(ext, "mcnf", "bicnf", "wcnf", "cnf", "dimacs") {
                        MultiOptInstance::from_dimacs_path(inst_path)?
                    } else if is_one_of!(ext, "opb", "mopb", "pbmo") {
                        MultiOptInstance::from_opb_path(inst_path, opb_opts)?
                    } else {
                        anyhow::bail!(Error::UnknownFileExtension(OsString::from(ext)))
                    },
                )
            } else {
                anyhow::bail!(Error::NoFileExtension)
            }
        }
        FileFormat::Dimacs => Ok(MultiOptInstance::from_dimacs_path(inst_path)?),
        FileFormat::Opb => Ok(MultiOptInstance::from_opb_path(inst_path, opb_opts)?),
    }
}

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
enum Error {
    #[error("Cannot infer file format from extension {0:?}")]
    UnknownFileExtension(OsString),
    #[error("To infer the file format, the file needs to have a file extension")]
    NoFileExtension,
    #[error("Invalid instance")]
    InvalidInstance,
    #[error("Invalid configuration")]
    InvalidConfig,
}
