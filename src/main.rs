use std::{fs, io, thread};

use maxpre::{MaxPre, PreproClauses};
use rustsat::{
    encodings::{card, pb},
    instances::{ReindexVars, ReindexingVarManager},
    types::{Assignment, Clause},
};
use rustsat_cadical::CaDiCaL;
use scuttle_core::{
    self, prepro,
    solver::{default_blocking_clause, CoreBoost},
    BiOptSat, LowerBounding, MaybeTerminatedError, PMinimal, Solve,
};

mod cli;
use cli::{Algorithm, CardEncoding, Cli, PbEncoding};

/// The SAT solver used
type Oracle = CaDiCaL<'static, 'static>;

/// P-Minimal instantiation used
type PMin<OFac> = PMinimal<Oracle, OFac, pb::DbGte, card::DbTotalizer, fn(Assignment) -> Clause>;
/// BiOptSat Instantiation used
type Bos<OFac, PBE, CE> = BiOptSat<Oracle, OFac, PBE, CE, fn(Assignment) -> Clause>;
/// Lower-bounding instantiation used
type Lb<OFac> = LowerBounding<Oracle, OFac, pb::DbGte, card::DbTotalizer, fn(Assignment) -> Clause>;

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

    let parsed = prepro::parse(cli.inst_path.clone(), cli.file_format, cli.opb_options)?;

    // FIXME: set correct number of original constraints
    let proof = if let Some(path) = &cli.proof_path {
        Some(pidgeons::Proof::new(
            io::BufWriter::new(fs::File::open(path)?),
            0,
            false,
        )?)
    } else {
        None
    };

    // MaxPre Preprocessing
    let (prepro, inst) = if cli.preprocessing {
        let (prepro, inst) = prepro::max_pre(parsed, &cli.maxpre_techniques, cli.maxpre_reindexing);
        (Some(prepro), inst)
    } else {
        (None, prepro::handle_soft_clauses(parsed))
    };

    // Reindexing
    let (inst, reindexer) = if cli.reindexing {
        let (reind, inst) = prepro::reindexing(inst);
        (inst, Some(reind))
    } else {
        (inst, None)
    };

    let oracle_factory = || {
        let mut o = Oracle::default();
        o.set_configuration(cli.cadical_config)
            .expect("failed to set cadical config");
        o
    };

    match cli.alg {
        Algorithm::PMinimal(opts, ref cb_opts) => {
            let mut solver = PMin::new(
                inst.cnf,
                inst.objs,
                inst.max_inst_var,
                inst.max_orig_var,
                opts,
                proof,
                oracle_factory,
                default_blocking_clause,
            )?;
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
            if inst.objs.len() != 2 {
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
                        type S<OFac> = Bos<OFac, pb::DbGte, card::DbTotalizer>;
                        let mut solver = S::new(
                            inst.cnf,
                            inst.objs,
                            inst.max_inst_var,
                            inst.max_orig_var,
                            opts,
                            proof,
                            oracle_factory,
                            default_blocking_clause,
                        )?;
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
                        type S<OFac> = Bos<OFac, pb::DynamicPolyWatchdog, card::DbTotalizer>;
                        let mut solver = S::new(
                            inst.cnf,
                            inst.objs,
                            inst.max_inst_var,
                            inst.max_orig_var,
                            opts,
                            proof,
                            oracle_factory,
                            default_blocking_clause,
                        )?;
                        setup_cli_interaction(&mut solver, cli)?;
                        solver.solve(cli.limits)?;
                        post_solve(&mut solver, cli, prepro, reindexer).into()
                    }
                },
            }
        }
        Algorithm::LowerBounding(opts, ref cb_opts) => {
            let mut solver = Lb::new(
                inst.cnf,
                inst.objs,
                inst.max_inst_var,
                inst.max_orig_var,
                opts,
                proof,
                oracle_factory,
                default_blocking_clause,
            )?;
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

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
enum Error {
    #[error("Invalid instance")]
    InvalidInstance,
    #[error("Invalid configuration")]
    InvalidConfig,
}
