use std::{fs, io, thread};

use maxpre::{MaxPre, PreproClauses};
use rustsat::{
    encodings::{card, pb},
    instances::ReindexVars,
    solvers::{DefaultInitializer, Initialize},
    types::Assignment,
};
use rustsat_cadical::CaDiCaL;
use scuttle_core::{
    self, prepro,
    types::{Instance, Reindexer},
    BiOptSat, CoreBoost, Init, InitDefaultBlock, KernelFunctions, KernelOptions, LowerBounding,
    MaybeTerminatedError, PMinimal, Solve,
};

mod cli;
use cli::{Algorithm, CadicalConfig, CardEncoding, Cli, PbEncoding};

/// The SAT solver used
type Oracle = CaDiCaL<'static, 'static>;

/// P-Minimal instantiation used
type PMin<OInit = DefaultInitializer> =
    PMinimal<Oracle, pb::DbGte, card::DbTotalizer, io::BufWriter<fs::File>, OInit>;
/// BiOptSat Instantiation used
type Bos<PBE, CE, OInit = DefaultInitializer> =
    BiOptSat<Oracle, PBE, CE, io::BufWriter<fs::File>, OInit>;
/// Lower-bounding instantiation used
type Lb<OInit = DefaultInitializer> =
    LowerBounding<Oracle, pb::DbGte, card::DbTotalizer, io::BufWriter<fs::File>, OInit>;

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

    // FIXME: this is terrible style, figure out how to make this neat
    // The problem is that not all algorithm configurations support core boosting
    match cli.alg {
        Algorithm::PMinimal(opts, ref cb_opts) => match cli.cadical_config {
            CadicalConfig::Default => {
                let mut alg = setup_alg::<PMin>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
            CadicalConfig::Plain => {
                let mut alg = setup_alg::<PMin<CaDiCaLPlainInit>>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
            CadicalConfig::Sat => {
                let mut alg = setup_alg::<PMin<CaDiCaLSatInit>>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
            CadicalConfig::Unsat => {
                let mut alg = setup_alg::<PMin<CaDiCaLUnsatInit>>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
        },
        Algorithm::BiOptSat(opts, pb_enc, card_enc, ref cb_opts) => {
            if inst.n_objs() != 2 {
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
                        type BosEnc<OInit = DefaultInitializer> =
                            Bos<pb::DbGte, card::DbTotalizer, OInit>;
                        match cli.cadical_config {
                            CadicalConfig::Default => {
                                let mut alg = setup_alg::<BosEnc>(cli, inst, opts)?;
                                let cont = if let Some(opts) = cb_opts {
                                    alg.core_boost(opts.clone())?
                                } else {
                                    true
                                };
                                if cont {
                                    alg.solve(cli.limits)?;
                                };
                                post_solve(alg, cli, prepro, reindexer)
                            }
                            CadicalConfig::Plain => {
                                let mut alg =
                                    setup_alg::<BosEnc<CaDiCaLPlainInit>>(cli, inst, opts)?;
                                let cont = if let Some(opts) = cb_opts {
                                    alg.core_boost(opts.clone())?
                                } else {
                                    true
                                };
                                if cont {
                                    alg.solve(cli.limits)?;
                                };
                                post_solve(alg, cli, prepro, reindexer)
                            }
                            CadicalConfig::Sat => {
                                let mut alg = setup_alg::<BosEnc<CaDiCaLSatInit>>(cli, inst, opts)?;
                                let cont = if let Some(opts) = cb_opts {
                                    alg.core_boost(opts.clone())?
                                } else {
                                    true
                                };
                                if cont {
                                    alg.solve(cli.limits)?;
                                };
                                post_solve(alg, cli, prepro, reindexer)
                            }
                            CadicalConfig::Unsat => {
                                let mut alg =
                                    setup_alg::<BosEnc<CaDiCaLUnsatInit>>(cli, inst, opts)?;
                                let cont = if let Some(opts) = cb_opts {
                                    alg.core_boost(opts.clone())?
                                } else {
                                    true
                                };
                                if cont {
                                    alg.solve(cli.limits)?;
                                };
                                post_solve(alg, cli, prepro, reindexer)
                            }
                        }
                    }
                },
                PbEncoding::Dpw => match card_enc {
                    CardEncoding::Tot => {
                        type BosEnc<OInit = DefaultInitializer> =
                            Bos<pb::DynamicPolyWatchdog, card::DbTotalizer, OInit>;
                        match cli.cadical_config {
                            CadicalConfig::Default => {
                                let mut alg = setup_alg::<BosEnc>(cli, inst, opts)?;
                                alg.solve(cli.limits)?;
                                post_solve(alg, cli, prepro, reindexer)
                            }
                            CadicalConfig::Plain => {
                                let mut alg =
                                    setup_alg::<BosEnc<CaDiCaLPlainInit>>(cli, inst, opts)?;
                                alg.solve(cli.limits)?;
                                post_solve(alg, cli, prepro, reindexer)
                            }
                            CadicalConfig::Sat => {
                                let mut alg = setup_alg::<BosEnc<CaDiCaLSatInit>>(cli, inst, opts)?;
                                alg.solve(cli.limits)?;
                                post_solve(alg, cli, prepro, reindexer)
                            }
                            CadicalConfig::Unsat => {
                                let mut alg =
                                    setup_alg::<BosEnc<CaDiCaLUnsatInit>>(cli, inst, opts)?;
                                alg.solve(cli.limits)?;
                                post_solve(alg, cli, prepro, reindexer)
                            }
                        }
                    }
                },
            }
        }
        Algorithm::LowerBounding(opts, ref cb_opts) => match cli.cadical_config {
            CadicalConfig::Default => {
                let mut alg = setup_alg::<Lb>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
            CadicalConfig::Plain => {
                let mut alg = setup_alg::<Lb<CaDiCaLPlainInit>>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
            CadicalConfig::Sat => {
                let mut alg = setup_alg::<Lb<CaDiCaLSatInit>>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
            CadicalConfig::Unsat => {
                let mut alg = setup_alg::<Lb<CaDiCaLUnsatInit>>(cli, inst, opts)?;
                let cont = if let Some(opts) = cb_opts {
                    alg.core_boost(opts.clone())?
                } else {
                    true
                };
                if cont {
                    alg.solve(cli.limits)?;
                };
                post_solve(alg, cli, prepro, reindexer)
            }
        },
    }
}

fn setup_alg<Alg>(cli: &Cli, inst: Instance, opts: KernelOptions) -> anyhow::Result<Alg>
where
    Alg: InitDefaultBlock + KernelFunctions,
{
    let mut alg = Alg::from_instance_default_blocking(inst, opts)?;

    // === Set up CLI interaction ===
    // Set up signal handling
    let mut interrupter = alg.interrupter();
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

    alg.attach_logger(cli.new_cli_logger());

    Ok(alg)
}

fn post_solve<Alg>(
    alg: Alg,
    cli: &Cli,
    mut prepro: Option<MaxPre>,
    reindexer: Option<Reindexer>,
) -> MaybeTerminatedError
where
    Alg: Solve,
{
    let pareto_front = alg.pareto_front();

    // Reverse reindexing
    let pareto_front = if let Some(reindexer) = reindexer {
        let reverse = |l| reindexer.reverse_lit(l);
        pareto_front.convert_solutions(&mut |s| {
            let s: Assignment = s.into_iter().filter_map(reverse).collect();
            s.truncate(reindexer.old_max_orig_var())
        })
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

    let (stats, ostats, estats) = alg.all_stats();
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

    MaybeTerminatedError::Done(())
}

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
enum Error {
    #[error("Invalid instance")]
    InvalidInstance,
    #[error("Invalid configuration")]
    InvalidConfig,
}

struct CaDiCaLPlainInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLPlainInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Plain)
            .expect("failed to set cadical config");
        slv
    }
}

struct CaDiCaLSatInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLSatInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Sat)
            .expect("failed to set cadical config");
        slv
    }
}

struct CaDiCaLUnsatInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLUnsatInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Unsat)
            .expect("failed to set cadical config");
        slv
    }
}
