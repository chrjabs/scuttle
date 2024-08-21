#![feature(min_specialization)]

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
    BiOptSat, CoreBoost, CoreBoostingOptions, Init, InitDefaultBlock, KernelOptions, LowerBounding,
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

    match cli.alg {
        Algorithm::PMinimal(opts, ref cb_opts) => match cli.cadical_config {
            CadicalConfig::Default => {
                run_alg::<PMin>(cli, inst, proof, opts, prepro, reindexer, cb_opts)
            }
            CadicalConfig::Plain => run_alg::<PMin<CaDiCalPlainInit>>(
                cli, inst, proof, opts, prepro, reindexer, cb_opts,
            ),
            CadicalConfig::Sat => {
                run_alg::<PMin<CaDiCalSatInit>>(cli, inst, proof, opts, prepro, reindexer, cb_opts)
            }
            CadicalConfig::Unsat => run_alg::<PMin<CaDiCalUnsatInit>>(
                cli, inst, proof, opts, prepro, reindexer, cb_opts,
            ),
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
                            CadicalConfig::Default => run_alg::<BosEnc>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                            CadicalConfig::Plain => run_alg::<BosEnc<CaDiCalPlainInit>>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                            CadicalConfig::Sat => run_alg::<BosEnc<CaDiCalSatInit>>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                            CadicalConfig::Unsat => run_alg::<BosEnc<CaDiCalUnsatInit>>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                        }
                    }
                },
                PbEncoding::Dpw => match card_enc {
                    CardEncoding::Tot => {
                        type BosEnc<OInit = DefaultInitializer> =
                            Bos<pb::DynamicPolyWatchdog, card::DbTotalizer, OInit>;
                        match cli.cadical_config {
                            CadicalConfig::Default => run_alg::<BosEnc>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                            CadicalConfig::Plain => run_alg::<BosEnc<CaDiCalPlainInit>>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                            CadicalConfig::Sat => run_alg::<BosEnc<CaDiCalSatInit>>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                            CadicalConfig::Unsat => run_alg::<BosEnc<CaDiCalUnsatInit>>(
                                cli, inst, proof, opts, prepro, reindexer, cb_opts,
                            ),
                        }
                    }
                },
            }
        }
        Algorithm::LowerBounding(opts, ref cb_opts) => match cli.cadical_config {
            CadicalConfig::Default => {
                run_alg::<Lb>(cli, inst, proof, opts, prepro, reindexer, cb_opts)
            }
            CadicalConfig::Plain => {
                run_alg::<Lb<CaDiCalPlainInit>>(cli, inst, proof, opts, prepro, reindexer, cb_opts)
            }
            CadicalConfig::Sat => {
                run_alg::<Lb<CaDiCalSatInit>>(cli, inst, proof, opts, prepro, reindexer, cb_opts)
            }
            CadicalConfig::Unsat => {
                run_alg::<Lb<CaDiCalUnsatInit>>(cli, inst, proof, opts, prepro, reindexer, cb_opts)
            }
        },
    }
}

fn run_alg<Alg>(
    cli: &Cli,
    inst: Instance,
    proof: Option<pidgeons::Proof<<Alg as Init>::ProofWriter>>,
    opts: KernelOptions,
    mut prepro: Option<MaxPre>,
    reindexer: Option<Reindexer>,
    cb_opts: &Option<CoreBoostingOptions>,
) -> MaybeTerminatedError
where
    Alg: InitDefaultBlock + Solve,
{
    let mut solver = Alg::from_instance_default_blocking(inst, opts, proof)?;

    // === Set up CLI interaction ===
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

    // === Core boosting ===
    let cont = core_boosting(&mut solver, cb_opts)?;

    // === Solving ===
    if cont {
        solver.solve(cli.limits)?;
    }

    // === Post solve ===
    let pareto_front = solver.pareto_front();

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

    MaybeTerminatedError::Done(())
}

/// Perform core boosting. This is the default implementation (when core boosting is not supported)
/// that only checks that core boosting is not called for.
fn core_boosting<Alg>(
    _alg: &mut Alg,
    opts: &Option<CoreBoostingOptions>,
) -> MaybeTerminatedError<bool> {
    assert!(opts.is_none());
    MaybeTerminatedError::Done(true)
}

/// Specialized variant for when core boosting is implemented
fn core_boostin<Alg>(
    alg: &mut Alg,
    opts: &Option<CoreBoostingOptions>,
) -> MaybeTerminatedError<bool>
where
    Alg: CoreBoost,
{
    if let Some(opts) = opts {
        alg.core_boost(opts.clone())
    } else {
        MaybeTerminatedError::Done(true)
    }
}

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
enum Error {
    #[error("Invalid instance")]
    InvalidInstance,
    #[error("Invalid configuration")]
    InvalidConfig,
}

struct CaDiCalPlainInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCalPlainInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Plain)
            .expect("failed to set cadical config");
        slv
    }
}

struct CaDiCalSatInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCalSatInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Sat)
            .expect("failed to set cadical config");
        slv
    }
}

struct CaDiCalUnsatInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCalUnsatInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Unsat)
            .expect("failed to set cadical config");
        slv
    }
}
