use std::{fs, io, thread};

use rustsat::{
    encodings::{card, pb},
    instances::ReindexVars,
    solvers::{DefaultInitializer, Initialize},
    types::Assignment,
};
use rustsat_cadical::CaDiCaL;
use scuttle_core::{
    self, BiOptSat, CoreBoost, Init, InitCertDefaultBlock, InitDefaultBlock, KernelFunctions,
    LeximaxIst, LowerBounding, MaybeTerminatedError, PMinimal, ParetoIhs, Solve,
    algs::leximax::{Msu3, SatUnsat},
    prepro,
    types::{Instance, Reindexer},
};

mod cli;
use ::tracing::{error, warn};
use cli::{Algorithm, CadicalConfig, CardEncoding, Cli, HittingSetSolver, PbEncoding};

mod tracing;

/// The SAT solver used
type Oracle = CaDiCaL<'static, 'static>;

/// P-Minimal instantiation used
type PMin<OInit = CaDiCaLDefaultInit> =
    PMinimal<Oracle, pb::GeneralizedTotalizer, card::Totalizer, io::BufWriter<fs::File>, OInit>;
/// BiOptSat Instantiation used
type Bos<PBE, CE, OInit = CaDiCaLDefaultInit> =
    BiOptSat<Oracle, PBE, CE, io::BufWriter<fs::File>, OInit>;
/// Lower-bounding instantiation used
type Lb<OInit = CaDiCaLDefaultInit> = LowerBounding<
    Oracle,
    pb::GeneralizedTotalizer,
    card::Totalizer,
    io::BufWriter<fs::File>,
    OInit,
>;
/// Paretop-k IHS instantiation used
type Ihs<Hss, OInit = CaDiCaLDefaultInit> = ParetoIhs<Oracle, Hss, OInit>;
type LmSu<OInit = CaDiCaLDefaultInit> =
    LeximaxIst<Oracle, SatUnsat<pb::GeneralizedTotalizer, card::Totalizer>, OInit>;
type LmMsu3<OInit = CaDiCaLDefaultInit> =
    LeximaxIst<Oracle, Msu3<pb::GeneralizedTotalizer, card::Totalizer>, OInit>;

macro_rules! run {
    // with proof
    ($slv:ident, $inst:expr_2021, $proof:expr_2021, $prepro:expr_2021, $reindexer:expr_2021, $opts:expr_2021, $cb_opts:expr_2021, $cli:expr_2021) => {
        if let Some(proof) = $proof {
            let mut alg = setup_alg_cert::<$slv>($inst, $opts, proof)?;
            let cont = if let Some(opts) = $cb_opts {
                handle_termination(alg.core_boost(opts.clone()))?.unwrap_or(false)
            } else {
                true
            };
            if cont {
                handle_termination(alg.solve($cli.limits))?;
            };
            post_solve(alg, $cli, $prepro, $reindexer)?;
        } else {
            let mut alg = setup_alg::<$slv>($inst, $opts)?;
            let cont = if let Some(opts) = $cb_opts {
                handle_termination(alg.core_boost(opts.clone()))?.unwrap_or(false)
            } else {
                true
            };
            if cont {
                handle_termination(alg.solve($cli.limits))?;
            };
            post_solve(alg, $cli, $prepro, $reindexer)?;
        }
    };
    // without proof
    (no-proof: $slv:ident, $inst:expr_2021, $prepro:expr_2021, $reindexer:expr_2021, $opts:expr_2021, $cb_opts:expr_2021, $cli:expr_2021) => {{
        let mut alg = setup_alg::<$slv>($inst, $opts)?;
        let cont = if let Some(opts) = $cb_opts {
            handle_termination(alg.core_boost(opts.clone()))?.unwrap_or(false)
        } else {
            true
        };
        if cont {
            handle_termination(alg.solve($cli.limits))?;
        };
        post_solve(alg, $cli, $prepro, $reindexer)?;
    }};
}

macro_rules! dispatch_options {
    // with proof
    ($slv:ident, $inst:expr_2021, $proof:expr_2021, $prepro:expr_2021, $reindexer:expr_2021, $opts:expr_2021, $cb_opts:expr_2021, $cli:expr_2021) => {
        match $cli.cadical_config {
            CadicalConfig::Default => {
                run!($slv, $inst, $proof, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
            CadicalConfig::Plain => {
                type Slv = $slv<CaDiCaLPlainInit>;
                run!(Slv, $inst, $proof, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
            CadicalConfig::Sat => {
                type Slv = $slv<CaDiCaLSatInit>;
                run!(Slv, $inst, $proof, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
            CadicalConfig::Unsat => {
                type Slv = $slv<CaDiCaLUnsatInit>;
                run!(Slv, $inst, $proof, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
        }
    };
    // without proof
    (no-proof: $slv:ident, $inst:expr_2021, $prepro:expr_2021, $reindexer:expr_2021, $opts:expr_2021, $cb_opts:expr_2021, $cli:expr_2021) => {
        match $cli.cadical_config {
            CadicalConfig::Default => {
                run!(no-proof: $slv, $inst, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
            CadicalConfig::Plain => {
                type Slv = $slv<CaDiCaLPlainInit>;
                run!(no-proof: Slv, $inst, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
            CadicalConfig::Sat => {
                type Slv = $slv<CaDiCaLSatInit>;
                run!(no-proof: Slv, $inst, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
            CadicalConfig::Unsat => {
                type Slv = $slv<CaDiCaLUnsatInit>;
                run!(no-proof: Slv, $inst, $prepro, $reindexer, $opts, $cb_opts, $cli)
            }
        }
    };
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::init();
    tracing::init(&cli.alg, cli.tracing_opts);

    match sub_main(&cli) {
        Ok(_) => (),
        Err(err) => {
            error!(target: "error", err = %err, backtrace = %err.backtrace());
        }
    };

    Ok(())
}

fn sub_main(cli: &Cli) -> anyhow::Result<()> {
    warn!("solving instance {:?}", cli.inst_path);

    let parsed = prepro::parse(cli.inst_path.clone(), cli.file_format, cli.opb_options)?;

    // MaxPre Preprocessing
    #[cfg(feature = "maxpre")]
    let (prepro, proof, inst) = if cli.preprocessing {
        anyhow::ensure!(
            cli.proof_paths.is_none(),
            "proof logging not supported with MaxPre preprocessing"
        );
        let (prepro, inst) =
            prepro::max_pre(parsed, &cli.maxpre_techniques, cli.maxpre_reindexing)?;
        (Some(prepro), None, inst)
    } else {
        let (proof, inst) = prepro::to_clausal(parsed, &cli.proof_paths)?;
        (None, proof, inst)
    };
    #[cfg(not(feature = "maxpre"))]
    let (prepro, (proof, inst)) = ((), prepro::to_clausal(parsed, &cli.proof_paths)?);

    // Reindexing
    let (inst, reindexer) = if cli.reindexing {
        anyhow::ensure!(
            cli.proof_paths.is_none(),
            "proof logging not supported with reindexing"
        );
        let (reind, inst) = prepro::reindexing(inst);
        (inst, Some(reind))
    } else {
        (inst, None)
    };

    match cli.alg {
        Algorithm::PMinimal(opts, ref cb_opts) => {
            dispatch_options!(PMin, inst, proof, prepro, reindexer, opts, cb_opts, cli)
        }
        Algorithm::BiOptSat(opts, pb_enc, card_enc, ref cb_opts) => {
            if inst.n_objs() != 2 {
                error!(target: "unsupported instance", "the bioptsat algorithm can only be run on bi-objective problems");
                anyhow::bail!(Error::InvalidInstance);
            }
            if cb_opts.is_some() && (pb_enc != PbEncoding::Gte || card_enc != CardEncoding::Tot) {
                error!(target: "unsupported configuration", "core boosting is only implemented for the GTE and Totalizer encodings");
                anyhow::bail!(Error::InvalidConfig);
            }
            match pb_enc {
                PbEncoding::Gte => match card_enc {
                    CardEncoding::Tot => {
                        type BosEnc<OInit = DefaultInitializer> =
                            Bos<pb::GeneralizedTotalizer, card::Totalizer, OInit>;
                        dispatch_options!(
                            BosEnc, inst, proof, prepro, reindexer, opts, cb_opts, cli
                        )
                    }
                },
            }
        }
        Algorithm::LowerBounding(opts, ref cb_opts) => {
            dispatch_options!(Lb, inst, proof, prepro, reindexer, opts, cb_opts, cli)
        }
        Algorithm::ParetoIhs(hitting_set_solver, kernel_opts, opts, ref cb_opts) => {
            match hitting_set_solver {
                HittingSetSolver::Highs => {
                    type IhsSlv<OInit = CaDiCaLDefaultInit> = Ihs<hitting_sets::HighsSolver, OInit>;
                    dispatch_options!(no-proof: IhsSlv, inst, prepro, reindexer, (kernel_opts, opts), cb_opts, cli)
                }
                #[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
                HittingSetSolver::Gurobi => {
                    type IhsSlv<OInit = CaDiCaLDefaultInit> =
                        Ihs<hitting_sets::GurobiSolver, OInit>;
                    dispatch_options!(no-proof: IhsSlv, inst, prepro, reindexer, (kernel_opts, opts), cb_opts, cli)
                }
            }
        }
        Algorithm::MipPd(mip_solver, threads) => match mip_solver {
            HittingSetSolver::Highs => {
                let mut alg = scuttle_core::MipPd::<hitting_sets::HighsSolver>::from_instance_default_blocking(inst, threads)?;

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

                handle_termination(alg.solve(cli.limits))?;

                post_solve(alg, cli, prepro, reindexer)?;
            }
            #[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
            HittingSetSolver::Gurobi => {
                let mut alg = scuttle_core::MipPd::<hitting_sets::GurobiSolver>::from_instance_default_blocking(inst, threads)?;

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

                handle_termination(alg.solve(cli.limits))?;

                post_solve(alg, cli, prepro, reindexer)?;
            }
        },
        Algorithm::LeximaxSatUnsat(opts, ref cb_opts) => {
            dispatch_options!(no-proof: LmSu, inst, prepro, reindexer, opts, cb_opts, cli)
        }
        Algorithm::LeximaxMsu3(opts, ref cb_opts) => {
            dispatch_options!(no-proof: LmMsu3, inst, prepro, reindexer, opts, cb_opts, cli)
        }
    }
    Ok(())
}

fn setup_alg<Alg>(inst: Instance, opts: <Alg as Init>::Options) -> anyhow::Result<Alg>
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

    Ok(alg)
}

fn setup_alg_cert<Alg>(
    inst: Instance,
    opts: <Alg as Init>::Options,
    proof: pigeons::Proof<Alg::ProofWriter>,
) -> anyhow::Result<Alg>
where
    Alg: InitCertDefaultBlock + KernelFunctions,
{
    let mut alg = Alg::from_instance_default_blocking_cert(inst, opts, proof)?;

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

    Ok(alg)
}

fn post_solve<Alg>(
    alg: Alg,
    cli: &Cli,
    #[cfg(feature = "maxpre")] mut prepro: Option<maxpre::MaxPre>,
    #[cfg(not(feature = "maxpre"))] _: (),
    reindexer: Option<Reindexer>,
) -> io::Result<()>
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
    #[cfg(feature = "maxpre")]
    let pareto_front = if let Some(ref mut prepro) = prepro {
        use maxpre::PreproClauses;
        pareto_front.convert_solutions(&mut |s| prepro.reconstruct(s))
    } else {
        pareto_front
    };

    let stats = alg.all_stats();

    if Alg::LEXIMAX {
        #[cfg(not(feature = "maxpre"))]
        tracing::wrap_up_leximax(pareto_front, stats, cli.wrap_up_opts);
        #[cfg(feature = "maxpre")]
        {
            use maxpre::PreproClauses;
            let maxpre_stats = prepro.map(|mp| mp.stats());
            tracing::wrap_up_leximax(
                pareto_front,
                (stats.0, stats.1, stats.2, stats.3, maxpre_stats),
                cli.wrap_up_opts,
            );
        }
    } else {
        #[cfg(not(feature = "maxpre"))]
        tracing::wrap_up(pareto_front, stats, cli.wrap_up_opts);
        #[cfg(feature = "maxpre")]
        {
            use maxpre::PreproClauses;
            let maxpre_stats = prepro.map(|mp| mp.stats());
            tracing::wrap_up(
                pareto_front,
                (stats.0, stats.1, stats.2, stats.3, maxpre_stats),
                cli.wrap_up_opts,
            );
        }
    }

    Ok(())
}

fn handle_termination<T>(ret: MaybeTerminatedError<T>) -> anyhow::Result<Option<T>> {
    match ret {
        MaybeTerminatedError::Done(val) => Ok(Some(val)),
        MaybeTerminatedError::Terminated(term) => {
            warn!("terminating: {term}");
            Ok(None)
        }
        MaybeTerminatedError::Error(err) => Err(err),
    }
}

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
enum Error {
    #[error("Invalid instance")]
    InvalidInstance,
    #[error("Invalid configuration")]
    InvalidConfig,
}

struct CaDiCaLDefaultInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLDefaultInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        // NOTE: ILB apparently causes CaDiCaL to diverge between proof logging or not?
        // It might also be bad for core-guided search performance
        slv.set_option("ilb", 0).unwrap();
        slv
    }
}

struct CaDiCaLPlainInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLPlainInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Plain)
            .expect("failed to set cadical config");
        // NOTE: ILB apparently causes CaDiCaL to diverge between proof logging or not?
        // It might also be bad for core-guided search performance
        slv.set_option("ilb", 0).unwrap();
        slv
    }
}

struct CaDiCaLSatInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLSatInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Sat)
            .expect("failed to set cadical config");
        // NOTE: ILB apparently causes CaDiCaL to diverge between proof logging or not?
        // It might also be bad for core-guided search performance
        slv.set_option("ilb", 0).unwrap();
        slv
    }
}

struct CaDiCaLUnsatInit;

impl Initialize<CaDiCaL<'static, 'static>> for CaDiCaLUnsatInit {
    fn init() -> CaDiCaL<'static, 'static> {
        let mut slv = CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Unsat)
            .expect("failed to set cadical config");
        // NOTE: ILB apparently causes CaDiCaL to diverge between proof logging or not?
        // It might also be bad for core-guided search performance
        slv.set_option("ilb", 0).unwrap();
        slv
    }
}
