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
    BiOptSat, CoreBoost, InitCertDefaultBlock, InitDefaultBlock, KernelFunctions, KernelOptions,
    LowerBounding, MaybeTerminatedError, PMinimal, Solve,
};

mod cli;
use cli::{Algorithm, CadicalConfig, CardEncoding, Cli, PbEncoding};

/// The SAT solver used
type Oracle = CaDiCaL<'static, 'static>;

/// P-Minimal instantiation used
type PMin<OInit = CaDiCaLDefaultInit> =
    PMinimal<Oracle, pb::DbGte, card::DbTotalizer, io::BufWriter<fs::File>, OInit>;
/// BiOptSat Instantiation used
type Bos<PBE, CE, OInit = CaDiCaLDefaultInit> =
    BiOptSat<Oracle, PBE, CE, io::BufWriter<fs::File>, OInit>;
/// Lower-bounding instantiation used
type Lb<OInit = CaDiCaLDefaultInit> =
    LowerBounding<Oracle, pb::DbGte, card::DbTotalizer, io::BufWriter<fs::File>, OInit>;

// TODO: this macro will potentially need a variant without core boosting
macro_rules! run {
    ($slv:ident, $inst:expr, $proof:expr, $prepro:expr, $reindexer:expr, $kernel_opts:expr, $cb_opts:expr, $cli:expr) => {
        if let Some(proof) = $proof {
            let mut alg = setup_alg_cert::<$slv>($cli, $inst, $kernel_opts, proof)?;
            let cont = if let Some(opts) = $cb_opts {
                handle_termination(alg.core_boost(opts.clone()), $cli)?.unwrap_or(false)
            } else {
                true
            };
            if cont {
                handle_termination(alg.solve($cli.limits), $cli)?;
            };
            post_solve(alg, $cli, $prepro, $reindexer)?;
        } else {
            let mut alg = setup_alg::<$slv>($cli, $inst, $kernel_opts)?;
            let cont = if let Some(opts) = $cb_opts {
                handle_termination(alg.core_boost(opts.clone()), $cli)?.unwrap_or(false)
            } else {
                true
            };
            if cont {
                handle_termination(alg.solve($cli.limits), $cli)?;
            };
            post_solve(alg, $cli, $prepro, $reindexer)?;
        }
    };
}

// TODO: this macro will potentially need a variant without core boosting
macro_rules! dispatch_options {
    ($slv:ident, $inst:expr, $proof:expr, $prepro:expr, $reindexer:expr, $kernel_opts:expr, $cb_opts:expr, $cli:expr) => {
        match $cli.cadical_config {
            CadicalConfig::Default => run!(
                $slv,
                $inst,
                $proof,
                $prepro,
                $reindexer,
                $kernel_opts,
                $cb_opts,
                $cli
            ),
            CadicalConfig::Plain => {
                type Slv = $slv<CaDiCaLPlainInit>;
                run!(
                    Slv,
                    $inst,
                    $proof,
                    $prepro,
                    $reindexer,
                    $kernel_opts,
                    $cb_opts,
                    $cli
                )
            }
            CadicalConfig::Sat => {
                type Slv = $slv<CaDiCaLSatInit>;
                run!(
                    Slv,
                    $inst,
                    $proof,
                    $prepro,
                    $reindexer,
                    $kernel_opts,
                    $cb_opts,
                    $cli
                )
            }
            CadicalConfig::Unsat => {
                type Slv = $slv<CaDiCaLUnsatInit>;
                run!(
                    Slv,
                    $inst,
                    $proof,
                    $prepro,
                    $reindexer,
                    $kernel_opts,
                    $cb_opts,
                    $cli
                )
            }
        }
    };
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::init();

    match sub_main(&cli) {
        Ok(_) => (),
        Err(err) => {
            cli.error(&format!("{err}"))?;
            cli.error(&format!("{}", err.backtrace()))?;
        }
    };

    Ok(())
}

fn sub_main(cli: &Cli) -> anyhow::Result<()> {
    cli.print_header()?;
    cli.print_solver_config()?;

    cli.info(&format!("solving instance {:?}", cli.inst_path))?;

    let parsed = prepro::parse(cli.inst_path.clone(), cli.file_format, cli.opb_options)?;

    // MaxPre Preprocessing
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
                cli.error("the bioptsat algorithm can only be run on bi-objective problems")?;
                anyhow::bail!(Error::InvalidInstance);
            }
            if cb_opts.is_some() && (pb_enc != PbEncoding::Gte || card_enc != CardEncoding::Tot) {
                cli.error("core boosting is only implemented for the GTE and Totalizer encodings")?;
                anyhow::bail!(Error::InvalidConfig);
            }
            match pb_enc {
                PbEncoding::Gte => match card_enc {
                    CardEncoding::Tot => {
                        type BosEnc<OInit = DefaultInitializer> =
                            Bos<pb::DbGte, card::DbTotalizer, OInit>;
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
    }
    Ok(())
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

fn setup_alg_cert<Alg>(
    cli: &Cli,
    inst: Instance,
    opts: KernelOptions,
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

    alg.attach_logger(cli.new_cli_logger());

    Ok(alg)
}

fn post_solve<Alg>(
    alg: Alg,
    cli: &Cli,
    mut prepro: Option<MaxPre>,
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

    Ok(())
}

fn handle_termination<T>(ret: MaybeTerminatedError<T>, cli: &Cli) -> anyhow::Result<Option<T>> {
    match ret {
        MaybeTerminatedError::Done(val) => Ok(Some(val)),
        MaybeTerminatedError::Terminated(term) => {
            cli.log_termination(&term)?;
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
