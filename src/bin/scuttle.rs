use std::{ffi::OsString, fmt, path::PathBuf, thread};

use maxpre::{MaxPre, PreproClauses, PreproMultiOpt};
use rustsat::{
    encodings::{card, pb},
    instances::{
        fio::{self, ParsingError},
        BasicVarManager, ManageVars, MultiOptInstance, ReindexVars, ReindexingVarManager,
    },
    solvers::SolverError,
    types::{Assignment, Clause},
};
use rustsat_cadical::CaDiCaL;
#[cfg(feature = "div-con")]
use scuttle::solver::divcon::SeqDivCon;
use scuttle::{
    self,
    cli::{Algorithm, CardEncoding, Cli, FileFormat, PbEncoding},
    solver::CoreBoost,
    BiOptSat, LoggerError, LowerBounding, PMinimal, Solve,
};

macro_rules! expect_no_term {
    ($e:expr, $cli:expr) => {
        match $e {
            Ok(x) => x,
            Err(term) => {
                $cli.log_termination(&term)?;
                if term.is_error() {
                    return Err(Error::from(term));
                }
                panic!("expected success or error");
            }
        }
    };
}

macro_rules! handle_term {
    ($e:expr, $cli:expr) => {
        match $e {
            Ok(cont) => cont,
            Err(term) => {
                $cli.log_termination(&term)?;
                if term.is_error() {
                    return Err(Error::from(term));
                }
                false
            }
        }
    };
}

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

fn main() -> Result<(), Error> {
    let cli = Cli::init();

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
            let mut solver = expect_no_term!(PMin::new_default_blocking(inst, oracle, opts), cli);
            setup_cli_interaction(&mut solver, &cli)?;
            let cont = if let Some(cb_opts) = cb_opts {
                handle_term!(solver.core_boost(cb_opts.clone()), cli)
            } else {
                true
            };
            if cont {
                handle_term!(solver.solve(cli.limits), cli);
            }
            post_solve(&mut solver, &cli, prepro, reindexer)
        }
        Algorithm::BiOptSat(opts, pb_enc, card_enc, ref cb_opts) => {
            if inst.n_objectives() != 2 {
                cli.error("the bioptsat algorithm can only be run on bi-objective problems")?;
                return Err(Error::InvalidInstance);
            }
            if cb_opts.is_some() && (pb_enc != PbEncoding::Gte || card_enc != CardEncoding::Tot) {
                cli.error("core boosting is only implemented for the GTE and Totalizer encodings")?;
                return Err(Error::InvalidConfig);
            }
            match pb_enc {
                PbEncoding::Gte => match card_enc {
                    CardEncoding::Tot => {
                        type S<VM> = Bos<pb::DbGte, card::DbTotalizer, VM>;
                        let mut solver =
                            expect_no_term!(S::new_default_blocking(inst, oracle, opts), cli);
                        setup_cli_interaction(&mut solver, &cli)?;
                        let cont = if let Some(cb_opts) = cb_opts {
                            handle_term!(solver.core_boost(cb_opts.clone()), cli)
                        } else {
                            true
                        };
                        if cont {
                            handle_term!(solver.solve(cli.limits), cli);
                        }
                        post_solve(&mut solver, &cli, prepro, reindexer)
                    }
                },
                PbEncoding::Dpw => match card_enc {
                    CardEncoding::Tot => {
                        type S<VM> = Bos<pb::DynamicPolyWatchdog, card::DbTotalizer, VM>;
                        let mut solver =
                            expect_no_term!(S::new_default_blocking(inst, oracle, opts), cli);
                        setup_cli_interaction(&mut solver, &cli)?;
                        handle_term!(solver.solve(cli.limits), cli);
                        post_solve(&mut solver, &cli, prepro, reindexer)
                    }
                },
            }
        }
        Algorithm::LowerBounding(opts, ref cb_opts) => {
            let mut solver = expect_no_term!(Lb::new_default_blocking(inst, oracle, opts), cli);
            setup_cli_interaction(&mut solver, &cli)?;
            let cont = if let Some(cb_opts) = cb_opts {
                handle_term!(solver.core_boost(cb_opts.clone()), cli)
            } else {
                true
            };
            if cont {
                handle_term!(solver.solve(cli.limits), cli);
            }
            post_solve(&mut solver, &cli, prepro, reindexer)
        }
        #[cfg(feature = "div-con")]
        Algorithm::DivCon(ref opts) => {
            let mut solver =
                expect_no_term!(Dc::new_default_blocking(inst, oracle, opts.clone()), cli);
            setup_cli_interaction(&mut solver, &cli)?;
            handle_term!(solver.solve(cli.limits), cli);
            post_solve(&mut solver, &cli, prepro, reindexer)
        }
    }
}

fn setup_cli_interaction<S: Solve>(solver: &mut S, cli: &Cli) -> Result<(), Error> {
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
) -> Result<(), Error> {
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
) -> Result<MultiOptInstance, Error> {
    match file_format {
        FileFormat::Infer => {
            if let Some(ext) = inst_path.extension() {
                let path_without_compr = inst_path.with_extension("");
                let ext = if is_one_of!(ext, "gz", "bz2", "xz") {
                    // Strip compression extension
                    match path_without_compr.extension() {
                        Some(ext) => ext,
                        None => return Err(Error::NoFileExtension),
                    }
                } else {
                    ext
                };
                if is_one_of!(ext, "mcnf", "bicnf", "wcnf", "cnf", "dimacs") {
                    Error::wrap_parser(MultiOptInstance::from_dimacs_path(inst_path))
                } else if is_one_of!(ext, "opb") {
                    Error::wrap_parser(MultiOptInstance::from_opb_path(inst_path, opb_opts))
                } else {
                    Err(Error::UnknownFileExtension(OsString::from(ext)))
                }
            } else {
                Err(Error::NoFileExtension)
            }
        }
        FileFormat::Dimacs => Error::wrap_parser(MultiOptInstance::from_dimacs_path(inst_path)),
        FileFormat::Opb => Error::wrap_parser(MultiOptInstance::from_opb_path(inst_path, opb_opts)),
    }
}

enum Error {
    UnknownFileExtension(OsString),
    NoFileExtension,
    Parsing(ParsingError),
    IO(std::io::Error),
    Logger(LoggerError),
    Oracle(SolverError),
    InvalidInstance,
    InvalidConfig,
    ResetWithoutCnf,
    CbAfterSolve,
}

impl From<std::io::Error> for Error {
    fn from(ioe: std::io::Error) -> Self {
        Error::IO(ioe)
    }
}

impl From<scuttle::Termination> for Error {
    fn from(value: scuttle::Termination) -> Self {
        match value {
            scuttle::Termination::LoggerError(err) => Error::Logger(err),
            scuttle::Termination::OracleError(err) => Error::Oracle(err),
            scuttle::Termination::ResetWithoutCnf => Error::ResetWithoutCnf,
            scuttle::Termination::CbAfterSolve => Error::CbAfterSolve,
            _ => panic!("Termination is not an error!"),
        }
    }
}

impl Error {
    fn wrap_parser(
        parser_result: Result<MultiOptInstance, ParsingError>,
    ) -> Result<MultiOptInstance, Error> {
        match parser_result {
            Ok(inst) => Ok(inst),
            Err(err) => Err(Error::Parsing(err)),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownFileExtension(ext) => {
                write!(f, "Cannot infer file format from extension {:?}", ext)
            }
            Self::NoFileExtension => write!(
                f,
                "To infer the file format, the file needs to have a file extension"
            ),
            Self::Parsing(err) => write!(f, "Error while parsing the input file: {}", err),
            Self::IO(err) => write!(f, "IO Error: {}", err),
            Self::Logger(err) => write!(f, "Logger Error: {}", err),
            Self::Oracle(err) => write!(f, "Oracle Error: {}", err),
            Self::InvalidInstance => write!(f, "Invalid instance"),
            Self::InvalidConfig => write!(f, "Invalid configuration"),
            Self::ResetWithoutCnf => write!(
                f,
                "Tried to reset the SAT oracle without having stored the original clauses"
            ),
            Self::CbAfterSolve => {
                write!(f, "Tried to call core boosting after calling solve")
            }
        }
    }
}
