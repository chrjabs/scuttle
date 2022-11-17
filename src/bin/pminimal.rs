#![cfg(feature = "build-binary")]

use std::{
    ffi::OsString,
    fmt,
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use maxpre::MaxPre;
use pminimal::{
    self,
    cli::{Cli, FileFormat},
    ExtendedSolveStats, PMinimal, Solve,
};
use rustsat::{
    encodings::{card, pb},
    instances::{MultiOptInstance, Objective, ParsingError, SatInstance},
    solvers::{ControlSignal, DefIncSolver},
};

static mut SIG_TERM_FLAG: Option<Arc<AtomicBool>> = None;

fn main() -> Result<(), MainError> {
    let cli = Cli::init();

    cli.print_header()?;
    cli.print_solver_config()?;

    cli.info(&format!("solving instance {:?}", cli.inst_path))?;

    let inst = parse_instance(cli.inst_path.clone(), cli.file_format)?;

    // MaxPre Preprocessing
    let (prepro, inst) = if cli.preprocessing {
        let (cnf, softs, _) = inst.as_hard_cls_soft_cls();
        let (softs, offsets) = softs.into_iter().unzip::<_, _, _, Vec<isize>>();
        let mut prepro = MaxPre::new(cnf, softs, false);
        prepro.preprocess(&cli.maxpre_techniques, 2, 1e9, false);
        let (cnf, softs) = prepro.prepro_instance();
        let sat_inst = SatInstance::from_iter(cnf);
        let objs = softs.into_iter().map(|s| Objective::from_iter(s));
        let removed_weight = prepro.removed_weight();
        let objs = std::iter::zip(offsets, removed_weight)
            .map(|(o1, o2)| o1 + o2 as isize)
            .zip(objs)
            .map(|(o, mut obj)| {
                obj.increase_offset(o);
                obj
            })
            .collect();
        let inst = MultiOptInstance::compose(sat_inst, objs);
        (Some(prepro), inst)
    } else {
        (None, inst)
    };

    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, DefIncSolver> =
        PMinimal::init_with_options(inst, cli.options, pminimal::default_blocking_clause);

    // Set up signal handling
    unsafe { SIG_TERM_FLAG = Some(Arc::new(AtomicBool::new(false))) };
    signal_hook::flag::register(
        signal_hook::consts::SIGTERM,
        Arc::clone(unsafe { SIG_TERM_FLAG.as_ref().unwrap() }),
    )?;
    signal_hook::flag::register(
        signal_hook::consts::SIGINT,
        Arc::clone(unsafe { SIG_TERM_FLAG.as_ref().unwrap() }),
    )?;
    signal_hook::flag::register(
        signal_hook::consts::SIGABRT,
        Arc::clone(unsafe { SIG_TERM_FLAG.as_ref().unwrap() }),
    )?;
    signal_hook::flag::register(
        signal_hook::consts::SIGXCPU,
        Arc::clone(unsafe { SIG_TERM_FLAG.as_ref().unwrap() }),
    )?;
    solver.attach_terminator(|| {
        unsafe {
            if let Some(flag) = &SIG_TERM_FLAG {
                if flag.load(Ordering::Relaxed) {
                    return ControlSignal::Terminate;
                }
            }
        }
        ControlSignal::Continue
    });

    solver.attach_logger(Box::new(cli.new_cli_logger()));

    if let Err(term) = solver.solve(cli.limits) {
        match term {
            pminimal::Termination::PPLimit => {
                cli.info("Solver terminated early because of Pareto point limit")
            }
            pminimal::Termination::SolsLimit => {
                cli.info("Solver terminated early because of solution limit")
            }
            pminimal::Termination::CandidatesLimit => {
                cli.info("Solver terminated early because of candidate limit")
            }
            pminimal::Termination::OracleCallsLimit => {
                cli.info("Solver terminated early because of oracle call limit")
            }
            pminimal::Termination::LoggerError(log_error) => cli.error(&format!(
                "Solver terminated because logger failed: {}",
                log_error
            )),
            pminimal::Termination::Callback => {
                cli.info("Solver terminated early because of interrupt signal")
            }
        }?
    };

    cli.info("finished solving the instance")?;

    let pareto_front = solver.pareto_front();

    // Solution reconstruction
    let pareto_front = if let Some(prepro) = prepro {
        pareto_front.convert_solutions(&mut |s| prepro.reconstruct(s))
    } else {
        pareto_front
    };

    cli.print_pareto_front(pareto_front)?;

    cli.print_stats(solver.stats())?;
    #[cfg(feature = "cadical")]
    {
        // Get extended stats for solver that supports stats
        cli.print_oracle_stats(solver.oracle_stats())?;
        cli.print_encoding_stats(solver.encoding_stats())?;
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
) -> Result<MultiOptInstance, MainError> {
    match file_format {
        FileFormat::Infer => {
            if let Some(ext) = inst_path.extension() {
                let path_without_compr = inst_path.with_extension("");
                let ext = if is_one_of!(ext, "gz", "bz2") {
                    // Strip compression extension
                    match path_without_compr.extension() {
                        Some(ext) => ext,
                        None => return Err(MainError::NoFileExtension),
                    }
                } else {
                    ext
                };
                if is_one_of!(ext, "mcnf", "bicnf", "wcnf", "cnf", "dimacs") {
                    MainError::wrap_parser(MultiOptInstance::from_dimacs_path(inst_path))
                } else if is_one_of!(ext, "opb") {
                    MainError::wrap_parser(MultiOptInstance::from_opb_path(inst_path))
                } else {
                    Err(MainError::UnknownFileExtension(OsString::from(ext)))
                }
            } else {
                Err(MainError::NoFileExtension)
            }
        }
        FileFormat::Dimacs => MainError::wrap_parser(MultiOptInstance::from_dimacs_path(inst_path)),
        FileFormat::Opb => MainError::wrap_parser(MultiOptInstance::from_opb_path(inst_path)),
    }
}

enum MainError {
    UnknownFileExtension(OsString),
    NoFileExtension,
    Parsing(ParsingError),
    IO(std::io::Error),
}

impl From<std::io::Error> for MainError {
    fn from(ioe: std::io::Error) -> Self {
        MainError::IO(ioe)
    }
}

impl MainError {
    fn wrap_parser(
        parser_result: Result<MultiOptInstance, ParsingError>,
    ) -> Result<MultiOptInstance, MainError> {
        match parser_result {
            Ok(inst) => Ok(inst),
            Err(err) => Err(MainError::Parsing(err)),
        }
    }
}

impl fmt::Debug for MainError {
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
        }
    }
}