#![cfg(feature = "build-binary")]

use std::{ffi::OsString, fmt, path::Path};

use pminimal::{
    self,
    cli::{Cli, FileFormat},
    ExtendedSolveStats, PMinimal, Solve,
};
use rustsat::{
    encodings::{card::Totalizer, pb::GeneralizedTotalizer},
    instances::{MultiOptInstance, ParsingError},
    solvers,
};

#[cfg(feature = "cadical")]
type Oracle = solvers::CaDiCaL<'static>;
#[cfg(not(feature = "cadical"))]
compile_error!("At least one of the solver features needs to be turned on");

fn main() -> Result<(), MainError> {
    let cli = Cli::init(MainError::IO);

    cli.print_header()?;
    cli.print_solver_config()?;

    cli.info(&format!("solving instance {}", cli.inst_path))?;

    let inst = parse_instance(cli.inst_path.clone(), cli.file_format.clone())?;

    let mut solver: PMinimal<GeneralizedTotalizer, Totalizer, _, _, Oracle> =
        PMinimal::init_with_options(inst, cli.options.clone(), pminimal::default_blocking_clause);

    solver.attach_logger(Box::new(cli.new_cli_logger()));

    if let Err(term) = solver.solve(cli.limits.clone()) {
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
        }?
    };
    
    cli.info("finished solving the instance")?;

    let pareto_front = solver.pareto_front();
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
    inst_path: String,
    file_format: FileFormat,
) -> Result<MultiOptInstance, MainError> {
    let inst_path = Path::new(&inst_path);
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
