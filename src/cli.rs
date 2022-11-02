//! # Command Line Interface for the Solver Binary

use std::fmt;

use crate::{
    types::{ParetoFront, ParetoPoint},
    EncodingStats, Limits, Options, OracleStats, Stats, WriteSolverLog,
};
use clap::{Parser, ValueEnum};
use termcolor::ColorChoice;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct CliArgs {
    /// The path to the instance file to load. Compressed files with an
    /// extension like `.bz2` or `.gz` can be read.
    inst_path: String,
    /// The maximum number of solutions to enumerate per Pareto point (0 is no limit)
    #[arg(long, default_value_t = 1)]
    max_sols_per_pp: usize,
    /// Whether to perform model tightening
    #[arg(long)]
    model_tightening: bool,
    /// Limit the number of Pareto points to enumerate (0 is no limit)
    #[arg(long, default_value_t = 0)]
    pp_limit: usize,
    /// Limit the number of solutions to enumerate (0 is no limit)
    #[arg(long, default_value_t = 0)]
    sol_limit: usize,
    /// Limit the number of candidates to consider (0 is not limit)
    #[arg(long, default_value_t = 0)]
    candidate_limit: usize,
    /// Limit the number of SAT oracle calls (0 is not limit)
    #[arg(long, default_value_t = 0)]
    oracle_call_limit: usize,
    #[arg(long, value_enum, default_value_t = FileFormat::Infer)]
    /// The file format of the input file. With infer, the file format is
    /// inferred from the file extension.
    file_format: FileFormat,
    #[command(flatten)]
    color: concolor_clap::Color,
    /// Print the solver configuration
    #[arg(long)]
    print_solver_config: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum FileFormat {
    /// Infer the file format from the file extension. `.mcnf`, `.cnf`, `.wcnf`
    /// or `.dimacs` are all interpreted as DIMACS files and `.opb` as an OPB
    /// file. All file extensions can also be prepended with `.bz2` or `.gz` if
    /// compression is used.
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

pub struct Cli {
    pub options: Options,
    pub limits: Limits,
    pub file_format: FileFormat,
    pub inst_path: String,
    color_stdout: ColorChoice,
    color_stderr: ColorChoice,
    print_solver_config: bool,
}

macro_rules! none_if_zero {
    ($val:expr) => {
        if $val == 0 {
            None
        } else {
            Some($val)
        }
    };
}

impl Cli {
    pub fn init() -> Self {
        let args = CliArgs::parse();
        let cli = Cli {
            options: Options {
                max_sols_per_pp: none_if_zero!(args.max_sols_per_pp),
                model_tightening: args.model_tightening,
            },
            limits: Limits {
                pps: none_if_zero!(args.pp_limit),
                sols: none_if_zero!(args.sol_limit),
                candidates: none_if_zero!(args.candidate_limit),
                oracle_calls: none_if_zero!(args.oracle_call_limit),
            },
            file_format: args.file_format,
            inst_path: args.inst_path.clone(),
            color_stdout: match args.color.color {
                concolor_clap::ColorChoice::Always => ColorChoice::Always,
                concolor_clap::ColorChoice::Never => ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stdout) {
                        ColorChoice::Auto
                    } else {
                        ColorChoice::Never
                    }
                }
            },
            color_stderr: match args.color.color {
                concolor_clap::ColorChoice::Always => ColorChoice::Always,
                concolor_clap::ColorChoice::Never => ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stderr) {
                        ColorChoice::Auto
                    } else {
                        ColorChoice::Never
                    }
                }
            },
            print_solver_config: args.print_solver_config,
        };
        cli.print_solver_config();
        cli
    }

    pub fn new_cli_logger(&self) -> CliLogger {
        CliLogger {
            color_stdout: self.color_stdout,
            log_candidates: todo!(),
            log_oracle_calls: todo!(),
            log_solutions: todo!(),
            log_pareto_points: todo!(),
        }
    }

    pub fn warning(&self, msg: &str) {
        todo!()
    }

    pub fn error(&self, msg: &str) {
        todo!()
    }

    pub fn info(&self, msg: &str) {
        todo!()
    }

    pub fn print_solver_config(&self) {
        if self.print_solver_config {
            todo!()
        }
    }

    pub fn print_pareto_front(&self, pareto_front: ParetoFront) {
        todo!()
    }

    pub fn print_stats(&self, stats: Stats) {
        todo!()
    }

    pub fn print_oracle_stats(&self, stats: OracleStats) {
        todo!()
    }

    pub fn print_encoding_stats(&self, stats: Vec<EncodingStats>) {
        todo!()
    }
}

pub struct CliLogger {
    color_stdout: ColorChoice,
    log_candidates: bool,
    log_oracle_calls: bool,
    log_solutions: bool,
    log_pareto_points: bool,
}

impl WriteSolverLog for CliLogger {
    fn log_candidate(&mut self, costs: &Vec<usize>) {
        if self.log_candidates {
            todo!()
        }
    }

    fn log_oracle_call(&mut self) {
        if self.log_oracle_calls {
            todo!()
        }
    }

    fn log_solution(&mut self) {
        if self.log_solutions {
            todo!()
        }
    }

    fn log_pareto_point(&mut self, pareto_point: &ParetoPoint) {
        if self.log_pareto_points {
            todo!()
        }
    }
}

#[test]
fn verify_cli_args() {
    use clap::CommandFactory;
    CliArgs::command().debug_assert()
}
