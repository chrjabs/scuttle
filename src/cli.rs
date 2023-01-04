//! # Command Line Interface for the Solver Binary

use std::io::Error as IOError;
use std::path::PathBuf;
use std::time::Duration;
use std::{
    fmt::{self},
    io::Write,
};

use crate::options::{EnumOptions, HeurImprOptions, HeurImprWhen};
use crate::{
    types::{ParetoFront, ParetoPoint},
    EncodingStats, Limits, Options, Stats, WriteSolverLog,
};
use crate::{LoggerError, Phase};
use clap::{crate_authors, crate_name, crate_version, Parser, ValueEnum};
use cpu_time::ProcessTime;
use rustsat::solvers::{self, SolverResult, SolverStats};
use termcolor::{Buffer, BufferWriter, Color, ColorSpec, WriteColor};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct CliArgs {
    /// The path to the instance file to load. Compressed files with an
    /// extension like `.bz2` or `.gz` can be read.
    inst_path: PathBuf,
    /// The type of enumeration to perform at each Pareto point
    #[arg(long)]
    enumeration: EnumOptionsArg,
    /// The limit for enumeration at each Pareto point (0 for no limit)
    #[arg(long, default_value_t = 0)]
    enumeration_limit: usize,
    /// When to perform solution tightening
    #[arg(long, default_value_t = HeurImprOptions::default().solution_tightening)]
    solution_tightening: HeurImprWhen,
    /// When to learn tightening clauses
    #[arg(long, default_value_t = HeurImprOptions::default().tightening_clauses)]
    tightening_clauses: HeurImprWhen,
    /// Reserve variables for the encodings in advance
    #[arg(long, default_value_t = Bool::from(Options::default().reserve_enc_vars))]
    reserve_encoding_vars: Bool,
    /// Reindex the variables in the instance before solving
    #[arg(long, default_value_t = Bool::from(false))]
    reindexing: Bool,
    /// Preprocess the instance with MaxPre before solving
    #[arg(long, default_value_t = Bool::from(false))]
    preprocessing: Bool,
    /// The preprocessing technique string to use
    #[arg(long, default_value_t = String::from("[[uvsrgc]VRTG]"))]
    maxpre_techniques: String,
    /// Reindex the variables in MaxPre
    #[arg(long, default_value_t = Bool::from(false))]
    maxpre_reindexing: Bool,
    #[cfg(feature = "cadical")]
    /// The CaDiCaL profile to use
    #[arg(long, default_value_t = CadicalConfig::Default)]
    cadical_config: CadicalConfig,
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
    /// Print solutions as binary assignments
    #[arg(long)]
    print_solutions: bool,
    /// Don't print statistics
    #[arg(long)]
    no_print_stats: bool,
    /// Log candidates along the search trace
    #[arg(long)]
    log_candidates: bool,
    /// Log found solutions as they are discovered
    #[arg(long)]
    log_solutions: bool,
    /// Log Pareto points as they are discovered
    #[arg(long)]
    log_pareto_points: bool,
    /// Log SAT oracle calls
    #[arg(long)]
    log_oracle_calls: bool,
    /// Log heuristic objective improvement
    #[arg(long)]
    log_heuristic_obj_improvement: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum Bool {
    /// Turn on feature
    True,
    /// Torn off feature
    False,
}

impl Bool {
    fn is_true(&self) -> bool {
        self == &Bool::True
    }
}

impl fmt::Display for Bool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bool::True => write!(f, "true"),
            Bool::False => write!(f, "false"),
        }
    }
}

impl From<bool> for Bool {
    fn from(val: bool) -> Self {
        if val {
            Bool::True
        } else {
            Bool::False
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum FileFormat {
    /// Infer the file format from the file extension. `.mcnf`, `.bicnf`,
    /// `.cnf`, `.wcnf` or `.dimacs` are all interpreted as DIMACS files and
    /// `.opb` as an OPB file. All file extensions can also be prepended with
    /// `.bz2` or `.gz` if compression is used.
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

#[cfg(feature = "cadical")]
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum CadicalConfig {
    /// Set default advanced internal options
    Default,
    /// Disable all internal preprocessing options
    Plain,
    /// Set internal options to target satisfiable instances
    SAT,
    /// Set internal options to target unsatisfiable instances
    UNSAT,
}

#[cfg(feature = "cadical")]
impl fmt::Display for CadicalConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CadicalConfig::Default => write!(f, "default"),
            CadicalConfig::Plain => write!(f, "plain"),
            CadicalConfig::SAT => write!(f, "sat"),
            CadicalConfig::UNSAT => write!(f, "unsat"),
        }
    }
}

#[cfg(feature = "cadical")]
impl Into<solvers::cadical::Config> for CadicalConfig {
    fn into(self) -> solvers::cadical::Config {
        match self {
            CadicalConfig::Default => solvers::cadical::Config::Default,
            CadicalConfig::Plain => solvers::cadical::Config::Plain,
            CadicalConfig::SAT => solvers::cadical::Config::SAT,
            CadicalConfig::UNSAT => solvers::cadical::Config::UNSAT,
        }
    }
}

#[derive(Default, Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum EnumOptionsArg {
    #[default]
    /// Don't enumerate at each Pareto point
    NoEnum,
    /// Enumerate Pareto-optimal solutions (with an optional limit) at each
    /// Pareto point using the provided blocking clause generator
    Solutions,
    /// Enumerate Pareto-MCSs (with an optional limit) at each Pareto point
    ParetoMCS,
}

pub struct Cli {
    pub options: Options,
    pub limits: Limits,
    pub file_format: FileFormat,
    pub inst_path: PathBuf,
    pub preprocessing: bool,
    pub maxpre_techniques: String,
    pub cadical_config: solvers::cadical::Config,
    pub reindexing: bool,
    pub maxpre_reindexing: bool,
    stdout: BufferWriter,
    stderr: BufferWriter,
    print_solver_config: bool,
    print_solutions: bool,
    print_stats: bool,
    color: concolor_clap::Color,
    logger_config: LoggerConfig,
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
        Self {
            options: Options {
                enumeration: match args.enumeration {
                    EnumOptionsArg::NoEnum => EnumOptions::NoEnum,
                    EnumOptionsArg::Solutions => {
                        EnumOptions::Solutions(none_if_zero!(args.enumeration_limit))
                    }
                    EnumOptionsArg::ParetoMCS => {
                        EnumOptions::PMCSs(none_if_zero!(args.enumeration_limit))
                    }
                },
                heuristic_improvements: HeurImprOptions {
                    solution_tightening: args.solution_tightening,
                    tightening_clauses: args.tightening_clauses,
                },
                reserve_enc_vars: args.reserve_encoding_vars.is_true(),
            },
            limits: Limits {
                pps: none_if_zero!(args.pp_limit),
                sols: none_if_zero!(args.sol_limit),
                candidates: none_if_zero!(args.candidate_limit),
                oracle_calls: none_if_zero!(args.oracle_call_limit),
            },
            file_format: args.file_format,
            inst_path: args.inst_path.clone(),
            preprocessing: args.preprocessing.is_true(),
            maxpre_techniques: args.maxpre_techniques,
            cadical_config: args.cadical_config.into(),
            reindexing: args.reindexing.is_true(),
            maxpre_reindexing: args.maxpre_reindexing.is_true(),
            stdout: BufferWriter::stdout(match args.color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stdout) {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            }),
            stderr: BufferWriter::stderr(match args.color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stderr) {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            }),
            print_solver_config: args.print_solver_config,
            print_solutions: args.print_solutions,
            print_stats: !args.no_print_stats,
            color: args.color,
            logger_config: LoggerConfig {
                log_candidates: args.log_candidates,
                log_solutions: args.log_solutions,
                log_pareto_points: args.log_pareto_points,
                log_oracle_calls: args.log_oracle_calls,
                log_heuristic_obj_improvement: args.log_heuristic_obj_improvement,
            },
        }
    }

    pub fn new_cli_logger(&self) -> CliLogger {
        CliLogger {
            stdout: BufferWriter::stdout(match self.color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stdout) {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            }),
            config: self.logger_config.clone(),
        }
    }

    pub fn warning(&self, msg: &str) -> Result<(), IOError> {
        let mut buffer = self.stderr.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Yellow)))?;
        write!(&mut buffer, "warning")?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(&mut buffer, ": ")?;
        buffer.reset()?;
        writeln!(&mut buffer, "{}", msg)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn error(&self, msg: &str) -> Result<(), IOError> {
        let mut buffer = self.stderr.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Red)))?;
        write!(&mut buffer, "error")?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(&mut buffer, ": ")?;
        buffer.reset()?;
        writeln!(&mut buffer, "{}", msg)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn info(&self, msg: &str) -> Result<(), IOError> {
        let mut buffer = self.stdout.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
        write!(&mut buffer, "info")?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(&mut buffer, ": ")?;
        buffer.reset()?;
        writeln!(&mut buffer, "{}", msg)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn print_header(&self) -> Result<(), IOError> {
        let mut buffer = self.stdout.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Green)))?;
        write!(&mut buffer, "{}", crate_name!())?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        writeln!(&mut buffer, " ({})", crate_version!())?;
        buffer.reset()?;
        writeln!(&mut buffer, "{}", crate_authors!("\n"))?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(buffer, "==============================")?;
        buffer.reset()?;
        writeln!(buffer)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn print_solver_config(&self) -> Result<(), IOError> {
        if self.print_solver_config {
            let mut buffer = self.stdout.buffer();
            Self::start_block(&mut buffer)?;
            buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
            write!(&mut buffer, "Solver Config")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(&mut buffer, ": ")?;
            buffer.reset()?;
            Self::print_parameter(
                &mut buffer,
                "enumeration",
                EnumPrinter::new(self.options.enumeration),
            )?;
            Self::print_parameter(
                &mut buffer,
                "solution-tightening",
                self.options.heuristic_improvements.solution_tightening,
            )?;
            Self::print_parameter(
                &mut buffer,
                "tightening-clauses",
                self.options.heuristic_improvements.tightening_clauses,
            )?;
            Self::print_parameter(&mut buffer, "pp-limit", OptVal::new(self.limits.pps))?;
            Self::print_parameter(&mut buffer, "sol-limit", OptVal::new(self.limits.sols))?;
            Self::print_parameter(
                &mut buffer,
                "candidate-limit",
                OptVal::new(self.limits.candidates),
            )?;
            Self::print_parameter(
                &mut buffer,
                "oracle-call-limit",
                OptVal::new(self.limits.oracle_calls),
            )?;
            Self::end_block(&mut buffer)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    pub fn print_pareto_front(&self, pareto_front: ParetoFront) -> Result<(), IOError> {
        let mut buffer = self.stdout.buffer();
        Self::start_block(&mut buffer)?;
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
        write!(&mut buffer, "Discovered Pareto Front")?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        writeln!(&mut buffer, ": ")?;
        buffer.reset()?;
        pareto_front.into_iter().fold(Ok(()), |res, pp| {
            if res.is_ok() {
                self.print_pareto_point(&mut buffer, pp)
            } else {
                res
            }
        })?;
        Self::end_block(&mut buffer)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn print_stats(&self, stats: Stats) -> Result<(), IOError> {
        if self.print_stats {
            let mut buffer = self.stdout.buffer();
            Self::start_block(&mut buffer)?;
            buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
            write!(&mut buffer, "Solver Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(&mut buffer, ": ")?;
            buffer.reset()?;
            Self::print_parameter(&mut buffer, "n-solve-calls", stats.n_solve_calls)?;
            Self::print_parameter(&mut buffer, "n-solutions", stats.n_solutions)?;
            Self::print_parameter(&mut buffer, "n-pareto-points", stats.n_pareto_points)?;
            Self::print_parameter(&mut buffer, "n-candidates", stats.n_candidates)?;
            Self::print_parameter(&mut buffer, "n-objectives", stats.n_objs)?;
            Self::print_parameter(&mut buffer, "n-orig-clauses", stats.n_orig_clauses)?;
            Self::end_block(&mut buffer)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    pub fn print_oracle_stats(&self, stats: SolverStats) -> Result<(), IOError> {
        if self.print_stats {
            let mut buffer = self.stdout.buffer();
            Self::start_block(&mut buffer)?;
            buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
            write!(&mut buffer, "Oracle Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(&mut buffer, ": ")?;
            buffer.reset()?;
            Self::print_parameter(&mut buffer, "n-sat-solves", stats.n_sat)?;
            Self::print_parameter(&mut buffer, "n-unsat-solves", stats.n_unsat)?;
            Self::print_parameter(&mut buffer, "n-clauses", stats.n_clauses)?;
            Self::print_parameter(&mut buffer, "max-var", OptVal::new(stats.max_var))?;
            Self::print_parameter(&mut buffer, "avg-clause-len", stats.avg_clause_len)?;
            Self::print_parameter(
                &mut buffer,
                "cpu-solve-time",
                DurPrinter::new(stats.cpu_solve_time),
            )?;
            Self::end_block(&mut buffer)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    pub fn print_encoding_stats(&self, stats: Vec<EncodingStats>) -> Result<(), IOError> {
        if self.print_stats {
            let mut buffer = self.stdout.buffer();
            Self::start_block(&mut buffer)?;
            buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
            write!(&mut buffer, "Encoding Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(&mut buffer, ": ")?;
            buffer.reset()?;
            stats
                .into_iter()
                .enumerate()
                .fold(Ok(()), |res, (idx, stats)| {
                    if res.is_ok() {
                        Self::print_enc_stats(&mut buffer, idx, stats)
                    } else {
                        res
                    }
                })?;
            Self::end_block(&mut buffer)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    pub fn print_maxpre_stats(&self, stats: maxpre::Stats) -> Result<(), IOError> {
        if self.print_stats {
            let mut buffer = self.stdout.buffer();
            Self::start_block(&mut buffer)?;
            buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
            write!(&mut buffer, "MaxPre Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(&mut buffer, ": ")?;
            buffer.reset()?;
            Self::print_parameter(&mut buffer, "n-objs", stats.n_objs)?;
            Self::print_parameter(
                &mut buffer,
                "n-orig-hard-clauses",
                stats.n_orig_hard_clauses,
            )?;
            Self::print_parameter(
                &mut buffer,
                "n-orig-soft-clauses",
                VecPrinter::new(&stats.n_orig_soft_clauses),
            )?;
            Self::print_parameter(&mut buffer, "max-orig-var", OptVal::new(stats.max_orig_var))?;
            Self::print_parameter(
                &mut buffer,
                "n-prepro-hard-clauses",
                stats.n_prepro_hard_clauses,
            )?;
            Self::print_parameter(
                &mut buffer,
                "n-prepro-soft-clauses",
                VecPrinter::new(&stats.n_prepro_soft_clauses),
            )?;
            Self::print_parameter(
                &mut buffer,
                "max-prepro-var",
                OptVal::new(stats.max_prepro_var),
            )?;
            Self::print_parameter(
                &mut buffer,
                "removed-weight",
                VecPrinter::new(&stats.removed_weight),
            )?;
            Self::print_parameter(
                &mut buffer,
                "prepro-time",
                DurPrinter::new(stats.prepro_time),
            )?;
            Self::print_parameter(
                &mut buffer,
                "reconst-time",
                DurPrinter::new(stats.reconst_time),
            )?;
            Self::end_block(&mut buffer)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn print_pareto_point(
        &self,
        buffer: &mut Buffer,
        pareto_point: ParetoPoint,
    ) -> Result<(), IOError> {
        Self::start_block(buffer)?;
        buffer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
        write!(buffer, "Pareto Point")?;
        buffer.reset()?;
        writeln!(
            buffer,
            ": costs: {}; n-sols: {}",
            VecPrinter::new(pareto_point.costs()),
            pareto_point.n_sols()
        )?;
        if self.print_solutions {
            pareto_point.into_iter().fold(Ok(()), |res, sol| {
                if res.is_ok() {
                    write!(buffer, "s {}", sol)
                } else {
                    res
                }
            })?
        }
        Self::end_block(buffer)?;
        Ok(())
    }

    fn print_enc_stats(
        buffer: &mut Buffer,
        idx: usize,
        stats: EncodingStats,
    ) -> Result<(), IOError> {
        Self::start_block(buffer)?;
        buffer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
        write!(buffer, "Encoding")?;
        buffer.reset()?;
        writeln!(buffer, " #{}", idx)?;
        Self::print_parameter(buffer, "n-clauses", stats.n_clauses)?;
        Self::print_parameter(buffer, "n-vars", stats.n_vars)?;
        Self::print_parameter(buffer, "offset", stats.offset)?;
        Self::print_parameter(buffer, "unit-weight", OptVal::new(stats.unit_weight))?;
        Self::end_block(buffer)?;
        Ok(())
    }

    fn print_parameter<V: fmt::Display>(
        buffer: &mut Buffer,
        name: &str,
        val: V,
    ) -> Result<(), IOError> {
        buffer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
        write!(buffer, "{}", name)?;
        buffer.reset()?;
        writeln!(buffer, ": {}", val)?;
        Ok(())
    }

    fn start_block(buffer: &mut Buffer) -> Result<(), IOError> {
        buffer.set_color(ColorSpec::new().set_dimmed(true))?;
        write!(buffer, ">>>>>")?;
        buffer.reset()?;
        writeln!(buffer)?;
        Ok(())
    }

    fn end_block(buffer: &mut Buffer) -> Result<(), IOError> {
        buffer.set_color(ColorSpec::new().set_dimmed(true))?;
        write!(buffer, "<<<<<")?;
        buffer.reset()?;
        writeln!(buffer)?;
        Ok(())
    }
}

#[derive(Clone)]
struct LoggerConfig {
    log_candidates: bool,
    log_solutions: bool,
    log_pareto_points: bool,
    log_oracle_calls: bool,
    log_heuristic_obj_improvement: bool,
}

pub struct CliLogger {
    stdout: BufferWriter,
    config: LoggerConfig,
}

impl CliLogger {
    fn wrap_error<T>(ires: Result<T, IOError>) -> Result<T, LoggerError> {
        match ires {
            Ok(t) => Ok(t),
            Err(ierror) => Err(LoggerError::new(ierror)),
        }
    }

    fn ilog_candidate(&self, costs: &[usize], phase: Phase) -> Result<(), IOError> {
        if self.config.log_candidates {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(&mut buffer, "candidate")?;
            buffer.reset()?;
            writeln!(
                &mut buffer,
                ": costs: {}; phase: {}; cpu-time: {}",
                VecPrinter::new(costs),
                phase,
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn ilog_oracle_call(&mut self, result: SolverResult, phase: Phase) -> Result<(), IOError> {
        if self.config.log_oracle_calls {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(&mut buffer, "oracle call")?;
            buffer.reset()?;
            writeln!(
                &mut buffer,
                ": result: {}; phase: {}; cpu-time: {}",
                result,
                phase,
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn ilog_solution(&mut self) -> Result<(), IOError> {
        if self.config.log_solutions {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(&mut buffer, "solution")?;
            buffer.reset()?;
            writeln!(
                &mut buffer,
                ": cpu-time: {}",
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn ilog_pareto_point(&mut self, pareto_point: &ParetoPoint) -> Result<(), IOError> {
        if self.config.log_pareto_points {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(&mut buffer, "pareto point")?;
            buffer.reset()?;
            writeln!(
                &mut buffer,
                ": costs: {}; n-sols: {}; cpu-time: {}",
                VecPrinter::new(pareto_point.costs()),
                pareto_point.n_sols(),
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn ilog_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
        learned_clauses: usize,
    ) -> Result<(), IOError> {
        if self.config.log_heuristic_obj_improvement {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(&mut buffer, "heuristic objective improvement")?;
            buffer.reset()?;
            writeln!(
                &mut buffer,
                ": obj-idx: {}; apparent-cost: {}; improved-cost: {}; learned-clauses: {}; cpu-time: {}",
                obj_idx, apparent_cost, improved_cost, learned_clauses,
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }
}

impl WriteSolverLog for CliLogger {
    fn log_candidate(&mut self, costs: &[usize], phase: Phase) -> Result<(), LoggerError> {
        Self::wrap_error(self.ilog_candidate(costs, phase))
    }

    fn log_oracle_call(&mut self, result: SolverResult, phase: Phase) -> Result<(), LoggerError> {
        Self::wrap_error(self.ilog_oracle_call(result, phase))
    }

    fn log_solution(&mut self) -> Result<(), LoggerError> {
        Self::wrap_error(self.ilog_solution())
    }

    fn log_pareto_point(&mut self, pareto_point: &ParetoPoint) -> Result<(), LoggerError> {
        Self::wrap_error(self.ilog_pareto_point(pareto_point))
    }

    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
        learned_clauses: usize,
    ) -> Result<(), LoggerError> {
        Self::wrap_error(self.ilog_heuristic_obj_improvement(
            obj_idx,
            apparent_cost,
            improved_cost,
            learned_clauses,
        ))
    }
}

struct OptVal<T> {
    val: Option<T>,
}

impl<T> OptVal<T> {
    fn new(val: Option<T>) -> Self {
        OptVal { val }
    }
}

impl<T: fmt::Display> fmt::Display for OptVal<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.val {
            Some(t) => fmt::Display::fmt(&t, f),
            None => write!(f, "none"),
        }
    }
}

struct VecPrinter<'a, C>
where
    C: 'a,
{
    costs: &'a [C],
}

impl<'a, C> VecPrinter<'a, C> {
    fn new(costs: &'a [C]) -> Self {
        VecPrinter { costs }
    }
}

impl<'a, C: fmt::Display> fmt::Display for VecPrinter<'a, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        self.costs.iter().fold(Ok(true), |res, cost| {
            if let Ok(first) = res {
                if !first {
                    write!(f, ", ")?
                };
                write!(f, "{}", cost)?;
                Ok(false)
            } else {
                res
            }
        })?;
        write!(f, ")")
    }
}

struct DurPrinter {
    dur: Duration,
}

impl DurPrinter {
    fn new(dur: Duration) -> Self {
        Self { dur }
    }
}

impl fmt::Display for DurPrinter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.dur)
    }
}

struct EnumPrinter {
    enumeration: EnumOptions,
}

impl EnumPrinter {
    fn new(enumeration: EnumOptions) -> Self {
        Self { enumeration }
    }
}

impl fmt::Display for EnumPrinter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.enumeration {
            EnumOptions::NoEnum => write!(f, "none"),
            EnumOptions::Solutions(None) => write!(f, "all solutions"),
            EnumOptions::PMCSs(None) => write!(f, "all Pareto-MCSs"),
            EnumOptions::Solutions(Some(limit)) => write!(f, "{} solutions", limit),
            EnumOptions::PMCSs(Some(limit)) => write!(f, "{} Pareto-MCSs", limit),
        }
    }
}

#[test]
fn verify_cli_args() {
    use clap::CommandFactory;
    CliArgs::command().debug_assert()
}
