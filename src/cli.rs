//! # Command Line Interface for the Solver Binary

use std::io::Error as IOError;
use std::path::PathBuf;
use std::time::Duration;
use std::{
    fmt::{self},
    io::Write,
};

use crate::options::{
    self, BuildEncodings, DivConOptions, EnumOptions, HeurImprOptions, HeurImprWhen,
};
use crate::{
    types::{NonDomPoint, ParetoFront},
    EncodingStats, KernelOptions, Limits, Stats, WriteSolverLog,
};
use crate::{LoggerError, Phase, Termination};
use clap::{crate_authors, crate_name, crate_version, Args, Parser, Subcommand, ValueEnum};
use cpu_time::ProcessTime;
use rustsat::{
    instances::fio,
    solvers::{SolverResult, SolverStats},
};
use termcolor::{Buffer, BufferWriter, Color, ColorSpec, WriteColor};

macro_rules! none_if_zero {
    ($val:expr) => {
        if $val == 0 {
            None
        } else {
            Some($val)
        }
    };
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct CliArgs {
    #[command(subcommand)]
    command: AlgorithmCommand,
}

#[derive(Subcommand)]
enum AlgorithmCommand {
    /// P-Minimal model enumeration - Soh et al. CP'17
    PMinimal {
        #[command(flatten)]
        shared: SharedArgs,
    },
    /// BiOptSat Linear Sat-Unsat - Jabs et al. SAT'22
    Bioptsat {
        #[command(flatten)]
        shared: SharedArgs,
        #[command(flatten)]
        obj_encs: ObjEncArgs,
    },
    /// Lower-bounding search - Cortes et al. TACAS'23
    LowerBounding {
        #[command(flatten)]
        shared: SharedArgs,
        /// Log fence updates
        #[arg(long)]
        log_fence: bool,
    },
    /// Divide and conquer prototype
    DivCon {
        #[command(flatten)]
        shared: SharedArgs,
        /// The divide and conquer recursion anchor to use
        #[arg(long, default_value_t = DivConAnchor::from(DivConOptions::default().anchor))]
        anchor: DivConAnchor,
        /// When/how to (re)build the objective encodings for upper bounding search
        #[arg(long, default_value_t = DivConOptions::default().build_encodings)]
        build_encodings: BuildEncodings,
        /// Log ideal and nadir points
        #[arg(long)]
        log_bound_points: bool,
    },
}

#[derive(Args)]
struct SharedArgs {
    /// Reserve variables for the encodings in advance
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().reserve_enc_vars))]
    reserve_encoding_vars: Bool,
    /// Use solution-guided search, aka phasing literals according to found solutions
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().solution_guided_search))]
    solution_guided_search: Bool,
    /// When to perform solution tightening
    #[arg(long, default_value_t = HeurImprOptions::default().solution_tightening)]
    solution_tightening: HeurImprWhen,
    /// Whether to perform core trimming in core-guided algorithms
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().core_trimming))]
    core_trimming: Bool,
    /// Whether to perform core trimming in core-guided algorithms
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().core_minimization))]
    core_minimization: Bool,
    /// Whether to perform core exhaustion in OLL
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().core_exhaustion))]
    core_exhaustion: Bool,
    /// The CaDiCaL profile to use
    #[arg(long, default_value_t = CadicalConfig::Default)]
    cadical_config: CadicalConfig,
    #[command(flatten)]
    enumeration: EnumArgs,
    #[command(flatten)]
    prepro: PreproArgs,
    #[command(flatten)]
    limits: LimitArgs,
    #[command(flatten)]
    file: FileArgs,
    #[command(flatten)]
    log: LogArgs,
}

#[derive(Args)]
struct ObjEncArgs {
    /// The encoding to use for weighted objectives
    #[arg(long, default_value_t = PbEncoding::default())]
    obj_pb_encoding: PbEncoding,
    /// The encoding to use for unweighted objectivesh
    #[arg(long, default_value_t = CardEncoding::default())]
    obj_card_encoding: CardEncoding,
}

#[derive(Args)]
struct EnumArgs {
    /// The type of enumeration to perform at each non-dominated point
    #[arg(long, default_value_t = EnumOptionsArg::NoEnum)]
    enumeration: EnumOptionsArg,
    /// The limit for enumeration at each non-dominated point (0 for no limit)
    #[arg(long, default_value_t = 0)]
    enumeration_limit: usize,
}

#[derive(Args)]
struct PreproArgs {
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
}

#[derive(Args)]
struct LimitArgs {
    /// Limit the number of non-dominated points to enumerate (0 is no limit)
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
}

impl Into<Limits> for &LimitArgs {
    fn into(self) -> Limits {
        Limits {
            pps: none_if_zero!(self.pp_limit),
            sols: none_if_zero!(self.sol_limit),
            candidates: none_if_zero!(self.candidate_limit),
            oracle_calls: none_if_zero!(self.oracle_call_limit),
        }
    }
}

#[derive(Args)]
struct FileArgs {
    /// The file format of the input file. With infer, the file format is
    /// inferred from the file extension.
    #[arg(long, value_enum, default_value_t = FileFormat::Infer)]
    file_format: FileFormat,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 0)]
    first_var_idx: u32,
    /// The path to the instance file to load. Compressed files with an
    /// extension like `.bz2` or `.gz` can be read.
    inst_path: PathBuf,
}

#[derive(Args)]
struct LogArgs {
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
    /// Verbosity of the solver output
    #[arg(short, long, default_value_t = 0)]
    verbosity: u8,
    /// Log candidates along the search trace
    #[arg(long)]
    log_candidates: bool,
    /// Log found solutions as they are discovered
    #[arg(long)]
    log_solutions: bool,
    /// Log non-dominated points as they are discovered
    #[arg(long)]
    log_non_dom: bool,
    /// Log SAT oracle calls
    #[arg(long)]
    log_oracle_calls: bool,
    /// Log heuristic objective improvement
    #[arg(long)]
    log_heuristic_obj_improvement: bool,
    /// Log extracted cores
    #[arg(long)]
    log_cores: bool,
    /// Log routine starts and ends till a given depth
    #[arg(long, default_value_t = 0)]
    log_routines: usize,
}

impl Into<LoggerConfig> for &LogArgs {
    fn into(self) -> LoggerConfig {
        LoggerConfig {
            log_candidates: self.log_candidates || self.verbosity >= 2,
            log_solutions: self.log_solutions,
            log_non_dom: self.log_non_dom || self.verbosity >= 1,
            log_oracle_calls: self.log_oracle_calls || self.verbosity >= 3,
            log_heuristic_obj_improvement: self.log_heuristic_obj_improvement
                || self.verbosity >= 3,
            log_fence: false,
            log_routines: std::cmp::max(self.log_routines, self.verbosity as usize * 2),
            log_bound_points: false,
            log_cores: self.log_cores || self.verbosity >= 2,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
pub enum PbEncoding {
    /// Generalized totalizer encoding - Joshi et al. CP'15
    #[default]
    Gte,
    /// Dynamic polynomial watchdog encoding - Paxian et al. SAT'18
    Dpw,
}

impl fmt::Display for PbEncoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PbEncoding::Gte => write!(f, "gte"),
            PbEncoding::Dpw => write!(f, "dpw"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
pub enum CardEncoding {
    /// Totalizer encoding - Ballieux and Boufkhad CP'03
    #[default]
    Tot,
}

impl fmt::Display for CardEncoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CardEncoding::Tot => write!(f, "tot"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum DivConAnchor {
    /// Linear Sat-Unsat for single-objective subproblems
    LinSu,
    /// BiOptSat (Sat-Unsat) for bi-objective subproblems
    Bioptsat,
    /// P-Minimal after the first ideal point was found
    PMinimal,
}

impl fmt::Display for DivConAnchor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DivConAnchor::LinSu => write!(f, "lin-su"),
            DivConAnchor::Bioptsat => write!(f, "bioptsat"),
            DivConAnchor::PMinimal => write!(f, "p-minimal"),
        }
    }
}

impl From<options::DivConAnchor> for DivConAnchor {
    fn from(value: options::DivConAnchor) -> Self {
        match value {
            options::DivConAnchor::LinSu => DivConAnchor::LinSu,
            options::DivConAnchor::BiOptSat => DivConAnchor::Bioptsat,
            options::DivConAnchor::PMinimal(_) => DivConAnchor::PMinimal,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum Bool {
    /// Turn on feature
    True,
    /// Torn off feature
    False,
}

impl Into<bool> for Bool {
    fn into(self) -> bool {
        self == Bool::True
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

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum CadicalConfig {
    /// Set default advanced internal options
    Default,
    /// Disable all internal preprocessing options
    Plain,
    /// Set internal options to target satisfiable instances
    Sat,
    /// Set internal options to target unsatisfiable instances
    Unsat,
}

impl fmt::Display for CadicalConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CadicalConfig::Default => write!(f, "default"),
            CadicalConfig::Plain => write!(f, "plain"),
            CadicalConfig::Sat => write!(f, "sat"),
            CadicalConfig::Unsat => write!(f, "unsat"),
        }
    }
}

impl From<CadicalConfig> for rustsat_cadical::Config {
    fn from(cfg: CadicalConfig) -> Self {
        match cfg {
            CadicalConfig::Default => rustsat_cadical::Config::Default,
            CadicalConfig::Plain => rustsat_cadical::Config::Plain,
            CadicalConfig::Sat => rustsat_cadical::Config::SAT,
            CadicalConfig::Unsat => rustsat_cadical::Config::UNSAT,
        }
    }
}

#[derive(Default, Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum EnumOptionsArg {
    #[default]
    /// Don't enumerate at each non-dominated point
    NoEnum,
    /// Enumerate Pareto-optimal solutions (with an optional limit) at each
    /// non-dominated point using the provided blocking clause generator
    Solutions,
    /// Enumerate Pareto-MCSs (with an optional limit) at each non-dominated point
    ParetoMCS,
}

impl fmt::Display for EnumOptionsArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EnumOptionsArg::NoEnum => write!(f, "no-enum"),
            EnumOptionsArg::Solutions => write!(f, "solutions"),
            EnumOptionsArg::ParetoMCS => write!(f, "pareto-mcs"),
        }
    }
}

pub struct Cli {
    pub limits: Limits,
    pub file_format: FileFormat,
    pub opb_options: fio::opb::Options,
    pub inst_path: PathBuf,
    pub preprocessing: bool,
    pub maxpre_techniques: String,
    pub reindexing: bool,
    pub maxpre_reindexing: bool,
    pub cadical_config: rustsat_cadical::Config,
    stdout: BufferWriter,
    stderr: BufferWriter,
    print_solver_config: bool,
    print_solutions: bool,
    print_stats: bool,
    color: concolor_clap::Color,
    logger_config: LoggerConfig,
    pub alg: Algorithm,
}

pub enum Algorithm {
    PMinimal(KernelOptions),
    BiOptSat(KernelOptions, PbEncoding, CardEncoding),
    LowerBounding(KernelOptions),
    DivCon(DivConOptions),
}

impl fmt::Display for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Algorithm::PMinimal(..) => write!(f, "p-pminimal"),
            Algorithm::BiOptSat(..) => write!(f, "bioptsat"),
            Algorithm::LowerBounding(..) => write!(f, "lower-bounding"),
            Algorithm::DivCon(..) => write!(f, "div-con"),
        }
    }
}

impl Cli {
    pub fn init() -> Self {
        let stdout = |color: concolor_clap::Color| {
            BufferWriter::stdout(match color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stderr) {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            })
        };
        let stderr = |color: concolor_clap::Color| {
            BufferWriter::stderr(match color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stderr) {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            })
        };
        let kernel_opts = |shared: SharedArgs| KernelOptions {
            enumeration: match shared.enumeration.enumeration {
                EnumOptionsArg::NoEnum => EnumOptions::NoEnum,
                EnumOptionsArg::Solutions => {
                    EnumOptions::Solutions(none_if_zero!(shared.enumeration.enumeration_limit))
                }
                EnumOptionsArg::ParetoMCS => {
                    EnumOptions::PMCSs(none_if_zero!(shared.enumeration.enumeration_limit))
                }
            },
            reserve_enc_vars: shared.reserve_encoding_vars.into(),
            heuristic_improvements: HeurImprOptions {
                solution_tightening: shared.solution_tightening,
            },
            solution_guided_search: shared.solution_guided_search.into(),
            core_trimming: shared.core_trimming.into(),
            core_minimization: shared.core_minimization.into(),
            core_exhaustion: shared.core_exhaustion.into(),
        };
        let cli = match CliArgs::parse().command {
            AlgorithmCommand::PMinimal { shared } => Cli {
                limits: (&shared.limits).into(),
                file_format: shared.file.file_format,
                opb_options: fio::opb::Options {
                    first_var_idx: shared.file.first_var_idx,
                    ..Default::default()
                },
                inst_path: shared.file.inst_path.clone(),
                preprocessing: shared.prepro.preprocessing.into(),
                maxpre_techniques: shared.prepro.maxpre_techniques.clone(),
                reindexing: shared.prepro.reindexing.into(),
                maxpre_reindexing: shared.prepro.maxpre_reindexing.into(),
                cadical_config: shared.cadical_config.into(),
                stdout: stdout(shared.log.color),
                stderr: stderr(shared.log.color),
                print_solver_config: shared.log.print_solver_config,
                print_solutions: shared.log.print_solutions,
                print_stats: !shared.log.no_print_stats,
                color: shared.log.color,
                logger_config: (&shared.log).into(),
                alg: Algorithm::PMinimal(kernel_opts(shared)),
            },
            AlgorithmCommand::Bioptsat { shared, obj_encs } => Cli {
                limits: (&shared.limits).into(),
                file_format: shared.file.file_format,
                opb_options: fio::opb::Options {
                    first_var_idx: shared.file.first_var_idx,
                    ..Default::default()
                },
                inst_path: shared.file.inst_path.clone(),
                preprocessing: shared.prepro.preprocessing.into(),
                maxpre_techniques: shared.prepro.maxpre_techniques.clone(),
                reindexing: shared.prepro.reindexing.into(),
                maxpre_reindexing: shared.prepro.maxpre_reindexing.into(),
                cadical_config: shared.cadical_config.into(),
                stdout: stdout(shared.log.color),
                stderr: stderr(shared.log.color),
                print_solver_config: shared.log.print_solver_config,
                print_solutions: shared.log.print_solutions,
                print_stats: !shared.log.no_print_stats,
                color: shared.log.color,
                logger_config: (&shared.log).into(),
                alg: Algorithm::BiOptSat(kernel_opts(shared), obj_encs.obj_pb_encoding, obj_encs.obj_card_encoding),
            },
            AlgorithmCommand::LowerBounding { shared, log_fence } => Cli {
                limits: (&shared.limits).into(),
                file_format: shared.file.file_format,
                opb_options: fio::opb::Options {
                    first_var_idx: shared.file.first_var_idx,
                    ..Default::default()
                },
                inst_path: shared.file.inst_path.clone(),
                preprocessing: shared.prepro.preprocessing.into(),
                maxpre_techniques: shared.prepro.maxpre_techniques.clone(),
                reindexing: shared.prepro.reindexing.into(),
                maxpre_reindexing: shared.prepro.maxpre_reindexing.into(),
                cadical_config: shared.cadical_config.into(),
                stdout: stdout(shared.log.color),
                stderr: stderr(shared.log.color),
                print_solver_config: shared.log.print_solver_config,
                print_solutions: shared.log.print_solutions,
                print_stats: !shared.log.no_print_stats,
                color: shared.log.color,
                logger_config: {
                    let mut conf: LoggerConfig = (&shared.log).into();
                    conf.log_fence = log_fence || shared.log.verbosity >= 2;
                    conf
                },
                alg: Algorithm::LowerBounding(kernel_opts(shared)),
            },
            AlgorithmCommand::DivCon {
                shared,
                anchor,
                build_encodings,
                log_bound_points,
            } => Cli {
                limits: (&shared.limits).into(),
                file_format: shared.file.file_format,
                opb_options: fio::opb::Options {
                    first_var_idx: shared.file.first_var_idx,
                    ..Default::default()
                },
                inst_path: shared.file.inst_path.clone(),
                preprocessing: shared.prepro.preprocessing.into(),
                maxpre_techniques: shared.prepro.maxpre_techniques.clone(),
                reindexing: shared.prepro.reindexing.into(),
                maxpre_reindexing: shared.prepro.maxpre_reindexing.into(),
                cadical_config: shared.cadical_config.into(),
                stdout: stdout(shared.log.color),
                stderr: stderr(shared.log.color),
                print_solver_config: shared.log.print_solver_config,
                print_solutions: shared.log.print_solutions,
                print_stats: !shared.log.no_print_stats,
                color: shared.log.color,
                logger_config: {
                    let mut conf: LoggerConfig = (&shared.log).into();
                    conf.log_bound_points = log_bound_points || shared.log.verbosity >= 2;
                    conf
                },
                alg: Algorithm::DivCon(DivConOptions {
                    kernel: kernel_opts(shared),
                    anchor: match anchor {
                        DivConAnchor::LinSu => options::DivConAnchor::LinSu,
                        DivConAnchor::Bioptsat => options::DivConAnchor::BiOptSat,
                        DivConAnchor::PMinimal => {
                            options::DivConAnchor::PMinimal(options::SubProblemSize::Smaller(0))
                        }
                    },
                    build_encodings,
                }),
            },
        };
        #[cfg(any(not(feature = "sol-tightening"), not(feature = "phasing")))]
        match &cli.alg {
            Algorithm::PMinimal(opts)
            | Algorithm::PMinimalDpw(opts)
            | Algorithm::LowerBounding(opts)
            | Algorithm::TriCore(opts)
            | Algorithm::DivCon(DivConOptions { kernel: opts, .. }) => {
                #[cfg(not(feature = "sol-tightening"))]
                if opts.heuristic_improvements.solution_tightening != HeurImprWhen::Never {
                    cli.warning(
                        "requested solution tightening but solver is built without this feature",
                    )
                    .expect("IO error during CLI initialization");
                }
                #[cfg(not(feature = "phasing"))]
                if opts.solution_guided_search {
                    cli.warning(
                        "requested solution guided search but solver is built without this feature",
                    )
                    .expect("IO error during CLI initialization");
                }
            }
        }
        cli
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
            routine_stack: vec![],
        }
    }

    pub fn warning(&self, msg: &str) -> Result<(), IOError> {
        let mut buffer = self.stderr.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Yellow)))?;
        write!(buffer, "warning")?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(buffer, ": ")?;
        buffer.reset()?;
        writeln!(buffer, "{}", msg)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn error(&self, msg: &str) -> Result<(), IOError> {
        let mut buffer = self.stderr.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Red)))?;
        write!(buffer, "error")?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(buffer, ": ")?;
        buffer.reset()?;
        writeln!(buffer, "{}", msg)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn info(&self, msg: &str) -> Result<(), IOError> {
        let mut buffer = self.stdout.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
        write!(buffer, "info")?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        write!(buffer, ": ")?;
        buffer.reset()?;
        writeln!(buffer, "{}", msg)?;
        self.stdout.print(&buffer)?;
        Ok(())
    }

    pub fn log_termination(&self, term: &Termination) -> Result<(), IOError> {
        let msg = &format!("{}", term);
        if term.is_error() {
            self.error(msg)
        } else {
            self.warning(msg)
        }
    }

    pub fn print_header(&self) -> Result<(), IOError> {
        let mut buffer = self.stdout.buffer();
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Green)))?;
        write!(buffer, "{}", crate_name!())?;
        buffer.reset()?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        writeln!(buffer, " ({})", crate_version!())?;
        buffer.reset()?;
        writeln!(buffer, "{}", crate_authors!("\n"))?;
        write!(buffer, "algorithm: ")?;
        buffer.set_color(ColorSpec::new().set_fg(Some(Color::Green)))?;
        writeln!(buffer, "{}", self.alg)?;
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
            write!(buffer, "Solver Config")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(buffer, ": ")?;
            buffer.reset()?;
            match self.alg {
                Algorithm::PMinimal(opts) | Algorithm::LowerBounding(opts) => {
                    Self::print_parameter(
                        &mut buffer,
                        "enumeration",
                        EnumPrinter::new(opts.enumeration),
                    )?;
                    Self::print_parameter(&mut buffer, "reserve-enc-vars", opts.reserve_enc_vars)?;
                }
                Algorithm::BiOptSat(opts, pb_enc, card_enc) => {
                    Self::print_parameter(
                        &mut buffer,
                        "enumeration",
                        EnumPrinter::new(opts.enumeration),
                    )?;
                    Self::print_parameter(&mut buffer, "reserve-enc-vars", opts.reserve_enc_vars)?;
                    Self::print_parameter(&mut buffer, "obj-pb-encoding", pb_enc)?;
                    Self::print_parameter(&mut buffer, "obj-card-encoding", card_enc)?;
                }
                Algorithm::DivCon(opts) => {
                    Self::print_parameter(
                        &mut buffer,
                        "enumeration",
                        EnumPrinter::new(opts.kernel.enumeration),
                    )?;
                    Self::print_parameter(
                        &mut buffer,
                        "reserve-enc-vars",
                        opts.kernel.reserve_enc_vars,
                    )?;
                    Self::print_parameter(&mut buffer, "anchor", opts.anchor)?;
                }
            }
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

    pub fn print_pareto_front<S: Clone + Eq + fmt::Display>(
        &self,
        pareto_front: ParetoFront<S>,
    ) -> Result<(), IOError> {
        let mut buffer = self.stdout.buffer();
        Self::start_block(&mut buffer)?;
        buffer.set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))?;
        write!(buffer, "Discovered Pareto Front")?;
        buffer.set_color(ColorSpec::new().set_bold(true))?;
        writeln!(buffer, ": ")?;
        buffer.reset()?;
        pareto_front.into_iter().fold(Ok(()), |res, pp| {
            if res.is_ok() {
                self.print_non_dom(&mut buffer, pp)
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
            write!(buffer, "Solver Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(buffer, ": ")?;
            buffer.reset()?;
            Self::print_parameter(&mut buffer, "n-solve-calls", stats.n_solve_calls)?;
            Self::print_parameter(&mut buffer, "n-solutions", stats.n_solutions)?;
            Self::print_parameter(&mut buffer, "n-non-dominated", stats.n_non_dominated)?;
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
            write!(buffer, "Oracle Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(buffer, ": ")?;
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
            write!(buffer, "Encoding Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(buffer, ": ")?;
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
            write!(buffer, "MaxPre Stats")?;
            buffer.reset()?;
            buffer.set_color(ColorSpec::new().set_bold(true))?;
            writeln!(buffer, ": ")?;
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

    fn print_non_dom<S: Clone + Eq + fmt::Display>(
        &self,
        buffer: &mut Buffer,
        non_dom: NonDomPoint<S>,
    ) -> Result<(), IOError> {
        Self::start_block(buffer)?;
        buffer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
        write!(buffer, "Non-dominated Point")?;
        buffer.reset()?;
        writeln!(
            buffer,
            ": costs: {}; n-sols: {}",
            VecPrinter::new(non_dom.costs()),
            non_dom.n_sols()
        )?;
        if self.print_solutions {
            non_dom.into_iter().fold(Ok(()), |res, sol| {
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
    log_non_dom: bool,
    log_oracle_calls: bool,
    log_heuristic_obj_improvement: bool,
    log_fence: bool,
    log_routines: usize,
    log_bound_points: bool,
    log_cores: bool,
}

pub struct CliLogger {
    stdout: BufferWriter,
    config: LoggerConfig,
    routine_stack: Vec<(&'static str, ProcessTime)>,
}

impl WriteSolverLog for CliLogger {
    fn log_candidate(&mut self, costs: &[usize], phase: Phase) -> Result<(), LoggerError> {
        if self.config.log_candidates {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "candidate")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": costs: {}; phase: {}; cpu-time: {}",
                VecPrinter::new(costs),
                phase,
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_oracle_call(&mut self, result: SolverResult) -> Result<(), LoggerError> {
        if self.config.log_oracle_calls {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "oracle call")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": result: {}; cpu-time: {}",
                result,
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_solution(&mut self) -> Result<(), LoggerError> {
        if self.config.log_solutions {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "solution")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": cpu-time: {}",
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_non_dominated(&mut self, non_dominated: &NonDomPoint) -> Result<(), LoggerError> {
        if self.config.log_non_dom {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "non-dominated point")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": costs: {}; n-sols: {}; cpu-time: {}",
                VecPrinter::new(non_dominated.costs()),
                non_dominated.n_sols(),
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
    ) -> Result<(), LoggerError> {
        if self.config.log_heuristic_obj_improvement {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "heuristic objective improvement")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": obj-idx: {}; apparent-cost: {}; improved-cost: {}; cpu-time: {}",
                obj_idx,
                apparent_cost,
                improved_cost,
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_fence(&mut self, fence: &[usize]) -> Result<(), LoggerError> {
        if self.config.log_fence {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "fence update")?;
            buffer.reset()?;
            writeln!(buffer, ": {}", VecPrinter::new(&fence))?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_routine_start(&mut self, desc: &'static str) -> Result<(), LoggerError> {
        self.routine_stack.push((desc, ProcessTime::now()));

        if self.config.log_routines >= self.routine_stack.len() {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Green)))?;
            write!(buffer, ">>> routine start")?;
            buffer.reset()?;
            writeln!(buffer, ": {}", desc)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_routine_end(&mut self) -> Result<(), LoggerError> {
        let (desc, start) = self.routine_stack.pop().expect("routine stack out of sync");

        if self.config.log_routines > self.routine_stack.len() {
            let duration = ProcessTime::now().duration_since(start);

            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Red)))?;
            write!(buffer, "<<< routine end")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": {}; duration: {}",
                desc,
                DurPrinter::new(duration)
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_end_solve(&mut self) -> Result<(), LoggerError> {
        while !self.routine_stack.is_empty() {
            self.log_routine_end()?;
        }
        Ok(())
    }

    fn log_ideal(&mut self, ideal: &[usize]) -> Result<(), LoggerError> {
        if self.config.log_bound_points {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
            write!(buffer, "ideal point")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": costs: {}; cpu-time: {}",
                VecPrinter::new(ideal),
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_nadir(&mut self, nadir: &[usize]) -> Result<(), LoggerError> {
        if self.config.log_bound_points {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
            write!(buffer, "nadir point")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": costs: {}; cpu-time: {}",
                VecPrinter::new(nadir),
                DurPrinter::new(ProcessTime::now().as_duration()),
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_core(&mut self, weight: usize, len: usize, red_len: usize) -> Result<(), LoggerError> {
        if self.config.log_cores {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "extracted core")?;
            buffer.reset()?;
            writeln!(
                buffer,
                ": weight: {}; original-len: {}; reduced-len: {}",
                weight, len, red_len,
            )?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
    }

    fn log_core_exhaustion(&mut self, exhausted: usize, weight: usize) -> Result<(), LoggerError> {
        if self.config.log_cores {
            let mut buffer = self.stdout.buffer();
            buffer.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)))?;
            write!(buffer, "exhausted core")?;
            buffer.reset()?;
            writeln!(buffer, ": exhausted: {}; weight: {}", exhausted, weight)?;
            self.stdout.print(&buffer)?;
        }
        Ok(())
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
