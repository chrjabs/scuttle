//! # Command Line Interface for the Solver Binary

use std::{fmt, path::PathBuf};

use ::tracing::Level;
use clap::{Args, Parser, Subcommand, ValueEnum, builder::styling};
use rustsat::instances::fio;
use scuttle_core::{
    Limits,
    options::{
        AfterCbOptions, CandidateSeeding, CoreBoostingOptions, CoreExtraction, CoreMinimization,
        EnumOptions, HeurImprOptions, HeurImprWhen, IhsCbOptions, IhsCbTreatment, IhsOptions,
        KernelOptions, MipPdOptions, ObjectiveMultipliers, Stratification,
    },
    prepro::FileFormat,
};

use crate::tracing;

macro_rules! none_if_zero {
    ($val:expr_2021) => {
        if $val == 0 { None } else { Some($val) }
    };
}

/// Cargo's color style
/// [source](https://github.com/crate-ci/clap-cargo/blob/master/src/style.rs)
const STYLES: styling::Styles = styling::Styles::styled()
    .header(styling::AnsiColor::Green.on_default().bold())
    .usage(styling::AnsiColor::Green.on_default().bold())
    .literal(styling::AnsiColor::Cyan.on_default().bold())
    .placeholder(styling::AnsiColor::Cyan.on_default())
    .error(styling::AnsiColor::Red.on_default().bold())
    .valid(styling::AnsiColor::Cyan.on_default().bold())
    .invalid(styling::AnsiColor::Yellow.on_default().bold());

#[derive(Parser)]
#[command(author, version, about, long_about = None, styles = STYLES)]
struct CliArgs {
    #[command(subcommand)]
    command: AlgorithmCommand,
    /// The random seed to use for random operations
    #[arg(long, default_value_t = KernelOptions::default().random_seed, global = true)]
    random_seed: u64,
    /// Reserve variables for the encodings in advance
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().reserve_enc_vars), global = true)]
    reserve_encoding_vars: Bool,
    /// Use solution-guided search, aka phasing literals according to found solutions
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().solution_guided_search), global = true)]
    solution_guided_search: Bool,
    /// When to perform solution tightening
    #[arg(long, default_value_t = HeurImprOptions::default().solution_tightening, global = true)]
    solution_tightening: HeurImprWhen,
    /// What type of core minimization to perform in OLL (core boosting)
    #[arg(long, alias = "core-minimization", default_value_t = CoreMinimization::default(), global = true)]
    oll_core_minimization: CoreMinimization,
    /// Whether to perform core exhaustion in OLL
    #[arg(long, default_value_t = Bool::from(KernelOptions::default().core_exhaustion), global = true)]
    core_exhaustion: Bool,
    /// Stratification in core-based algorithms
    ///
    /// Possible values:
    /// - `none`
    /// - `all`
    /// - any combination of the following, separated by `+`
    ///     - `strat`
    ///     - `exp-strat`
    ///     - `multi-level`
    ///     - `dist`
    #[arg(long, alias = "strat", default_value_t = KernelOptions::default().stratification, global = true)]
    stratification: Stratification,
    /// The CaDiCaL profile to use
    #[arg(long, default_value_t = CadicalConfig::Default, global = true)]
    cadical_config: CadicalConfig,
    #[command(flatten)]
    enumeration: EnumArgs,
    #[command(flatten)]
    prepro: PreproArgs,
    #[command(flatten)]
    limits: LimitArgs,
    #[command(flatten)]
    log: LogArgs,
    /// Whether to perform core boosting before running the algorithm
    #[arg(long, default_value_t = Bool::True, global = true, help_heading = "Core-boosting options")]
    core_boosting: Bool,
}

impl CliArgs {
    fn kernel_opts(&self) -> KernelOptions {
        KernelOptions {
            random_seed: self.random_seed,
            enumeration: match self.enumeration.enumeration {
                EnumOptionsArg::NoEnum => EnumOptions::NoEnum,
                EnumOptionsArg::Solutions => {
                    EnumOptions::Solutions(none_if_zero!(self.enumeration.enumeration_limit))
                }
                EnumOptionsArg::ParetoMCS => {
                    EnumOptions::PMCSs(none_if_zero!(self.enumeration.enumeration_limit))
                }
            },
            reserve_enc_vars: self.reserve_encoding_vars.into(),
            heuristic_improvements: HeurImprOptions {
                solution_tightening: self.solution_tightening,
            },
            solution_guided_search: self.solution_guided_search.into(),
            core_minimization: self.oll_core_minimization,
            core_exhaustion: self.core_exhaustion.into(),
            store_cnf: false,
            stratification: self.stratification,
        }
    }
}

#[derive(Subcommand, Clone)]
enum AlgorithmCommand {
    /// P-Minimal model enumeration - Soh et al. CP'17
    #[command(alias = "pmin")]
    PMinimal {
        #[command(flatten)]
        cb: CoreBoostingArgs,
        #[command(flatten)]
        file: FileArgs,
        #[command(flatten)]
        proof: ProofArgs,
    },
    /// BiOptSat Linear Sat-Unsat - Jabs et al. SAT'22
    #[command(alias = "bos")]
    Bioptsat {
        #[command(flatten)]
        cb: CoreBoostingArgs,
        #[command(flatten)]
        obj_encs: ObjEncArgs,
        #[command(flatten)]
        file: FileArgs,
        #[command(flatten)]
        proof: ProofArgs,
    },
    /// Lower-bounding search - Cortes et al. TACAS'23
    #[command(alias = "lb")]
    LowerBounding {
        #[command(flatten)]
        cb: CoreBoostingArgs,
        #[command(flatten)]
        file: FileArgs,
        #[command(flatten)]
        proof: ProofArgs,
    },
    /// Paretop-k IHS
    #[command(alias = "ihs")]
    ParetoIhs {
        /// The hitting set solver to use
        #[arg(long, alias = "hss", default_value_t = HittingSetSolver::default())]
        hitting_set_solver: HittingSetSolver,
        /// The number of threads for the hitting set solver
        #[arg(long, alias = "hitting-set-solver-threads", default_value_t = hitting_sets::Threads::default())]
        hss_threads: hitting_sets::Threads,
        /// Whether to seed constraints over only objective variables into the hitting set solver
        #[arg(long, default_value_t = Bool::from(IhsOptions::default().seeding))]
        seeding: Bool,
        /// The core extraction method to use in IHS
        #[arg(long, default_value_t = IhsOptions::default().core_extraction)]
        ihs_core_extraction: CoreExtraction,
        /// Candidate seeding
        #[arg(long, default_value_t = CandidateSeeding::default())]
        candidate_seeding: CandidateSeeding,
        /// What type of core minimization to perform in the IHS loop
        #[arg(long, default_value_t = IhsOptions::default().core_minimization, global = true)]
        ihs_core_minimization: CoreMinimization,
        /// Use upper bound solutions as starting point for the hitting set solver
        #[arg(long, default_value_t = Bool::from(IhsOptions::default().starting_points), global = true)]
        use_starting_points: Bool,
        /// Use randomized objective multipliers for evaluating robustness
        #[arg(long, default_value_t = ObjectiveMultipliers::default(), global = true)]
        multipliers: ObjectiveMultipliers,
        /// Precompute a given number of lexicographic optima, which is possible without adding PD
        /// cuts
        ///
        /// It is recommended to not set this higher than 8
        #[arg(long, default_value_t = IhsOptions::default().precompute_lexicographic, global = true)]
        precompute_lexicographic: usize,
        /// The maximum number of allowed failures when precomputing lexicographic optima
        #[arg(long, default_value_t = IhsOptions::default().max_failed_precompute_lex, global = true)]
        max_failed_precompute_lex: usize,
        /// Whether to precompute lexicographic solutions when the instance is fully seeded
        #[arg(long, default_value_t = Bool::from(IhsOptions::default().fully_seeded_precompute_lex), global = true)]
        fully_seeded_precompute_lex: Bool,
        /// Use reduced cost fixing
        #[arg(long, default_value_t = Bool::from(IhsOptions::default().reduced_cost_fixing), global = true)]
        reduced_cost_fixing: Bool,
        /// Use upper bounds
        #[arg(long, default_value_t = Bool::from(IhsOptions::default().upper_bounds), global = true)]
        upper_bounds: Bool,
        #[command(flatten)]
        cb: IhsCoreBoostingArgs,
        #[command(flatten)]
        file: FileArgs,
    },
    /// MIP with PD cuts
    #[command(alias = "mip")]
    MipPd {
        /// The random seed to use for random operations
        #[arg(long, default_value_t = MipPdOptions::default().random_seed, global = true)]
        random_seed: u64,
        /// The hitting set solver to use
        #[arg(long, default_value_t = HittingSetSolver::default())]
        mip_solver: HittingSetSolver,
        /// The number of threads for the hitting set solver
        #[arg(long, default_value_t = hitting_sets::Threads::default())]
        threads: hitting_sets::Threads,
        /// Use randomized objective multipliers for evaluating robustness
        #[arg(long, default_value_t = ObjectiveMultipliers::default(), global = true)]
        multipliers: ObjectiveMultipliers,
        /// Precompute a given number of lexicographic optima, which is possible without adding PD
        /// cuts
        ///
        /// It is recommended to not set this higher than 8
        #[arg(long, default_value_t = IhsOptions::default().precompute_lexicographic, global = true)]
        precompute_lexicographic: usize,
        #[command(flatten)]
        file: FileArgs,
    },
    /// SAT-based Leximax optimization - Cabral et al. SAT'22 (Sat-Unsat variant)
    #[command(alias = "lm-su")]
    LeximaxSatUnsat {
        #[command(flatten)]
        cb: CoreBoostingArgs,
        #[command(flatten)]
        file: FileArgs,
        #[command(flatten)]
        proof: ProofArgs,
    },
}

#[derive(Args, Copy, Clone)]
struct ObjEncArgs {
    /// The encoding to use for weighted objectives
    #[arg(long, default_value_t = PbEncoding::default())]
    obj_pb_encoding: PbEncoding,
    /// The encoding to use for unweighted objectivesh
    #[arg(long, default_value_t = CardEncoding::default())]
    obj_card_encoding: CardEncoding,
}

#[derive(Args, Copy, Clone)]
#[command(next_help_heading = "Core-boosting options")]
struct CoreBoostingArgs {
    /// If true, don't merge OLL totalizers into GTE but ignore the totalizer structure.
    #[arg(long, default_value_t = CoreBoostingOptions::default().rebase.into(), global = true)]
    rebase_encodings: Bool,
    /// Whether to reset the oracle after finding a global ideal point, i.e., core boosting
    #[arg(long, default_value_t = matches!(CoreBoostingOptions::default().after, AfterCbOptions::Reset).into(), global = true)]
    reset_after_cb: Bool,
    /// Whether to perform inprocessing, i.e., preprocessing after core boosting
    #[arg(long, default_value_t = matches!(CoreBoostingOptions::default().after, AfterCbOptions::Inpro(_)).into())]
    #[cfg(feature = "maxpre")]
    inprocessing: Bool,
    /// [Disabled at compile time] Whether to perform inprocessing, i.e., preprocessing after core boosting
    #[arg(long, default_value_t = Disabled::False, global = true)]
    #[cfg(not(feature = "maxpre"))]
    inprocessing: Disabled,
}

impl CoreBoostingArgs {
    fn parse(self, #[cfg(feature = "maxpre")] prepro_techs: String) -> (CoreBoostingOptions, bool) {
        let after = if self.reset_after_cb.into() {
            AfterCbOptions::Reset
        } else {
            AfterCbOptions::Nothing
        };
        #[cfg(feature = "maxpre")]
        let after = if self.inprocessing.into() {
            AfterCbOptions::Inpro(prepro_techs)
        } else {
            after
        };
        let store_cnf = self.inprocessing.into() || self.reset_after_cb.into();
        (
            CoreBoostingOptions {
                rebase: self.rebase_encodings.into(),
                after,
            },
            store_cnf,
        )
    }
}

#[derive(Args, Copy, Clone)]
struct IhsCoreBoostingArgs {
    /// How core boosting should be treated in the IHS algorithm
    #[arg(long, default_value_t = IhsCbTreatment::default(), help_heading = "Core-boosting options")]
    ihs_cb_treatment: IhsCbTreatment,
}

impl From<IhsCoreBoostingArgs> for IhsCbOptions {
    fn from(val: IhsCoreBoostingArgs) -> Self {
        IhsCbOptions {
            treatment: val.ihs_cb_treatment,
        }
    }
}

#[derive(ValueEnum, Copy, Clone, Default)]
pub enum HittingSetSolver {
    /// The HiGHS MIP solver
    #[cfg_attr(not(any(feature = "gurobi9", feature = "gurobi12")), default)]
    Highs,
    #[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
    #[cfg_attr(any(feature = "gurobi9", feature = "gurobi12"), default)]
    #[cfg_attr(any(feature = "gurobi9"), value(alias = "gurobi9"))]
    #[cfg_attr(any(feature = "gurobi12"), value(alias = "gurobi12"))]
    /// The Gurobi MIP solver
    Gurobi,
}

impl fmt::Display for HittingSetSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HittingSetSolver::Highs => write!(f, "highs"),
            #[cfg(feature = "gurobi9")]
            HittingSetSolver::Gurobi => write!(f, "gurobi9"),
            #[cfg(feature = "gurobi12")]
            HittingSetSolver::Gurobi => write!(f, "gurobi12"),
        }
    }
}

#[derive(Args, Copy, Clone)]
#[command(next_help_heading = "Enumeration options")]
struct EnumArgs {
    /// The type of enumeration to perform at each non-dominated point
    #[arg(long, default_value_t = EnumOptionsArg::NoEnum, global = true)]
    enumeration: EnumOptionsArg,
    /// The limit for enumeration at each non-dominated point (0 for no limit)
    #[arg(long, default_value_t = 0, global = true)]
    enumeration_limit: usize,
}

#[derive(Args)]
#[command(next_help_heading = "Preprocessing options")]
struct PreproArgs {
    /// Reindex the variables in the instance before solving
    #[arg(long, default_value_t = Bool::from(false), global = true)]
    reindexing: Bool,
    /// Preprocess the instance with MaxPre before solving
    #[arg(long, default_value_t = Bool::from(false), global = true)]
    #[cfg(feature = "maxpre")]
    preprocessing: Bool,
    /// [Disabled at compile time] Preprocess the instance with MaxPre before solving
    #[arg(long, default_value_t = Disabled::False, global = true)]
    #[cfg(not(feature = "maxpre"))]
    preprocessing: Disabled,
    /// The preprocessing technique string to use
    #[arg(long, default_value_t = String::from("[[uvsrgc]VRTG]"), global = true)]
    maxpre_techniques: String,
    /// Reindex the variables in MaxPre
    #[arg(long, default_value_t = Bool::from(false), global = true)]
    #[cfg(feature = "maxpre")]
    maxpre_reindexing: Bool,
    /// [Disabled at compile time] Reindex the variables in MaxPre
    #[arg(long, default_value_t = Disabled::False, global = true)]
    #[cfg(not(feature = "maxpre"))]
    maxpre_reindexing: Disabled,
}

#[derive(Args, Copy, Clone)]
#[command(next_help_heading = "Solver limits")]
struct LimitArgs {
    /// Limit the number of non-dominated points to enumerate (0 is no limit)
    #[arg(
        long,
        alias = "pareto-point-limit",
        alias = "non-dom-limit",
        alias = "non-dominated-point-limit",
        default_value_t = 0,
        global = true
    )]
    pp_limit: usize,
    /// Limit the number of solutions to enumerate (0 is no limit)
    #[arg(long, alias = "solution-limit", default_value_t = 0, global = true)]
    sol_limit: usize,
    /// Limit the number of candidates to consider (0 is not limit)
    #[arg(long, default_value_t = 0, global = true)]
    candidate_limit: usize,
    /// Limit the number of SAT oracle calls (0 is not limit)
    #[arg(long, default_value_t = 0, global = true)]
    oracle_call_limit: usize,
}

impl From<LimitArgs> for Limits {
    fn from(value: LimitArgs) -> Self {
        Limits {
            pps: none_if_zero!(value.pp_limit),
            sols: none_if_zero!(value.sol_limit),
            candidates: none_if_zero!(value.candidate_limit),
            oracle_calls: none_if_zero!(value.oracle_call_limit),
        }
    }
}

#[derive(Args, Clone)]
#[command(next_help_heading = "Input file")]
struct FileArgs {
    /// The file format of the input file. With infer, the file format is
    /// inferred from the file extension.
    #[arg(long, value_enum, default_value_t = FileFormat::Infer, global=true)]
    file_format: FileFormat,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1, global = true)]
    first_var_idx: u32,
    /// The path to the instance file to load. Compressed files with an
    /// extension like `.bz2` or `.gz` can be read.
    inst_path: PathBuf,
}

#[derive(ValueEnum, Clone, Copy, Debug, Default)]
pub enum ColorOpt {
    Always,
    #[default]
    Auto,
    Never,
}

impl fmt::Display for ColorOpt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ColorOpt::Always => write!(f, "always"),
            ColorOpt::Auto => write!(f, "auto"),
            ColorOpt::Never => write!(f, "never"),
        }
    }
}

#[derive(Args, Copy, Clone)]
#[command(next_help_heading = "Printing options")]
struct LogArgs {
    /// Print the solver configuration
    #[arg(long, global = true, alias = "config")]
    print_solver_config: bool,
    /// Print solutions as binary assignments
    #[arg(long, global = true, alias = "solutions", alias = "sols")]
    print_solutions: bool,
    /// Don't print statistics
    #[arg(
        long,
        global = true,
        alias = "no-stats",
        alias = "no-statistics",
        alias = "no-print-statistics"
    )]
    no_print_stats: bool,
    /// When to enable coloured output
    #[arg(long, global = true, default_value_t = ColorOpt::default())]
    color: ColorOpt,
    /// Verbosity of the solver output
    #[command(flatten)]
    verbosity: clap_verbosity_flag::Verbosity<clap_verbosity_flag::WarnLevel>,
    /// Whether to print timestamps
    #[arg(long, global=true, default_value_t = Bool::from(true))]
    timestamps: Bool,
    /// Log candidates along the search trace
    #[arg(long, global = true)]
    log_candidates: bool,
    /// Log found solutions as they are discovered
    #[arg(long, global = true)]
    log_solutions: bool,
    /// Log non-dominated points as they are discovered
    #[arg(long, global = true, alias = "log_non_dom")]
    log_non_dominated: bool,
    /// Log SAT oracle calls
    #[arg(long, global = true)]
    log_oracle_calls: bool,
    /// Log ideal and nadir points
    #[arg(long, global = true)]
    log_bound_points: bool,
}

impl From<LogArgs> for Option<tracing::Options> {
    fn from(value: LogArgs) -> Self {
        let level = value.verbosity.tracing_level()?;
        Some(tracing::Options {
            color: value.color,
            print_config: value.print_solver_config || level >= Level::DEBUG,
            timestamps: value.timestamps.into(),
            candidates: value.log_candidates,
            solutions: value.log_solutions,
            non_dominated: value.log_non_dominated,
            oracle_calls: value.log_oracle_calls,
            bound_points: value.log_bound_points,
            level,
        })
    }
}

impl From<LogArgs> for tracing::WrapUpOptions {
    fn from(value: LogArgs) -> Self {
        tracing::WrapUpOptions {
            color: value.color,
            print_solutions: value.print_solutions,
            print_stats: !value.no_print_stats,
        }
    }
}

#[derive(Args, Clone)]
struct ProofArgs {
    /// The path to write the VeriPB proof to. If not provided, will not write a proof.
    proof_path: Option<PathBuf>,
    /// The path to output the VeriPB input to.
    ///
    /// VeriPB does not natively understand multi-objective input files, so Scuttle will write only
    /// the constraints to a separate OPB file for VeriPB to use as input, while the objectives are
    /// written to the proof as an order.
    veripb_input_path: Option<PathBuf>,
}

impl ProofArgs {
    fn proof_paths(self) -> Option<(PathBuf, Option<PathBuf>)> {
        self.proof_path.map(|pp| (pp, self.veripb_input_path))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
pub enum PbEncoding {
    /// Generalized totalizer encoding - Joshi et al. CP'15
    #[default]
    Gte,
    // /// Dynamic polynomial watchdog encoding - Paxian et al. SAT'18
    // Dpw,
}

impl fmt::Display for PbEncoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PbEncoding::Gte => write!(f, "gte"),
            // PbEncoding::Dpw => write!(f, "dpw"),
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
pub enum Bool {
    /// Turn on feature
    True,
    /// Turn off feature
    False,
}

impl From<Bool> for bool {
    fn from(val: Bool) -> Self {
        val == Bool::True
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
        if val { Bool::True } else { Bool::False }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum Disabled {
    /// Turn off feature
    False,
}

impl From<Disabled> for bool {
    fn from(_: Disabled) -> Self {
        false
    }
}

impl fmt::Display for Disabled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Disabled::False => write!(f, "false"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum CadicalConfig {
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
            CadicalConfig::Sat => rustsat_cadical::Config::Sat,
            CadicalConfig::Unsat => rustsat_cadical::Config::Unsat,
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
    #[cfg(feature = "maxpre")]
    pub preprocessing: bool,
    #[cfg(feature = "maxpre")]
    pub maxpre_techniques: String,
    pub reindexing: bool,
    #[cfg(feature = "maxpre")]
    pub maxpre_reindexing: bool,
    pub cadical_config: CadicalConfig,
    pub alg: Algorithm,
    pub proof_paths: Option<(PathBuf, Option<PathBuf>)>,
    pub tracing_opts: Option<tracing::Options>,
    pub wrap_up_opts: tracing::WrapUpOptions,
}

pub enum Algorithm {
    PMinimal(KernelOptions, Option<CoreBoostingOptions>),
    BiOptSat(
        KernelOptions,
        PbEncoding,
        CardEncoding,
        Option<CoreBoostingOptions>,
    ),
    LowerBounding(KernelOptions, Option<CoreBoostingOptions>),
    ParetoIhs(
        HittingSetSolver,
        KernelOptions,
        IhsOptions,
        Option<IhsCbOptions>,
    ),
    MipPd(HittingSetSolver, MipPdOptions),
    LeximaxSatUnsat(KernelOptions, Option<CoreBoostingOptions>),
}

impl fmt::Display for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Algorithm::PMinimal(..) => write!(f, "p-pminimal"),
            Algorithm::BiOptSat(..) => write!(f, "bioptsat"),
            Algorithm::LowerBounding(..) => write!(f, "lower-bounding"),
            Algorithm::ParetoIhs(..) => write!(f, "pareto-ihs"),
            Algorithm::MipPd(..) => write!(f, "mip-pd"),
            Algorithm::LeximaxSatUnsat(..) => write!(f, "leximax"),
        }
    }
}

impl Cli {
    pub fn init() -> Self {
        let args = CliArgs::parse();
        let mut kernel_opts = args.kernel_opts();
        match args.command {
            AlgorithmCommand::PMinimal { cb, file, proof } => {
                let cb = if args.core_boosting.into() {
                    let (cbo, store) = cb.parse(
                        #[cfg(feature = "maxpre")]
                        args.prepro.maxpre_techniques.clone(),
                    );
                    if store {
                        kernel_opts.store_cnf = true;
                    }
                    Some(cbo)
                } else {
                    None
                };
                let proof_paths = proof.proof_paths();
                Cli {
                    limits: args.limits.into(),
                    file_format: file.file_format,
                    opb_options: fio::opb::Options {
                        first_var_idx: file.first_var_idx,
                        ..Default::default()
                    },
                    inst_path: file.inst_path.clone(),
                    #[cfg(feature = "maxpre")]
                    preprocessing: args.prepro.preprocessing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_techniques: args.prepro.maxpre_techniques.clone(),
                    reindexing: args.prepro.reindexing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_reindexing: args.prepro.maxpre_reindexing.into(),
                    cadical_config: args.cadical_config,
                    alg: Algorithm::PMinimal(kernel_opts, cb),
                    proof_paths,
                    tracing_opts: args.log.into(),
                    wrap_up_opts: args.log.into(),
                }
            }
            AlgorithmCommand::Bioptsat {
                cb,
                file,
                proof,
                obj_encs,
            } => {
                let cb = if args.core_boosting.into() {
                    let (cbo, store) = cb.parse(
                        #[cfg(feature = "maxpre")]
                        args.prepro.maxpre_techniques.clone(),
                    );
                    if store {
                        kernel_opts.store_cnf = true;
                    }
                    Some(cbo)
                } else {
                    None
                };
                let proof_paths = proof.proof_paths();
                Cli {
                    limits: args.limits.into(),
                    file_format: file.file_format,
                    opb_options: fio::opb::Options {
                        first_var_idx: file.first_var_idx,
                        ..Default::default()
                    },
                    inst_path: file.inst_path.clone(),
                    #[cfg(feature = "maxpre")]
                    preprocessing: args.prepro.preprocessing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_techniques: args.prepro.maxpre_techniques.clone(),
                    reindexing: args.prepro.reindexing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_reindexing: args.prepro.maxpre_reindexing.into(),
                    cadical_config: args.cadical_config,
                    alg: Algorithm::BiOptSat(
                        kernel_opts,
                        obj_encs.obj_pb_encoding,
                        obj_encs.obj_card_encoding,
                        cb,
                    ),
                    proof_paths,
                    tracing_opts: args.log.into(),
                    wrap_up_opts: args.log.into(),
                }
            }
            AlgorithmCommand::LowerBounding { cb, file, proof } => {
                let cb = if args.core_boosting.into() {
                    let (cbo, store) = cb.parse(
                        #[cfg(feature = "maxpre")]
                        args.prepro.maxpre_techniques.clone(),
                    );
                    if store {
                        kernel_opts.store_cnf = true;
                    }
                    Some(cbo)
                } else {
                    None
                };
                let proof_paths = proof.proof_paths();
                Cli {
                    limits: args.limits.into(),
                    file_format: file.file_format,
                    opb_options: fio::opb::Options {
                        first_var_idx: file.first_var_idx,
                        ..Default::default()
                    },
                    inst_path: file.inst_path.clone(),
                    #[cfg(feature = "maxpre")]
                    preprocessing: args.prepro.preprocessing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_techniques: args.prepro.maxpre_techniques.clone(),
                    reindexing: args.prepro.reindexing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_reindexing: args.prepro.maxpre_reindexing.into(),
                    cadical_config: args.cadical_config,
                    alg: Algorithm::LowerBounding(kernel_opts, cb),
                    proof_paths,
                    tracing_opts: args.log.into(),
                    wrap_up_opts: args.log.into(),
                }
            }
            AlgorithmCommand::ParetoIhs {
                hitting_set_solver,
                seeding,
                ihs_core_extraction,
                candidate_seeding,
                ihs_core_minimization,
                use_starting_points,
                multipliers,
                precompute_lexicographic,
                max_failed_precompute_lex,
                fully_seeded_precompute_lex: precompute_fully_seeded,
                reduced_cost_fixing,
                upper_bounds,
                hss_threads,
                cb,
                file,
            } => Cli {
                limits: args.limits.into(),
                file_format: file.file_format,
                opb_options: fio::opb::Options {
                    first_var_idx: file.first_var_idx,
                    ..Default::default()
                },
                inst_path: file.inst_path.clone(),
                #[cfg(feature = "maxpre")]
                preprocessing: args.prepro.preprocessing.into(),
                #[cfg(feature = "maxpre")]
                maxpre_techniques: args.prepro.maxpre_techniques.clone(),
                reindexing: args.prepro.reindexing.into(),
                #[cfg(feature = "maxpre")]
                maxpre_reindexing: args.prepro.maxpre_reindexing.into(),
                cadical_config: args.cadical_config,
                alg: Algorithm::ParetoIhs(
                    hitting_set_solver,
                    kernel_opts,
                    IhsOptions {
                        seeding: seeding.into(),
                        core_extraction: ihs_core_extraction,
                        candidate_seeding,
                        hss_threads,
                        core_minimization: ihs_core_minimization,
                        starting_points: use_starting_points.into(),
                        multipliers,
                        precompute_lexicographic,
                        max_failed_precompute_lex,
                        fully_seeded_precompute_lex: precompute_fully_seeded.into(),
                        reduced_cost_fixing: reduced_cost_fixing.into(),
                        upper_bounds: upper_bounds.into(),
                    },
                    if args.core_boosting.into() {
                        Some(cb.into())
                    } else {
                        None
                    },
                ),
                proof_paths: None,
                tracing_opts: args.log.into(),
                wrap_up_opts: args.log.into(),
            },
            AlgorithmCommand::MipPd {
                random_seed,
                mip_solver,
                multipliers,
                precompute_lexicographic,
                threads,
                file,
            } => Cli {
                limits: args.limits.into(),
                file_format: file.file_format,
                opb_options: fio::opb::Options {
                    first_var_idx: file.first_var_idx,
                    ..Default::default()
                },
                inst_path: file.inst_path.clone(),
                #[cfg(feature = "maxpre")]
                preprocessing: args.prepro.preprocessing.into(),
                #[cfg(feature = "maxpre")]
                maxpre_techniques: args.prepro.maxpre_techniques.clone(),
                reindexing: args.prepro.reindexing.into(),
                #[cfg(feature = "maxpre")]
                maxpre_reindexing: args.prepro.maxpre_reindexing.into(),
                cadical_config: args.cadical_config,
                alg: Algorithm::MipPd(
                    mip_solver,
                    MipPdOptions {
                        random_seed,
                        threads,
                        multipliers,
                        precompute_lexicographic,
                    },
                ),
                proof_paths: None,
                tracing_opts: args.log.into(),
                wrap_up_opts: args.log.into(),
            },
            AlgorithmCommand::LeximaxSatUnsat { cb, file, proof } => {
                let cb = if args.core_boosting.into() {
                    let (cbo, store) = cb.parse(
                        #[cfg(feature = "maxpre")]
                        args.prepro.maxpre_techniques.clone(),
                    );
                    if store {
                        kernel_opts.store_cnf = true;
                    }
                    Some(cbo)
                } else {
                    None
                };
                let proof_paths = proof.proof_paths();
                Cli {
                    limits: args.limits.into(),
                    file_format: file.file_format,
                    opb_options: fio::opb::Options {
                        first_var_idx: file.first_var_idx,
                        ..Default::default()
                    },
                    inst_path: file.inst_path.clone(),
                    #[cfg(feature = "maxpre")]
                    preprocessing: args.prepro.preprocessing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_techniques: args.prepro.maxpre_techniques.clone(),
                    reindexing: args.prepro.reindexing.into(),
                    #[cfg(feature = "maxpre")]
                    maxpre_reindexing: args.prepro.maxpre_reindexing.into(),
                    cadical_config: args.cadical_config,
                    alg: Algorithm::LeximaxSatUnsat(kernel_opts, cb),
                    proof_paths,
                    tracing_opts: args.log.into(),
                    wrap_up_opts: args.log.into(),
                }
            }
        }
    }
}

#[test]
fn verify_cli_args() {
    use clap::CommandFactory;
    CliArgs::command().debug_assert()
}
