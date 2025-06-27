//! # CLI logging via the `tracing` crate

use std::{fmt, io::IsTerminal};

use owo_colors::{OwoColorize, Style};
use rustsat::solvers::SolverStats;
use scuttle_core::{
    CoreBoostingOptions, EncodingStats, KernelOptions, Stats,
    options::{IhsCbOptions, IhsOptions, MipPdOptions},
    types::ParetoFront,
};
use tracing::Level;
use tracing_subscriber::{
    fmt::format::FmtSpan, layer::SubscriberExt, registry::Registry, util::SubscriberInitExt,
};

use crate::cli::{self, Algorithm};

mod filter;
mod format;
mod spans;

pub fn init(alg: &Algorithm, options: Option<Options>) {
    let Some(options) = options else {
        return;
    };
    let color = match options.color {
        cli::ColorOpt::Always => true,
        cli::ColorOpt::Auto => std::io::stdout().is_terminal(),
        cli::ColorOpt::Never => false,
    };
    header(alg, options.print_config, color);
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_ansi(color)
        .with_span_events(FmtSpan::ACTIVE)
        .event_format(format::Format::new(options.into()));
    Registry::default()
        .with(spans::Spans)
        .with(fmt_layer)
        .with(filter::Filter::new(options.into()))
        .init();
}

#[derive(Debug, Clone, Copy)]
pub struct Options {
    pub color: cli::ColorOpt,
    pub print_config: bool,
    pub timestamps: bool,
    pub candidates: bool,
    pub solutions: bool,
    pub non_dominated: bool,
    pub oracle_calls: bool,
    pub bound_points: bool,
    pub level: Level,
}

fn header(alg: &Algorithm, print_config: bool, color: bool) {
    let styles = if color {
        Styles::colored()
    } else {
        Styles::plain()
    };
    println!(
        "{} ({})",
        clap::crate_name!().style(styles.name),
        git_version::git_version!().style(styles.version)
    );
    println!("{}", clap::crate_authors!().style(styles.authors));
    println!(
        "{}: {}",
        "algorithm".style(styles.algorithm),
        alg.style(styles.alg_name)
    );
    println!("{}", "==============================".style(styles.divider));
    if print_config {
        config(alg, &styles);
    }
}

macro_rules! print_kv {
    ($key:expr, $val:expr, $styles:expr) => {
        print_kv!("", $key, $val, $styles);
    };
    ($indent:literal, $key:expr, $val:expr, $styles:expr) => {
        println!(
            " {}{}: {}",
            $indent,
            $key.style($styles.key),
            $val.style($styles.val)
        );
    };
}

fn kernel_opts(opts: &KernelOptions, styles: &Styles) {
    println!(
        " {}{}",
        "[".style(styles.scope),
        "Kernel Options".style(styles.h2)
    );

    let KernelOptions {
        random_seed,
        enumeration,
        reserve_enc_vars,
        heuristic_improvements,
        solution_guided_search,
        core_minimization,
        core_exhaustion,
        stratification,
        store_cnf,
    } = *opts;
    print_kv!(" ", "enumeration", enumeration, styles);
    print_kv!(" ", "random-seed", random_seed, styles);
    print_kv!(" ", "reserve-enc-vars", reserve_enc_vars, styles);
    print_kv!(
        " ",
        "heuristic-improvements",
        heuristic_improvements,
        styles
    );
    print_kv!(
        " ",
        "solution-guided-search",
        solution_guided_search,
        styles
    );
    print_kv!(" ", "core-minimization", core_minimization, styles);
    print_kv!(" ", "core-exhaustion", core_exhaustion, styles);
    print_kv!(" ", "stratification", stratification, styles);
    print_kv!(" ", "store-cnf", store_cnf, styles);

    println!(" {}", "]".style(styles.scope));
}

fn core_boosting(opts: &Option<CoreBoostingOptions>, styles: &Styles) {
    println!(
        " {}{}",
        "[".style(styles.scope),
        "Core Boosting Options".style(styles.h2)
    );

    if let Some(CoreBoostingOptions { rebase, after }) = opts {
        print_kv!(" ", "rebase", rebase, styles);
        print_kv!(" ", "after", after, styles);
    } else {
        print!("  {}", "none".style(styles.key));
    }

    println!(" {}", "]".style(styles.scope));
}

fn config(alg: &Algorithm, styles: &Styles) {
    println!(
        "{}{}",
        "[".style(styles.scope),
        "Solver Config".style(styles.h1)
    );

    match alg {
        Algorithm::BiOptSat(_, pb_encoding, card_encoding, _) => {
            print_kv!("obj-pb-encoding", pb_encoding, styles);
            print_kv!("obj-card-encoding", card_encoding, styles);
        }
        Algorithm::ParetoIhs(hitting_set_solver, _, ihs_options, ihs_cb_options) => {
            print_kv!("hitting-set-solver", hitting_set_solver, styles);
            let IhsOptions {
                hss_threads,
                seeding,
                candidate_seeding,
                core_extraction,
                core_minimization,
                starting_points,
                multipliers,
                precompute_lexicographic,
                max_failed_precompute_lex,
                fully_seeded_precompute_lex,
                reduced_cost_fixing,
                upper_bounds,
            } = ihs_options;
            print_kv!("hss-threads", hss_threads, styles);
            print_kv!("seeding", seeding, styles);
            print_kv!("candidate-seeding", candidate_seeding, styles);
            print_kv!("core-extraction", core_extraction, styles);
            print_kv!("core-minimization", core_minimization, styles);
            print_kv!("starting-points", starting_points, styles);
            print_kv!("multipliers", multipliers, styles);
            print_kv!("precompute-lexicographic", precompute_lexicographic, styles);
            print_kv!(
                "max-failed-precompute-lex",
                max_failed_precompute_lex,
                styles
            );
            print_kv!(
                "fully-seeded-precompute-lex",
                fully_seeded_precompute_lex,
                styles
            );
            print_kv!("reduced-cost-fixing", reduced_cost_fixing, styles);
            print_kv!("upper-bounds", upper_bounds, styles);
            println!(
                " {}{}",
                "[".style(styles.scope),
                "Core Boosting Options".style(styles.h2)
            );
            if let Some(IhsCbOptions { treatment }) = ihs_cb_options {
                print_kv!("treatment", treatment, styles);
            } else {
                print!("  {}", "none".style(styles.key));
            }
            println!(" {}", "]".style(styles.scope));
        }
        Algorithm::MipPd(hitting_set_solver, options) => {
            print_kv!("hitting-set-solver", hitting_set_solver, styles);
            let MipPdOptions {
                random_seed,
                threads,
                multipliers,
                precompute_lexicographic,
            } = options;
            print_kv!("random-seed", random_seed, styles);
            print_kv!("threads", threads, styles);
            print_kv!("multipliers", multipliers, styles);
            print_kv!("precompute-lexicographic", precompute_lexicographic, styles);
        }
        _ => (),
    }

    if let Algorithm::PMinimal(opts, _)
    | Algorithm::BiOptSat(opts, _, _, _)
    | Algorithm::LowerBounding(opts, _)
    | Algorithm::ParetoIhs(_, opts, _, _) = alg
    {
        kernel_opts(opts, styles);
    }

    if let Algorithm::PMinimal(_, cb)
    | Algorithm::BiOptSat(_, _, _, cb)
    | Algorithm::LowerBounding(_, cb) = alg
    {
        core_boosting(cb, styles);
    }

    println!("{}", "]".style(styles.scope));
}

pub fn wrap_up<S>(
    pareto_front: ParetoFront<S>,
    #[cfg(not(feature = "maxpre"))] stats: (
        Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
        Option<hitting_sets::Statistics>,
    ),
    #[cfg(feature = "maxpre")] stats: (
        Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
        Option<hitting_sets::Statistics>,
        Option<maxpre::Stats>,
    ),
    options: WrapUpOptions,
) where
    S: Clone + Eq + fmt::Display,
{
    let color = match options.color {
        cli::ColorOpt::Always => true,
        cli::ColorOpt::Auto => std::io::stdout().is_terminal(),
        cli::ColorOpt::Never => false,
    };
    let styles = if color {
        Styles::colored()
    } else {
        Styles::plain()
    };
    print_pareto_front(pareto_front, options.print_solutions, &styles);
    if options.print_stats {
        print_stats(stats, &styles);
    }
}

fn print_pareto_front<S>(pareto_front: ParetoFront<S>, print_solutions: bool, styles: &Styles)
where
    S: Clone + Eq + fmt::Display,
{
    println!(
        "{}{}",
        "[".style(styles.scope),
        "Discovered Pareto Front".style(styles.h1)
    );

    for non_dom in pareto_front {
        println!(
            " {}{} costs={:?} n_sols={}",
            "[".style(styles.scope),
            "Non-dominated Point".style(styles.h2),
            non_dom.costs(),
            non_dom.n_sols(),
        );
        if print_solutions {
            for sol in non_dom {
                println!("{} {}", "v".style(styles.key), sol.style(styles.val));
            }
        }
        println!(" {}", "]".style(styles.scope));
    }

    println!("{}", "]".style(styles.scope));
}

fn print_stats(
    #[cfg(not(feature = "maxpre"))] (
        Stats {
            n_solve_calls,
            n_solutions,
            n_non_dominated,
            n_candidates,
            n_oracle_calls: _,
            n_objs,
            n_real_objs,
            n_orig_clauses,
        },
        solver_stats,
        enc_stats,
        hss_stats,
    ): (
        Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
        Option<hitting_sets::Statistics>,
    ),
    #[cfg(feature = "maxpre")] (
        Stats {
            n_solve_calls,
            n_solutions,
            n_non_dominated,
            n_candidates,
            n_oracle_calls: _,
            n_objs,
            n_real_objs,
            n_orig_clauses,
        },
        solver_stats,
        enc_stats,
        hss_stats,
        maxpre_stats,
    ): (
        Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
        Option<hitting_sets::Statistics>,
        Option<maxpre::Stats>,
    ),
    styles: &Styles,
) {
    println!(
        "{}{}",
        "[".style(styles.scope),
        "Statistics".style(styles.h1)
    );

    print_kv!("solve-calls", n_solve_calls, styles);
    print_kv!("solutions", n_solutions, styles);
    print_kv!("non-dominated", n_non_dominated, styles);
    print_kv!("candidates", n_candidates, styles);
    print_kv!("objectives", n_objs, styles);
    print_kv!("orig-clauses", n_orig_clauses, styles);
    print_kv!("real-objs", n_real_objs, styles);

    if let Some(SolverStats {
        n_sat,
        n_unsat,
        n_terminated: _,
        n_clauses,
        max_var,
        avg_clause_len,
        cpu_solve_time,
    }) = solver_stats
    {
        println!(
            " {}{}",
            "[".style(styles.scope),
            "Oracle Statistics".style(styles.h2)
        );

        print_kv!(" ", "sat-solves", n_sat, styles);
        print_kv!(" ", "unsat-solves", n_unsat, styles);
        print_kv!(" ", "clauses", n_clauses, styles);
        print_kv!(" ", "max-var", OptVal::new(max_var), styles);
        print_kv!(" ", "avg-clause-len", avg_clause_len, styles);
        print_kv!(
            " ",
            "cpu-solve-time",
            format_args!("{}s", cpu_solve_time.as_secs_f64()),
            styles
        );

        println!(" {}", "]".style(styles.scope));
    }

    if let Some(stats) = enc_stats {
        println!(
            " {}{}",
            "[".style(styles.scope),
            "Encoding Statistics".style(styles.h2)
        );

        for (
            idx,
            EncodingStats {
                n_clauses,
                n_vars,
                offset,
                unit_weight,
            },
        ) in stats.into_iter().enumerate()
        {
            println!(
                "  {}{}",
                "[".style(styles.scope),
                format_args!("Encoding #{idx}").style(styles.h2)
            );

            print_kv!("  ", "clauses", n_clauses, styles);
            print_kv!("  ", "vars", n_vars, styles);
            print_kv!("  ", "offset", offset, styles);
            print_kv!("  ", "unit-weight", OptVal::new(unit_weight), styles);

            println!("  {}", "]".style(styles.scope));
        }

        println!(" {}", "]".style(styles.scope));
    }

    if let Some(hitting_sets::Statistics {
        solve_time,
        lp_solve_time,
        n_solves,
        n_lp_solves,
        n_cores,
        n_abstract_cores,
        n_seeded,
        n_learned_units,
    }) = hss_stats
    {
        println!(
            " {}{}",
            "[".style(styles.scope),
            "Hitting Set Solver Statistics".style(styles.h2)
        );

        print_kv!(" ", "cores", n_cores, styles);
        print_kv!(" ", "abstract-cores", n_abstract_cores, styles);
        print_kv!(" ", "seeded", n_seeded, styles);
        print_kv!(" ", "learned-units", n_learned_units, styles);
        print_kv!(" ", "solve-calls", n_solves, styles);
        print_kv!(" ", "lp-solve-calls", n_lp_solves, styles);
        print_kv!(
            " ",
            "cpu-solve-time",
            format_args!("{}s", solve_time.as_secs_f64()),
            styles
        );
        print_kv!(
            " ",
            "cpu-lp-solve-time",
            format_args!("{}s", lp_solve_time.as_secs_f64()),
            styles
        );

        println!(" {}", "]".style(styles.scope));
    }

    #[cfg(feature = "maxpre")]
    if let Some(stats) = maxpre_stats {
        println!(
            " {}{}",
            "[".style(styles.scope),
            "MaxPre Statistics".style(styles.h2)
        );

        print_kv!(" ", "orig-hard-clauses", stats.n_orig_hard_clauses, styles);
        print_kv!(
            " ",
            "orig-soft-clauses",
            format_args!("{:?}", stats.n_orig_soft_clauses),
            styles
        );
        print_kv!(" ", "max-orig-var", OptVal::new(stats.max_orig_var), styles);
        print_kv!(
            " ",
            "prepro-hard-clauses",
            stats.n_prepro_hard_clauses,
            styles
        );
        print_kv!(
            " ",
            "prepro-soft-clauses",
            format_args!("{:?}", stats.n_prepro_soft_clauses),
            styles
        );
        print_kv!(
            " ",
            "max-prepro-var",
            OptVal::new(stats.max_prepro_var),
            styles
        );
        print_kv!(
            " ",
            "removed-weight",
            format_args!("{:?}", stats.removed_weight),
            styles
        );
        print_kv!(
            " ",
            "prepro-time",
            format_args!("{}s", stats.prepro_time.as_secs_f64()),
            styles
        );
        print_kv!(
            " ",
            "reconst-time",
            format_args!("{}s", stats.reconst_time.as_secs_f64()),
            styles
        );

        println!(" {}", "]".style(styles.scope));
    }

    println!("{}", "]".style(styles.scope));
}

#[derive(Debug, Clone, Copy)]
pub struct WrapUpOptions {
    pub color: cli::ColorOpt,
    pub print_solutions: bool,
    pub print_stats: bool,
}

#[derive(Debug, Default, Clone, Copy)]
struct Styles {
    timestamp: Style,
    span_time: Style,
    trace: LevelStyles,
    debug: LevelStyles,
    info: LevelStyles,
    warn: LevelStyles,
    error: LevelStyles,
    // Header styles
    name: Style,
    version: Style,
    authors: Style,
    algorithm: Style,
    alg_name: Style,
    // Structure styles
    divider: Style,
    scope: Style,
    // Wrap up
    h1: Style,
    h2: Style,
    key: Style,
    val: Style,
}

#[derive(Debug, Default, Clone, Copy)]
struct LevelStyles {
    event_name: Style,
    span_name: Style,
    span_symb: Style,
}

impl Styles {
    fn plain() -> Self {
        Self::default()
    }

    fn colored() -> Self {
        Styles {
            timestamp: Style::new().dimmed(),
            span_time: Style::new().dimmed(),
            trace: LevelStyles {
                event_name: Style::new().cyan(),
                span_name: Style::new().cyan(),
                span_symb: Style::new().cyan().dimmed(),
            },
            debug: LevelStyles {
                event_name: Style::new().magenta().italic(),
                span_name: Style::new().purple().italic(),
                span_symb: Style::new().purple().dimmed(),
            },
            info: LevelStyles {
                event_name: Style::new().blue().bold(),
                span_name: Style::new().green().bold(),
                span_symb: Style::new().green().dimmed(),
            },
            warn: LevelStyles {
                event_name: Style::new().yellow().bold(),
                span_name: Style::new().yellow().bold(),
                span_symb: Style::new().yellow().dimmed(),
            },
            error: LevelStyles {
                event_name: Style::new().red().bold(),
                span_name: Style::new().red().bold(),
                span_symb: Style::new().red().dimmed(),
            },
            // Header styles
            name: Style::new().green().bold(),
            version: Style::new().bold(),
            authors: Style::new(),
            algorithm: Style::new().italic(),
            alg_name: Style::new().green(),
            divider: Style::new().bold(),
            scope: Style::new().dimmed(),
            h1: Style::new().blue().bold(),
            h2: Style::new().purple(),
            key: Style::new().cyan(),
            val: Style::new(),
        }
    }

    fn event_name(&self, level: &Level) -> Style {
        match *level {
            Level::TRACE => self.trace.event_name,
            Level::DEBUG => self.debug.event_name,
            Level::INFO => self.info.event_name,
            Level::WARN => self.warn.event_name,
            Level::ERROR => self.error.event_name,
        }
    }

    fn span_name(&self, level: &Level) -> Style {
        match *level {
            Level::TRACE => self.trace.span_name,
            Level::DEBUG => self.debug.span_name,
            Level::INFO => self.info.span_name,
            Level::WARN => self.warn.span_name,
            Level::ERROR => self.error.span_name,
        }
    }

    fn span_symb(&self, level: &Level) -> Style {
        match *level {
            Level::TRACE => self.trace.span_symb,
            Level::DEBUG => self.debug.span_symb,
            Level::INFO => self.info.span_symb,
            Level::WARN => self.warn.span_symb,
            Level::ERROR => self.error.span_symb,
        }
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
