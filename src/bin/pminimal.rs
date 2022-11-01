#![cfg(feature = "build-binary")]

use clap::Parser;
use pminimal::{Options, Solve};
use rustsat::solvers;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// The path to the instance file to load. If the path ends in `.opb` it is
    /// pares as an OPB file, otherwise as a DIMACS MCNF.
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
}

#[cfg(feature = "cadical")]
type Oracle = solvers::CaDiCaL<'static>;
#[cfg(not(feature = "cadical"))]
compile_error!("At least one of the solver features needs to be turned on");

fn main() {
    let cli = Cli::parse();

    let mut options = Options::default();
    options.max_sols_per_pp = if cli.max_sols_per_pp > 0 {
        Some(cli.max_sols_per_pp)
    } else {
        None
    };
    options.model_tightening = cli.model_tightening;
}
