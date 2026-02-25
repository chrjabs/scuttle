# Scuttle - A Multi-Objective MaxSAT Solver in Rust

Scuttle is a multi-objective MaxSAT solver written in Rust and based on the
[RustSAT](https://github.com/chrjabs/rustsat) library and the
[CaDiCaL](https://github.com/arminbiere/cadical) SAT solver.

## Publications

This solver was used in the following publications.
For each publication, a tag (specified in brackets) marks the exact revision used:

- CP'23 (`cp23`): "Preprocessing in SAT-Based Multi-Objective Combinatorial
  Optimization" \[5\]. Additional material
  [here](https://bitbucket.org/coreo-group/mo-prepro).
- CPAIOR'24 (`cpaior24`): "Core Boosting in SAT-Based Multi-Objective
  Optimization" \[6\]. Additional material in `cpaior24/`.
- TACAS'25 (`tacas25`): "Certifying Pareto-Optimality in Multi-Objective
  Maximum Satisfiability" \[7\]. Additional material in `tacas25/`.
- JELIA'25 (`jelia25`): "Engineering and Evaluating Multi-objective
  Pseudo-Boolean Optimizers" \[8\]
- CPAIOR'26 (`cpaior26`): "Multi-objective Maximum Satisfiability by
  Single-objective Implicit Hitting Set Optimization" \[9\]. Additional
  material in `cpaior26/`.

## Algorithms

| First argument   | Description                                                                 |
| ---------------- | --------------------------------------------------------------------------- |
| `p-minimal`      | P-Minimal model enumeration as described in \[1\] and \[2\]                 |
| `lower-bounding` | Lower-bounding search as described in \[3\] (called "core-guided" there)    |
| `bioptsat`       | Sat-Unsat variant of the BiOptSat algorithm described in \[4\]              |
| `pareto-ihs`     | Multi-objective implicity hitting set optimization described in \[9\]       |
| `mip-pd`         | MIP-based algorithm optimizing scalarization and introducing PD cuts \[10\] |

## Building

**Note**: Scuttle requires nightly Rust, which can be installed via `rustup`.

If you simply want a binary of the solver, you can install it straight from
[the repository](https://bitbucket.org/coreo-group/scuttle) by running `cargo
+nightly install --locked --git https://bitbucket.org/coreo-group/scuttle`.

To build the project from source, run `cargo +nightly build` in a clone of this
repository.

By default, only the HiGHS hitting set solver is included. To enable Gurobi add
either `--features=gurobi12` or `gurobi9`.

By default, MaxPre preprocessing is not included in the build anymore. To
include preprocessing with MaxPre, add `--features=maxpre`.

### Features

- `gurobi12`: enables support for Gurobi version 12 as the hitting set solver
- `gurobi9`: enables support for Gurobi version 9 as the hitting set solver
- `sol-tightening`: includes heuristic tightening of solutions after they are found in the build
- `maxpre`: includes preprocessing with MaxPre in the build

## What's The Name

[Apparently](https://crabbingzone.com/what-is-group-of-crabs-called/) "scuttle"
is one of multiple term for a group of crabs, which seemed fitting for a
_multi_-objective solver in _Rust_.

## References

- \[1\] Takehide Soh and Mutsunori Banbara and Naoyuki Tamura and Daniel Le
  Berre: _Solving Multiobjective Discrete Optimization Problems with
  Propositional Minimal Model Generation_, CP 2017.
- \[2\] Miyuki Koshimura and Hidetomo Nabeshima and Hiroshi Fujita and Ryuzo
  Hasegawa: _Minimal Model Generation with Respect to an Atom Set_, FTP
  2009\.
- \[3\] Joao Cortes and Ines Lynce and Vasco M. Maquinho: _New Core-Guided
  and Hitting Set Algorithms for Multi-Objective Combinatorial Optimization_,
  TACAS 2023.
- \[4\] Christoph Jabs and Jeremias Berg and Andreas Niskanen and Matti
  Järvisalo: _MaxSAT-Based Bi-Objective Boolean Optimization_, SAT 2022.
- \[5\] Christoph Jabs and Jeremias Berg and Hannes Ihalainen and Matti
  Järvisalo: _Preprocessing in SAT-Based Multi-Objective Combinatorial
  Optimization_, CP 2023.
- \[6\] Christoph Jabs and Jeremias Berg and Matti Järvisalo: _Core Boosting
  in SAT-Based Multi-Objective Optimization_, CPAIOR 2024.
- \[7\] Christoph Jabs and Jeremias Berg and Bart Boergarts and Matti
  Järvisalo: _Certifying Pareto-Optimality in
  Multi-Objective Maximum Satisfiability_, TACAS 2025.
- \[8\] Christoph Jabs and Jeremias Berg and Matti Järvisalo: _Engineering and
  Evaluating Multi-objective Pseudo-Boolean Optimizers_, JELIA 2025.
- \[9\] Christoph Jabs and Jeremias Berg and Matti Järvisalo: _Multi-objective
  Maximum Satisfiability by Single-objective Implicit Hitting Set
  Optimization_, CPAIOR 2026.
- \[10\] John Sylva and Alejandro Crema: _A method for finding the set of
  non-dominated vectors for multiple objective integer linear programs_, EOR
  2004.
