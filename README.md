# Scuttle - A Multi-Objective MaxSAT Solver in Rust

Scuttle is a multi-objective MaxSAT solver written in Rust and based on the
[RustSAT](https://github.com/chrjabs/rustsat) library and the
[CaDiCaL](https://github.com/arminbiere/cadical) SAT solver.

## Publications

This solver was used in our CP'23 paper on preprocessing for multi-objective
optimization \[5\], our CPAIOR'24 paper on core boosting \[6\], and our
TACAS'25 paper on proof-logging for multi-objective MaxSAT \[7\]. Additional
material for the CP'23 paper can be found
[here](https://bitbucket.org/coreo-group/mo-prepro), material for the
CPAIOR'24 paper is available in the `cpaior24/` directory, and for the TACAS'25
paper in the `tacas25/` directory in this repository.

## Algorithms

| First argument   | Description                                                               |
| ---------------- | ------------------------------------------------------------------------- |
| `p-minimal`      | P-Minimal model enumeration as described in \[1\] and \[2\]               |
| `lower-bounding` | Lower-bounding search as described in \[3\] (called "core-guiding" there) |
| `bioptsat`       | Sat-Unsat variant of the BiOptSat algorithm described in \[4\]            |

## Building

**Note**: Scuttle requires nightly Rust, which can be installed via `rustup`.

If you simply want a binary of the solver, you can install it from
[crates.io](https://crates.io) by running `cargo +nightly install --locked scuttle`.

To build the project from source, make sure to initialize the git submodules
with `git submodule update --init --recursive`. You can then build `scuttle` by
running `cargo +nightly build`.

### Features

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
