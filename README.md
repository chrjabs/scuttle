# Scuttle - A Multi-Objective MaxSAT Solver in Rust

Scuttle is a multi-objective MaxSAT solver written in Rust and based on the
[rustsat](https://github.com/chrjabs/rustsat) library and the
[CaDiCaL](https://github.com/arminbiere/cadical) SAT solver.

## Algorithms

For now the only implemented algorithm is P-minimal model enumeration.

> Soh, T., Banbara, M., Tamura, N., & Le Berre, D. (2017). _Solving Multiobjective Discrete Optimization Problems with Propositional Minimal Model Generation_. CP.

## What's The Name

[Apparently](https://crabbingzone.com/what-is-group-of-crabs-called/) "scuttle"
is one of multiple term for a group of crabs, which seemed fitting for a
_multi_-objective solver in _Rust_.