Full empirical data for our CPAIOR'24 submission can be found in `cpaior24/`.

# Scuttle - A Multi-Objective MaxSAT Solver in Rust

Scuttle is a multi-objective MaxSAT solver written in Rust and based on the
[rustsat](https://github.com/chrjabs/rustsat) library and the
[CaDiCaL](https://github.com/arminbiere/cadical) SAT solver.

## Algorithms

| `--algorithm=`   | Description                                                               |
| ---------------- | ------------------------------------------------------------------------- |
| `p-minimal`      | P-Minimal model enumeration as described in \[1\] and \[2\]               |
| `lower-bounding` | Lower-bounding search as described in \[3\] (called "core-guiding" there) |

### References

- \[1\] Takehide Soh and Mutsunori Banbara and Naoyuki Tamura and Daniel Le
  Berre: _Solving Multiobjective Discrete Optimization Problems with
  Propositional Minimal Model Generation_, CP 2017.
- \[2\] Miyuki Koshimura and Hidetomo Nabeshima and Hiroshi Fujita and Ryuzo
  Hasegawa: _Minimal Model Generation with Respect to an Atom Set_, FTP
  2009.
- \[3\] Joao Cortes and Ines Lynce and Vasco M. Maquinho: _New Core-Guided
  and Hitting Set Algorithms for Multi-Objective Combinatorial Optimization_,
  TACAS 2023.

## What's The Name

[Apparently](https://crabbingzone.com/what-is-group-of-crabs-called/) "scuttle"
is one of multiple term for a group of crabs, which seemed fitting for a
_multi_-objective solver in _Rust_.
