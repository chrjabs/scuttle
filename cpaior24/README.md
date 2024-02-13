# Supplementary Material for CPAIOR'24 Paper

This directory includes additional materials for our CPAIOR'24 paper "Core
Boosting in SAT-Based Multi-Objective Optimization". Included are additional
details about the empirical results (in `appendix.pdf`), numeric evaluation data
(in `data/`) , and instructions on how to replicate experiments (in this file).

## Benchmark Instances

All benchmark instances used in our evaluation can be downloaded at
`https://cs.helsinki.fi/group/coreo/benchmarks/multi-opt/<hash>.mcnf.xz` where
instances are identified by their hash. This includes _all_ instances that we
randomly sampeled the 320 used instances from.  The files are named following a
`<hash>.mcnf.xz` pattern with additional metadata for the instances (identified
by their hash) being provided in the `data/mcnf_meta.csv` table.  The metadata
includes the family of the instances, the number of objectives, the sum of
weights in each objective and whether the instance was selected for our
evaluation. Note that the family `lidr` from the paper is called `mlic` in the
metadata.

To download all instances selected for the evaluation, use the following command:
```bash
mkdir instances
hashes=$(cat data/mcnf_meta.csv | cut -d ',' -f1,9 | grep 'True' | cut -d ',' -f1 | tr '\n' ',' | sed 's/,$/\n/')
cd instances
curl -Z -O "https://cs.helsinki.fi/group/coreo/benchmarks/multi-opt/{${hashes}}.mcnf.xz"
```

## Evaluation Data

The data collected during the empirical evaluation is available in the `data/`
directory. The `mcnf_runtime.csv` file contains runtime measurements
(`<config>_CPUTIME`) and solved/timeout information (`<config>_result`) of the
different evaluated configurations. `mcnf_core_boosting.csv` contains
additional data about how much time was spent core boosting
(`<config>_CB_CPUTIME`). `mcnf_clauses.csv` contains data on the number of
clauses in the objective encodings with (`cb_enc_clauses_MERGING`) and without
core boosting (`cb_enc_clauses_NO_CB`).

The configurations are named as follows:
- `scuttle_pmin`: P-Minimal without core boosting
- `scuttle_dc_pmin`: P-Minimal with core boosting
- `scuttle_pmin_prepro`: P-Minimal with MaxPre
- `scuttle_bos_gte`: BiOptSat without core boosting
- `scuttle_dc_bos`: BiOptSat with core boosting
- `scuttle_bos_gte_prepro`: BiOptSat with MaxPre
- `scuttle_lb`: LowerBound without core boosting
- `scuttle_dc_lb`: LowerBound with core boosting
- `scuttle_lb_prepro`: LowerBound with MaxPre

## Source Code

In our evaluation we used the versions of
[`scuttle`](https://github.com/chrjabs/scuttle),
[`rustsat`](https://github.com/chrjabs/rustsat), and
[`maxpre-rs`](https://github.com/chrjabs/maxpre-rs) at the respective
`cpaior24` tags. To build this specific version, use the following commands
with Rust installed:

```bash
mkdir cpaior-scuttle
cd cpaior-scuttle
git clone --branch cpaior24 git@github.com:chrjabs/rustsat.git
git clone --branch cpaior24 git@github.com:chrjabs/scuttle.git
git clone --branch cpaior24 git@github.com:chrjabs/maxpre-rs.git
cargo install --path scuttle --root .
```

After these commands, the scuttle binary will be at `cpaior-scuttle/bin/scuttle`.

With the version updated since the `cpaior24` tag (the `main` branch or scuttle
version `>=0.3`), core boosting is available through a more convenient
`--core-boosting=true` CLI option.

## MCNF File Format

The MCNF file format is an extension of the [new DIMACS WCNF
format](https://maxsat-evaluations.github.io/2022/rules.html#input) to multiple
objectives, which we call DIMACS MCNF. An example of this file format is the
following:

```text
c <comment>
h 1 2 3 0
o1 5 1 0
o2 7 2 3 0
```

Comments start with `c`, as in other DIMACS formats. Hard clauses start
with an `h`, as in WCNF files. Soft clauses are of the following form
`o<obj idx> <weight> <lit 1> ... <lit n> 0`. The first token must be a
positive number preceded by an 'o', indicating what objective this soft
clause belongs to. After that, the format is identical to a soft clause
in a WCNF file.

## Used Commands

### Running the Algorithms

These are the commands used for running the configurations equivalent to
the experiments in the paper. Note that we updated the code since the
evaluation was run to provide an easier CLI. To run the exact same code
used in the evaluation, check out the `cpaior24` tag and follow the
instructions there.

#### P-Minimal

No core boosting
```bash
scuttle p-minimal -v2 --core-boosting=false --preprocessing=false <instance>
```

With core boosting
```bash
scuttle p-minimal -v2 --core-boosting=true --preprocessing=false <instance>
```

With MaxPre
```bash
scuttle p-minimal -v2 --core-boosting=false --preprocessing=true <instance>
```

#### BiOptSat

No core boosting
```bash
scuttle bioptsat -v2 --obj-pb-encoding=gte --core-boosting=false --preprocessing=false <instance>
```

With core boosting
```bash
scuttle bioptsat -v2 --obj-pb-encoding=gte --core-boosting=true --preprocessing=false <instance>
```

With MaxPre
```bash
scuttle bioptsat -v2 --obj-pb-encoding=gte --core-boosting=false --preprocessing=true <instance>
```

#### LowerBound

No core boosting
```bash
scuttle lower-bounding -v2 --core-boosting=false --preprocessing=false <instance>
```

With core boosting
```bash
scuttle lower-bounding -v2 --core-boosting=true --preprocessing=false <instance>
```

With MaxPre
```bash
scuttle lower-bounding -v2 --core-boosting=false --preprocessing=true <instance>
```
