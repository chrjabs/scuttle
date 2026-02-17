# Supplementary Material for CPAIOR'26 Paper

This directory includes additional materials for our CPAIOR'26 paper
"Multi-Objective Maximum Satisfiability by Single-Objective Implicit Hitting
Set Optimization". Included are additional details about the empirical results
(in `appendix.pdf`), numeric evaluation data (in `data/`) , and instructions on
how to replicate experiments (in this file).

**NOTE**: the experiments in the paper were run with the solver version at the
`cpaior26` tag.
From this tag to the `v0.5.0` release, some usability improvements and
dependency updates were made to the solver.

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
hashes=$(tail -n+2 data/scatter-data.csv | cut -d ',' -f1 | tr '\n' ',' | sed 's/,$/\n/')
cd instances
curl -Z -O "https://cs.helsinki.fi/group/coreo/benchmarks/multi-opt/{${hashes}}.mcnf.xz"
```

## Evaluation Data

The data collected during the empirical evaluation is available in the `data/`
directory. The `runtime-data.csv` file contains per-instance runtimes for
different configurations. All timeouts and memouts are marked as `3600.0`

The configurations are named as follows:
- `p-minimal`: Scuttle P-Minimal without core boosting
- `p-minimal-cb`: Scuttle P-Minimal with core boosting
- `clm-ihs`: The ClmIhs algorithm, implementation available [here](https://github.com/chrjabs/moco-openwbo)
- `mip-pd`: MipPd as implemented by us
- `pareto-ihs`: The best ParetoIHS configuration as implemented by us
- `pareto-ihs-norm`: ParetoIHS with the normalized scalarization constants
- `pareto-ihs-lex`: ParetoIHS with lexicogrpahic scalarization constants
- `pareto-ihs-noprecomp`: ParetoIHS without precomputing lexicographic optima
- `pareto-ihs-norcf`: ParetoIHS without reduced cost fixing
- `pareto-ihs-nowce`: ParetoIHS without WCE
- `pareto-ihs-nomin`: ParetoIHS without core minimization
- `pareto-ihs-noseeding`: ParetoIHS without constraint seeding
- `pareto-ihs-cb`: ParetoIHS with core boosting

Furthermore, the `progress-<family>` files contain the data of how the
algorithms progress over time.

## Used Commands

### Running the Algorithms

These are the commands used for running the configurations equivalent to
the experiments in the paper.

#### P-Minimal

No core boosting
```bash
scuttle p-minimal p-minimal --core-boosting=false -v2 [instance]
```

With core boosting
```bash
scuttle p-minimal p-minimal --core-boosting=true -v2 [instance]
```

#### ClmIhs

```bash
open-wbo -cardinality=1 -pb=2 -no-bmo -formula=2 -algorithm=9 -pbobjf=4 -eps=1 -part_par=100 -apmode=1 -no-cubounds -no-clbounds [instance]
```

#### MipPd

```bash
scuttle mip-pd --mip-solver=gurobi12 --multipliers=ones -v2 [instance]
```

#### ParetoIHS

Best configuration
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=ones --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```

Normalized scalarization constants
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=normalized --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```

Lexicographic scalarization constants
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=lexicographic --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```

Lexicographic scalarization constants
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=lexicographic --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```

No precomputation
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=ones --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=0 --reduced-cost-fixing=true [instance]
```

No reduced cost fixing
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=ones --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=false [instance]
```

No WCE
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=ones --ihs-core-minimization=full --ihs-core-extraction=single -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```

No core minimization
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=ones --ihs-core-minimization=none --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```

No constraint seeding
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=false --use-starting-points=false --multipliers=ones --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true --seeding=false [instance]
```

Core boosting
```bash
scuttle pareto-ihs --hitting-set-solver=gurobi12 --core-boosting=true --ihs-cb-treatment=translate-katsirelos-reform --use-starting-points=false --multipliers=ones --ihs-core-minimization=full --ihs-core-extraction=wce -v2 --precompute-lexicographic=8 --reduced-cost-fixing=true [instance]
```
