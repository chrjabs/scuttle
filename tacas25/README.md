# TACAS 2025 Artefact - Certifying Pareto-Optimality in Multi-Objective Maximum Satisfiability

This is the artefact description to go with the paper "Certifying
Pareto-Optimality in Multi-Objective Maximum Satisfiabillity" for voluntary
evaluation at TACAS 2025.

The artefact is designed to be executed in the [TACAS artefact evaluation
VM](https://doi.org/10.5281/zenodo.7113223) (Ubuntu 22.04 LTS). Building the
software requires internet access, so the network adapter has to be enabled in
the VirtualBox settings of the VM.

## Download Artefact

The artefact can be downloaded from
[Zenodo](https://doi.org/10.5281/zenodo.14731485) and it has the following DOI:
`10.5281/zenodo.14731485`. In the following we assume that the artefact is
unpacked at the location `${ARTEFACT}`.

## Installation

All pieces of software required for running the experiments in our paper can be
installed in the TACAS Ubuntu VM by running the following command:
```bash
${ARTEFACT}/scripts/install.sh`.
```
This will install the following software, which is all included in the
artefact:

- Our implementation: the MO-MaxSAT solver `scuttle` extended with proof
    logging
- The proof checker `VeriPB` (at commit
    `fa86e38016cb7be21d086b84f829fa93b7e93bce`), which was retrieved from
    [GitLab](https://gitlab.com/MIAOresearch/software/VeriPB)
- The `runsolver` tool used for running experiments. Originally from
    [here](https://www.cril.univ-artois.fr/en/software/runsolver/), retrieved from
    [GitHub](https://github.com/chrjabs/runsolver) at commit
    `adf45810890dc9f6db06104d7842c2a26eb48f7a`

## Light Review

To verify that the software was installed correctly for the light review, the following command can be run:

```bash
${ARTEFACT}/scripts/single-experiment.sh ${ARTEFACT}/benchmarks/0ec932de353de4de3bc67c4caec08bb9.mcnf.xz p-minimal cb --core-boosting=true
```

If it produces output similar to the following, especially the last line, where
the number might differ, everything works correctly.

```
Determined ${ARTEFACT} as `/home/tacas23/artefact`
Writing baseline files to `/home/tacas23/artefact/results/0ec932de353de4de3bc67c4caec08bb9.p-minimal.cb.baseline.{out,var,wat}`
Writing proof-logging files to `/home/tacas23/artefact/results/0ec932de353de4de3bc67c4caec08bb9.p-minimal.cb.logging.{out,var,wat,pbp,opb}`
Writing proof-checking files to `/home/tacas23/artefact/results/0ec932de353de4de3bc67c4caec08bb9.p-minimal.cb.veripb.{out,var,wat}`
0ec932de353de4de3bc67c4caec08bb9,0.025938,0.057236,2.41056
```

## Running Experiments

Running all experiments presented in our paper took many hours on a compute
cluster. In the following we describe how to run a subset of the experiments
that should be possible to run in about one hour. For completeness, a script
for running _all_ experiments is provided as
`${ARTEFACT}/scripts/experiments-all.sh`.

For the artefact evaluation we include a script that runs experiments for the
`P-Minimal` algorithm with core boosting on 6 relatively small instances.
These experiments can be run with the following command:
```bash
${ARTEFACT}/scripts/experiments.sh > ${ARTEFACT}/results.csv
```

This will write a CSV file with the experiment results to `${ARTEFACT}/results.csv`.
The CSV file has the following columns:

| CSV Column Name          | Description                                                                                         |
| ------------------------ | --------------------------------------------------------------------------------------------------- |
| `inst-hash`              | A hash value identifying each instance. See the Benchmarks section below.                           |
| `pmin-cb-baseline`       | The CPU runtime in seconds for the solver baseline without proof logging, or `timeout` or `memout`. |
| `pmin-cb-proof-logging`  | The CPU runtime in seconds for the solver run with proof logging, or `timeout` or `memout`.         |
| `pmin-cb-proof-checking` | The CPU runtime in seconds for proof checking with `VeriPB`, or `timeout` or `memout`.              |

Furthermore, all solver and proof checking logs, as well as the proof files will
be written into `${ARTEFACT}/results/`. Note that the read/write speed into
this folder can have a significant impact on the experiment runtime and the
proofs can get quite large (especially when running all experiments).

To compute the average proof-logging overhead in percent for the run
experiments, the following command can be used:
```bash
tail -n+2 ${ARTEFACT}/results.csv | awk -F',' '{sum+=($3/$2)-1;}END{print sum/NR*100;}'
```
Note however, that the write speed of the filesystem for `${ARTEFACT}` can have
a significant impact on the proof-logging overhead, especially for the
instances used here, where running times are relatively low.

Similarly, to compute how much longer proof checking takes, compared to proof
generation, the following command can be used:
```bash
tail -n+2 ${ARTEFACT}/results.csv | awk -F',' '{sum+=($4/$3)-1;}END{print sum/NR*100;}'
```

## Benchmarks

We include all benchmarks we used in our experiments in the artefact, these
benchmarks do not all orginate from our work. We retrieved the instances from
the sources described below and converted them to our `.mcnf` instance format.

The instances are all identified by a hash value, and they are located at
`${ARTEFACT}/benchmarks/<hash>.mcnf.xz`. Metadata for each benchmark, most
notably the domain/family they belong to, can be found in
`${ARTEFACT}/data/mcnf_meta.csv`.

### Benchmark Source

The benchmark set is the same as used in \[2\] and retrieved as described
[here](https://bitbucket.org/coreo-group/scuttle/src/main/cpaior24/README.md)

Originally the instances stem from:
- `set-cover-sc` and `set-cover-ep` were randomly generated in \[1\] and \[2\]
- `packup` instances were generated in \[3\]
- `lidr` instances were generated from data in \[1\]
- `ftp` instances were first used in \[4\] and the original OPB instances
    retrieved from
    [here](https://sat.inesc-id.pt/~jcortes/artifacts/TACAS2023/pbmo/flying-tourist-problem/)
- `spot5` instances were reverse-engineered from single-objective MaxSAT
    instances in \[2\]. The single-objective instances were submitted to the
    MaxSAT Evaluation and are described in \[5\].

## References

- \[1\] Jabs, C. J., Berg, J., Niskanen, A., & Järvisalo, M. (2022).
    _MaxSAT-based bi-objective boolean optimization_. In International Conference on
    Theory and Applications of Satisfiability Testing (pp. 12-1). Schloss
    Dagstuhl-Leibniz-Zentrum für Informatik.
- \[2\] Jabs, C., Berg, J., & Järvisalo, M. (2024, May). _Core Boosting in
    SAT-Based Multi-objective Optimization_. In International Conference on the
    Integration of Constraint Programming, Artificial Intelligence, and Operations
    Research (pp. 1-19). Cham: Springer Nature Switzerland.
- \[3\] Jabs, C., Berg, J., Ihalainen, H., & Järvisalo, M. (2023).
    _Preprocessing in SAT-based multi-objective combinatorial optimization_. In 29th
    International Conference on Principles and Practice of Constraint Programming
    (CP 2023). Schloss Dagstuhl-Leibniz-Zentrum für Informatik.
- \[4\] Cortes, J., Lynce, I., & Manquinho, V. (2023, April). _New core-guided
    and hitting set algorithms for multi-objective combinatorial optimization_. In
    International Conference on Tools and Algorithms for the Construction and
    Analysis of Systems (pp. 55-73). Cham: Springer Nature Switzerland.
- \[5\] Heras, F., Larrosa, J., De Givry, S., & Schiex, T. (2008). _2006 and
    2007 Max-SAT evaluations: Contributed instances_. Journal on Satisfiability,
    Boolean Modeling and Computation, 4(2-4), 239-250.
