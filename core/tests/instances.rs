use std::{fs::File, io::BufWriter};

use libtest_mimic::{Arguments, Failed};
use pigeons::Proof;
use scuttle_core::{
    algs::{InitDefaultBlock, Solve},
    options::{
        CoreMinimization, EnumOptions, IhsCbOptions, IhsCbTreatment, IhsOptions, MipPdOptions,
        ObjectiveMultipliers,
    },
    types::{Instance, ParetoFront},
    CoreBoost, CoreBoostingOptions, Init, InitCert, InitCertDefaultBlock, KernelFunctions,
    KernelOptions,
};

use setup::TestSetup;

fn main() {
    let args = Arguments::from_args();
    let mut tests = vec![];

    let vars = [
        ("", KernelOptions::default()),
        (
            "no-heur",
            KernelOptions {
                heuristic_improvements: scuttle_core::options::HeurImprOptions::none(),
                ..KernelOptions::default()
            },
        ),
        (
            "all-heur",
            KernelOptions {
                heuristic_improvements: scuttle_core::options::HeurImprOptions::all(),
                ..KernelOptions::default()
            },
        ),
        (
            "other-reserve",
            KernelOptions {
                reserve_enc_vars: !scuttle_core::options::KernelOptions::default().reserve_enc_vars,
                ..KernelOptions::default()
            },
        ),
        (
            "other-sol-guided",
            KernelOptions {
                solution_guided_search: !scuttle_core::options::KernelOptions::default()
                    .solution_guided_search,
                ..KernelOptions::default()
            },
        ),
    ];

    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "p-minimal",
                id,
                run_test::<scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .collect_tests(),
        );
        tests.extend(
            TestSetup::new(
                "lower-bounding",
                id,
                run_test::<scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .collect_tests(),
        );
        tests.extend(
            TestSetup::new(
                "bioptsat",
                id,
                run_test::<scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .filter(|m| m.n_objs > 2)
            .collect_tests(),
        );
    }

    let vars = [
        ("", (KernelOptions::default(), IhsOptions::default())),
        (
            "nomin",
            (
                KernelOptions::default(),
                IhsOptions {
                    core_minimization: CoreMinimization::None,
                    ..IhsOptions::default()
                },
            ),
        ),
        (
            "other-wce",
            (
                KernelOptions::default(),
                IhsOptions {
                    wce: !IhsOptions::default().wce,
                    ..IhsOptions::default()
                },
            ),
        ),
        (
            "nomin-other-wce",
            (
                KernelOptions::default(),
                IhsOptions {
                    wce: !IhsOptions::default().wce,
                    core_minimization: CoreMinimization::None,
                    ..IhsOptions::default()
                },
            ),
        ),
        (
            "randmult",
            (
                KernelOptions::default(),
                IhsOptions {
                    multipliers: ObjectiveMultipliers::NormalizedRandom,
                    ..IhsOptions::default()
                },
            ),
        ),
        (
            "lexmult",
            (
                KernelOptions::default(),
                IhsOptions {
                    multipliers: ObjectiveMultipliers::Lexicographic,
                    ..IhsOptions::default()
                },
            ),
        ),
        (
            "no-precomplex",
            (
                KernelOptions::default(),
                IhsOptions {
                    precompute_lexicographic: 0,
                    ..IhsOptions::default()
                },
            ),
        ),
        (
            "other-rcf",
            (
                KernelOptions::default(),
                IhsOptions {
                    reduced_cost_fixing: !IhsOptions::default().reduced_cost_fixing,
                    ..IhsOptions::default()
                },
            ),
        ),
    ];
    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "pareto-ihs<highs>",
                id,
                run_test::<
                    scuttle_core::ParetoIhs<
                        rustsat_cadical::CaDiCaL<'static, 'static>,
                        hitting_sets::HighsSolver,
                    >,
                >,
                opts,
            )
            .allow_dominated(true)
            .collect_tests(),
        );
    }
    #[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "pareto-ihs<gurobi>",
                id,
                run_test::<
                    scuttle_core::ParetoIhs<
                        rustsat_cadical::CaDiCaL<'static, 'static>,
                        hitting_sets::GurobiSolver,
                    >,
                >,
                opts,
            )
            .allow_dominated(true)
            .collect_tests(),
        );
    }

    let vars = [
        (
            "cb-ignore",
            IhsCbOptions {
                treatment: IhsCbTreatment::Ignore,
            },
        ),
        (
            "cb-translate",
            IhsCbOptions {
                treatment: IhsCbTreatment::Translate,
            },
        ),
        (
            "cb-translate-reform",
            IhsCbOptions {
                treatment: IhsCbTreatment::TranslateReform,
            },
        ),
        (
            "cb-abstract",
            IhsCbOptions {
                treatment: IhsCbTreatment::Abstract,
            },
        ),
        (
            "cb-ihs",
            IhsCbOptions {
                treatment: IhsCbTreatment::Ihs,
            },
        ),
    ];
    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "pareto-ihs<highs>",
                id,
                run_cb_test::<
                    scuttle_core::ParetoIhs<
                        rustsat_cadical::CaDiCaL<'static, 'static>,
                        hitting_sets::HighsSolver,
                    >,
                >,
                opts,
            )
            .allow_dominated(true)
            .collect_tests(),
        );
    }
    #[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "pareto-ihs<gurobi>",
                id,
                run_cb_test::<
                    scuttle_core::ParetoIhs<
                        rustsat_cadical::CaDiCaL<'static, 'static>,
                        hitting_sets::GurobiSolver,
                    >,
                >,
                opts,
            )
            .allow_dominated(true)
            .collect_tests(),
        );
    }

    let vars = [
        ("", MipPdOptions::default()),
        (
            "randmult",
            MipPdOptions {
                multipliers: ObjectiveMultipliers::NormalizedRandom,
                ..MipPdOptions::default()
            },
        ),
        (
            "lexmult",
            MipPdOptions {
                multipliers: ObjectiveMultipliers::Lexicographic,
                ..MipPdOptions::default()
            },
        ),
        (
            "precomplex",
            MipPdOptions {
                precompute_lexicographic: 8,
                ..MipPdOptions::default()
            },
        ),
    ];
    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "mip-pd<highs>",
                id,
                run_mippd_test::<hitting_sets::HighsSolver>,
                opts,
            )
            .collect_tests(),
        );
        #[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
        tests.extend(
            TestSetup::new(
                "mip-pd<gurobi>",
                id,
                run_mippd_test::<hitting_sets::GurobiSolver>,
                opts,
            )
            .collect_tests(),
        );
    }

    let vars = [
        ("cb", CoreBoostingOptions::default()),
        (
            "cb-rebase",
            CoreBoostingOptions {
                rebase: true,
                ..CoreBoostingOptions::default()
            },
        ),
    ];

    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "p-minimal",
                id,
                run_cb_test::<scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts.clone(),
            )
            .collect_tests(),
        );
        tests.extend(
            TestSetup::new(
                "lower-bounding",
                id,
                run_cb_test::<
                    scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts.clone(),
            )
            .collect_tests(),
        );
        tests.extend(
            TestSetup::new(
                "bioptsat",
                id,
                run_cb_test::<scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .filter(|m| m.n_objs > 2)
            .collect_tests(),
        );
    }

    let vars = [
        ("cert", KernelOptions::default()),
        (
            "cert:no-heur",
            KernelOptions {
                heuristic_improvements: scuttle_core::options::HeurImprOptions::none(),
                ..KernelOptions::default()
            },
        ),
        (
            "cert:all-heur",
            KernelOptions {
                heuristic_improvements: scuttle_core::options::HeurImprOptions::all(),
                ..KernelOptions::default()
            },
        ),
        (
            "cert:other-reserve",
            KernelOptions {
                reserve_enc_vars: !scuttle_core::options::KernelOptions::default().reserve_enc_vars,
                ..KernelOptions::default()
            },
        ),
        (
            "cert:other-sol-guided",
            KernelOptions {
                solution_guided_search: !scuttle_core::options::KernelOptions::default()
                    .solution_guided_search,
                ..KernelOptions::default()
            },
        ),
    ];

    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "p-minimal",
                id,
                run_certified_test::<
                    scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts,
            )
            .collect_certified_tests(),
        );
        tests.extend(
            TestSetup::new(
                "lower-bounding",
                id,
                run_certified_test::<
                    scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts,
            )
            .collect_certified_tests(),
        );
        tests.extend(
            TestSetup::new(
                "bioptsat",
                id,
                run_certified_test::<
                    scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts,
            )
            .filter(|m| m.n_objs > 2)
            .collect_certified_tests(),
        );
    }

    let vars = [
        ("cert:cb", CoreBoostingOptions::default()),
        (
            "cert:cb-rebase",
            CoreBoostingOptions {
                rebase: true,
                ..CoreBoostingOptions::default()
            },
        ),
    ];

    for (id, opts) in vars {
        tests.extend(
            TestSetup::new(
                "p-minimal",
                id,
                run_certified_cb_test::<
                    scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts.clone(),
            )
            .collect_certified_tests(),
        );
        tests.extend(
            TestSetup::new(
                "lower-bounding",
                id,
                run_certified_cb_test::<
                    scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts.clone(),
            )
            .collect_certified_tests(),
        );
        tests.extend(
            TestSetup::new(
                "bioptsat",
                id,
                run_certified_cb_test::<
                    scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>,
                >,
                opts,
            )
            .filter(|m| m.n_objs > 2)
            .collect_certified_tests(),
        );
    }

    let opts = KernelOptions {
        enumeration: EnumOptions::Solutions(None),
        ..KernelOptions::default()
    };
    tests.extend(
        TestSetup::new(
            "p-minimal",
            "enum",
            run_test::<scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>>,
            opts,
        )
        .sol_enum(true)
        .filter(|m| !m.enum_data)
        .collect_tests(),
    );
    tests.extend(
        TestSetup::new(
            "lower-bounding",
            "enum",
            run_test::<scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>>,
            opts,
        )
        .sol_enum(true)
        .filter(|m| !m.enum_data)
        .collect_tests(),
    );
    tests.extend(
        TestSetup::new(
            "bioptsat",
            "enum",
            run_test::<scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>>,
            opts,
        )
        .sol_enum(true)
        .filter(|m| !m.enum_data || m.n_objs > 2)
        .collect_tests(),
    );

    #[cfg(feature = "maxpre")]
    {
        let opts = KernelOptions::default();
        let techs = "[[uvsrgc]VRTG]";
        tests.extend(
            TestSetup::new(
                "p-minimal",
                "prepro",
                run_test::<scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .preprocessing(Some(techs))
            .collect_tests(),
        );
        tests.extend(
            TestSetup::new(
                "lower-bounding",
                "prepro",
                run_test::<scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .preprocessing(Some(techs))
            .collect_tests(),
        );
        tests.extend(
            TestSetup::new(
                "bioptsat",
                "prepro",
                run_test::<scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>>,
                opts,
            )
            .preprocessing(Some(techs))
            .filter(|m| m.n_objs > 2)
            .collect_tests(),
        );
    }

    libtest_mimic::run(&args, tests).exit();
}

fn run_test<Alg>(inst: Instance, opts: <Alg as Init>::Options) -> Result<ParetoFront, Failed>
where
    Alg: InitDefaultBlock + Solve,
{
    let mut alg = Alg::from_instance_default_blocking(inst, opts)?;
    match alg.solve(scuttle_core::Limits::none()) {
        scuttle_core::MaybeTerminatedError::Done(_) => (),
        scuttle_core::MaybeTerminatedError::Terminated(t) => {
            return Err(format!("solving terminated early: {t}").into())
        }
        scuttle_core::MaybeTerminatedError::Error(e) => {
            return Err(format!("solving error: {e}").into())
        }
    }
    Ok(alg.pareto_front())
}

fn run_cb_test<Alg>(
    inst: Instance,
    cb_opts: <Alg as CoreBoost>::Options,
) -> Result<ParetoFront, Failed>
where
    Alg: InitDefaultBlock + Solve + CoreBoost,
{
    let mut alg = Alg::from_instance_default_blocking(inst, <Alg as Init>::Options::default())?;
    let cont = match alg.core_boost(cb_opts) {
        scuttle_core::MaybeTerminatedError::Done(cont) => cont,
        scuttle_core::MaybeTerminatedError::Terminated(t) => {
            return Err(format!("solving terminated early: {t}").into())
        }
        scuttle_core::MaybeTerminatedError::Error(e) => {
            return Err(format!("solving error: {e}").into())
        }
    };
    if cont {
        match alg.solve(scuttle_core::Limits::none()) {
            scuttle_core::MaybeTerminatedError::Done(_) => (),
            scuttle_core::MaybeTerminatedError::Terminated(t) => {
                return Err(format!("solving terminated early: {t}").into())
            }
            scuttle_core::MaybeTerminatedError::Error(e) => {
                return Err(format!("solving error: {e}").into())
            }
        }
    }
    Ok(alg.pareto_front())
}

fn run_certified_test<Alg>(
    inst: Instance,
    proof: Proof<BufWriter<File>>,
    opts: <Alg as Init>::Options,
) -> Result<ParetoFront, Failed>
where
    Alg: InitCert<ProofWriter = BufWriter<File>> + InitCertDefaultBlock + Solve,
{
    let mut alg = Alg::from_instance_default_blocking_cert(inst, opts, proof)?;
    match alg.solve(scuttle_core::Limits::none()) {
        scuttle_core::MaybeTerminatedError::Done(_) => (),
        scuttle_core::MaybeTerminatedError::Terminated(t) => {
            return Err(format!("solving terminated early: {t}").into())
        }
        scuttle_core::MaybeTerminatedError::Error(e) => {
            return Err(format!("solving error: {e}").into())
        }
    }
    Ok(alg.pareto_front())
}

fn run_certified_cb_test<Alg>(
    inst: Instance,
    proof: Proof<BufWriter<File>>,
    cb_opts: <Alg as CoreBoost>::Options,
) -> Result<ParetoFront, Failed>
where
    Alg: InitCert<ProofWriter = BufWriter<File>> + InitCertDefaultBlock + Solve + CoreBoost,
{
    let mut alg =
        Alg::from_instance_default_blocking_cert(inst, <Alg as Init>::Options::default(), proof)?;
    let cont = match alg.core_boost(cb_opts) {
        scuttle_core::MaybeTerminatedError::Done(cont) => cont,
        scuttle_core::MaybeTerminatedError::Terminated(t) => {
            return Err(format!("solving terminated early: {t}").into())
        }
        scuttle_core::MaybeTerminatedError::Error(e) => {
            return Err(format!("solving error: {e}").into())
        }
    };
    if cont {
        match alg.solve(scuttle_core::Limits::none()) {
            scuttle_core::MaybeTerminatedError::Done(_) => (),
            scuttle_core::MaybeTerminatedError::Terminated(t) => {
                return Err(format!("solving terminated early: {t}").into())
            }
            scuttle_core::MaybeTerminatedError::Error(e) => {
                return Err(format!("solving error: {e}").into())
            }
        }
    }
    Ok(alg.pareto_front())
}

fn run_mippd_test<Hss>(inst: Instance, opts: MipPdOptions) -> Result<ParetoFront, Failed>
where
    Hss: hitting_sets::HittingSetSolver,
{
    let mut alg = scuttle_core::MipPd::<Hss>::from_instance_default_blocking(inst, opts)?;
    match alg.solve(scuttle_core::Limits::none()) {
        scuttle_core::MaybeTerminatedError::Done(_) => (),
        scuttle_core::MaybeTerminatedError::Terminated(t) => {
            return Err(format!("solving terminated early: {t}").into())
        }
        scuttle_core::MaybeTerminatedError::Error(e) => {
            return Err(format!("solving error: {e}").into())
        }
    }
    Ok(alg.pareto_front())
}

mod setup {
    use std::{
        ffi::OsStr,
        fs::File,
        io::{BufRead, BufReader, BufWriter},
        path::Path,
    };

    use libtest_mimic::{Failed, Trial};
    use pigeons::Proof;
    use scuttle_core::types::{Instance, ParetoFront};

    pub struct TestSetup<'a, F, O> {
        run_fn: F,
        opts: O,
        alg: &'a str,
        variant: &'a str,
        sol_enum: bool,
        allow_dominated: bool,
        filter: Box<dyn Fn(Meta) -> bool>,
        #[cfg(feature = "maxpre")]
        techniques: Option<&'static str>,
    }

    #[derive(Debug, Copy, Clone)]
    pub struct Meta {
        pub n_objs: usize,
        pub enum_data: bool,
    }

    impl Default for Meta {
        fn default() -> Self {
            Self {
                n_objs: Default::default(),
                enum_data: true,
            }
        }
    }

    impl<'a, F, O> TestSetup<'a, F, O> {
        pub fn new(alg: &'a str, variant: &'a str, run_fn: F, opts: O) -> Self {
            Self {
                run_fn,
                opts,
                alg,
                variant,
                sol_enum: false,
                allow_dominated: false,
                filter: Box::new(|_| false),
                #[cfg(feature = "maxpre")]
                techniques: None,
            }
        }

        pub fn filter(mut self, filter: impl Fn(Meta) -> bool + 'static) -> Self {
            self.filter = Box::new(filter);
            self
        }

        fn kind(&self) -> String {
            format!(
                "{}{}{}",
                self.alg,
                if self.variant.is_empty() { "" } else { ":" },
                self.variant
            )
        }

        fn ignore_or_skip(&self, path: &Path) -> Decision {
            let prefix = match path.extension() {
                Some(ext) if ext == OsStr::new("mcnf") => 'c',
                Some(ext) if ext == OsStr::new("opb") => '*',
                _ => panic!("unknown file extension"),
            };
            for line in
                BufReader::new(File::open(path).expect("failed to open instance file")).lines()
            {
                let line = line.expect("failed to read test config");
                let Some(line) = line.strip_prefix(prefix) else {
                    return Decision::Keep;
                };
                if let Some(meta) = line.trim_start().strip_prefix("meta:") {
                    let mut mv = Meta::default();
                    for m in meta.split(',') {
                        let (key, val) = m.split_once('=').expect("invalid meta format");
                        match key {
                            "n-objs" => {
                                mv.n_objs = val.trim().parse().expect("invalid meta format")
                            }
                            "enum-data" => mv.enum_data = val.trim() == "true",
                            _ => eprintln!("ignoring meta key {key}"),
                        }
                    }
                    if (*self.filter)(mv) {
                        return Decision::Skip;
                    }
                };
                if line.trim() == "no-test" {
                    return Decision::Skip;
                }
                if line.trim() == "ignore-test" {
                    return Decision::Ignore;
                }
                let Some(line) = line.strip_prefix(" ignore-test:") else {
                    continue;
                };
                if line.trim() == self.alg {
                    return Decision::Ignore;
                }
                if line.trim() == self.kind() {
                    return Decision::Ignore;
                }
            }
            Decision::Keep
        }
    }

    impl<F, O> TestSetup<'_, F, O>
    where
        F: Fn(Instance, O) -> Result<ParetoFront, Failed> + Clone + Send + 'static,
        O: Clone + Send + 'static,
    {
        pub fn sol_enum(mut self, val: bool) -> Self {
            self.sol_enum = val;
            self
        }

        pub fn allow_dominated(mut self, val: bool) -> Self {
            self.allow_dominated = val;
            self
        }

        #[cfg(feature = "maxpre")]
        pub fn preprocessing(mut self, techniques: Option<&'static str>) -> Self {
            self.techniques = techniques;
            self
        }

        pub fn collect_tests(self) -> Vec<Trial> {
            let manifest_dir = env!("CARGO_MANIFEST_DIR");
            let mut tests = vec![];
            for entry in std::fs::read_dir(format!("{manifest_dir}/data/"))
                .expect("failed to find test instances")
            {
                let entry = entry.unwrap();
                let file_type = entry.file_type().unwrap();
                let path = entry.path();
                if file_type.is_file() {
                    match path.extension() {
                        Some(ext) if ext == OsStr::new("mcnf") || ext == OsStr::new("opb") => {
                            let name = path.file_stem().unwrap().to_str().unwrap().to_string();
                            if name == "empty" {
                                continue;
                            }
                            let dec = self.ignore_or_skip(&path);
                            if dec == Decision::Skip {
                                // eprintln!("filtered out file `{path:?}` for {}", self.kind());
                                continue;
                            }
                            let run_fn = self.run_fn.clone();
                            let opts = self.opts.clone();
                            #[cfg(not(feature = "maxpre"))]
                            tests.push(
                                Trial::test(name, move || {
                                    run_test(
                                        &path,
                                        run_fn,
                                        opts,
                                        self.sol_enum,
                                        self.allow_dominated,
                                    )
                                })
                                .with_kind(self.kind())
                                .with_ignored_flag(dec == Decision::Ignore),
                            );
                            #[cfg(feature = "maxpre")]
                            if let Some(tech) = self.techniques {
                                tests.push(
                                    Trial::test(name, move || {
                                        run_prepro_test(&path, run_fn, opts, tech)
                                    })
                                    .with_kind(self.kind())
                                    .with_ignored_flag(dec == Decision::Ignore),
                                );
                            } else {
                                tests.push(
                                    Trial::test(name, move || {
                                        run_test(&path, run_fn, opts, self.sol_enum)
                                    })
                                    .with_kind(self.kind())
                                    .with_ignored_flag(dec == Decision::Ignore),
                                );
                            };
                        }
                        _ => eprintln!("skipping file `{path:?}`"),
                    }
                } else if file_type.is_dir() {
                    eprintln!("skipping subdir `{path:?}`");
                }
            }
            tests
        }
    }

    impl<F, O> TestSetup<'_, F, O>
    where
        F: Fn(Instance, Proof<BufWriter<File>>, O) -> Result<ParetoFront, Failed>
            + Clone
            + Send
            + 'static,
        O: Clone + Send + 'static,
    {
        pub fn collect_certified_tests(self) -> Vec<Trial> {
            let manifest_dir = env!("CARGO_MANIFEST_DIR");
            let mut tests = vec![];
            for entry in std::fs::read_dir(format!("{manifest_dir}/data/"))
                .expect("failed to find test instances")
            {
                let entry = entry.unwrap();
                let file_type = entry.file_type().unwrap();
                let path = entry.path();
                if file_type.is_file() {
                    match path.extension() {
                        Some(ext) if ext == OsStr::new("mcnf") || ext == OsStr::new("opb") => {
                            let name = path.file_stem().unwrap().to_str().unwrap().to_string();
                            let dec = self.ignore_or_skip(&path);
                            if dec == Decision::Skip {
                                // eprintln!("filtered out file `{path:?}` for {}", self.kind());
                                continue;
                            }
                            let run_fn = self.run_fn.clone();
                            let opts = self.opts.clone();
                            tests.push(
                                Trial::test(name, move || run_certified_test(&path, run_fn, opts))
                                    .with_kind(self.kind())
                                    .with_ignored_flag(dec == Decision::Ignore),
                            );
                        }
                        _ => eprintln!("skipping file `{path:?}`"),
                    }
                } else if file_type.is_dir() {
                    eprintln!("skipping subdir `{path:?}`");
                }
            }
            tests
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Decision {
        Keep,
        Ignore,
        Skip,
    }

    #[derive(Clone, Copy, Debug)]
    enum ParetoCmp {
        Equal,
        ADomB,
        BDomA,
        Incomparable,
    }

    fn pareto_compare(a: &[isize], b: &[isize]) -> ParetoCmp {
        a.iter()
            .zip(b)
            .fold(ParetoCmp::Equal, |cmp, (a, b)| match a.cmp(b) {
                std::cmp::Ordering::Less => match cmp {
                    ParetoCmp::Equal | ParetoCmp::ADomB => ParetoCmp::ADomB,
                    ParetoCmp::BDomA | ParetoCmp::Incomparable => ParetoCmp::Incomparable,
                },
                std::cmp::Ordering::Equal => cmp,
                std::cmp::Ordering::Greater => match cmp {
                    ParetoCmp::Equal | ParetoCmp::BDomA => ParetoCmp::BDomA,
                    ParetoCmp::ADomB | ParetoCmp::Incomparable => ParetoCmp::Incomparable,
                },
            })
    }

    fn check_pf_shape(
        path: &Path,
        pf: ParetoFront,
        sol_enum: bool,
        allow_dominated: bool,
    ) -> Result<(), Failed> {
        let prefix = match path.extension() {
            Some(ext) if ext == OsStr::new("mcnf") => 'c',
            Some(ext) if ext == OsStr::new("opb") => '*',
            _ => panic!("unknown file extension"),
        };
        let mut truth = rustsat::types::RsHashSet::<(Vec<isize>, usize)>::default();
        // filter out dominated points
        let pf: ParetoFront = if allow_dominated {
            let mut points: Vec<_> = pf.into_iter().collect();
            dbg!(points.len());
            let mut new_last = 0;
            'outer: for last in 0..points.len() {
                points.swap(last, new_last);
                for cmp in 0..new_last {
                    match pareto_compare(points[cmp].costs(), points[new_last].costs()) {
                        ParetoCmp::Equal => {
                            dbg!(points[cmp].costs());
                            dbg!(points[new_last].costs());
                            let (head, tail) = points.split_at_mut(new_last);
                            for sol in tail[0].iter() {
                                head[cmp].add_sol(sol.clone())
                            }
                            continue 'outer;
                        }
                        ParetoCmp::ADomB => continue 'outer,
                        ParetoCmp::BDomA => {
                            points.swap(cmp, new_last);
                            // check whether cmp+1..new_last is dominated by cmp
                            let mut other = cmp + 1;
                            while other < new_last {
                                match pareto_compare(points[cmp].costs(), points[other].costs()) {
                                    ParetoCmp::Equal => {
                                        let (head, tail) = points.split_at_mut(other);
                                        for sol in tail[0].iter() {
                                            head[cmp].add_sol(sol.clone())
                                        }
                                        new_last -= 1;
                                        points.swap(other, new_last);
                                    }
                                    ParetoCmp::ADomB => {
                                        new_last -= 1;
                                        points.swap(other, new_last);
                                    }
                                    ParetoCmp::BDomA => unreachable!(),
                                    ParetoCmp::Incomparable => {
                                        other += 1;
                                    }
                                }
                            }
                            continue 'outer;
                        }
                        ParetoCmp::Incomparable => {}
                    }
                }
                new_last += 1;
            }
            points.truncate(new_last);
            dbg!(points.len());
            points.into_iter().collect()
        } else {
            pf
        };

        for line in BufReader::new(File::open(path).expect("failed to open instance file")).lines()
        {
            let line = line.expect("failed to read test config");
            let Some(line) = line.strip_prefix(prefix) else {
                break;
            };
            let Some(line) = line.strip_prefix(" nd (") else {
                continue;
            };
            let (costs, count) = line.split_once(')').expect("invalid nd specification");
            let costs: Vec<isize> = costs
                .split(',')
                .map(|cst| cst.trim().parse().expect("invalid cost specification"))
                .collect();
            let count: usize = if sol_enum {
                count.trim_start().strip_prefix(',').map_or(1, |cnt| {
                    cnt.trim().parse().expect("invalid count specification")
                })
            } else {
                1
            };
            truth.insert((costs, count));
        }
        if pf.len() != truth.len() {
            return Err(format!(
                "pareto front length mismatch: was {}, should be {}",
                pf.len(),
                truth.len()
            )
            .into());
        }
        let pf: rustsat::types::RsHashSet<(Vec<isize>, usize)> = pf
            .into_iter()
            .map(|pp| (pp.costs().to_vec(), if sol_enum { pp.n_sols() } else { 1 }))
            .collect();
        if pf != truth {
            return Err(format!(
                "pareto front shape mismatch:\n  was       {pf:?},\n  should be {truth:?}",
            )
            .into());
        }
        Ok(())
    }

    fn run_test<F, O>(
        path: &Path,
        run_fn: F,
        opts: O,
        sol_enum: bool,
        allow_dominated: bool,
    ) -> Result<(), Failed>
    where
        F: Fn(Instance, O) -> Result<ParetoFront, Failed>,
    {
        let (_, inst) = scuttle_core::prepro::to_clausal(
            scuttle_core::prepro::parse(
                path,
                scuttle_core::prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            &None,
        )
        .expect("failed to parse instance");
        check_pf_shape(path, run_fn(inst, opts)?, sol_enum, allow_dominated)
    }

    #[cfg(feature = "maxpre")]
    fn run_prepro_test<F, O>(
        path: &Path,
        run_fn: F,
        opts: O,
        techniques: &str,
    ) -> Result<(), Failed>
    where
        F: Fn(Instance, O) -> Result<ParetoFront, Failed>,
    {
        use maxpre::PreproClauses;
        let (mut prepro, inst) = scuttle_core::prepro::max_pre(
            scuttle_core::prepro::parse(
                path,
                scuttle_core::prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            techniques,
            true,
        )
        .expect("failed to parse instance");
        check_pf_shape(
            path,
            run_fn(inst, opts)?.convert_solutions(&mut |s| prepro.reconstruct(s)),
            false,
            false,
        )
    }

    fn run_certified_test<F, O>(path: &Path, run_fn: F, opts: O) -> Result<(), Failed>
    where
        F: Fn(Instance, Proof<BufWriter<File>>, O) -> Result<ParetoFront, Failed>,
    {
        let proof_path = new_temp_path();
        let input_path = new_temp_path();
        let (proof, inst) = scuttle_core::prepro::to_clausal(
            scuttle_core::prepro::parse(
                path,
                scuttle_core::prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            &Some((proof_path.to_path_buf(), Some(input_path.to_path_buf()))),
        )
        .expect("failed to parse instance");
        let proof = proof.unwrap();
        print_file(&input_path);
        check_pf_shape(path, run_fn(inst, proof, opts)?, false, false)?;
        verify_proof(input_path, proof_path)
    }

    fn new_temp_path() -> tempfile::TempPath {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary file");
        file.into_temp_path()
    }

    fn print_file<P: AsRef<std::path::Path>>(path: P) {
        use std::io::BufRead;
        println!("Printing file: {:?}", path.as_ref());
        println!("=============");
        for line in
            std::io::BufReader::new(std::fs::File::open(path).expect("could not open file")).lines()
        {
            println!("{}", line.unwrap());
        }
        println!("=============");
    }

    fn verify_proof<P1: AsRef<std::path::Path>, P2: AsRef<std::path::Path>>(
        instance: P1,
        proof: P2,
    ) -> Result<(), Failed> {
        println!("start checking proof");
        let out = std::process::Command::new("veripb")
            .arg("--forceCheckDeletion")
            .arg(instance.as_ref())
            .arg(proof.as_ref())
            .output()
            .expect("failed to run veripb");
        print_file(proof);
        if out.status.success() {
            return Ok(());
        }
        Err(format!("verification failed: {out:?}").into())
    }
}
