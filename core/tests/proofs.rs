macro_rules! check_pf_shape {
    ($pf:expr, $t:expr) => {{
        let pps_set: rustsat::types::RsHashSet<(Vec<isize>, usize)> = $pf
            .into_iter()
            .map(|pp| (pp.costs().clone(), pp.n_sols()))
            .collect();
        let shape_set: rustsat::types::RsHashSet<(Vec<isize>, usize)> = $t.into_iter().collect();
        assert_eq!(pps_set, shape_set);
    }};
}

macro_rules! test_instance {
    ($s:ty, $o:expr, $i:expr, $t:expr) => {{
        use scuttle_core::{prepro, InitCertDefaultBlock, KernelFunctions, Solve};
        let inst = prepro::handle_soft_clauses(
            prepro::parse(
                $i,
                prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
        );
        let (proof, path) = crate::new_proof(inst.n_clauses(), false);
        let mut solver = <$s>::from_instance_default_blocking_cert(inst, $o, proof).unwrap();
        solver.solve(scuttle_core::Limits::none()).unwrap();
        let pf = solver.pareto_front();
        drop(solver); // ensure proof is concluded
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
        crate::verify_proof("./veripb-input.opb", path);
    }};
}

macro_rules! small {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/small.mcnf",
            vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)]
        )
    };
}

macro_rules! medium {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/medium.mcnf",
            vec![
                (vec![0, 10], 1),
                (vec![2, 8], 1),
                (vec![4, 6], 1),
                (vec![6, 4], 1),
                (vec![8, 2], 1),
                (vec![10, 0], 1),
            ]
        )
    };
}

fn new_proof(
    num_constraints: usize,
    optimization: bool,
) -> (
    pidgeons::Proof<std::io::BufWriter<std::fs::File>>,
    tempfile::TempPath,
) {
    let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
    let (file, path) = file.into_parts();
    (
        pidgeons::Proof::new(std::io::BufWriter::new(file), num_constraints, optimization)
            .expect("failed to start proof"),
        path,
    )
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

fn verify_proof<P1: AsRef<std::path::Path>, P2: AsRef<std::path::Path>>(instance: P1, proof: P2) {
    println!("start checking proof");
    let out = std::process::Command::new("veripb")
        .arg(instance.as_ref())
        .arg(proof.as_ref())
        .output()
        .expect("failed to run veripb");
    print_file(proof);
    if out.status.success() {
        return;
    }
    panic!("verification failed: {out:?}")
}

mod pmin {
    type S = scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>;

    #[test]
    fn pmin_small_cert() {
        small!(S, scuttle_core::KernelOptions::default());
    }

    #[test]
    fn pmin_medium_cert() {
        medium!(S, scuttle_core::KernelOptions::default());
        panic!()
    }
}