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
        let vpb_input =
            tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        let (vpb_input, vpb_input_path) = vpb_input.into_parts();
        let mut writer = std::io::BufWriter::new(vpb_input);
        let iter = inst
            .iter_clauses()
            .map(|cl| rustsat::instances::fio::opb::FileLine::<Option<_>>::Clause(cl.clone()));
        rustsat::instances::fio::opb::write_opb_lines(
            &mut writer,
            iter,
            rustsat::instances::fio::opb::Options::default(),
        )
        .unwrap();
        drop(writer);
        crate::print_file(&vpb_input_path);
        let (proof, path) = crate::new_proof(inst.n_clauses(), false);
        let mut solver = <$s>::from_instance_default_blocking_cert(inst, $o, proof).unwrap();
        solver.solve(scuttle_core::Limits::none()).unwrap();
        let pf = solver.pareto_front();
        drop(solver); // ensure proof is concluded
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
        crate::verify_proof(vpb_input_path, path);
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

macro_rules! medium_weighted {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/medium-weighted.mcnf",
            vec![
                (vec![0, 15], 1),
                (vec![1, 14], 1),
                (vec![2, 13], 1),
                (vec![3, 12], 1),
                (vec![4, 11], 1),
                (vec![5, 10], 1),
                (vec![6, 9], 1),
                (vec![7, 8], 1),
                (vec![8, 7], 1),
                (vec![9, 6], 1),
                (vec![10, 5], 1),
                (vec![11, 4], 1),
                (vec![12, 3], 1),
                (vec![13, 2], 1),
                (vec![14, 1], 1),
                (vec![15, 0], 1),
            ]
        )
    };
}

macro_rules! four {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/four.mcnf",
            vec![
                (vec![0, 0, 0, 1], 1),
                (vec![0, 0, 1, 0], 1),
                (vec![0, 1, 0, 0], 1),
                (vec![1, 0, 0, 0], 1),
            ]
        )
    };
}

macro_rules! set_cover_3 {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/set-cover-3.mcnf",
            vec![
                (vec![67, 221, 130], 1),
                (vec![229, 54, 151], 1),
                (vec![136, 169, 28], 1),
                (vec![75, 214, 149], 1),
                (vec![223, 64, 152], 1),
                (vec![230, 160, 49], 1),
                (vec![90, 139, 63], 1),
                (vec![198, 72, 152], 1),
                (vec![101, 255, 59], 1),
                (vec![102, 135, 99], 1),
                (vec![154, 77, 93], 1),
                (vec![207, 114, 87], 1),
                (vec![158, 109, 92], 1),
            ]
        )
    };
}

macro_rules! generate_tests {
    ($mod:ident, $s:ty, $o:expr) => {
        mod $mod {
            #[test]
            fn small_cert() {
                small!($s, $o);
            }

            #[test]
            fn medium_cert() {
                medium!($s, $o);
            }

            #[test]
            fn medium_weighted_cert() {
                medium_weighted!($s, $o);
            }

            #[test]
            fn four_cert() {
                four!($s, $o);
            }

            #[test]
            fn set_cover_3_cert() {
                set_cover_3!($s, $o);
            }
        }
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
        pidgeons::Proof::new_with_conclusion(
            std::io::BufWriter::new(file),
            num_constraints,
            optimization,
            pidgeons::OutputGuarantee::None,
            &pidgeons::Conclusion::<&str>::Unsat(Some(pidgeons::ConstraintId::last(1))),
        )
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
        .arg("--forceCheckDeletion")
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
    generate_tests!(default, super::S, scuttle_core::KernelOptions::default());
}

mod lb {
    type S = scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_tests!(default, super::S, scuttle_core::KernelOptions::default());
}
