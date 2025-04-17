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
        let proof_path = crate::new_temp_path();
        let input_path = crate::new_temp_path();
        let (proof, inst) = prepro::to_clausal(
            prepro::parse(
                $i,
                prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            &Some((proof_path.to_path_buf(), Some(input_path.to_path_buf()))),
        )
        .unwrap();
        let proof = proof.unwrap();
        crate::print_file(&input_path);
        let mut solver = <$s>::from_instance_default_blocking_cert(inst, $o, proof).unwrap();
        solver.solve(scuttle_core::Limits::none()).unwrap();
        let pf = solver.pareto_front();
        drop(solver); // ensure proof is concluded
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
        crate::verify_proof(input_path, proof_path);
    }};
    ($s:ty, $o:expr, $cbo:expr, $i:expr, $t:expr) => {{
        use scuttle_core::{prepro, CoreBoost, InitCertDefaultBlock, KernelFunctions, Solve};
        let proof_path = crate::new_temp_path();
        let input_path = crate::new_temp_path();
        let (proof, inst) = prepro::to_clausal(
            prepro::parse(
                $i,
                prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            &Some((proof_path.to_path_buf(), Some(input_path.to_path_buf()))),
        )
        .unwrap();
        let proof = proof.unwrap();
        crate::print_file(&input_path);
        let mut solver = <$s>::from_instance_default_blocking_cert(inst, $o, proof).unwrap();
        let cont = solver.core_boost($cbo).unwrap();
        if cont {
            solver.solve(scuttle_core::Limits::none()).unwrap();
        }
        let pf = solver.pareto_front();
        drop(solver); // ensure proof is concluded
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
        crate::verify_proof(input_path, proof_path);
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
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

macro_rules! medium_weighted_2 {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/medium-weighted-2.mcnf",
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/medium-weighted-2.mcnf",
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

macro_rules! medium_weighted_3 {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/medium-weighted-3.mcnf",
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/medium-weighted-3.mcnf",
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

macro_rules! core_boost {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/core-boost.mcnf",
            vec![
                (vec![3, 8], 1),
                (vec![4, 6], 1),
                (vec![6, 4], 1),
                (vec![8, 2], 1),
                (vec![11, 0], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/core-boost.mcnf",
            vec![
                (vec![3, 8], 1),
                (vec![4, 6], 1),
                (vec![6, 4], 1),
                (vec![8, 2], 1),
                (vec![11, 0], 1),
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
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
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
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

macro_rules! dal2 {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/dal2.opb",
            vec![
                (vec![19, 4, 8, 0, 0, 0, 0], 1),
                (vec![19, 4, 7, 1, 0, 0, 0], 1),
                (vec![19, 4, 7, 0, 1, 0, 0], 1),
                (vec![19, 4, 6, 1, 1, 0, 0], 1),
                (vec![19, 4, 5, 1, 2, 0, 0], 1),
                (vec![19, 4, 5, 0, 3, 0, 0], 1),
                (vec![19, 4, 6, 0, 2, 0, 0], 1),
                (vec![19, 4, 6, 2, 0, 0, 0], 1),
                (vec![19, 4, 5, 3, 0, 0, 0], 1),
                (vec![19, 4, 5, 2, 1, 0, 0], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/dal2.opb",
            vec![
                (vec![19, 4, 8, 0, 0, 0, 0], 1),
                (vec![19, 4, 7, 1, 0, 0, 0], 1),
                (vec![19, 4, 7, 0, 1, 0, 0], 1),
                (vec![19, 4, 6, 1, 1, 0, 0], 1),
                (vec![19, 4, 5, 1, 2, 0, 0], 1),
                (vec![19, 4, 5, 0, 3, 0, 0], 1),
                (vec![19, 4, 6, 0, 2, 0, 0], 1),
                (vec![19, 4, 6, 2, 0, 0, 0], 1),
                (vec![19, 4, 5, 3, 0, 0, 0], 1),
                (vec![19, 4, 5, 2, 1, 0, 0], 1),
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
            fn medium_weighted_2_cert() {
                medium_weighted_2!($s, $o);
            }

            #[test]
            fn medium_weighted_3_cert() {
                medium_weighted_3!($s, $o);
            }

            #[test]
            fn core_boost_cert() {
                core_boost!($s, $o);
            }

            #[test]
            fn four_cert() {
                four!($s, $o);
            }

            #[test]
            fn set_cover_3_cert() {
                set_cover_3!($s, $o);
            }

            #[test]
            fn dal2() {
                dal2!($s, $o);
            }
        }
    };

    ($mod:ident, $s:ty, $o:expr, $cbo:expr) => {
        mod $mod {
            #[test]
            fn small_cert() {
                small!($s, $o, $cbo);
            }

            #[test]
            fn medium_cert() {
                medium!($s, $o, $cbo);
            }

            #[test]
            fn medium_weighted_cert() {
                medium_weighted!($s, $o, $cbo);
            }

            #[test]
            fn medium_weighted_2_cert() {
                medium_weighted_2!($s, $o, $cbo);
            }

            #[test]
            fn medium_weighted_3_cert() {
                medium_weighted_3!($s, $o, $cbo);
            }

            #[test]
            fn core_boost_cert() {
                core_boost!($s, $o, $cbo);
            }

            #[test]
            fn four_cert() {
                four!($s, $o, $cbo);
            }

            #[test]
            fn set_cover_3_cert() {
                set_cover_3!($s, $o, $cbo);
            }

            #[test]
            fn dal2() {
                dal2!($s, $o, $cbo);
            }
        }
    };
}

macro_rules! generate_biobj_tests {
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
            fn medium_weighted_2_cert() {
                medium_weighted_2!($s, $o);
            }

            #[test]
            fn medium_weighted_3_cert() {
                medium_weighted_3!($s, $o);
            }

            #[test]
            fn core_boost_cert() {
                core_boost!($s, $o);
            }
        }
    };
    ($mod:ident, $s:ty, $o:expr, $cbo:expr) => {
        mod $mod {
            #[test]
            fn small_cert() {
                small!($s, $o, $cbo);
            }

            #[test]
            fn medium_cert() {
                medium!($s, $o, $cbo);
            }

            #[test]
            fn medium_weighted_cert() {
                medium_weighted!($s, $o, $cbo);
            }

            #[test]
            fn medium_weighted_2_cert() {
                medium_weighted_2!($s, $o, $cbo);
            }

            #[test]
            fn medium_weighted_3_cert() {
                medium_weighted_3!($s, $o, $cbo);
            }

            #[test]
            fn core_boost_cert() {
                core_boost!($s, $o, $cbo);
            }
        }
    };
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
    generate_tests!(
        core_boost,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions::default()
    );
}

mod lb {
    type S = scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_tests!(default, super::S, scuttle_core::KernelOptions::default());
    generate_tests!(
        core_boost,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions::default()
    );
}

mod bos {
    type S = scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_biobj_tests!(default, super::S, scuttle_core::KernelOptions::default());
    generate_biobj_tests!(
        core_boost,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions::default()
    );
}
