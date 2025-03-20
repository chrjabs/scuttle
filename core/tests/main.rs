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
        use scuttle_core::{prepro, InitDefaultBlock, KernelFunctions, Solve};
        let (_, inst) = prepro::to_clausal(
            prepro::parse(
                $i,
                prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            &None,
        )
        .unwrap();
        let mut solver = <$s>::from_instance_default_blocking(inst, $o).unwrap();
        solver.solve(scuttle_core::Limits::none()).unwrap();
        let pf = solver.pareto_front();
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
    }};
    ($s:ty, $o:expr, $cbo:expr, $i:expr, $t:expr) => {{
        use scuttle_core::{prepro, CoreBoost, InitDefaultBlock, KernelFunctions, Solve};
        let (_, inst) = prepro::to_clausal(
            prepro::parse(
                $i,
                prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            &None,
        )
        .unwrap();
        let mut solver = <$s>::from_instance_default_blocking(inst, $o).unwrap();
        let cont = solver.core_boost($cbo).unwrap();
        if cont {
            solver.solve(scuttle_core::Limits::none()).unwrap();
        }
        let pf = solver.pareto_front();
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
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

macro_rules! medium_single {
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

macro_rules! medium_all {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/medium.mcnf",
            vec![
                (vec![0, 10], 1),
                (vec![2, 8], 5),
                (vec![4, 6], 10),
                (vec![6, 4], 10),
                (vec![8, 2], 5),
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
                (vec![2, 8], 5),
                (vec![4, 6], 10),
                (vec![6, 4], 10),
                (vec![8, 2], 5),
                (vec![10, 0], 1),
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

macro_rules! parkinsons {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/parkinsons_mlic.mcnf",
            vec![
                (vec![0, 147], 1),
                (vec![2, 31], 1),
                (vec![3, 19], 1),
                (vec![4, 14], 1),
                (vec![5, 11], 1),
                (vec![6, 10], 1),
                (vec![7, 9], 1),
                (vec![8, 8], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/parkinsons_mlic.mcnf",
            vec![
                (vec![0, 147], 1),
                (vec![2, 31], 1),
                (vec![3, 19], 1),
                (vec![4, 14], 1),
                (vec![5, 11], 1),
                (vec![6, 10], 1),
                (vec![7, 9], 1),
                (vec![8, 8], 1),
            ]
        )
    };
}

macro_rules! mushroom {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/mushroom_mlic.mcnf",
            vec![
                (vec![0, 505], 1),
                (vec![2, 144], 1),
                (vec![3, 60], 1),
                (vec![4, 43], 1),
                (vec![5, 29], 1),
                (vec![6, 12], 1),
                (vec![7, 7], 1),
                (vec![8, 3], 1),
                (vec![9, 2], 1),
                (vec![10, 0], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/mushroom_mlic.mcnf",
            vec![
                (vec![0, 505], 1),
                (vec![2, 144], 1),
                (vec![3, 60], 1),
                (vec![4, 43], 1),
                (vec![5, 29], 1),
                (vec![6, 12], 1),
                (vec![7, 7], 1),
                (vec![8, 3], 1),
                (vec![9, 2], 1),
                (vec![10, 0], 1),
            ]
        )
    };
}

macro_rules! dal {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/dal.opb",
            vec![
                (vec![8, 0, 0, 0, 0, 7, 2], 1),
                (vec![7, 1, 0, 0, 0, 7, 2], 1),
                (vec![7, 0, 1, 0, 0, 7, 2], 1),
                (vec![6, 0, 2, 0, 0, 7, 2], 1),
                (vec![6, 2, 0, 0, 0, 7, 2], 1),
                (vec![6, 1, 1, 0, 0, 7, 2], 1),
                (vec![5, 1, 2, 0, 0, 7, 2], 1),
                (vec![4, 1, 3, 0, 0, 7, 2], 1),
                (vec![3, 1, 4, 0, 0, 7, 2], 1),
                (vec![3, 0, 5, 0, 0, 7, 2], 1),
                (vec![4, 0, 4, 0, 0, 7, 2], 1),
                (vec![4, 2, 2, 0, 0, 7, 2], 1),
                (vec![3, 2, 3, 0, 0, 7, 2], 1),
                (vec![5, 0, 3, 0, 0, 7, 2], 1),
                (vec![5, 3, 0, 0, 0, 7, 2], 1),
                (vec![5, 2, 1, 0, 0, 7, 2], 1),
                (vec![4, 4, 0, 0, 0, 7, 2], 1),
                (vec![4, 3, 1, 0, 0, 7, 2], 1),
                (vec![3, 3, 2, 0, 0, 7, 2], 1),
                (vec![3, 5, 0, 0, 0, 7, 2], 1),
                (vec![3, 4, 1, 0, 0, 7, 2], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/dal.opb",
            vec![
                (vec![8, 0, 0, 0, 0, 7, 2], 1),
                (vec![7, 1, 0, 0, 0, 7, 2], 1),
                (vec![7, 0, 1, 0, 0, 7, 2], 1),
                (vec![6, 0, 2, 0, 0, 7, 2], 1),
                (vec![6, 2, 0, 0, 0, 7, 2], 1),
                (vec![6, 1, 1, 0, 0, 7, 2], 1),
                (vec![5, 1, 2, 0, 0, 7, 2], 1),
                (vec![4, 1, 3, 0, 0, 7, 2], 1),
                (vec![3, 1, 4, 0, 0, 7, 2], 1),
                (vec![3, 0, 5, 0, 0, 7, 2], 1),
                (vec![4, 0, 4, 0, 0, 7, 2], 1),
                (vec![4, 2, 2, 0, 0, 7, 2], 1),
                (vec![3, 2, 3, 0, 0, 7, 2], 1),
                (vec![5, 0, 3, 0, 0, 7, 2], 1),
                (vec![5, 3, 0, 0, 0, 7, 2], 1),
                (vec![5, 2, 1, 0, 0, 7, 2], 1),
                (vec![4, 4, 0, 0, 0, 7, 2], 1),
                (vec![4, 3, 1, 0, 0, 7, 2], 1),
                (vec![3, 3, 2, 0, 0, 7, 2], 1),
                (vec![3, 5, 0, 0, 0, 7, 2], 1),
                (vec![3, 4, 1, 0, 0, 7, 2], 1),
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

macro_rules! set_cover {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/set-cover.mcnf",
            vec![
                (vec![302, 133], 1),
                (vec![195, 228], 1),
                (vec![253, 175], 1),
                (vec![284, 143], 1),
                (vec![173, 278], 1),
                (vec![147, 289], 1),
                (vec![223, 185], 1),
                (vec![268, 162], 1),
                (vec![343, 119], 1),
                (vec![341, 123], 1),
                (vec![325, 129], 1),
                (vec![273, 152], 1),
                (vec![264, 171], 1),
                (vec![216, 216], 1),
                (vec![220, 196], 1),
                (vec![192, 266], 1),
                (vec![185, 274], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/set-cover.mcnf",
            vec![
                (vec![302, 133], 1),
                (vec![195, 228], 1),
                (vec![253, 175], 1),
                (vec![284, 143], 1),
                (vec![173, 278], 1),
                (vec![147, 289], 1),
                (vec![223, 185], 1),
                (vec![268, 162], 1),
                (vec![343, 119], 1),
                (vec![341, 123], 1),
                (vec![325, 129], 1),
                (vec![273, 152], 1),
                (vec![264, 171], 1),
                (vec![216, 216], 1),
                (vec![220, 196], 1),
                (vec![192, 266], 1),
                (vec![185, 274], 1),
            ]
        )
    };
}

macro_rules! packup_3 {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/packup-3.mcnf",
            vec![
                (vec![2, 3, 5], 1),
                (vec![2, 4, 3], 1),
                (vec![2, 5, 2], 1),
                (vec![3, 2, 5], 1),
                (vec![3, 3, 3], 1),
                (vec![3, 4, 2], 1),
                (vec![3, 5, 1], 1),
                (vec![4, 1, 5], 1),
                (vec![4, 2, 3], 1),
                (vec![4, 3, 2], 1),
                (vec![4, 4, 1], 1),
                (vec![4, 5, 0], 1),
                (vec![5, 1, 4], 1),
                (vec![5, 2, 2], 1),
                (vec![5, 3, 1], 1),
                (vec![5, 4, 0], 1),
                (vec![6, 1, 3], 1),
                (vec![6, 2, 1], 1),
                (vec![6, 3, 0], 1),
                (vec![7, 1, 2], 1),
                (vec![7, 2, 0], 1),
                (vec![8, 1, 1], 1),
                (vec![9, 1, 0], 1),
                (vec![11, 0, 6], 1),
                (vec![12, 0, 5], 1),
                (vec![13, 0, 4], 1),
                (vec![14, 0, 3], 1),
                (vec![15, 0, 2], 1),
                (vec![16, 0, 1], 1),
                (vec![17, 0, 0], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/packup-3.mcnf",
            vec![
                (vec![2, 3, 5], 1),
                (vec![2, 4, 3], 1),
                (vec![2, 5, 2], 1),
                (vec![3, 2, 5], 1),
                (vec![3, 3, 3], 1),
                (vec![3, 4, 2], 1),
                (vec![3, 5, 1], 1),
                (vec![4, 1, 5], 1),
                (vec![4, 2, 3], 1),
                (vec![4, 3, 2], 1),
                (vec![4, 4, 1], 1),
                (vec![4, 5, 0], 1),
                (vec![5, 1, 4], 1),
                (vec![5, 2, 2], 1),
                (vec![5, 3, 1], 1),
                (vec![5, 4, 0], 1),
                (vec![6, 1, 3], 1),
                (vec![6, 2, 1], 1),
                (vec![6, 3, 0], 1),
                (vec![7, 1, 2], 1),
                (vec![7, 2, 0], 1),
                (vec![8, 1, 1], 1),
                (vec![9, 1, 0], 1),
                (vec![11, 0, 6], 1),
                (vec![12, 0, 5], 1),
                (vec![13, 0, 4], 1),
                (vec![14, 0, 3], 1),
                (vec![15, 0, 2], 1),
                (vec![16, 0, 1], 1),
                (vec![17, 0, 0], 1),
            ]
        )
    };
}

macro_rules! ftp {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/ftp.mcnf",
            vec![
                (vec![345, 6125], 1),
                (vec![356, 4760], 1),
                (vec![364, 4150], 1),
                (vec![373, 3845], 1),
                (vec![383, 3390], 1),
                (vec![392, 2760], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/ftp.mcnf",
            vec![
                (vec![345, 6125], 1),
                (vec![356, 4760], 1),
                (vec![364, 4150], 1),
                (vec![373, 3845], 1),
                (vec![383, 3390], 1),
                (vec![392, 2760], 1),
            ]
        )
    };
}

macro_rules! spot5 {
    ($s:ty, $o:expr) => {
        test_instance!(
            $s,
            $o,
            "./data/spot5.mcnf",
            vec![
                (vec![222, 33], 1),
                (vec![223, 32], 1),
                (vec![224, 31], 1),
                (vec![226, 30], 1),
                (vec![228, 29], 1),
                (vec![230, 28], 1),
                (vec![233, 27], 1),
                (vec![235, 26], 1),
                (vec![238, 25], 1),
                (vec![240, 24], 1),
                (vec![243, 23], 1),
                (vec![248, 22], 1),
                (vec![253, 21], 1),
            ]
        )
    };
    ($s:ty, $o:expr, $cbo:expr) => {
        test_instance!(
            $s,
            $o,
            $cbo,
            "./data/spot5.mcnf",
            vec![
                (vec![222, 33], 1),
                (vec![223, 32], 1),
                (vec![224, 31], 1),
                (vec![226, 30], 1),
                (vec![228, 29], 1),
                (vec![230, 28], 1),
                (vec![233, 27], 1),
                (vec![235, 26], 1),
                (vec![238, 25], 1),
                (vec![240, 24], 1),
                (vec![243, 23], 1),
                (vec![248, 22], 1),
                (vec![253, 21], 1),
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

macro_rules! generate_biobj_tests {
    ($mod:ident, $s:ty, $o:expr) => {
        mod $mod {
            #[test]
            fn small() {
                small!($s, $o)
            }

            #[test]
            fn medium_single() {
                medium_single!($s, $o)
            }

            #[test]
            fn medium_all() {
                let mut opts = $o;
                opts.set_enumeration(scuttle_core::options::EnumOptions::Solutions(None));
                medium_all!($s, opts)
            }

            #[test]
            fn parkinsons() {
                parkinsons!($s, $o)
            }

            #[test]
            #[ignore]
            fn mushroom() {
                mushroom!($s, $o)
            }

            #[test]
            fn set_cover() {
                set_cover!($s, $o)
            }

            #[test]
            #[ignore]
            fn ftp() {
                ftp!($s, $o)
            }

            #[test]
            #[ignore]
            fn spot5() {
                spot5!($s, $o)
            }
        }
    };
    ($mod:ident, $s:ty, $o:expr, $cbo:expr) => {
        mod $mod {
            #[test]
            fn small() {
                small!($s, $o, $cbo)
            }

            #[test]
            fn medium_single() {
                medium_single!($s, $o, $cbo)
            }

            #[test]
            fn medium_all() {
                let mut opts = $o;
                opts.set_enumeration(scuttle_core::options::EnumOptions::Solutions(None));
                medium_all!($s, opts, $cbo)
            }

            #[test]
            fn parkinsons() {
                parkinsons!($s, $o, $cbo)
            }

            #[test]
            #[ignore]
            fn mushroom() {
                mushroom!($s, $o, $cbo)
            }

            #[test]
            fn set_cover() {
                set_cover!($s, $o, $cbo)
            }

            #[test]
            #[ignore]
            fn ftp() {
                ftp!($s, $o, $cbo)
            }

            #[test]
            #[ignore]
            fn spot5() {
                spot5!($s, $o, $cbo)
            }
        }
    };
}

macro_rules! generate_tests {
    ($mod:ident, $s:ty, $o:expr) => {
        mod $mod {
            #[test]
            fn small() {
                small!($s, $o)
            }

            #[test]
            fn medium_single() {
                medium_single!($s, $o)
            }

            #[test]
            fn medium_all() {
                let mut opts = $o;
                opts.set_enumeration(scuttle_core::options::EnumOptions::Solutions(None));
                medium_all!($s, opts)
            }

            #[test]
            fn four() {
                four!($s, $o)
            }

            #[test]
            fn parkinsons() {
                parkinsons!($s, $o)
            }

            #[test]
            #[ignore]
            fn mushroom() {
                mushroom!($s, $o)
            }

            #[test]
            fn dal() {
                dal!($s, $o)
            }

            #[test]
            fn dal2() {
                dal2!($s, $o)
            }

            #[test]
            fn set_cover() {
                set_cover!($s, $o)
            }

            #[test]
            fn packup_3() {
                packup_3!($s, $o)
            }

            #[test]
            #[ignore]
            fn ftp() {
                ftp!($s, $o)
            }

            #[test]
            #[ignore]
            fn spot5() {
                spot5!($s, $o)
            }

            #[test]
            fn set_cover_3() {
                set_cover_3!($s, $o)
            }
        }
    };
    ($mod:ident, $s:ty, $o:expr, $cbo:expr) => {
        mod $mod {
            #[test]
            fn small() {
                small!($s, $o, $cbo)
            }

            #[test]
            fn medium_single() {
                medium_single!($s, $o, $cbo)
            }

            #[test]
            fn medium_all() {
                let mut opts = $o;
                opts.set_enumeration(scuttle_core::options::EnumOptions::Solutions(None));
                medium_all!($s, opts, $cbo)
            }

            #[test]
            fn four() {
                four!($s, $o, $cbo)
            }

            #[test]
            fn parkinsons() {
                parkinsons!($s, $o, $cbo)
            }

            #[test]
            #[ignore]
            fn mushroom() {
                mushroom!($s, $o, $cbo)
            }

            #[test]
            fn dal() {
                dal!($s, $o, $cbo)
            }

            #[test]
            fn dal2() {
                dal2!($s, $o, $cbo)
            }

            #[test]
            fn set_cover() {
                set_cover!($s, $o, $cbo)
            }

            #[test]
            fn packup_3() {
                packup_3!($s, $o, $cbo)
            }

            #[test]
            #[ignore]
            fn ftp() {
                ftp!($s, $o, $cbo)
            }

            #[test]
            #[ignore]
            fn spot5() {
                spot5!($s, $o, $cbo)
            }

            #[test]
            fn set_cover_3() {
                set_cover_3!($s, $o, $cbo)
            }
        }
    };
}

mod pmin {
    type S = scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_tests!(default, super::S, scuttle_core::KernelOptions::default());
    generate_tests!(
        no_heur,
        super::S,
        scuttle_core::KernelOptions {
            heuristic_improvements: scuttle_core::options::HeurImprOptions::none(),
            ..Default::default()
        }
    );
    generate_tests!(
        all_heur,
        super::S,
        scuttle_core::KernelOptions {
            heuristic_improvements: scuttle_core::options::HeurImprOptions::all(),
            ..Default::default()
        }
    );
    generate_tests!(
        other_reserve,
        super::S,
        scuttle_core::KernelOptions {
            reserve_enc_vars: !scuttle_core::KernelOptions::default().reserve_enc_vars,
            ..Default::default()
        }
    );
    generate_tests!(
        other_sol_guided,
        super::S,
        scuttle_core::KernelOptions {
            solution_guided_search: !scuttle_core::KernelOptions::default().solution_guided_search,
            ..Default::default()
        }
    );
    generate_tests!(
        cb,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions::default()
    );
    generate_tests!(
        cb_rebase,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions {
            rebase: true,
            ..Default::default()
        }
    );
}

mod lb {
    type S = scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_tests!(default, super::S, scuttle_core::KernelOptions::default());
    generate_tests!(
        cb,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions::default()
    );
    generate_tests!(
        cb_rebase,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions {
            rebase: true,
            ..Default::default()
        }
    );
}

mod bioptsat {
    type S = scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_biobj_tests!(default, super::S, scuttle_core::KernelOptions::default());
    generate_biobj_tests!(
        cb,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions::default()
    );
    generate_biobj_tests!(
        cb_rebase,
        super::S,
        scuttle_core::KernelOptions::default(),
        scuttle_core::CoreBoostingOptions {
            rebase: true,
            ..Default::default()
        }
    );
}
