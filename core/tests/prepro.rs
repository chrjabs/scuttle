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
    ($s:ty, $o:expr, $tech:expr, $i:expr, $t:expr) => {{
        use maxpre::PreproClauses;
        use scuttle_core::{prepro, InitDefaultBlock, KernelFunctions, Solve};
        let (mut prepro, inst) = prepro::max_pre(
            prepro::parse(
                $i,
                prepro::FileFormat::Infer,
                rustsat::instances::fio::opb::Options::default(),
            )
            .unwrap(),
            $tech,
            true,
        )
        .unwrap();
        let mut solver = <$s>::from_instance_default_blocking(inst, $o).unwrap();
        solver.solve(scuttle_core::Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), $t.len());
        check_pf_shape!(pf, $t);
    }};
}

macro_rules! small {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
            "./data/small.mcnf",
            vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)]
        )
    }};
}

macro_rules! medium_single {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
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
    }};
}

macro_rules! four {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
            "./data/four.mcnf",
            vec![
                (vec![0, 0, 0, 1], 1),
                (vec![0, 0, 1, 0], 1),
                (vec![0, 1, 0, 0], 1),
                (vec![1, 0, 0, 0], 1),
            ]
        )
    }};
}

macro_rules! parkinsons {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
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
    }};
}

macro_rules! mushroom {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
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
    }};
}

macro_rules! dal {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
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
    }};
}

macro_rules! set_cover {
    ($s:ty, $o:expr, $tech:expr) => {{
        test_instance!(
            $s,
            $o,
            $tech,
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
    }};
}

macro_rules! packup_3 {
    ($s:ty, $o:expr, $tech:expr) => {
        test_instance!(
            $s,
            $o,
            $tech,
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

macro_rules! generate_biobj_tests {
    ($mod:ident, $s:ty, $o:expr, $tech:expr) => {
        mod $mod {
            #[test]
            fn small() {
                small!($s, $o, $tech)
            }

            #[test]
            fn medium_single() {
                medium_single!($s, $o, $tech)
            }

            #[test]
            fn parkinsons() {
                parkinsons!($s, $o, $tech)
            }

            #[test]
            #[ignore]
            fn mushroom() {
                mushroom!($s, $o, $tech)
            }

            #[test]
            #[ignore]
            fn set_cover() {
                set_cover!($s, $o, $tech)
            }
        }
    };
}

macro_rules! generate_tests {
    ($mod:ident, $s:ty, $o:expr, $tech:expr) => {
        mod $mod {
            #[test]
            fn small() {
                small!($s, $o, $tech)
            }

            #[test]
            fn medium_single() {
                medium_single!($s, $o, $tech)
            }

            #[test]
            fn four() {
                four!($s, $o, $tech)
            }

            #[test]
            fn parkinsons() {
                parkinsons!($s, $o, $tech)
            }

            #[test]
            #[ignore]
            fn mushroom() {
                mushroom!($s, $o, $tech)
            }

            #[test]
            fn dal() {
                dal!($s, $o, $tech)
            }

            #[test]
            #[ignore]
            fn set_cover() {
                set_cover!($s, $o, $tech)
            }

            #[test]
            fn packup_3() {
                packup_3!($s, $o, $tech)
            }
        }
    };
}

mod pmin {
    type S = scuttle_core::PMinimal<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_tests!(
        default,
        super::S,
        scuttle_core::KernelOptions::default(),
        "[[uvsrgc]VRTG]"
    );
}

mod lb {
    type S = scuttle_core::LowerBounding<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_tests!(
        default,
        super::S,
        scuttle_core::KernelOptions::default(),
        "[[uvsrgc]VRTG]"
    );
}

mod bioptsat {
    type S = scuttle_core::BiOptSat<rustsat_cadical::CaDiCaL<'static, 'static>>;
    generate_biobj_tests!(
        default,
        super::S,
        scuttle_core::KernelOptions::default(),
        "[[uvsrgc]VRTG]"
    );
}
