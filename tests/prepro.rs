#![cfg(feature = "build-binary")]

use maxpre::{MaxPre, PreproClauses, PreproMultiOpt};
use rustsat::{
    encodings::{card, pb},
    instances::{fio, BasicVarManager, MultiOptInstance},
    types::{Assignment, Clause, RsHashSet},
};
use rustsat_cadical::CaDiCaL;
use scuttle::{self, types::ParetoFront, Limits, Options, PMinimal, Solve};

fn check_pf_shape(pf: ParetoFront, shape: Vec<(Vec<isize>, usize)>) {
    let pps_set: RsHashSet<(Vec<isize>, usize)> = pf
        .into_iter()
        .map(|pp| (pp.costs().clone(), pp.n_sols()))
        .collect();
    let shape_set: RsHashSet<(Vec<isize>, usize)> = shape.into_iter().collect();
    assert_eq!(pps_set, shape_set);
}

fn preprocess_inst(inst: MultiOptInstance, techniques: &str) -> (MultiOptInstance, MaxPre) {
    let mut prepro = <MaxPre as PreproMultiOpt>::new(inst, false);
    prepro.preprocess(techniques, 0, 1e9);
    let inst = PreproMultiOpt::prepro_instance(&mut prepro);
    (inst, prepro)
}

macro_rules! small {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/small.mcnf").unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 3);
        let shape = vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! medium_single {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/medium.mcnf").unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 6);
        let shape = vec![
            (vec![0, 10], 1),
            (vec![2, 8], 1),
            (vec![4, 6], 1),
            (vec![6, 4], 1),
            (vec![8, 2], 1),
            (vec![10, 0], 1),
        ];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! four {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/four.mcnf").unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 4);
        let shape = vec![
            (vec![0, 0, 0, 1], 1),
            (vec![0, 0, 1, 0], 1),
            (vec![0, 1, 0, 0], 1),
            (vec![1, 0, 0, 0], 1),
        ];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! parkinsons {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/parkinsons_mlic.mcnf").unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 8);
        let shape = vec![
            (vec![0, 147], 1),
            (vec![2, 31], 1),
            (vec![3, 19], 1),
            (vec![4, 14], 1),
            (vec![5, 11], 1),
            (vec![6, 10], 1),
            (vec![7, 9], 1),
            (vec![8, 8], 1),
        ];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! mushroom {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/mushroom_mlic.mcnf").unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 10);
        let shape = vec![
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
        ];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! dal {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_opb_path("./data/dal.opb", fio::opb::Options::default())
                .unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 21);
        let shape = vec![
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
        ];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! set_cover {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/set-cover.mcnf").unwrap();
        let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver
            .pareto_front()
            .convert_solutions(&mut |s| prepro.reconstruct(s));
        assert_eq!(pf.len(), 17);
        let shape = vec![
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
        ];
        check_pf_shape(pf, shape);
    }};
}

type Oracle = CaDiCaL<'static, 'static>;

type PMin = PMinimal<
    pb::DefIncUpperBounding,
    card::DefIncUpperBounding,
    BasicVarManager,
    fn(Assignment) -> Clause,
    Oracle,
>;

#[test]
fn small_prepro() {
    small!(PMin, Options::default())
}

#[test]
fn medium_prepro() {
    medium_single!(PMin, Options::default())
}

#[test]
fn four_prepro() {
    four!(PMin, Options::default())
}

#[test]
fn parkinsons_prepro() {
    parkinsons!(PMin, Options::default())
}

#[test]
#[ignore]
fn mushroom_prepro() {
    mushroom!(PMin, Options::default())
}

#[test]
fn dal_prepro() {
    dal!(PMin, Options::default())
}

#[test]
fn set_cover_prepro() {
    set_cover!(PMin, Options::default())
}
