#![cfg(feature = "build-binary")]

use maxpre::{MaxPre, PreproClauses, PreproMultiOpt};
use pminimal::{self, types::ParetoFront, Limits, Options, PMinimal, Solve};
use rustsat::{
    encodings::{card, pb},
    instances::MultiOptInstance,
    solvers,
    types::RsHashSet,
};

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

fn small(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/small.mcnf").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 3);
    let shape = vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)];
    check_pf_shape(pf, shape);
}

fn medium_single(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/medium.mcnf").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 6);
    let shape = vec![
        (vec![0, 10], 1),
        (vec![2, 8], 1),
        (vec![4, 6], 1),
        (vec![6, 4], 1),
        (vec![8, 2], 1),
        (vec![10, 0], 1),
    ];
    check_pf_shape(pf, shape);
}

fn four(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/four.mcnf").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 4);
    let shape = vec![
        (vec![0, 0, 0, 1], 1),
        (vec![0, 0, 1, 0], 1),
        (vec![0, 1, 0, 0], 1),
        (vec![1, 0, 0, 0], 1),
    ];
    check_pf_shape(pf, shape);
}

fn parkinsons(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path("./data/parkinsons_mlic.mcnf").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 8);
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
}

fn mushroom(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path("./data/mushroom_mlic.mcnf").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 10);
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
}

pub fn dal(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_opb_path("./data/dal.opb").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 21);
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
}

pub fn set_cover(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path("./data/set-cover.mcnf").unwrap();
    let (inst, mut prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver
        .pareto_front()
        .convert_solutions(&mut |s| prepro.reconstruct(s));
    assert_eq!(pf.n_pps(), 17);
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
}

#[test]
fn small_prepro() {
    small(Options::default())
}

#[test]
fn medium_prepro() {
    medium_single(Options::default())
}

#[test]
fn four_prepro() {
    four(Options::default())
}

#[test]
fn parkinsons_prepro() {
    parkinsons(Options::default())
}

#[test]
#[ignore]
fn mushroom_prepro() {
    mushroom(Options::default())
}

#[test]
fn dal_prepro() {
    dal(Options::default())
}

#[test]
fn set_cover_prepro() {
    set_cover(Options::default())
}
