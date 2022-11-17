#![cfg(feature = "build-binary")]

use std::{collections::HashSet, path::Path};

use maxpre::MaxPre;
use pminimal::{self, types::ParetoFront, Limits, Options, PMinimal, Solve};
use rustsat::{
    encodings::{card, pb},
    instances::{MultiOptInstance, Objective, SatInstance},
    solvers,
};

fn check_pf_shape(pf: ParetoFront, shape: Vec<(Vec<isize>, usize)>) {
    let pps_set: HashSet<(Vec<isize>, usize)> = pf
        .into_iter()
        .map(|pp| (pp.costs().clone(), pp.n_sols()))
        .collect();
    let shape_set: HashSet<(Vec<isize>, usize)> = shape.into_iter().collect();
    assert_eq!(pps_set, shape_set);
}

fn preprocess_inst(inst: MultiOptInstance, techniques: &str) -> (MultiOptInstance, MaxPre) {
    let (cnf, softs, _) = inst.as_hard_cls_soft_cls();
    let (softs, offsets) = softs.into_iter().unzip::<_, _, _, Vec<isize>>();
    let mut prepro = MaxPre::new(cnf, softs, false);
    prepro.preprocess(techniques, 0, 1e9, false);
    let (cnf, softs) = prepro.prepro_instance();
    let sat_inst = SatInstance::from_iter(cnf);
    let objs = softs.into_iter().map(|s| Objective::from_iter(s));
    let removed_weight = prepro.removed_weight();
    let objs = std::iter::zip(offsets, removed_weight)
        .map(|(o1, o2)| o1 + o2 as isize)
        .zip(objs)
        .map(|(o, mut obj)| {
            obj.increase_offset(o);
            obj
        })
        .collect();
    let inst = MultiOptInstance::compose(sat_inst, objs);
    (inst, prepro)
}

fn small(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/small.mcnf")).unwrap();
    let (inst, prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
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
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/medium.mcnf")).unwrap();
    let (inst, prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
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
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/four.mcnf")).unwrap();
    let (inst, prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
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
        MultiOptInstance::from_dimacs_path(Path::new("./data/parkinsons_mlic.mcnf")).unwrap();
    let (inst, prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
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
        MultiOptInstance::from_dimacs_path(Path::new("./data/mushroom_mlic.mcnf")).unwrap();
    let (inst, prepro) = preprocess_inst(inst, "[[uvsrgc]VRTG]");
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
