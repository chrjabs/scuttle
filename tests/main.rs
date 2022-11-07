use std::{collections::HashSet, path::Path};

use pminimal::{self, types::ParetoFront, Limits, Options, PMinimal, Solve};
use rustsat::{
    encodings::{card, pb},
    instances::MultiOptInstance,
    solvers,
};

#[cfg(feature = "cadical")]
type Oracle = solvers::CaDiCaL<'static>;
#[cfg(not(feature = "cadical"))]
compile_error!("At least one of the solver features needs to be turned on");

fn check_pf_shape(pf: ParetoFront, shape: Vec<(Vec<isize>, usize)>) {
    let pps_set: HashSet<(Vec<isize>, usize)> = pf
        .into_iter()
        .map(|pp| (pp.costs().clone(), pp.n_sols()))
        .collect();
    let shape_set: HashSet<(Vec<isize>, usize)> = shape.into_iter().collect();
    assert_eq!(pps_set, shape_set);
}

#[test]
fn small() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/small.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, Oracle> =
        PMinimal::default_init(inst);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 3);
    let shape = vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)];
    check_pf_shape(pf, shape);
}

#[test]
fn medium_single() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/medium.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, Oracle> =
        PMinimal::default_init(inst);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
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

#[test]
fn medium_all() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/medium.mcnf")).unwrap();
    let mut opts = Options::default();
    opts.max_sols_per_pp = None;
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, Oracle> =
        PMinimal::init_with_options(inst, opts, pminimal::default_blocking_clause);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 6);
    let shape = vec![
        (vec![0, 10], 1),
        (vec![2, 8], 5),
        (vec![4, 6], 10),
        (vec![6, 4], 10),
        (vec![8, 2], 5),
        (vec![10, 0], 1),
    ];
    check_pf_shape(pf, shape);
}

#[test]
fn four() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/four.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, Oracle> =
        PMinimal::default_init(inst);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 4);
    let shape = vec![
        (vec![0, 0, 0, 1], 1),
        (vec![0, 0, 1, 0], 1),
        (vec![0, 1, 0, 0], 1),
        (vec![1, 0, 0, 0], 1),
    ];
    check_pf_shape(pf, shape);
}

#[test]
fn parkinsons_single() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/parkinsons_mlic.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, Oracle> =
        PMinimal::default_init(inst);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
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
