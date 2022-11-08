use std::{collections::HashSet, path::Path};

use pminimal::{
    self, options::HeurImprOptions, types::ParetoFront, Limits, Options, PMinimal, Solve,
};
use rustsat::{
    encodings::{card, pb},
    instances::MultiOptInstance,
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

fn small(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/small.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 3);
    let shape = vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)];
    check_pf_shape(pf, shape);
}

fn medium_single(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/medium.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
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

fn medium_all(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/medium.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
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

fn four(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/four.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
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

fn parkinsons(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/parkinsons_mlic.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
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

fn mushroom(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/mushroom_mlic.mcnf")).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
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
fn small_default() {
    small(Options::default())
}

#[test]
fn medium_single_default() {
    medium_single(Options::default())
}

#[test]
fn medium_all_default() {
    let mut opts = Options::default();
    opts.max_sols_per_pp = None;
    medium_all(opts)
}

#[test]
fn four_default() {
    four(Options::default())
}

#[test]
fn parkinsons_default() {
    parkinsons(Options::default())
}

#[test]
#[ignore]
fn mushroom_default() {
    mushroom(Options::default())
}

#[test]
fn small_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    small(opts)
}

#[test]
fn medium_single_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    medium_single(opts)
}

#[test]
fn medium_all_no_heur() {
    let mut opts = Options::default();
    opts.max_sols_per_pp = None;
    opts.heuristic_improvements = HeurImprOptions::none();
    medium_all(opts)
}

#[test]
fn four_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    four(opts)
}

#[test]
fn parkinsons_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    parkinsons(opts)
}

#[test]
#[ignore]
fn mushroom_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    mushroom(opts)
}

#[test]
fn small_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    small(opts)
}

#[test]
fn medium_single_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    medium_single(opts)
}

#[test]
fn medium_all_all_heur() {
    let mut opts = Options::default();
    opts.max_sols_per_pp = None;
    opts.heuristic_improvements = HeurImprOptions::all();
    medium_all(opts)
}

#[test]
fn four_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    four(opts)
}

#[test]
fn parkinsons_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    parkinsons(opts)
}

#[test]
#[ignore]
fn mushroom_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    mushroom(opts)
}

#[test]
fn small_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    small(opts)
}

#[test]
fn medium_single_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    medium_single(opts)
}

#[test]
fn medium_all_other_reserve() {
    let mut opts = Options::default();
    opts.max_sols_per_pp = None;
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    medium_all(opts)
}

#[test]
fn four_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    four(opts)
}

#[test]
fn parkinsons_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    parkinsons(opts)
}

#[test]
#[ignore]
fn mushroom_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    mushroom(opts)
}
