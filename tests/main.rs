use pminimal::{
    self,
    options::{EnumOptions, HeurImprOptions},
    types::ParetoFront,
    Limits, Options, PMinimal, Solve,
};
use rustsat::{
    encodings::{card, pb},
    instances::{fio, MultiOptInstance},
    solvers,
    types::RsHashSet,
};

pub fn check_pf_shape(pf: ParetoFront, shape: Vec<(Vec<isize>, usize)>) {
    let pps_set: RsHashSet<(Vec<isize>, usize)> = pf
        .into_iter()
        .map(|pp| (pp.costs().clone(), pp.n_sols()))
        .collect();
    let shape_set: RsHashSet<(Vec<isize>, usize)> = shape.into_iter().collect();
    assert_eq!(pps_set, shape_set);
}

pub fn small(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/small.mcnf").unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 3);
    let shape = vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)];
    check_pf_shape(pf, shape);
}

pub fn medium_single(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/medium.mcnf").unwrap();
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

pub fn medium_all(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/medium.mcnf").unwrap();
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

pub fn four(opts: Options) {
    let inst: MultiOptInstance = MultiOptInstance::from_dimacs_path("./data/four.mcnf").unwrap();
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

pub fn parkinsons(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path("./data/parkinsons_mlic.mcnf").unwrap();
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

pub fn mushroom(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path("./data/mushroom_mlic.mcnf").unwrap();
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

pub fn dal(opts: Options) {
    let inst: MultiOptInstance =
        MultiOptInstance::from_opb_path("./data/dal.opb", fio::opb::Options::default()).unwrap();
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
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
    let mut solver: PMinimal<pb::DefIncUB, card::DefIncUB, _, _, solvers::DefIncSolver> =
        PMinimal::default_init_with_options(inst, opts);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
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
    opts.enumeration = EnumOptions::Solutions(None);
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
fn dal_default() {
    dal(Options::default())
}

#[test]
fn set_cover_default() {
    set_cover(Options::default())
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
    opts.enumeration = EnumOptions::Solutions(None);
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
fn dal_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    dal(opts)
}

#[test]
#[ignore]
fn set_cover_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    set_cover(opts)
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
    opts.enumeration = EnumOptions::Solutions(None);
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
fn dal_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    dal(opts)
}

#[test]
fn set_cover_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    set_cover(opts)
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
    opts.enumeration = EnumOptions::Solutions(None);
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

#[test]
fn dal_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    dal(opts)
}

#[test]
fn set_cover_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    set_cover(opts)
}

#[test]
fn small_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    small(opts)
}

#[test]
fn medium_single_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    medium_single(opts)
}

#[test]
fn medium_all_other_sol_guided() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    opts.solution_guided_search = !opts.solution_guided_search;
    medium_all(opts)
}

#[test]
fn four_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    four(opts)
}

#[test]
fn parkinsons_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    parkinsons(opts)
}

#[test]
#[ignore]
fn mushroom_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    mushroom(opts)
}

#[test]
fn dal_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    dal(opts)
}

#[test]
fn set_cover_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    set_cover(opts)
}
