use rustsat::{
    encodings::{card, pb},
    instances::{fio, BasicVarManager, MultiOptInstance},
    types::{Assignment, Clause, RsHashSet},
};
use rustsat_cadical::CaDiCaL;
use scuttle::{
    self,
    options::{EnumOptions, HeurImprOptions},
    types::ParetoFront,
    KernelFunctions, Limits, LowerBounding, Options, PMinimal, Solve,
};

fn check_pf_shape(pf: ParetoFront, shape: Vec<(Vec<isize>, usize)>) {
    let pps_set: RsHashSet<(Vec<isize>, usize)> = pf
        .into_iter()
        .map(|pp| (pp.costs().clone(), pp.n_sols()))
        .collect();
    let shape_set: RsHashSet<(Vec<isize>, usize)> = shape.into_iter().collect();
    assert_eq!(pps_set, shape_set);
}

macro_rules! small {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/small.mcnf").unwrap();
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
        assert_eq!(pf.len(), 3);
        let shape = vec![(vec![0, 4], 1), (vec![2, 2], 1), (vec![4, 0], 1)];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! medium_single {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/medium.mcnf").unwrap();
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
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

macro_rules! medium_all {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/medium.mcnf").unwrap();
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
        assert_eq!(pf.len(), 6);
        let shape = vec![
            (vec![0, 10], 1),
            (vec![2, 8], 5),
            (vec![4, 6], 10),
            (vec![6, 4], 10),
            (vec![8, 2], 5),
            (vec![10, 0], 1),
        ];
        check_pf_shape(pf, shape);
    }};
}

macro_rules! four {
    ($s:ty, $o:expr) => {{
        let inst: MultiOptInstance =
            MultiOptInstance::from_dimacs_path("./data/four.mcnf").unwrap();
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
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
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
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
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
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
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
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
        let mut solver = <$s>::new_defaults(inst, $o).unwrap();
        solver.solve(Limits::none()).unwrap();
        let pf = solver.pareto_front();
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

type Lb = LowerBounding<
    pb::DefIncUpperBounding,
    card::DefIncUpperBounding,
    BasicVarManager,
    fn(Assignment) -> Clause,
    Oracle,
>;

#[test]
fn pmin_small_default() {
    small!(PMin, Options::default())
}

#[test]
fn pmin_medium_single_default() {
    medium_single!(PMin, Options::default())
}

#[test]
fn pmin_medium_all_default() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    medium_all!(PMin, opts)
}

#[test]
fn pmin_four_default() {
    four!(PMin, Options::default())
}

#[test]
fn pmin_parkinsons_default() {
    parkinsons!(PMin, Options::default())
}

#[test]
#[ignore]
fn pmin_mushroom_default() {
    mushroom!(PMin, Options::default())
}

#[test]
fn pmin_dal_default() {
    dal!(PMin, Options::default())
}

#[test]
fn pmin_set_cover_default() {
    set_cover!(PMin, Options::default())
}

#[test]
fn pmin_small_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    small!(PMin, opts)
}

#[test]
fn pmin_medium_single_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    medium_single!(PMin, opts)
}

#[test]
fn pmin_medium_all_no_heur() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    opts.heuristic_improvements = HeurImprOptions::none();
    medium_all!(PMin, opts)
}

#[test]
fn pmin_four_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    four!(PMin, opts)
}

#[test]
fn pmin_parkinsons_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    parkinsons!(PMin, opts)
}

#[test]
#[ignore]
fn pmin_mushroom_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    mushroom!(PMin, opts)
}

#[test]
fn pmin_dal_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    dal!(PMin, opts)
}

#[test]
#[ignore]
fn pmin_set_cover_no_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::none();
    set_cover!(PMin, opts)
}

#[test]
fn pmin_small_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    small!(PMin, opts)
}

#[test]
fn pmin_medium_single_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    medium_single!(PMin, opts)
}

#[test]
fn pmin_medium_all_all_heur() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    opts.heuristic_improvements = HeurImprOptions::all();
    medium_all!(PMin, opts)
}

#[test]
fn pmin_four_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    four!(PMin, opts)
}

#[test]
fn pmin_parkinsons_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    parkinsons!(PMin, opts)
}

#[test]
#[ignore]
fn pmin_mushroom_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    mushroom!(PMin, opts)
}

#[test]
fn pmin_dal_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    dal!(PMin, opts)
}

#[test]
fn pmin_set_cover_all_heur() {
    let mut opts = Options::default();
    opts.heuristic_improvements = HeurImprOptions::all();
    set_cover!(PMin, opts)
}

#[test]
fn pmin_small_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    small!(PMin, opts)
}

#[test]
fn pmin_medium_single_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    medium_single!(PMin, opts)
}

#[test]
fn pmin_medium_all_other_reserve() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    medium_all!(PMin, opts)
}

#[test]
fn pmin_four_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    four!(PMin, opts)
}

#[test]
fn pmin_parkinsons_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    parkinsons!(PMin, opts)
}

#[test]
#[ignore]
fn pmin_mushroom_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    mushroom!(PMin, opts)
}

#[test]
fn pmin_dal_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    dal!(PMin, opts)
}

#[test]
fn pmin_set_cover_other_reserve() {
    let mut opts = Options::default();
    opts.reserve_enc_vars = !opts.reserve_enc_vars;
    set_cover!(PMin, opts)
}

#[test]
fn pmin_small_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    small!(PMin, opts)
}

#[test]
fn pmin_medium_single_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    medium_single!(PMin, opts)
}

#[test]
fn pmin_medium_all_other_sol_guided() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    opts.solution_guided_search = !opts.solution_guided_search;
    medium_all!(PMin, opts)
}

#[test]
fn pmin_four_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    four!(PMin, opts)
}

#[test]
fn pmin_parkinsons_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    parkinsons!(PMin, opts)
}

#[test]
#[ignore]
fn pmin_mushroom_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    mushroom!(PMin, opts)
}

#[test]
fn pmin_dal_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    dal!(PMin, opts)
}

#[test]
fn pmin_set_cover_other_sol_guided() {
    let mut opts = Options::default();
    opts.solution_guided_search = !opts.solution_guided_search;
    set_cover!(PMin, opts)
}

#[test]
fn lb_small_default() {
    small!(Lb, Options::default())
}

#[test]
fn lb_medium_single_default() {
    medium_single!(Lb, Options::default())
}

#[test]
fn lb_medium_all_default() {
    let mut opts = Options::default();
    opts.enumeration = EnumOptions::Solutions(None);
    medium_all!(Lb, opts)
}

#[test]
fn lb_four_default() {
    four!(Lb, Options::default())
}

#[test]
fn lb_parkinsons_default() {
    parkinsons!(Lb, Options::default())
}

#[test]
#[ignore]
fn lb_mushroom_default() {
    mushroom!(Lb, Options::default())
}

#[test]
fn lb_dal_default() {
    dal!(Lb, Options::default())
}

#[test]
#[ignore]
fn lb_set_cover_default() {
    set_cover!(Lb, Options::default())
}
