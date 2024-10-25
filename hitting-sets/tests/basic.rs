use hitting_sets::{BuildSolver, CompleteSolveResult, HittingSetSolver};
use rustsat::{
    lit,
    types::{Cl, RsHashMap},
};

fn basic<S: HittingSetSolver>() {
    let objective: RsHashMap<_, _> = [(lit![0], 2), (lit![1], 1), (lit![2], 1), (lit![3], 3)]
        .into_iter()
        .collect();
    let mut builder = S::Builder::new([objective]);
    let mut solver = builder.init();
    solver.add_core(Cl::new(&[lit![1], lit![3]]));
    solver.add_core(Cl::new(&[lit![0], lit![1], lit![2]]));
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    dbg!(cost, &hitting_set);
    assert_eq!(cost, 1.);
    assert_eq!(hitting_set, vec![!lit![0], lit![1], !lit![2], !lit![3]]);
    solver.add_core(Cl::new(&[lit![0], lit![2]]));
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    assert_eq!(cost, 2.);
    assert_eq!(hitting_set, vec![!lit![0], lit![1], lit![2], !lit![3]]);
    solver.add_core(Cl::new(&[lit![0], lit![3]]));
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    assert_eq!(cost, 3.);
    assert_eq!(hitting_set, vec![lit![0], lit![1], !lit![2], !lit![3]]);
}

#[cfg(feature = "highs")]
#[test]
fn highs_basic() {
    basic::<hitting_sets::HighsSolver>()
}
