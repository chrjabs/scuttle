use hitting_sets::{BuildSolver, HittingSetSolver};
use rustsat::{lit, types::Cl};

fn basic<S: HittingSetSolver>() {
    let mut builder = S::Builder::new([(lit![0], 2), (lit![1], 1), (lit![2], 1), (lit![3], 3)]);
    builder.reserve_vars(4, 4);
    let mut solver = builder.init();
    solver.add_core(Cl::new(&[lit![1], lit![3]]));
    solver.add_core(Cl::new(&[lit![0], lit![1], lit![2]]));
    let (cost, hitting_set) = solver.optimal_hitting_set();
    dbg!(cost, &hitting_set);
    assert_eq!(cost, 1);
    assert_eq!(hitting_set, vec![lit![1]]);
    solver.add_core(Cl::new(&[lit![0], lit![2]]));
    let (cost, hitting_set) = solver.optimal_hitting_set();
    assert_eq!(cost, 2);
    assert_eq!(hitting_set, vec![lit![1], lit![2]]);
    solver.add_core(Cl::new(&[lit![0], lit![3]]));
    let (cost, mut hitting_set) = solver.optimal_hitting_set();
    hitting_set.sort_unstable();
    assert_eq!(cost, 3);
    assert_eq!(hitting_set, vec![lit![0], lit![1]]);
}

#[cfg(feature = "highs")]
#[test]
fn highs_basic() {
    basic::<hitting_sets::HighsSolver>()
}
