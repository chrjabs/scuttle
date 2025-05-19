use hitting_sets::{BuildSolver, CompleteSolveResult, HittingSetSolver};
use rustsat::{
    lit,
    types::{Cl, RsHashMap},
};

fn cores<S: HittingSetSolver>() {
    let objective: RsHashMap<_, _> = [(lit![0], 2), (lit![1], 1), (lit![2], 1), (lit![3], 3)]
        .into_iter()
        .collect();
    let builder = S::Builder::new([objective]);
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

fn pd_cuts<S: HittingSetSolver>() {
    // NOTE: based on `data/paper-example.mcnf`
    let obj1: RsHashMap<_, _> = [(lit![1], 3), (lit![2], 4), (lit![3], 2), (lit![4], 5)]
        .into_iter()
        .collect();
    let obj2: RsHashMap<_, _> = [(lit![0], 7), (lit![1], 4), (lit![2], 1), (lit![3], 2)]
        .into_iter()
        .collect();
    let builder = S::Builder::new([obj1, obj2]);
    let mut solver = builder.init();
    solver.add_core(Cl::new(&[lit![0], lit![1], lit![2]]));
    solver.add_core(Cl::new(&[lit![0], lit![1], lit![3]]));
    solver.add_core(Cl::new(&[lit![1], lit![2], lit![4]]));
    solver.add_core(Cl::new(&[lit![2], lit![3], lit![4]]));
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    assert_eq!(cost, 9.);
    assert_eq!(
        hitting_set,
        vec![!lit![0], !lit![1], lit![2], lit![3], !lit![4]]
    );
    solver.add_pd_cut(&[6, 3]);
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    assert_eq!(cost, 11.);
    assert_eq!(
        hitting_set,
        vec![!lit![0], lit![1], !lit![2], lit![3], !lit![4]]
    );
    solver.add_pd_cut(&[5, 6]);
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    assert_eq!(cost, 12.);
    assert_eq!(
        hitting_set,
        vec![lit![0], !lit![1], lit![2], !lit![3], !lit![4]]
    );
    solver.add_pd_cut(&[4, 8]);
    assert_eq!(
        solver.optimal_hitting_set(),
        CompleteSolveResult::Infeasible
    );
}

fn pd_cuts_2<S: HittingSetSolver>() {
    // NOTE: based on `data/small.mcnf`
    let obj1: RsHashMap<_, _> = [(lit![1], 1), (lit![3], 1)].into_iter().collect();
    let obj2: RsHashMap<_, _> = [(lit![0], 1), (lit![2], 1)].into_iter().collect();
    let builder = S::Builder::new([obj1, obj2]);
    let mut solver = builder.init();
    solver.add_core(Cl::new(&[lit![0], lit![1]]));
    solver.add_core(Cl::new(&[lit![1], lit![2]]));
    solver.add_core(Cl::new(&[lit![2], lit![3]]));
    let CompleteSolveResult::Optimal(cost, _) = solver.optimal_hitting_set() else {
        panic!()
    };
    assert_eq!(cost, 2.);
    solver.add_pd_cut(&[1, 1]);
    solver.add_pd_cut(&[2, 0]);
    let CompleteSolveResult::Optimal(cost, mut hitting_set) = solver.optimal_hitting_set() else {
        panic!()
    };
    hitting_set.sort_unstable();
    assert_eq!(cost, 2.);
    assert_eq!(hitting_set, vec![lit![0], !lit![1], lit![2], !lit![3]]);
    solver.add_pd_cut(&[0, 2]);
    assert_eq!(
        solver.optimal_hitting_set(),
        CompleteSolveResult::Infeasible
    );
}

#[cfg(feature = "highs")]
mod highs {
    #[test]
    fn cores() {
        super::cores::<hitting_sets::HighsSolver>()
    }

    #[test]
    fn pd_cuts() {
        super::pd_cuts::<hitting_sets::HighsSolver>()
    }

    #[test]
    fn pd_cuts_2() {
        super::pd_cuts_2::<hitting_sets::HighsSolver>()
    }
}

#[cfg(feature = "gurobi")]
mod gurobi {
    #[test]
    fn cores() {
        super::cores::<hitting_sets::GurobiSolver>()
    }

    #[test]
    fn pd_cuts() {
        super::pd_cuts::<hitting_sets::GurobiSolver>()
    }

    #[test]
    fn pd_cuts_2() {
        super::pd_cuts_2::<hitting_sets::GurobiSolver>()
    }
}
