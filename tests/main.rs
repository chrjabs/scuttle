use std::{collections::HashSet, path::Path};

use pminimal::{self, Limits, PMinimal, Solve};
use rustsat::{
    encodings::{card::Totalizer, pb::GeneralizedTotalizer},
    instances::MultiOptInstance,
    solvers,
};

#[cfg(feature = "cadical")]
type Oracle = solvers::CaDiCaL<'static>;
#[cfg(not(feature = "cadical"))]
compile_error!("At least one of the solver features needs to be turned on");

#[test]
fn medium() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/medium.mcnf")).unwrap();
    let mut solver: PMinimal<GeneralizedTotalizer, Totalizer, _, _, Oracle> =
        PMinimal::init(inst, pminimal::default_blocking_clause);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 6);
    let pps: HashSet<Vec<isize>> = pf.into_iter().map(|pp| pp.costs().clone()).collect();
    let mut shape = HashSet::new();
    shape.insert(vec![0, 10]);
    shape.insert(vec![2, 8]);
    shape.insert(vec![4, 6]);
    shape.insert(vec![6, 4]);
    shape.insert(vec![8, 2]);
    shape.insert(vec![10, 0]);
    assert_eq!(pps, shape);
}

#[test]
fn parkinsons() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(Path::new("./data/parkinsons.mcnf")).unwrap();
    let mut solver: PMinimal<GeneralizedTotalizer, Totalizer, _, _, Oracle> =
        PMinimal::init(inst, pminimal::default_blocking_clause);
    solver.solve(Limits::none()).unwrap();
    let pf = solver.pareto_front();
    assert_eq!(pf.n_pps(), 8);
    let pps: HashSet<Vec<isize>> = pf.into_iter().map(|pp| pp.costs().clone()).collect();
    let mut shape = HashSet::new();
    shape.insert(vec![0, 147]);
    shape.insert(vec![2, 31]);
    shape.insert(vec![3, 19]);
    shape.insert(vec![4, 14]);
    shape.insert(vec![5, 11]);
    shape.insert(vec![6, 10]);
    shape.insert(vec![7, 9]);
    shape.insert(vec![8, 8]);
    assert_eq!(pps, shape);
}
