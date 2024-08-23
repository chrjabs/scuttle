//! # Proof Writing Functionality

use itertools::Itertools;
use pidgeons::{ConstraintId, Order};

use crate::types::Objective;

pub fn objectives_as_order(objs: &[Objective]) -> Order {
    let mut order = Order::new(String::from("pareto"));
    for (idx, obj) in objs.iter().enumerate() {
        let mult = obj.unit_weight();
        let constr = format!(
            "{} >= 0",
            obj.iter().format_with(" ", |(l, w), f| {
                let (u, v) = order.use_var(&l.var());
                let neg = if l.is_neg() { "~" } else { "" };
                f(&format_args!(
                    "-{cf} {neg}{u} +{cf} {neg}{v}",
                    cf = w * mult
                ))
            })
        );
        // For O_idx, this proof sums up the following constraints
        // - O_idx(u) <= O_idx(v)
        // - O_idx(v) <= O_idx(w)
        // - O_idx(u) > O_idx(w)
        // This will always lead to a contradiction, proving transitivity
        let trans_proof = vec![
            ConstraintId::abs(idx + 1)
                + ConstraintId::abs(objs.len() + idx + 1)
                + ConstraintId::last(1),
        ];
        order.add_definition_constraint(&constr, trans_proof, None)
    }
    order
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
        process::Command,
    };

    use rustsat::lit;

    use crate::types::Objective;

    fn print_file<P: AsRef<Path>>(path: P) {
        println!();
        for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
            println!("{}", line.unwrap());
        }
        println!();
    }

    fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
        println!("start checking proof");
        let out = Command::new("veripb")
            .arg(instance.as_ref())
            .arg(proof.as_ref())
            .output()
            .expect("failed to run veripb");
        print_file(proof);
        if out.status.success() {
            return;
        }
        panic!("verification failed: {out:?}")
    }

    fn new_proof(
        num_constraints: usize,
        optimization: bool,
    ) -> pidgeons::Proof<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        pidgeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
    }

    #[test]
    fn order_format() {
        let objectives = [
            Objective::Unweighted {
                offset: 3,
                unit_weight: 2,
                lits: vec![lit![0], !lit![1], lit![2], lit![3]],
            },
            Objective::Weighted {
                offset: 42,
                lits: [(lit![4], 4), (lit![2], 2), (lit![42], 42)]
                    .into_iter()
                    .collect(),
            },
            Objective::Constant { offset: 11 },
        ];
        let order = super::objectives_as_order(&objectives);
        let formatted = format!("{order}");
        let expected = r#"def_order pareto
  vars
    left u_x3 u_x5 u_x43 u_x4 u_x1 u_x2
    right v_x3 v_x5 v_x43 v_x4 v_x1 v_x2
    aux
  end
  def
    -2 u_x1 +2 v_x1 -2 ~u_x2 +2 ~v_x2 -2 u_x3 +2 v_x3 -2 u_x4 +2 v_x4 >= 0 ;
    -4 u_x5 +4 v_x5 -2 u_x3 +2 v_x3 -42 u_x43 +42 v_x43 >= 0 ;
     >= 0 ;
  end
  transitivity
    vars
      fresh_right w_x3 w_x5 w_x43 w_x4 w_x1 w_x2
    end
    proof
      proofgoal #1
        pol 1 4 + -1 +
      qed -1
      proofgoal #2
        pol 2 5 + -1 +
      qed -1
      proofgoal #3
        pol 3 6 + -1 +
      qed -1
    qed
  end
end
"#;
        debug_assert_eq!(&formatted, expected);
    }

    #[test]
    fn order_check() {
        let objectives = [
            Objective::Unweighted {
                offset: 3,
                unit_weight: 2,
                lits: vec![lit![0], !lit![1], lit![2], lit![3]],
            },
            Objective::Weighted {
                offset: 42,
                lits: [(lit![4], 4), (lit![2], 2), (lit![42], 42)]
                    .into_iter()
                    .collect(),
            },
            Objective::Constant { offset: 11 },
        ];
        let order = super::objectives_as_order(&objectives);

        let mut proof = new_proof(0, false);
        proof.define_order(&order).unwrap();
        proof.load_order(order.name(), order.used_vars()).unwrap();

        let proof_file = proof
            .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(
            format!("{manifest}/../rustsat/data/empty.opb"),
            proof_file.path(),
        );
        panic!()
    }
}
