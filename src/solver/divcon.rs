//! # Divide and Conquer Multi-Objective Optimization

use rustsat::encodings::pb::dpw;

mod sequential;
pub use sequential::DivCon as SeqDivCon;

#[derive(Clone)]
struct ObjEncData {
    structure: dpw::Structure,
    offset: usize,
}
