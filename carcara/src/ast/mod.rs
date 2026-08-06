//! The abstract syntax tree (AST) for the Alethe proof format.
//!
//! This module also contains various utilities for manipulating Alethe proofs and terms.

mod context;
mod evaluate;
mod iter;
mod macros;
mod node;
mod polyeq;
pub mod pool;
pub mod printer;
mod problem;
mod proof;
pub mod rare_rules;
mod rc;
mod substitution;
mod term;
#[cfg(test)]
mod tests;

pub use context::{Context, ContextStack};
pub use evaluate::Value;
pub use iter::ProofIter;
pub use node::{ProofNode, ProofNodeForest, StepNode, SubproofNode};
pub use polyeq::{alpha_equiv, polyeq, Polyeq, PolyeqComparable, PolyeqConfig};
pub use problem::{Problem, ProblemPrelude};
pub use proof::{AnchorArg, Proof, ProofCommand, ProofStep, Subproof};
pub use rc::Rc;
pub use substitution::{Substitution, SubstitutionError};
pub use term::{
    Binder, BindingList, Constant, NaryCase, Operator, ParamOperator, QualifiedOperator, Sort,
    SortedVar, Term,
};

pub(crate) use carcara_macros::match_term;
pub(crate) use macros::{build_term, impl_str_conversion_traits, match_term_err};

#[cfg(test)]
pub(crate) use node::compare_forests;
#[cfg(test)]
pub(crate) use node::compare_nodes;
