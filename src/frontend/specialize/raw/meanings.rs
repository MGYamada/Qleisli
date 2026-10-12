//! Native leaves for the original two-port Meaning obligation.
use crate::contract::{BasisType, exact::Matrix};
use crate::interchange::{finite_leaf::CheckedUnitaryLeaf, pure_leaf::CheckedPureLeaf};

#[derive(Debug)]
pub(in crate::frontend::specialize) enum Leaf {
    Unitary(CheckedUnitaryLeaf),
    Pure(CheckedPureLeaf),
}
impl Leaf {
    pub(in crate::frontend::specialize) fn domain(&self) -> &BasisType {
        match self {
            Self::Unitary(l) => l.boundary().signature(),
            Self::Pure(l) => l.boundary().domain(),
        }
    }
    pub(in crate::frontend::specialize) fn codomain(&self) -> &BasisType {
        match self {
            Self::Unitary(l) => l.boundary().signature(),
            Self::Pure(l) => l.boundary().codomain(),
        }
    }
    pub(in crate::frontend::specialize) fn meaning(&self) -> &Matrix {
        match self {
            Self::Unitary(l) => l.meaning(),
            Self::Pure(l) => l.meaning(),
        }
    }
    pub(in crate::frontend::specialize) fn unitary(&self) -> Option<&CheckedUnitaryLeaf> {
        match self {
            Self::Unitary(l) => Some(l),
            Self::Pure(_) => None,
        }
    }
}
