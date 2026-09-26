//! Mixed values, lexical bindings, and the current ownership representation.
//!
//! A quantum value owns a slot even when its basis has zero wires (`Q<Unit>`).
//! `None` in Env is a consumed binding: retain its name until scope exit so it
//! continues to hide a function. Registers track operation rights, not whether
//! the corresponding quantum subsystems are independent or entangled.

use std::collections::BTreeMap;

use super::super::{TreeSize, Ty, total_size};
use crate::ir::{ClassicalId, TokenId, WireId};

pub(super) type Slot = u32;
pub(super) type Env = BTreeMap<String, Option<Value>>;

pub(super) fn env_size(env: &Env) -> usize {
    total_size(
        env.values()
            .map(|value| 1 + value.as_ref().map_or(0, |value| value.tree_size().nodes)),
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Value {
    Unit,
    Classical(ClassicalId),
    Quantum(Slot, Ty),
    Pair(Box<Value>, Box<Value>),
}

impl Value {
    pub(super) fn tree_size(&self) -> TreeSize {
        let mut size = TreeSize::default();
        let mut pending = vec![(self, 1)];
        while let Some((value, depth)) = pending.pop() {
            size.nodes += 1;
            size.depth = size.depth.max(depth);
            match value {
                Self::Pair(a, b) => pending.extend([(a.as_ref(), depth + 1), (b, depth + 1)]),
                Self::Quantum(_, basis) => {
                    let basis = basis.tree_size();
                    size.nodes += basis.nodes;
                    size.depth = size.depth.max(depth + basis.depth);
                }
                _ => {}
            }
        }
        size
    }

    pub(super) fn ty(&self) -> Ty {
        match self {
            Self::Unit => Ty::Unit,
            Self::Classical(_) => Ty::CBit,
            Self::Quantum(_, basis) => Ty::Q(Box::new(basis.clone())),
            Self::Pair(a, b) => Ty::pair(a.ty(), b.ty()),
        }
    }

    pub(super) fn owns_quantum(&self) -> bool {
        match self {
            Self::Quantum(..) => true,
            Self::Pair(a, b) => a.owns_quantum() || b.owns_quantum(),
            _ => false,
        }
    }

    pub(super) fn pair(a: Self, b: Self) -> Self {
        Self::Pair(Box::new(a), Box::new(b))
    }
}

#[derive(Clone)]
pub(super) struct Register {
    pub(super) token: TokenId,
    pub(super) wires: Vec<WireId>,
    pub(super) basis: Ty,
}

impl Register {
    pub(super) fn size(&self) -> usize {
        1 + self.wires.len() + self.basis.tree_size().nodes
    }
}
