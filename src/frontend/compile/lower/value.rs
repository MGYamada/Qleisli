//! Mixed values, lexical bindings, and the current ownership representation.
//!
//! A quantum value owns a slot even when its basis has zero wires (`Q<Unit>`).
//! Consumed and hidden bindings retain their names until scope exit so they
//! continue to hide functions. A hidden binding belongs to an outer frame and
//! cannot be captured by a computed body; it has not thereby been consumed.
//! Registers track operation rights, not whether the corresponding quantum
//! subsystems are independent or entangled.

use std::collections::BTreeMap;

use super::super::{TreeSize, Ty, total_size};
use crate::ir::{ClassicalId, TokenId, WireId};

pub(super) type Slot = u32;
pub(super) type Env = BTreeMap<crate::frontend::resolve::locals::BinderKey, Binding>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Binding {
    Live(Value),
    Consumed,
    Hidden { quantum: bool },
}

impl Binding {
    pub(super) fn as_ref(&self) -> Option<&Value> {
        match self {
            Self::Live(value) => Some(value),
            Self::Consumed | Self::Hidden { .. } => None,
        }
    }

    pub(super) fn take(&mut self) -> Option<Value> {
        match self {
            Self::Live(_) => match std::mem::replace(self, Self::Consumed) {
                Self::Live(value) => Some(value),
                _ => unreachable!("live binding"),
            },
            Self::Consumed | Self::Hidden { .. } => None,
        }
    }

    pub(super) fn hidden(&self) -> Self {
        match self {
            Self::Live(value) => Self::Hidden {
                quantum: value.owns_quantum(),
            },
            Self::Consumed | Self::Hidden { .. } => self.clone(),
        }
    }
}

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
    /// Retains the complete Q type, including zero-width basis owners.
    Quantum(Slot, Ty),
    Pair(Box<Value>, Box<Value>),
    Tuple(Vec<Value>),
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
                Self::Tuple(fields) => {
                    pending.extend(fields.iter().map(|field| (field, depth + 1)))
                }
                Self::Quantum(_, ty) => {
                    let ty = ty.tree_size();
                    // The value node itself already counts the Q owner.
                    size.nodes += ty.nodes - 1;
                    size.depth = size.depth.max(depth + ty.depth - 1);
                }
                _ => {}
            }
        }
        size
    }

    pub(super) fn ty(&self) -> Ty {
        match self {
            Self::Unit => Ty::unit(),
            Self::Classical(_) => Ty::bit(),
            Self::Quantum(_, ty) => ty.clone(),
            Self::Pair(a, b) => Ty::pair(a.ty(), b.ty()),
            Self::Tuple(fields) => Ty::tuple(fields.iter().map(Self::ty).collect()),
        }
    }

    pub(super) fn owns_quantum(&self) -> bool {
        match self {
            Self::Quantum(_, ty) => ty.linear(),
            Self::Pair(a, b) => a.owns_quantum() || b.owns_quantum(),
            Self::Tuple(fields) => fields.iter().any(Self::owns_quantum),
            _ => false,
        }
    }

    pub(super) fn quantum(slot: Slot, basis: Ty) -> Self {
        Self::Quantum(slot, Ty::quantum(basis))
    }

    pub(super) fn pair(a: Self, b: Self) -> Self {
        Self::Pair(Box::new(a), Box::new(b))
    }

    pub(super) fn tuple(mut fields: Vec<Self>) -> Self {
        if fields.len() == 2 {
            let b = fields.pop().expect("second field");
            Self::pair(fields.pop().expect("first field"), b)
        } else {
            Self::Tuple(fields)
        }
    }

    pub(super) fn into_fields(self) -> Option<Vec<Self>> {
        match self {
            Self::Pair(a, b) => Some(vec![*a, *b]),
            Self::Tuple(fields) => Some(fields),
            _ => None,
        }
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
