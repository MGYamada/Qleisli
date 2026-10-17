//! Mixed values, lexical bindings, and the current ownership representation.
//!
//! A quantum value owns a slot even when its basis has zero wires (`Q<Unit>`).
//! Consumed and hidden bindings retain their names until scope exit so they
//! continue to hide functions. A hidden binding belongs to an outer frame and
//! cannot be captured by a computed body; it has not thereby been consumed.
//! Registers track operation rights, not whether the corresponding quantum
//! subsystems are independent or entangled.

use std::collections::BTreeMap;

use super::super::{Kind, TreeSize, Ty, total_size};
use crate::ir::ClassicalId;

pub(super) use crate::frontend::raw_state::Slot;
pub(super) type Register = crate::frontend::raw_state::Register<u32>;
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
    EmptyBits,
    Classical(ClassicalId),
    /// One ordinary Bits<n> value, in its declared low-axis-first bit order.
    /// It is neither an ordinary tuple nor an ordinary Bit at width one.
    Bits(Vec<ClassicalId>),
    /// Retains the complete Q type, including zero-width basis owners.
    Quantum(Slot, Ty),
    Pair(Box<Value>, Box<Value>),
    Tuple(Vec<Value>),
}

impl Value {
    pub(super) fn outputs(
        &self,
        registers: &BTreeMap<Slot, Register>,
        quantum: &mut Vec<crate::ir::TokenId>,
        classical: &mut Vec<ClassicalId>,
    ) {
        fn counts(value: &Value) -> (usize, usize) {
            match value {
                Value::Quantum(..) => (1, 0),
                Value::Classical(_) => (0, 1),
                Value::Bits(ids) => (0, ids.len()),
                Value::Pair(a, b) => {
                    let a = counts(a);
                    let b = counts(b);
                    (a.0 + b.0, a.1 + b.1)
                }
                Value::Tuple(fields) => fields.iter().fold((0, 0), |total, field| {
                    let child = counts(field);
                    (total.0 + child.0, total.1 + child.1)
                }),
                Value::Unit | Value::EmptyBits => (0, 0),
            }
        }
        // Production callers charge the complete value before output copying.
        // Reserve the complete lists once, avoiding repeated movement of an
        // earlier word when a later word in the same product is appended.
        let (quantum_count, classical_count) = counts(self);
        quantum.reserve_exact(quantum_count);
        classical.reserve_exact(classical_count);
        self.write_outputs(registers, quantum, classical);
    }

    fn write_outputs(
        &self,
        registers: &BTreeMap<Slot, Register>,
        quantum: &mut Vec<crate::ir::TokenId>,
        classical: &mut Vec<ClassicalId>,
    ) {
        match self {
            Self::Quantum(slot, _) => quantum.push(registers[slot].token),
            Self::Classical(id) => classical.push(*id),
            Self::Bits(ids) => classical.extend_from_slice(ids),
            Self::Pair(a, b) => {
                a.write_outputs(registers, quantum, classical);
                b.write_outputs(registers, quantum, classical);
            }
            Self::Tuple(fields) => {
                for field in fields {
                    field.write_outputs(registers, quantum, classical);
                }
            }
            Self::Unit | Self::EmptyBits => {}
        }
    }

    pub(super) fn tree_size(&self) -> TreeSize {
        fn basis(ty: &Ty, depth: usize, size: &mut TreeSize) {
            size.nodes += 1;
            size.depth = size.depth.max(depth);
            match &ty.kind {
                Kind::Q(inner) => basis(inner, depth + 1, size),
                Kind::Tuple(fields) => {
                    for field in fields {
                        basis(field, depth + 1, size);
                    }
                }
                _ => {}
            }
        }
        fn visit(value: &Value, depth: usize, size: &mut TreeSize) {
            size.nodes += 1;
            size.depth = size.depth.max(depth);
            match value {
                Value::Pair(a, b) => {
                    visit(a, depth + 1, size);
                    visit(b, depth + 1, size);
                }
                Value::Tuple(fields) => {
                    for field in fields {
                        visit(field, depth + 1, size);
                    }
                }
                Value::Quantum(_, ty) => {
                    // The value node itself already counts the Q owner.
                    let Kind::Q(inner) = &ty.kind else {
                        unreachable!("quantum value retains its exact Q type")
                    };
                    basis(inner, depth + 1, size);
                }
                // Count the data cells copied with this ordinary word, while
                // retaining one structural Bits leaf and its original depth.
                Value::Bits(ids) => size.nodes += ids.len(),
                _ => {}
            }
        }
        let mut size = TreeSize::default();
        visit(self, 1, &mut size);
        size
    }

    pub(super) fn ty(&self) -> Ty {
        match self {
            Self::Unit => Ty::unit(),
            Self::EmptyBits => Ty::empty_bits(),
            Self::Classical(_) => Ty::bit(),
            Self::Bits(ids) => Ty::bits(
                u32::try_from(ids.len()).expect("finite word storage has a checked u32 width"),
            ),
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

    pub(super) fn bits(ids: Vec<ClassicalId>) -> Self {
        if ids.is_empty() {
            Self::EmptyBits
        } else {
            Self::Bits(ids)
        }
    }

    /// The caller has checked the finite width. Reserve data, traversal and
    /// any existing input-list movement before allocating or issuing an ID.
    pub(super) fn input_word<E>(
        width: usize,
        inputs: &mut Vec<ClassicalId>,
        mut reserve: impl FnMut(usize) -> Result<(), E>,
        mut issue: impl FnMut() -> ClassicalId,
    ) -> Result<Self, E> {
        let needed = inputs.len().saturating_add(width);
        let growth = if needed > inputs.capacity() {
            needed
        } else {
            0
        };
        reserve(
            width
                .saturating_mul(2)
                .saturating_add(growth)
                .saturating_add(1),
        )?;
        if growth != 0 {
            inputs.reserve_exact(width);
        }
        let mut ids = Vec::with_capacity(width);
        for _ in 0..width {
            let id = issue();
            inputs.push(id);
            ids.push(id);
        }
        Ok(Self::bits(ids))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::instrument::ResultAtom;
    use crate::ir::TokenId;

    #[test]
    fn ordinary_word_outputs_preserve_bit_order_and_zero_width_quantum_owner() {
        let registers = BTreeMap::from([(
            0,
            Register {
                token: TokenId(4),
                wires: Vec::new(),
                basis: Ty::bits(0),
            },
        )]);
        let word = Value::bits(vec![ClassicalId(9), ClassicalId(2)]);
        let value = Value::pair(word, Value::quantum(0, Ty::bits(0)));
        let mut quantum = Vec::new();
        let mut classical = Vec::new();
        value.outputs(&registers, &mut quantum, &mut classical);
        assert_eq!(classical, [ClassicalId(9), ClassicalId(2)]);
        assert_eq!(quantum, [TokenId(4)]);
        assert_eq!(value.ty(), Ty::pair(Ty::bits(2), Ty::quantum(Ty::bits(0))));
        assert!(!Value::bits(vec![ClassicalId(3)]).owns_quantum());
        assert_ne!(
            Value::bits(vec![ClassicalId(3)]).ty(),
            Value::Classical(ClassicalId(3)).ty()
        );
        assert_eq!(Value::bits(Vec::new()), Value::EmptyBits);
        assert_ne!(Value::EmptyBits.ty(), Value::Unit.ty());
    }

    #[test]
    fn word_data_cells_are_included_in_existing_value_copy_accounting() {
        let word = Value::bits(vec![ClassicalId(8), ClassicalId(1)]);
        assert_eq!(word.ty().tree_size().nodes, 1);
        assert_eq!(word.tree_size(), TreeSize { nodes: 3, depth: 1 });
        let nested = Value::pair(word, Value::quantum(0, Ty::bits(0)));
        assert_eq!(nested.tree_size(), TreeSize { nodes: 6, depth: 3 });
        assert!(nested.owns_quantum());
    }

    #[test]
    fn input_word_work_refusal_precedes_storage_and_identity_changes() {
        let mut inputs = vec![ClassicalId(7)];
        inputs.shrink_to_fit();
        let capacity = inputs.capacity();
        inputs.resize(capacity, ClassicalId(7));
        let original = inputs.clone();
        let mut issued = 0;
        let result = Value::input_word(
            1,
            &mut inputs,
            |cells| {
                assert_eq!(cells, capacity + 4);
                Err("bounded work exhausted")
            },
            || {
                issued += 1;
                ClassicalId(8)
            },
        );
        assert_eq!(result, Err("bounded work exhausted"));
        assert_eq!(inputs, original);
        assert_eq!(inputs.capacity(), capacity);
        assert_eq!(issued, 0);

        let value =
            Value::input_word(1, &mut inputs, |_| Ok::<_, ()>(()), || ClassicalId(8)).unwrap();
        assert_eq!(value.ty(), Ty::bits(1));
        assert_eq!(&inputs[..capacity], original.as_slice());
        assert_eq!(inputs[capacity], ClassicalId(8));
    }

    #[test]
    fn one_bit_word_instrument_interface_remains_distinct_from_bit_and_unit() {
        let result = Ty::pair(Ty::bits(1), Ty::pair(Ty::bit(), Ty::bits(0)));
        let signature = crate::frontend::instrument::signature(
            &[Ty::quantum(Ty::bits(1))],
            &result,
            |size| Some(*size),
            &mut crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap();
        assert_eq!(signature.input, crate::contract::BasisType::Bits(1));
        assert_eq!(
            signature.result,
            [
                ResultAtom::Pair,
                ResultAtom::Bits(1),
                ResultAtom::Pair,
                ResultAtom::Bit,
                ResultAtom::Bits(0),
            ]
        );
    }
}
