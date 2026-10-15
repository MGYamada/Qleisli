//! Exact closure of common checked interfaces, independent of lowering profiles.
//!
//! This module grants no capabilities or accepted handles. Original resolution,
//! normalized premises and exact type trees remain the source judgment; each
//! adapter supplies its existing concrete capacity check.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::ast::Span;
use super::check::{
    CheckedProgram, Interface, Linear, Result, SourceError, StaticKind, close_type_budgeted,
    type_size_budgeted,
};
use super::resolve::DefId;
use super::resolve::locals::BinderKey;
use super::types::{Kind, Type};
use std::collections::{BTreeMap, BTreeSet};

type ClosedType = Type<u32>;

/// Borrow one interface only through its original complete checked collection.
/// No standalone Interface, foreign resolution or rewritten source is accepted.
#[derive(Clone, Copy)]
pub(super) struct CheckedInterface<'a> {
    interface: &'a Interface,
    span: Span,
}
impl<'a> CheckedInterface<'a> {
    pub(super) fn original(
        program: &'a CheckedProgram,
        definition: DefId,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, 1)?;
        if !program.effects.contains_key(&definition) {
            return Err(SourceError::new(
                "type",
                span,
                "closed interface requires a checked ordinary runtime function",
            ));
        }
        let interface = program.interfaces.get(&definition).ok_or_else(|| {
            SourceError::new("static", span, "missing original checked runtime interface")
        })?;
        let declaration = program.resolution.declaration(definition);
        if declaration.ast_index != interface.ast_index
            || declaration.kind != interface.kind
            || program.resolution.module_name(declaration.module) != interface.module
        {
            return Err(SourceError::new(
                "source",
                span,
                "checked interface does not match its original declaration",
            ));
        }
        Ok(Self { interface, span })
    }
}

/// Original BinderKey substitutions. Construction validates the complete host
/// name/category maps once; retaining the borrowed interface prevents a caller
/// from pairing those maps with another definition's interface.
pub(super) struct ClosedSubstitution<'a> {
    checked: CheckedInterface<'a>,
    naturals: BTreeMap<BinderKey, u32>,
    bases: BTreeMap<BinderKey, ClosedType>,
}

pub(super) struct ClosedInterface {
    pub naturals: BTreeMap<BinderKey, u32>,
    pub bases: BTreeMap<BinderKey, ClosedType>,
    pub parameters: Vec<ClosedType>,
    pub result: ClosedType,
    pub operations: BTreeMap<BinderKey, ClosedOperation>,
}

pub(super) struct ClosedOperation {
    pub input: ClosedType,
    pub codomain: Option<ClosedType>,
    access: [bool; 3],
    pub meaning: Option<DefId>,
}
impl ClosedOperation {
    pub fn output(&self) -> &ClosedType {
        self.codomain.as_ref().unwrap_or(&self.input)
    }
    pub fn ceiling(&self) -> crate::ir::Effect {
        if self.codomain.is_some() && !self.access[1] && !self.access[2] {
            crate::ir::Effect::Isometry
        } else {
            crate::ir::Effect::Unitary
        }
    }
}

pub(super) fn check_named_bindings_budgeted<V>(
    actual: &BTreeMap<String, V>,
    expected: &BTreeSet<&str>,
    category: &str,
    subject: &str,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    for name in actual.keys() {
        charge(span, name.len() + 1)?;
    }
    charge(span, expected.len())?;
    if actual.len() == expected.len() && expected.iter().all(|name| actual.contains_key(*name)) {
        return Ok(());
    }
    let missing = expected
        .iter()
        .filter(|name| !actual.contains_key(**name))
        .copied()
        .collect::<Vec<_>>()
        .join(", ");
    let unexpected = actual
        .keys()
        .filter(|name| !expected.contains(name.as_str()))
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(", ");
    Err(SourceError::new(
        "static",
        span,
        format!(
            "concrete {category} bindings for {subject} must exactly match the declaration; missing [{missing}]; unexpected [{unexpected}]"
        ),
    ))
}

impl<'a> ClosedSubstitution<'a> {
    pub(super) fn named_budgeted<B>(
        checked: CheckedInterface<'a>,
        types: &BTreeMap<String, B>,
        naturals: &BTreeMap<String, u32>,
        basis: impl Fn(&B) -> &ClosedType,
        subject: &str,
        mut charge: impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        let interface = checked.interface;
        let span = checked.span;
        // Reserve both temporary binding sets and retained map entries before
        // collecting them. Copy the original binder identities, never a name-
        // resolved substitute from another definition or source collection.
        charge(
            span,
            interface.statics.len().checked_mul(3).ok_or_else(|| {
                SourceError::new("limit", span, "closed binding accounting overflow")
            })?,
        )?;
        let expected_types = interface
            .statics
            .iter()
            .filter_map(|formal| {
                matches!(formal.kind, StaticKind::Basis).then_some(formal.key.name.as_str())
            })
            .collect();
        let expected_naturals = interface
            .statics
            .iter()
            .filter_map(|formal| {
                matches!(formal.kind, StaticKind::Natural).then_some(formal.key.name.as_str())
            })
            .collect();
        check_named_bindings_budgeted(types, &expected_types, "Basis", subject, span, &mut charge)?;
        check_named_bindings_budgeted(
            naturals,
            &expected_naturals,
            "natural",
            subject,
            span,
            &mut charge,
        )?;
        for formal in &interface.statics {
            charge(span, formal.key.name.len() + 1)?;
        }
        for value in types.values() {
            let ty = basis(value);
            let size = type_size_budgeted(ty, 4096, 64, true, span, &mut charge)?;
            // Unlike a selected BasisBinding, a profile-neutral caller has no
            // prior closed-Basis wrapper. Bound this borrowed validation before
            // allocating its traversal stack or copying a replacement tree.
            charge(
                span,
                size.nodes.checked_mul(2).ok_or_else(|| {
                    SourceError::new("limit", span, "closed Basis accounting overflow")
                })?,
            )?;
            let mut pending = vec![ty];
            while let Some(node) = pending.pop() {
                match &node.kind {
                    Kind::Parameter(_) => {
                        return Err(SourceError::new(
                            "type",
                            span,
                            "a Basis binding must be a closed ordinary type",
                        ));
                    }
                    Kind::Tuple(fields) if fields.len() < 2 => {
                        return Err(SourceError::new(
                            "type",
                            span,
                            "a Basis binding tuple requires at least two fields",
                        ));
                    }
                    Kind::Tuple(fields) => pending.extend(fields),
                    // type_size_budgeted already rejected every Q subtree.
                    Kind::Q(_) => unreachable!("ordinary Basis preflight"),
                    _ => {}
                }
            }
            charge(span, size.nodes)?;
        }
        let resolved_naturals = interface
            .statics
            .iter()
            .filter(|formal| matches!(formal.kind, StaticKind::Natural))
            .map(|formal| (formal.key.clone(), naturals[&formal.key.name]))
            .collect();
        let resolved_bases = interface
            .statics
            .iter()
            .filter(|formal| matches!(formal.kind, StaticKind::Basis))
            .map(|formal| (formal.key.clone(), basis(&types[&formal.key.name]).clone()))
            .collect();
        Ok(Self {
            checked,
            naturals: resolved_naturals,
            bases: resolved_bases,
        })
    }
}

fn closed_linear(
    linear: &Linear,
    naturals: &BTreeMap<BinderKey, u32>,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<i128> {
    charge(span, 1)?;
    linear
        .terms
        .iter()
        .try_fold(linear.constant, |sum, (key, coefficient)| {
            charge(span, 1)?;
            let n = naturals.get(key).ok_or_else(|| {
                SourceError::new(
                    "static",
                    span,
                    format!("missing concrete natural {}", key.name),
                )
            })?;
            let term = coefficient.checked_mul(i128::from(*n)).ok_or_else(|| {
                SourceError::new("limit", span, "concrete premise multiplication overflow")
            })?;
            sum.checked_add(term).ok_or_else(|| {
                SourceError::new("limit", span, "concrete premise addition overflow")
            })
        })
}

/// Close normalized common facts, retaining both exact operation ports. The
/// capacity callback may refuse a profile, but cannot rewrite the closed type.
pub(super) fn close_interface_budgeted(
    substitution: ClosedSubstitution<'_>,
    subject: &str,
    mut charge: impl FnMut(Span, usize) -> Result<()>,
    mut capacity: impl FnMut(&ClosedType, Span) -> Result<()>,
) -> Result<ClosedInterface> {
    let interface = substitution.checked.interface;
    let span = substitution.checked.span;
    let resolved_naturals = substitution.naturals;
    let resolved_bases = substitution.bases;
    let mut satisfied = false;
    for alternative in &interface.premises.alternatives {
        charge(span, 1)?;
        let mut valid = true;
        for constraint in alternative {
            if closed_linear(constraint, &resolved_naturals, span, &mut charge)? > 0 {
                valid = false;
                break;
            }
        }
        if valid {
            satisfied = true;
            break;
        }
    }
    if !satisfied {
        for premise in &interface.numeric_premises {
            // These affine expressions were normalized by the complete common
            // judgment, under the original preceding guards. Evaluate them
            // only to locate an already rejected closed constraint; never
            // reparse a predicate or use this diagnostic as acceptance.
            let checked = (|| {
                charge(premise.span, 1)?;
                let left =
                    closed_linear(&premise.left, &resolved_naturals, premise.span, &mut charge)?;
                let right = closed_linear(
                    &premise.right,
                    &resolved_naturals,
                    premise.span,
                    &mut charge,
                )?;
                use crate::frontend::ast::Compare;
                let (valid, comparison) = match premise.comparison {
                    Compare::Eq => (left == right, "=="),
                    Compare::Ne => (left != right, "!="),
                    Compare::Lt => (left < right, "<"),
                    Compare::Le => (left <= right, "<="),
                    Compare::Gt => (left > right, ">"),
                    Compare::Ge => (left >= right, ">="),
                };
                if !valid {
                    // Account for rendering the original normalized names and
                    // the diagnostic before constructing their owned String.
                    let cells = premise
                        .left
                        .storage_cells()?
                        .checked_add(premise.right.storage_cells()?)
                        .and_then(|cells| cells.checked_add(subject.len() + 128))
                        .ok_or_else(|| {
                            SourceError::new(
                                "limit",
                                premise.span,
                                "premise diagnostic accounting overflow",
                            )
                        })?;
                    charge(premise.span, cells)?;
                    return Err(SourceError::new(
                        "size",
                        premise.span,
                        format!(
                            "concrete {subject} premise `{} {comparison} {}` is false (evaluated {left} {comparison} {right})",
                            premise.left, premise.right,
                        ),
                    ));
                }
                Ok::<_, SourceError>(())
            })();
            checked.map_err(|error| error.in_module(&interface.module))?;
        }
        // Keep the original failure if a rejected Context has no false source
        // comparison (for example, a future additional implicit constraint).
        return Err(
            SourceError::new("size", span, "concrete function premise is false")
                .in_module(&interface.module),
        );
    }
    let mut close = |ty: &crate::frontend::check::Ty| -> Result<ClosedType> {
        let closed =
            close_type_budgeted(ty, &resolved_naturals, &resolved_bases, span, &mut charge)?;
        capacity(&closed, span)?;
        Ok(closed)
    };
    let parameters = interface
        .params
        .iter()
        .map(&mut close)
        .collect::<Result<_>>()?;
    let result = close(&interface.result)?;
    let operations = interface
        .statics
        .iter()
        .filter_map(|formal| match &formal.kind {
            StaticKind::Operation {
                basis,
                codomain,
                access,
                meaning,
            } => Some((|| {
                let input = ClosedType::quantum(close(basis)?);
                let output = codomain
                    .as_ref()
                    .map(|ty| close(ty).map(ClosedType::quantum))
                    .transpose()?;
                Ok((
                    formal.key.clone(),
                    ClosedOperation {
                        input,
                        codomain: output,
                        access: *access,
                        meaning: *meaning,
                    },
                ))
            })()),
            _ => None,
        })
        .collect::<Result<_>>()?;
    Ok(ClosedInterface {
        naturals: resolved_naturals,
        bases: resolved_bases,
        parameters,
        result,
        operations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked(source: &str) -> CheckedProgram {
        let module = crate::frontend::parser::parse_module(source).unwrap();
        super::super::check::program_with(
            BTreeMap::from([("main", &module)]),
            super::super::check::SourceLimits::selected(),
            |_, _, _, _, _, _, _| Ok(()),
        )
        .unwrap()
        .0
    }

    fn closed(
        program: &CheckedProgram,
        name: &str,
        bases: BTreeMap<String, ClosedType>,
        naturals: BTreeMap<String, u32>,
    ) -> Result<ClosedInterface> {
        let definition = program
            .resolution
            .qualified(&format!("main::{name}"))
            .unwrap();
        let checked =
            CheckedInterface::original(program, definition, Span::default(), &mut |_, _| Ok(()))?;
        let substitution = ClosedSubstitution::named_budgeted(
            checked,
            &bases,
            &naturals,
            |ty| ty,
            "test",
            |_, _| Ok(()),
        )?;
        close_interface_budgeted(substitution, "test", |_, _| Ok(()), |_, _| Ok(()))
    }

    #[test]
    fn common_closure_does_not_adopt_the_selected_eight_bit_profile() {
        let program = checked("pub unitary fn id[const A: Basis](q: Q<A>) -> Q<A> {q}");
        // This is only a closed type, with no IR, matrix, execution or native
        // quantum case generated. The selected public wrapper stays bounded.
        let basis = ClosedType::bits(9);
        let result = closed(
            &program,
            "id",
            BTreeMap::from([("A".into(), basis.clone())]),
            BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(result.parameters, [ClosedType::quantum(basis.clone())]);
        assert_eq!(result.result, ClosedType::quantum(basis));
        assert_eq!(
            crate::frontend::specialize::BasisBinding::parse("Bits<9>")
                .unwrap_err()
                .code(),
            "limit"
        );
    }

    #[test]
    fn rectangular_requirements_keep_exact_ports_and_original_meaning_identity() {
        let program = checked(
            "fn route[const A: Basis, const B: Basis, const U: Op<A -> B>](q: Q<A>) -> Q<B> requires Applicable(U) {U(q)}",
        );
        let input = ClosedType::unit();
        let output = ClosedType::pair(ClosedType::bits(0), ClosedType::bit());
        let result = closed(
            &program,
            "route",
            BTreeMap::from([("A".into(), input.clone()), ("B".into(), output.clone())]),
            BTreeMap::new(),
        )
        .unwrap();
        let operation = result.operations.values().next().unwrap();
        assert_eq!(operation.input, ClosedType::quantum(input));
        assert_eq!(operation.output(), &ClosedType::quantum(output));
        assert_eq!(operation.ceiling(), crate::ir::Effect::Isometry);
        assert!(operation.meaning.is_none());

        let program = checked(
            "unitary fn same(q: Q<Bit>) -> Q<Bit> {q}\nmeaning M: Bit = reference(same);\nfn apply[const U: Op<Bit,M>](q: Q<Bit>) -> Q<Bit> requires Applicable(U) {U(q)}",
        );
        let result = closed(&program, "apply", BTreeMap::new(), BTreeMap::new()).unwrap();
        let operation = result.operations.values().next().unwrap();
        assert_eq!(operation.ceiling(), crate::ir::Effect::Unitary);
        assert_eq!(
            operation.meaning,
            Some(program.resolution.qualified("main::M").unwrap())
        );
        assert!(operation.codomain.is_none());
    }

    #[test]
    fn runtime_closure_rejects_a_rectangular_meaning_declaration() {
        let program = checked(
            "use std::quantum::{finish,init0};
             isometry fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);init0()}
             meaning Prepared:Unit -> Bit=reference(prepare);",
        );
        let id = program.resolution.qualified("main::Prepared").unwrap();
        let interface = program.interface(id);
        assert!(matches!(&interface.meaning_input().kind, Kind::Unit));
        assert!(matches!(&interface.result.kind, Kind::Bit));
        assert!(!program.effects.contains_key(&id));
        let runtime = closed(&program, "prepare", BTreeMap::new(), BTreeMap::new()).unwrap();
        assert_eq!(
            runtime.parameters,
            [ClosedType::quantum(ClosedType::unit())]
        );
        assert_eq!(runtime.result, ClosedType::quantum(ClosedType::bit()));
        let error = match closed(&program, "Prepared", BTreeMap::new(), BTreeMap::new()) {
            Err(error) => error,
            Ok(_) => panic!("a rectangular Meaning was closed as a runtime interface"),
        };
        assert_eq!(error.code, "type");
        assert!(error.message.contains("checked ordinary runtime function"));
    }

    #[test]
    fn normalized_false_premises_keep_the_original_clause_and_location() {
        let program =
            checked("unitary fn id[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> requires n >= 1 {q}");
        let result = closed(
            &program,
            "id",
            BTreeMap::new(),
            BTreeMap::from([("n".into(), 0)]),
        );
        let error = match result {
            Err(error) => error,
            Ok(_) => panic!("false normalized premise accepted"),
        };
        let definition = program.resolution.qualified("main::id").unwrap();
        assert_eq!(error.code, "size");
        assert_eq!(error.module.as_deref(), Some("main"));
        assert_eq!(
            error.span,
            program.interface(definition).numeric_premises[0].span
        );
        assert!(error.message.contains("n >= 1"));
        assert!(error.message.contains("evaluated 0 >= 1"));
    }
}
