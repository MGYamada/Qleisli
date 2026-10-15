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
    /// Consume already charged bindings from original source occurrences.
    /// Unlike host names, these keys must belong to this exact interface.
    pub(super) fn binders_budgeted(
        checked: CheckedInterface<'a>,
        bases: BTreeMap<BinderKey, ClosedType>,
        naturals: BTreeMap<BinderKey, u32>,
        subject: &str,
        mut charge: impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        let interface = checked.interface;
        let span = checked.span;
        charge(
            span,
            interface.statics.len().checked_mul(3).ok_or_else(|| {
                SourceError::new("limit", span, "closed binding accounting overflow")
            })?,
        )?;
        validate_bound_keys(&bases, interface, true, subject, span, &mut charge)?;
        validate_bound_keys(&naturals, interface, false, subject, span, &mut charge)?;
        for formal in &interface.statics {
            charge(span, formal.key.name.len() + 1)?;
        }
        for ty in bases.values() {
            validate_closed_basis(ty, span, &mut charge)?;
        }
        Ok(Self {
            checked,
            naturals,
            bases,
        })
    }

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
            validate_closed_basis(basis(value), span, &mut charge)?;
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

fn validate_bound_keys<V>(
    values: &BTreeMap<BinderKey, V>,
    interface: &Interface,
    bases: bool,
    subject: &str,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    let category_matches = |kind: &StaticKind| {
        if bases {
            matches!(kind, StaticKind::Basis)
        } else {
            matches!(kind, StaticKind::Natural)
        }
    };
    let mut expected = 0usize;
    for formal in &interface.statics {
        charge(span, 1)?;
        expected += usize::from(category_matches(&formal.kind));
    }
    let mut matching = values.len() == expected;
    for key in values.keys() {
        charge(span, key.name.len() + 1)?;
        let mut found = false;
        for formal in &interface.statics {
            charge(span, 1)?;
            if key == &formal.key && category_matches(&formal.kind) {
                found = true;
                break;
            }
        }
        matching &= found;
    }
    if !matching {
        charge(span, subject.len() + 128)?;
        let category = if bases { "Basis" } else { "natural" };
        return Err(SourceError::new(
            "static",
            span,
            format!(
                "concrete {category} bindings for {subject} must belong to the original declaration"
            ),
        ));
    }
    Ok(())
}

fn validate_closed_basis(
    ty: &ClosedType,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    let size = type_size_budgeted(ty, 4096, 64, true, span, charge)?;
    charge(
        span,
        size.nodes
            .checked_mul(2)
            .ok_or_else(|| SourceError::new("limit", span, "closed Basis accounting overflow"))?,
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
            Kind::Q(_) => unreachable!("ordinary Basis preflight"),
            _ => {}
        }
    }
    charge(span, size.nodes)
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

    fn original_formal(program: &CheckedProgram, function: &str, name: &str) -> BinderKey {
        let definition = program
            .resolution
            .qualified(&format!("main::{function}"))
            .unwrap();
        program
            .interface(definition)
            .statics
            .iter()
            .find(|formal| formal.key.name == name)
            .unwrap()
            .key
            .clone()
    }

    fn binder_closed(
        program: &CheckedProgram,
        name: &str,
        bases: BTreeMap<BinderKey, ClosedType>,
        naturals: BTreeMap<BinderKey, u32>,
    ) -> Result<ClosedInterface> {
        let definition = program
            .resolution
            .qualified(&format!("main::{name}"))
            .unwrap();
        let original =
            CheckedInterface::original(program, definition, Span::default(), &mut |_, _| Ok(()))?;
        let substitution =
            ClosedSubstitution::binders_budgeted(original, bases, naturals, "test", |_, _| Ok(()))?;
        close_interface_budgeted(substitution, "test", |_, _| Ok(()), |_, _| Ok(()))
    }

    #[test]
    fn binder_substitution_rejects_foreign_categories_and_cardinality() {
        let program = checked(
            "fn first[const A:Basis,const n:Nat,const U:Op<A>](q:Q<A>)->Q<A>
             requires n >= 1,Applicable(U){q}
             fn second[const A:Basis,const n:Nat](q:Q<A>)->Q<A> requires n >= 1{q}",
        );
        let a = original_formal(&program, "first", "A");
        let n = original_formal(&program, "first", "n");
        let u = original_formal(&program, "first", "U");
        let other_a = original_formal(&program, "second", "A");
        let other_n = original_formal(&program, "second", "n");
        assert_eq!(a.name, other_a.name);
        assert_ne!(a, other_a);
        assert_eq!(n.name, other_n.name);
        assert_ne!(n, other_n);
        let valid_bases = BTreeMap::from([(a.clone(), ClosedType::unit())]);
        let valid_naturals = BTreeMap::from([(n.clone(), 1)]);
        assert!(
            binder_closed(
                &program,
                "first",
                valid_bases.clone(),
                valid_naturals.clone()
            )
            .is_ok()
        );
        for bases in [
            BTreeMap::new(),
            BTreeMap::from([(other_a.clone(), ClosedType::unit())]),
            BTreeMap::from([(n.clone(), ClosedType::unit())]),
            BTreeMap::from([(u, ClosedType::unit())]),
            BTreeMap::from([
                (a.clone(), ClosedType::unit()),
                (other_a, ClosedType::unit()),
            ]),
        ] {
            let error = binder_closed(&program, "first", bases, valid_naturals.clone())
                .err()
                .expect("foreign, wrong-category, missing or extra Basis key accepted");
            assert_eq!(error.code, "static");
        }
        for naturals in [
            BTreeMap::new(),
            BTreeMap::from([(other_n.clone(), 1)]),
            BTreeMap::from([(a, 1)]),
            BTreeMap::from([(n, 1), (other_n, 1)]),
        ] {
            let error = binder_closed(&program, "first", valid_bases.clone(), naturals)
                .err()
                .expect("foreign, wrong-category, missing or extra natural key accepted");
            assert_eq!(error.code, "static");
        }
    }

    fn same_closed_interface(named: &ClosedInterface, bound: &ClosedInterface) {
        assert_eq!(named.bases, bound.bases);
        assert_eq!(named.naturals, bound.naturals);
        assert_eq!(named.parameters, bound.parameters);
        assert_eq!(named.result, bound.result);
        assert_eq!(
            named.operations.keys().collect::<Vec<_>>(),
            bound.operations.keys().collect::<Vec<_>>()
        );
        for (key, expected) in &named.operations {
            let actual = &bound.operations[key];
            assert_eq!(actual.input, expected.input);
            assert_eq!(actual.codomain, expected.codomain);
            assert_eq!(actual.access, expected.access);
            assert_eq!(actual.meaning, expected.meaning);
            assert_eq!(actual.ceiling(), expected.ceiling());
        }
    }

    #[test]
    fn named_and_binder_closure_keep_separate_ports_meaning_and_premises() {
        let program = checked(
            "fn route[const A:Basis,const B:Basis,const n:Nat,const U:Op<A -> B>](q:Q<A>)->Q<B>
             requires n >= 1,Applicable(U){U(q)}
             unitary fn same(q:Q<Bit>)->Q<Bit>{q}
             meaning M:Bit=reference(same);
             fn refined[const U:Op<Bit,M>](q:Q<Bit>)->Q<Bit>
             requires Applicable(U),Adjointable(U){U(q)}",
        );
        let a = original_formal(&program, "route", "A");
        let b = original_formal(&program, "route", "B");
        let n = original_formal(&program, "route", "n");
        let input = ClosedType::unit();
        let output = ClosedType::pair(ClosedType::bits(0), ClosedType::bit());
        let named_bases =
            BTreeMap::from([("A".into(), input.clone()), ("B".into(), output.clone())]);
        let bound_bases = BTreeMap::from([(a, input.clone()), (b, output.clone())]);
        let named = closed(
            &program,
            "route",
            named_bases.clone(),
            BTreeMap::from([("n".into(), 1)]),
        )
        .unwrap();
        let bound = binder_closed(
            &program,
            "route",
            bound_bases.clone(),
            BTreeMap::from([(n.clone(), 1)]),
        )
        .unwrap();
        same_closed_interface(&named, &bound);
        let operation = bound.operations.values().next().unwrap();
        assert_eq!(operation.input, ClosedType::quantum(input));
        assert_eq!(operation.output(), &ClosedType::quantum(output));
        assert_eq!(operation.ceiling(), crate::ir::Effect::Isometry);

        let named = closed(&program, "refined", BTreeMap::new(), BTreeMap::new()).unwrap();
        let bound = binder_closed(&program, "refined", BTreeMap::new(), BTreeMap::new()).unwrap();
        same_closed_interface(&named, &bound);
        let operation = bound.operations.values().next().unwrap();
        assert_eq!(operation.access, [true, true, false]);
        assert_eq!(
            operation.meaning,
            Some(program.resolution.qualified("main::M").unwrap())
        );

        let named = closed(
            &program,
            "route",
            named_bases,
            BTreeMap::from([("n".into(), 0)]),
        )
        .err()
        .expect("false named premise accepted");
        let bound = binder_closed(&program, "route", bound_bases, BTreeMap::from([(n, 0)]))
            .err()
            .expect("false binder premise accepted");
        assert_eq!(named.code, "size");
        assert_eq!(bound.code, named.code);
        assert_eq!(bound.module, named.module);
        assert_eq!(bound.span, named.span);
        assert_eq!(bound.message, named.message);
    }

    #[test]
    fn both_substitution_paths_reject_nonordinary_or_unclosed_basis_trees() {
        let program = checked("unitary fn id[const A:Basis](q:Q<A>)->Q<A>{q}");
        let a = original_formal(&program, "id", "A");
        let parameter = ClosedType::parameter(super::super::types::TypeParameter {
            key: Some(a.clone()),
            name: "A".into(),
            span: Span::default(),
        });
        for (basis, message) in [
            (ClosedType::quantum(ClosedType::unit()), "quantum ownership"),
            (
                ClosedType::pair(ClosedType::unit(), ClosedType::quantum(ClosedType::bit())),
                "quantum ownership",
            ),
            (parameter, "closed ordinary type"),
            (ClosedType::tuple(vec![]), "at least two fields"),
            (
                ClosedType::pair(
                    ClosedType::unit(),
                    ClosedType::tuple(vec![ClosedType::unit()]),
                ),
                "at least two fields",
            ),
        ] {
            let named = closed(
                &program,
                "id",
                BTreeMap::from([("A".into(), basis.clone())]),
                BTreeMap::new(),
            )
            .err()
            .expect("invalid named Basis accepted");
            let bound = binder_closed(
                &program,
                "id",
                BTreeMap::from([(a.clone(), basis)]),
                BTreeMap::new(),
            )
            .err()
            .expect("invalid bound Basis accepted");
            for error in [named, bound] {
                assert_eq!(error.code, "type");
                assert!(error.message.contains(message), "{error:?}");
            }
        }
    }

    #[test]
    fn binder_closure_preserves_distinct_zero_width_basis_tags() {
        let program = checked("unitary fn id[const A:Basis](q:Q<A>)->Q<A>{q}");
        let a = original_formal(&program, "id", "A");
        let mut results = Vec::new();
        for basis in [ClosedType::unit(), ClosedType::bits(0)] {
            assert_eq!(basis.basis_width(), Some(0));
            let result = binder_closed(
                &program,
                "id",
                BTreeMap::from([(a.clone(), basis.clone())]),
                BTreeMap::new(),
            )
            .unwrap();
            assert_eq!(result.parameters, [ClosedType::quantum(basis.clone())]);
            assert_eq!(result.result, ClosedType::quantum(basis));
            results.push(result.result);
        }
        assert_ne!(results[0], results[1]);
    }

    #[test]
    fn basis_validation_stops_at_preallocation_charge_failures() {
        let span = Span::default();
        let mut calls = 0;
        let error = validate_closed_basis(&ClosedType::unit(), span, &mut |_, _| {
            calls += 1;
            Err(SourceError::new(
                "limit",
                span,
                "initial traversal reservation",
            ))
        })
        .unwrap_err();
        assert_eq!(calls, 1);
        assert_eq!(error.message, "initial traversal reservation");

        // Three ordinary nodes require a bounded first walk. Refuse its next
        // reservation before the second walk can reach the unresolved node.
        let unresolved = ClosedType::pair(
            ClosedType::unit(),
            ClosedType::parameter(super::super::types::TypeParameter {
                key: None,
                name: "unresolved".into(),
                span,
            }),
        );
        let mut remaining = 6usize;
        let mut declined = None;
        let error = validate_closed_basis(&unresolved, span, &mut |_, cells| {
            remaining = remaining.checked_sub(cells).ok_or_else(|| {
                declined = Some(cells);
                SourceError::new("limit", span, "second traversal reservation")
            })?;
            Ok(())
        })
        .unwrap_err();
        assert_eq!(remaining, 0);
        assert_eq!(declined, Some(6));
        assert_eq!(error.code, "limit");
        assert_eq!(error.message, "second traversal reservation");
    }

    #[test]
    fn binder_mismatch_stops_before_constructing_its_diagnostic() {
        let program = checked("unitary fn id[const A:Basis](q:Q<A>)->Q<A>{q}");
        let definition = program.resolution.qualified("main::id").unwrap();
        let interface = program.interface(definition);
        let span = Span::default();
        let subject = "mismatch control";
        let mut declined = false;
        let error = validate_bound_keys(
            &BTreeMap::<BinderKey, ClosedType>::new(),
            interface,
            true,
            subject,
            span,
            &mut |_, cells| {
                if cells > 1 {
                    declined = true;
                    return Err(SourceError::new("limit", span, "diagnostic reservation"));
                }
                Ok(())
            },
        )
        .unwrap_err();
        assert!(declined);
        assert_eq!(error.code, "limit");
        assert_eq!(error.message, "diagnostic reservation");
    }
}
