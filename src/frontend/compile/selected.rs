//! Selected ordinary roots use the common original-source compiler and v2 gate.
//! No projected or rewritten source supplies their independent type binding.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::source::SourceCollection;

/// A selected ordinary source and its actual native-accepted artifact. The
/// retained request checks the original interface and every canonical input
/// and hidden output history; it does not prove source preservation.
/// This first selected profile emits only classical Raw instructions.
#[derive(Debug)]
pub struct SelectedOrdinaryProgram {
    source: Instantiation,
    program: AcceptedProgram,
    parameters: usize,
}

impl SelectedOrdinaryProgram {
    pub fn source(&self) -> &Instantiation {
        &self.source
    }
    pub fn program(&self) -> &AcceptedProgram {
        &self.program
    }
    /// Counts original parameters, including zero-width Unit/record values.
    pub fn runtime_parameters(&self) -> usize {
        self.parameters
    }
}

pub(in crate::frontend) fn compile(
    source: &Instantiation,
    originals: &SourceCollection,
    kernel: &crate::interchange::native::Kernel,
) -> Result<SelectedOrdinaryProgram, Diagnostic> {
    process(source, originals, kernel).map_err(Diagnostic::from_compile)
}

fn process(
    selected: &Instantiation,
    originals: &SourceCollection,
    kernel: &crate::interchange::native::Kernel,
) -> Result<SelectedOrdinaryProgram, CompileError> {
    let originals = Originals::Selected(originals);
    // Selected preparations own their AST. Borrow it intact and obtain a fresh
    // complete common judgment with its actual occurrence associations. Never
    // combine cached facts with indices from another check, clone an AST into
    // a synthetic Project, or turn a generic header into a nongeneric one.
    let PreparedSource {
        checked: source,
        occurrences,
        interface_naturals,
    } = prepare_borrowed_originals(originals, SourceLimits::selected())?;
    let entry = source.resolution.qualified(selected.entry()).map_err(|_| {
        originals.error(SourceError::new(
            "name",
            Span::default(),
            "selected entry is not exported",
        ))
    })?;
    let declarations: BTreeMap<_, _> = source
        .resolution
        .declarations()
        .map(|(key, record)| {
            (
                key,
                &originals
                    .module(&record.name.0)
                    .expect("original module")
                    .ast
                    .decls[record.ast_index],
            )
        })
        .collect();
    let declaration = declarations[&entry];
    let module = &source.resolution.declaration(entry).name.0;
    let error = |message| {
        originals
            .error(SourceError::new("unsupported", declaration.span, message).in_module(module))
    };
    if kernel.edition() != selected.program().edition() {
        return Err(error(
            "selected kernel edition differs from the captured source edition",
        ));
    }
    if !declaration.public || matches!(declaration.kind, FnKind::Static | FnKind::Meaning) {
        return Err(error(
            "typed selected execution requires an exported runtime function",
        ));
    }
    if !declaration.static_params.is_empty()
        || !selected.types().is_empty()
        || !selected.naturals().is_empty()
        || !selected.operations().is_empty()
    {
        return Err(error(
            "generic selected ordinary roots require independent original static-binder transport",
        ));
    }
    let interface = &source.interfaces[&entry];
    if interface.params.iter().any(|ty| ty.linear()) || interface.result.linear() {
        return Err(error(
            "typed selected ordinary roots require ordinary input and output ports",
        ));
    }
    let parameters = declaration.params.len();
    let mut compiler = Compiler {
        kernel: kernel.clone(),
        originals,
        source,
        interface_naturals,
        locals: Forest::from_occurrences(occurrences),
        declarations,
        force_ordinary_root: true,
        selected_entry: Some(entry),
        selected_calls: 0,
        basis: BTreeMap::new(),
        deferred_nominal_tables: BTreeSet::new(),
        checked: BTreeMap::new(),
        function_evidence: BTreeMap::new(),
        instrument_evidence: BTreeMap::new(),
        source_rows: BTreeMap::new(),
        source_sets: BTreeMap::new(),
        pure_equations: Vec::new(),
        computed_normalizations: Vec::new(),
        meanings: BTreeMap::new(),
        providers: BTreeMap::new(),
        instances: vec![],
        concrete_context: instances::Context::default(),
        work: 0,
        checking: Some(entry),
        exact_work: crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        closed_meanings: BTreeMap::new(),
    };
    let module = compiler.source.resolution.declaration(entry).name.0.clone();
    let span = compiler.declarations[&entry].span;
    // All siblings already underwent the complete source judgment. Concrete
    // eligibility applies to this root's full lexical dependency closure,
    // including inactive regions; an unused unsupported sibling is no root.
    let mut pending = vec![entry];
    let mut closure = BTreeSet::new();
    while let Some(key) = pending.pop() {
        compiler.charge(&module, span, compiler.declarations.len() + 2)?;
        if !closure.insert(key) {
            continue;
        }
        let original = compiler.declarations[&key];
        if !original.static_params.is_empty() && original.kind != FnKind::Static {
            return Err(compiler.error(
                &module,
                span,
                ErrorCode::Unsupported,
                "selected ordinary dependencies require independent generic transport",
            ));
        }
        if original.kind != FnKind::Static {
            if let Err((span, message)) =
                profile::check(original, &compiler.source.interfaces[&key])
            {
                return Err(compiler.originals.error(
                    SourceError::new("unsupported", span, message)
                        .in_module(&compiler.source.resolution.declaration(key).name.0),
                ));
            }
        }
        let uses = compiler.source.lexical[&key].resolved_uses();
        compiler.charge(&module, span, uses.len().saturating_mul(3) + 1)?;
        for usage in compiler.source.lexical[&key].resolved_uses() {
            if let ResolvedUse::Global(Target::Declaration(callee)) = usage.target {
                pending.push(callee);
            }
        }
    }
    compiler.prepare_selected_classical_tables(Some(&closure))?;
    prepare_evidence_dependencies(&mut compiler, &closure, &module, span)?;
    let program = lower::lower_function(&mut compiler, &entry)?;
    compiler.checked.insert(entry, program.clone());
    // The selected producer's classical-only limits do not reclassify dormant
    // quantum/control obligations from the complete common source judgment.
    // They use the existing finite evidence gates and never replace this root.
    compiler.force_ordinary_root = false;
    // Global dormant passes visit original obligations outside this root's
    // closure. Prepare their actual Meaning/table dependencies under the
    // existing finite evidence profile, without widening the selected root.
    prepare_dormant_dependencies(&mut compiler, &closure, &module, span)?;
    compiler.check_dormant_operations()?;
    compiler.check_dormant_controls()?;
    compiler.check_dormant_function_contracts()?;
    let program = program
        .retain_instruments(compiler.instrument_evidence.into_values().collect())
        .retain_pure_equations(compiler.pure_equations)
        .retain_computed_normalizations(compiler.computed_normalizations);
    Ok(SelectedOrdinaryProgram {
        source: selected.clone(),
        program,
        parameters,
    })
}

fn prepare_dormant_dependencies(
    compiler: &mut Compiler<'_>,
    root_closure: &BTreeSet<Key>,
    module: &str,
    span: Span,
) -> Result<(), CompileError> {
    compiler.charge(
        module,
        span,
        compiler
            .source
            .obligations
            .len()
            .saturating_mul(4)
            .saturating_add(compiler.source.body_statics.len())
            .saturating_add(1),
    )?;
    let mut pending = Vec::new();
    for obligation in &compiler.source.obligations {
        use check::ObligationKind;
        // Match the three global dormant passes. Ordinary provider/call
        // metadata alone does not request concrete execution of its owner.
        match obligation.kind {
            ObligationKind::MeaningEquality { required, supplied } => {
                pending.push(obligation.definition);
                pending.push(required);
                pending.extend(supplied);
            }
            ObligationKind::FunctionEquality {
                implementation,
                specification,
            } => {
                pending.push(obligation.definition);
                pending.extend([implementation, specification]);
            }
            ObligationKind::ControlSectors => pending.push(obligation.definition),
            _ => {}
        }
    }
    pending.extend(
        compiler
            .source
            .body_statics
            .values()
            .filter(|plan| {
                !matches!(
                    plan.kind,
                    check::plans::BodyStaticKind::PrimitiveCall { .. }
                )
            })
            .map(|plan| plan.owner),
    );
    let mut needed = BTreeSet::new();
    while let Some(key) = pending.pop() {
        compiler.charge(module, span, compiler.declarations.len() + 2)?;
        if !needed.insert(key) {
            continue;
        }
        let uses = compiler.source.lexical[&key].resolved_uses();
        compiler.charge(module, span, uses.len().saturating_mul(3) + 1)?;
        for usage in compiler.source.lexical[&key].resolved_uses() {
            if let ResolvedUse::Global(Target::Declaration(callee)) = usage.target {
                pending.push(callee);
            }
        }
    }
    // Root tables already passed their stricter selected limits. Do not
    // replace them with a second preparation under the dormant profile.
    needed.retain(|key| !root_closure.contains(key));
    prepare_evidence_dependencies(compiler, &needed, module, span)
}

/// Prepare actual closed bodies demanded by Meaning references and fixed
/// function pairs. Merely owning a dormant obligation does not make its whole
/// declaration an execution root. Reuse the normal dependency order and native
/// lowerer; no surrogate body can populate the checked cache.
fn prepare_evidence_dependencies(
    compiler: &mut Compiler<'_>,
    needed: &BTreeSet<Key>,
    module: &str,
    span: Span,
) -> Result<(), CompileError> {
    compiler.charge(
        module,
        span,
        compiler
            .source
            .obligations
            .len()
            .saturating_mul(3)
            .saturating_add(needed.len())
            .saturating_add(1),
    )?;
    let mut pending = Vec::new();
    for obligation in &compiler.source.obligations {
        if needed.contains(&obligation.definition) {
            if let check::ObligationKind::FunctionEquality {
                implementation,
                specification,
            } = obligation.kind
            {
                pending.extend([implementation, specification]);
            }
        }
    }
    for key in needed {
        if compiler.declarations[key].kind == FnKind::Meaning {
            pending.push(*key);
        }
        if let FnBody::MeaningReference { function } = &compiler.declarations[key].body {
            let owner = &compiler.source.resolution.declaration(*key).name.0;
            let Callee::User(reference) = compiler.resolve(owner, function)? else {
                return Err(compiler.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "Meaning reference requires its original ordinary definition",
                ));
            };
            pending.push(reference);
        }
    }
    let mut evidence = BTreeSet::new();
    while let Some(key) = pending.pop() {
        compiler.charge(module, span, compiler.declarations.len() + 2)?;
        if !evidence.insert(key) {
            continue;
        }
        let uses = compiler.source.lexical[&key].resolved_uses();
        compiler.charge(module, span, uses.len().saturating_mul(3) + 1)?;
        for usage in compiler.source.lexical[&key].resolved_uses() {
            if let ResolvedUse::Global(Target::Declaration(callee)) = usage.target {
                pending.push(callee);
            }
        }
    }
    // Evidence bodies have the existing finite quantum profile. They do not
    // inherit the selected ordinary producer's classical-only Raw restriction.
    let selected = compiler.force_ordinary_root;
    let checking = compiler.checking;
    compiler.force_ordinary_root = false;
    let result = (|| {
        // Only actual Meaning/function evidence roots demand tables. A Nat
        // obligation in an unused owner does not require every classical
        // callee elsewhere in that owner's body to become a concrete table.
        compiler.charge(module, span, evidence.len() + 1)?;
        let tables: BTreeSet<_> = evidence
            .iter()
            .copied()
            .filter(|key| {
                compiler.declarations[key].kind == FnKind::Classical
                    && !compiler.basis.contains_key(key)
                    && !compiler.deferred_nominal_tables.contains(key)
            })
            .collect();
        compiler.prepare_selected_classical_tables(Some(&tables))?;
        for ordinal in 0..compiler.source.dependency_order.len() {
            let key = compiler.source.dependency_order[ordinal];
            compiler.checking = Some(key);
            let declaration = compiler.declarations[&key];
            if declaration.kind == FnKind::Meaning {
                if evidence.contains(&key) && !compiler.meanings.contains_key(&key) {
                    compiler.compile_meaning(&key)?;
                }
            } else if evidence.contains(&key)
                && declaration.static_params.is_empty()
                && !matches!(declaration.kind, FnKind::Static | FnKind::Classical)
                && !compiler.checked.contains_key(&key)
            {
                let actual = lower::lower_function(compiler, &key)?;
                compiler.checked.insert(key, actual);
            }
        }
        Ok(())
    })();
    compiler.force_ordinary_root = selected;
    compiler.checking = checking;
    result
}

pub(super) fn check_raw_capacity(
    compiler: &mut Compiler<'_>,
    module: &str,
    span: Span,
    raw: &crate::ir::RawProgram,
) -> Result<(), CompileError> {
    use crate::ir::RawOp;
    compiler.charge(module, span, 2)?;
    let mut pending = vec![(raw.operations.as_slice(), 0usize)];
    let mut count = 0usize;
    while let Some((operations, depth)) = pending.pop() {
        compiler.charge(module, span, operations.len() + 1)?;
        count = count.saturating_add(operations.len());
        if count > 10_000 || depth > 16 {
            return Err(compiler.error(
                module,
                span,
                ErrorCode::Limit,
                "selected ordinary Raw exceeds 10000 instructions or branch depth 16",
            ));
        }
        for operation in operations {
            match operation {
                RawOp::ClassicalConst {..} | RawOp::ClassicalNot {..} |
                RawOp::ClassicalXor {..} | RawOp::ClassicalAnd {..} => {}
                RawOp::ClassicalBranch { then_ops, else_ops, quantum_phis, .. } if quantum_phis.is_empty() => {
                    compiler.charge(module, span, 4)?;
                    pending.push((then_ops, depth + 1));
                    pending.push((else_ops, depth + 1));
                }
                _ => return Err(compiler.error(module, span, ErrorCode::Unsupported,
                    "selected nominal execution currently requires classical Raw instructions; quantum temporary values remain unsupported")),
            }
        }
    }
    Ok(())
}

pub(super) fn check_type_capacity(
    compiler: &Compiler<'_>,
    work: &mut usize,
    module: &str,
    span: Span,
    ty: &Ty,
) -> Result<(), CompileError> {
    if !compiler.force_ordinary_root {
        return Ok(());
    }
    compiler.charge_at(work, module, span, 2)?;
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        compiler.charge_at(work, module, span, 2)?;
        match &ty.kind {
            Kind::Bits(width) if *width > 8 => {
                return Err(compiler.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "selected ordinary words exceed eight bits",
                ));
            }
            Kind::Q(_) => {
                return Err(compiler.error(
                    module,
                    span,
                    ErrorCode::Unsupported,
                    "selected nominal execution currently requires classical temporary values",
                ));
            }
            Kind::Tuple(fields) => {
                compiler.charge_at(work, module, span, fields.len())?;
                pending.extend(fields);
            }
            Kind::Nominal(nominal) => {
                compiler.charge_at(work, module, span, nominal.fields().len())?;
                pending.extend(nominal.fields());
            }
            _ => {}
        }
    }
    Ok(())
}
