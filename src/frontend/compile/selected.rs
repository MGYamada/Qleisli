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
    for ordinal in 0..compiler.source.dependency_order.len() {
        let key = compiler.source.dependency_order[ordinal];
        if closure.contains(&key) && compiler.declarations[&key].kind == FnKind::Meaning {
            compiler.compile_meaning(&key)?;
        }
    }
    let program = lower::lower_function(&mut compiler, &entry)?;
    // The selected producer's classical-only limits do not reclassify dormant
    // quantum/control obligations from the complete common source judgment.
    // They use the existing finite evidence gates and never replace this root.
    compiler.force_ordinary_root = false;
    compiler.check_dormant_operations()?;
    compiler.check_dormant_controls()?;
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
