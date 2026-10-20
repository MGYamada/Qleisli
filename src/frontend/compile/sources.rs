//! Relevant original source provenance, with bytes interned once per compilation.
//! This metadata is not a replay project, source-preservation proof or acceptance.
use super::*;
use crate::contract::function::{SourceRows, SourceView};
use crate::frontend::resolve::locals::Table;
use crate::ir::{CircuitAction, CircuitStep, RawOp, RawProgram};

impl Compiler<'_> {
    pub(super) fn retained_sources(
        &mut self,
        module: &str,
        span: Span,
        roots: &[Key],
        bindings: &operations::Bindings,
        bodies: &[&RawProgram],
    ) -> Result<SourceRows, CompileError> {
        let mut work = self.work;
        let result = (|| {
            let mut collector = Collector {
                compiler: self,
                module,
                span,
                work: &mut work,
                pending: Vec::new(),
                definitions: BTreeSet::new(),
                modules: BTreeSet::new(),
                receipts: BTreeSet::new(),
            };
            // Project entry selection has no lexical UseInfo. A reexported
            // main::main still supplies the host's entry, so its exact export
            // chain belongs to the source receipts produced in this project.
            let resolution = &collector.compiler.source.resolution;
            if let Some(owner) = resolution.module("main") {
                if resolution.local(owner, "main").is_none()
                    && resolution.qualified("main::main").is_ok()
                {
                    resolution.visit_name_sources(owner, "main::main", |module| {
                        collector.source(resolution.module_name(module), None)
                    })?;
                }
            }
            for &root in roots {
                collector.root(root, None)?;
            }
            for operation in bindings.values() {
                collector.operation(operation)?;
            }
            for body in bodies {
                collector.raw(body)?;
            }
            while let Some(key) = collector.pending.pop() {
                collector.definition(key)?;
            }
            collector.charge(collector.modules.iter().map(|name| name.len() + 1).sum())?;
            Ok::<_, CompileError>(
                collector
                    .modules
                    .into_iter()
                    .map(str::to_owned)
                    .collect::<Vec<_>>(),
            )
        })();
        self.work = work;
        let modules = result?;
        self.charge(
            module,
            span,
            modules
                .iter()
                .map(|name| name.len() + 1)
                .sum::<usize>()
                .saturating_mul(self.source_sets.len() + 1),
        )?;
        if let Some(rows) = self.source_sets.get(&modules) {
            return Ok(Arc::clone(rows));
        }
        self.retain_source_modules(module, span, modules)
    }

    pub(super) fn retain_source_modules(
        &mut self,
        module: &str,
        span: Span,
        modules: Vec<String>,
    ) -> Result<SourceRows, CompileError> {
        use crate::contract::function::{
            MAX_FUNCTION_SOURCE_BYTES, MAX_FUNCTION_SOURCES, MAX_IDENTITY_NAME_BYTES,
        };
        // Preflight the entire requested closure before any original string copy.
        if modules.len() > MAX_FUNCTION_SOURCES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "relevant source closure exceeds its metadata profile (at most 128 source modules)",
            ));
        }
        let mut retained_bytes = 0usize;
        let mut copy_bytes = 0usize;
        for name in &modules {
            self.charge(
                module,
                span,
                name.len().saturating_mul(self.source_rows.len() + 1) + 1,
            )?;
            if name.len() > MAX_IDENTITY_NAME_BYTES {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "function source identity paths exceed their 4096-byte limit",
                ));
            }
            let source =
                self.project.modules.get(name).ok_or_else(|| {
                    self.error(module, span, ErrorCode::InvalidIr,
                "relevant source closure references a module outside the original collection")
                })?;
            retained_bytes = retained_bytes
                .saturating_add(name.len())
                .saturating_add(source.source.len());
            if !self.source_rows.contains_key(name) {
                copy_bytes = copy_bytes
                    .saturating_add(source.source.len())
                    .saturating_add(name.len().saturating_mul(2));
            }
        }
        if retained_bytes > MAX_FUNCTION_SOURCE_BYTES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "relevant source closure exceeds 1 MiB including module names",
            ));
        }
        self.charge(module, span, copy_bytes.saturating_add(modules.len().saturating_mul(4)))
            .map_err(|mut error| {
                error.message.push_str("; retaining complete original bytes of the relevant source closure; each module is copied and charged once across closures"); error
            })?;
        let mut rows = Vec::with_capacity(modules.len());
        for name in &modules {
            let row = if let Some(row) = self.source_rows.get(name) {
                Arc::clone(row)
            } else {
                let row = Arc::new((name.clone(), self.project.modules[name].source.clone()));
                self.source_rows.insert(name.clone(), Arc::clone(&row));
                row
            };
            rows.push(row);
        }
        let rows = Arc::new(rows);
        self.source_sets.insert(modules, Arc::clone(&rows));
        Ok(rows)
    }
}

struct Collector<'a, 'project> {
    compiler: &'a Compiler<'project>,
    module: &'a str,
    span: Span,
    work: &'a mut usize,
    pending: Vec<Key>,
    definitions: BTreeSet<Key>,
    modules: BTreeSet<&'a str>,
    receipts: BTreeSet<usize>,
}
impl<'a> Collector<'a, '_> {
    fn charge(&mut self, amount: usize) -> Result<(), CompileError> {
        self.compiler
            .charge_at(self.work, self.module, self.span, amount)
    }
    fn refusal(&mut self, message: &'static str) -> Result<(), CompileError> {
        self.charge(message.len() + 1)?;
        Err(self
            .compiler
            .error(self.module, self.span, ErrorCode::InvalidIr, message))
    }
    fn root(&mut self, key: Key, origin: Option<&Table>) -> Result<(), CompileError> {
        self.charge(self.compiler.source.lexical.len() + self.definitions.len() + 4)?;
        let Some(table) = self.compiler.source.lexical.get(&key) else {
            return self.refusal("source closure root lacks its original lexical table");
        };
        if !self.compiler.locals().original_table_is(key, table)
            || origin.is_some_and(|origin| !std::ptr::eq(origin, table.as_ref()))
        {
            return self.refusal("source closure root belongs to another original collection");
        }
        if self.definitions.insert(key) {
            self.pending.push(key);
        }
        Ok(())
    }
    fn source(&mut self, name: &'a str, expected: Option<&str>) -> Result<(), CompileError> {
        self.charge(
            name.len()
                .saturating_mul(self.compiler.project.modules.len() + self.modules.len() + 1)
                + 2,
        )?;
        let Some(source) = self.compiler.project.modules.get(name) else {
            return self.refusal("retained dependency source is outside the original collection");
        };
        if let Some(expected) = expected {
            self.charge(expected.len().saturating_add(source.source.len()))?;
            if expected != source.source {
                return self.refusal(
                    "retained dependency source bytes differ from the original collection",
                );
            }
        }
        self.modules.insert(name);
        Ok(())
    }
    fn rows(&mut self, sources: SourceView<'a>) -> Result<(), CompileError> {
        for row in sources.iter() {
            let (name, text) = row;
            self.charge(
                name.len()
                    .saturating_mul(self.compiler.source_rows.len() + 1)
                    + 1,
            )?;
            // Only the same immutable interned allocation avoids a byte comparison.
            // Equal names, lengths or foreign numeric identities never suffice.
            let interned = self
                .compiler
                .source_rows
                .get(name)
                .is_some_and(|original| std::ptr::eq(original.as_ref(), row));
            self.source(name, (!interned).then_some(text.as_str()))?;
        }
        Ok(())
    }
    fn definition(&mut self, key: Key) -> Result<(), CompileError> {
        self.charge(self.compiler.declarations.len() + self.compiler.source.interfaces.len() + 6)?;
        let Some(record) = self.compiler.source.resolution.try_declaration(key) else {
            return self.refusal("source closure has an unknown original definition");
        };
        let original = self
            .compiler
            .project
            .modules
            .get(&record.name.0)
            .and_then(|source| source.ast.decls.get(record.ast_index));
        if !original
            .zip(self.compiler.declarations.get(&key))
            .is_some_and(|(actual, kept)| std::ptr::eq(actual, *kept))
        {
            return self.refusal("source closure definition differs from its original declaration");
        }
        // Static Nat helpers have original lexical tables but no runtime Interface.
        let declaration = original.expect("original declaration matched");
        self.charge(
            record
                .name
                .0
                .len()
                .saturating_mul(2)
                .saturating_add(record.name.1.len())
                .saturating_add(declaration.name.text.len()),
        )?;
        if declaration.name.text != record.name.1 {
            return self.refusal("source closure name differs from its original declaration");
        }
        if declaration.kind != FnKind::Static {
            let Some(interface) = self.compiler.source.interfaces.get(&key) else {
                return self.refusal("source closure definition lacks its original interface");
            };
            if interface.module != record.name.0
                || interface.ast_index != record.ast_index
                || interface.kind != declaration.kind
            {
                return self
                    .refusal("source closure interface differs from its original declaration");
            }
        }
        self.source(&record.name.0, None)?;
        let table = &self.compiler.source.lexical[&key];
        // All original uses count, even inactive branches and zero repetitions.
        // Diagnostic candidates and same-spelled globals never replace locals.
        for usage in table.resolved_uses() {
            self.charge(2)?;
            match usage.target {
                ResolvedUse::Global(Target::Declaration(next)) => {
                    self.charge(usage.name.len().saturating_add(1))?;
                    let resolution = &self.compiler.source.resolution;
                    resolution.visit_name_sources(record.module, &usage.name, |owner| {
                        self.source(resolution.module_name(owner), None)
                    })?;
                    self.root(next, None)?;
                }
                ResolvedUse::Global(Target::Primitive(_)) => {}
                ResolvedUse::Local(id) if table.try_binder(id).is_some() => {}
                _ => {
                    return self
                        .refusal("source closure has an unresolved or foreign original use");
                }
            }
        }
        if let Some(program) = self.compiler.checked.get(&key) {
            self.raw(program.raw())?;
        }
        if let Some(meaning) = self.compiler.meanings.get(&key) {
            self.raw(&meaning.raw)?;
        }
        Ok(())
    }
    fn operation(&mut self, root: &'a operations::Operation) -> Result<(), CompileError> {
        use operations::Node;
        self.charge(1)?;
        let mut pending = vec![root];
        while let Some(operation) = pending.pop() {
            self.charge(4)?;
            match operation.node.as_ref() {
                Node::Provider(receipt) => self.receipt(receipt)?,
                Node::Pure(pure) => {
                    let Some(origin) = &pure.origin else {
                        return self.refusal("pure operation has no original source association");
                    };
                    self.root(origin.definition, Some(&origin.table))?;
                    if let Some(meaning) = origin.meaning {
                        self.root(meaning, None)?;
                    }
                    self.rows(origin.equation.source_view())?;
                    self.raw(pure.leaf.program().raw())?;
                    if let Some(inverse) = &pure.inverse {
                        self.receipt(inverse)?;
                    }
                }
                Node::Requested(meaning, child) => {
                    self.root(*meaning, None)?;
                    pending.push(child);
                }
                Node::Inverse(child) | Node::Controlled(child) | Node::Repeat(_, child) => {
                    pending.push(child)
                }
                Node::Then(left, right)
                | Node::Tensor(left, right)
                | Node::Conjugate(left, right) => pending.extend([left, right]),
            }
        }
        Ok(())
    }
    fn receipt(
        &mut self,
        receipt: &'a Arc<crate::contract::FunctionEvidence>,
    ) -> Result<(), CompileError> {
        self.charge(self.receipts.len() + 2)?;
        if !self.receipts.insert(Arc::as_ptr(receipt) as usize) {
            return Ok(());
        }
        self.rows(receipt.identity_parts().2)?;
        self.raw(receipt.implementation())?;
        self.raw(receipt.specification())
    }
    fn steps(&mut self, steps: &'a [CircuitStep]) -> Result<(), CompileError> {
        for step in steps {
            self.charge(1)?;
            if let CircuitAction::Contract { evidence, .. } = &step.action {
                self.receipt(evidence)?;
            }
        }
        Ok(())
    }
    fn raw(&mut self, raw: &'a RawProgram) -> Result<(), CompileError> {
        self.charge(1)?;
        let mut pending = vec![raw.operations.as_slice()];
        while let Some(operations) = pending.pop() {
            for operation in operations {
                self.charge(3)?;
                match operation {
                    RawOp::ApplyUnitary { steps, .. } => self.steps(steps)?,
                    RawOp::CertifiedCompute {
                        use_steps,
                        logical_steps,
                        ..
                    } => {
                        self.steps(use_steps)?;
                        self.steps(logical_steps)?;
                    }
                    RawOp::ClassicalBranch {
                        then_ops, else_ops, ..
                    } => pending.extend([then_ops.as_slice(), else_ops.as_slice()]),
                    _ => {}
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    fn project(sources: &[(&str, &str)]) -> Project {
        Project {
            edition_context: crate::frontend::project::ProjectEdition::Explicit(
                crate::edition::Edition::E2026,
            ),
            root: PathBuf::from("main.qli"),
            modules: sources
                .iter()
                .map(|(name, text)| {
                    (
                        (*name).into(),
                        SourceModule {
                            name: (*name).into(),
                            path: PathBuf::from(format!("{name}.qli")),
                            source: (*text).into(),
                            ast: crate::frontend::parser::parse_module(text).unwrap(),
                            imports: BTreeMap::new(),
                            origin: ModuleOrigin::Local,
                        },
                    )
                })
                .collect(),
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn original_closure_keeps_nat_meaning_and_inactive_edges_but_not_unused_imports() {
        let project = project(&[
            ("main", "use phase::turn;use dormant::unused;use unrelated::ignored;
              unitary fn original[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0 {turn(q)}else{power(unused,0)(q)}}
              meaning M:Bit=reference(turn);"),
            ("phase", "use numbers::exponent;
              pub unitary fn turn(q:Q<Bit>)->Q<Bit>{phase[1,exponent[0]()](q)}"),
            ("numbers", "pub static fn exponent[const n:Nat]()->Nat{n+1}"),
            ("dormant", "pub unitary fn unused(q:Q<Bit>)->Q<Bit>{q}"),
            ("unrelated", "pub unitary fn ignored(q:Q<Bit>)->Q<Bit>{q}"),
        ]);
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let original = compiler
            .source
            .resolution
            .qualified("main::original")
            .unwrap();
        let meaning = compiler.source.resolution.qualified("main::M").unwrap();
        let rows = compiler
            .retained_sources(
                "main",
                Span::default(),
                &[original, meaning],
                &operations::Bindings::new(),
                &[],
            )
            .unwrap();
        assert_eq!(
            rows.iter().map(|row| row.0.as_str()).collect::<Vec<_>>(),
            ["dormant", "main", "numbers", "phase"]
        );
        for row in rows.iter() {
            assert_eq!(row.1, project.modules[&row.0].source);
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn local_operation_shadow_does_not_retain_its_global_diagnostic_candidate() {
        let project = project(&[
            (
                "main",
                "use unused::op;unitary fn original[const op:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(op){op(q)}",
            ),
            ("unused", "pub unitary fn op(q:Q<Bit>)->Q<Bit>{q}"),
        ]);
        let mut compiler = super::super::snapshot_tests::compiler(&project);
        let key = compiler
            .source
            .resolution
            .qualified("main::original")
            .unwrap();
        let rows = compiler
            .retained_sources(
                "main",
                Span::default(),
                &[key],
                &operations::Bindings::new(),
                &[],
            )
            .unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].0, "main");
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn foreign_equal_shaped_lexical_origin_is_not_a_current_source_root() {
        let first = project(&[("main", "unitary fn original(q:Q<Unit>)->Q<Unit>{q}")]);
        let second = project(&[("main", "unitary fn original(q:Q<Unit>)->Q<Unit>{q}")]);
        let compiler = super::super::snapshot_tests::compiler(&first);
        let foreign = super::super::snapshot_tests::compiler(&second);
        let key = compiler
            .source
            .resolution
            .qualified("main::original")
            .unwrap();
        let mut work = 0;
        let mut collector = Collector {
            compiler: &compiler,
            module: "main",
            span: Span::default(),
            work: &mut work,
            pending: Vec::new(),
            definitions: BTreeSet::new(),
            modules: BTreeSet::new(),
            receipts: BTreeSet::new(),
        };
        let error = collector
            .root(key, Some(&foreign.source.lexical[&key]))
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::InvalidIr);
        assert!(error.message.contains("another original collection"));
        assert!(collector.pending.is_empty());
    }
}
