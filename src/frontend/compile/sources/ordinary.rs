//! Original type-path rows for an ordinary root's untrusted proposal.
//! Native resolution separately checks which retained rows justify the type.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

impl Compiler<'_> {
    pub(in crate::frontend::compile) fn retained_ordinary_type_sources(
        &mut self,
        key: Key,
        module: &str,
        span: Span,
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
                types: BTreeSet::new(),
                modules: BTreeSet::new(),
                receipts: BTreeSet::new(),
            };
            collector.ordinary_signature(key)?;
            while let Some(dependency) = collector.pending.pop() {
                match dependency {
                    Dependency::Type(key) => collector.nominal(key, false)?,
                    Dependency::Function(_) => {
                        collector.refusal("ordinary type closure reached a function body")?;
                    }
                }
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
        self.retain_source_modules(module, span, result?)
    }
}

impl Collector<'_, '_> {
    fn ordinary_signature(&mut self, key: Key) -> Result<(), CompileError> {
        self.charge(
            self.compiler.source.lexical.len()
                + self.compiler.declarations.len()
                + self.compiler.source.interfaces.len()
                + 6,
        )?;
        let Some(table) = self.compiler.source.lexical.get(&key) else {
            return self.refusal("ordinary type closure lacks its original lexical table");
        };
        if !self.compiler.locals().original_table_is(key, table) {
            return self.refusal("ordinary type closure belongs to another original collection");
        }
        let Some(record) = self.compiler.source.resolution.try_declaration(key) else {
            return self.refusal("ordinary type closure has an unknown definition");
        };
        let original = self
            .compiler
            .originals
            .module(&record.name.0)
            .and_then(|source| source.ast.decls.get(record.ast_index));
        if !original
            .zip(self.compiler.declarations.get(&key))
            .is_some_and(|(actual, kept)| std::ptr::eq(actual, *kept))
        {
            return self.refusal("ordinary type closure differs from its original declaration");
        }
        let declaration = original.expect("original declaration matched");
        let Some(interface) = self.compiler.source.interfaces.get(&key) else {
            return self.refusal("ordinary type closure lacks its original interface");
        };
        self.charge(record.name.0.len() + record.name.1.len() + declaration.name.text.len())?;
        if declaration.name.text != record.name.1
            || interface.module != record.name.0
            || interface.ast_index != record.ast_index
            || interface.kind != declaration.kind
            || !declaration.static_params.is_empty()
        {
            return self.refusal("ordinary type closure has a different or open interface");
        }
        self.source(&record.name.0, None)?;
        for parameter in &declaration.params {
            self.signature_type(key, record.module, &parameter.ty)?;
        }
        self.signature_type(key, record.module, &declaration.return_type)
    }

    fn signature_type(
        &mut self,
        definition: Key,
        module: crate::frontend::resolve::ModuleId,
        original: &crate::frontend::ast::Type,
    ) -> Result<(), CompileError> {
        self.charge(1)?;
        let mut pending = vec![original];
        while let Some(ty) = pending.pop() {
            self.charge(2)?;
            match &ty.kind {
                TypeKind::Unit | TypeKind::Bit | TypeKind::Bits(_) => {}
                TypeKind::Q(inner) => pending.push(inner),
                TypeKind::Tuple(fields) => {
                    self.charge(fields.len())?;
                    pending.extend(fields);
                }
                TypeKind::Named(name) => {
                    self.charge(name.text.len() + self.compiler.source.lexical.len() + 3)?;
                    let locals = self.compiler.locals();
                    if locals
                        .try_reference_site(name)
                        .is_none_or(|site| site.definition() != definition)
                    {
                        return self.refusal("ordinary type name lacks its original occurrence");
                    }
                    let ResolvedUse::Global(Target::Type(key)) = locals.usage(name).target else {
                        return self.refusal("ordinary type name is not a finite declaration");
                    };
                    let resolution = &self.compiler.source.resolution;
                    if resolution.lookup_visible(module, &name.text) != Ok(Some(Target::Type(key)))
                    {
                        return self.refusal("ordinary type name changed its original resolution");
                    }
                    resolution.visit_name_sources(module, &name.text, |owner| {
                        self.source(resolution.module_name(owner), None)
                    })?;
                    self.type_root(key)?;
                }
            }
        }
        Ok(())
    }
}
