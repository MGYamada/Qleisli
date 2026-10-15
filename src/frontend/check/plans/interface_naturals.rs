//! Original Nat occurrences in checked declaration interfaces.
//!
//! These plans and their formal-only environment are untrusted source metadata.
//! Signature scopes contain no body aliases or conditional/fold regions. Both
//! logical ports of abbreviated Op/Meaning interfaces retain the same original
//! occurrence; no new source node, capability or accepted evidence is invented.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum InterfaceSlot {
    Parameter(usize),
    Result,
    MeaningInput,
    OperationInput { ordinal: usize, formal: BinderKey },
    OperationOutput { ordinal: usize, formal: BinderKey },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum TypeChild {
    Quantum,
    Tuple(usize),
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct InterfaceNatural {
    pub owner: DefId,
    pub slot: InterfaceSlot,
    pub path: Vec<TypeChild>,
    pub type_node: NodeId,
    pub natural: Arc<ResolvedNatural>,
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct InterfaceNaturals {
    pub environment: Arc<StaticEnvironment>,
    pub roots: Vec<InterfaceNatural>,
}

#[derive(Clone, Copy)]
pub(in crate::frontend) struct InterfaceNaturalContext<'a, 'ast> {
    pub owner: DefId,
    pub declaration: &'ast ast::Decl,
    pub resolution: &'a Resolution,
    pub interfaces: &'a BTreeMap<DefId, Interface>,
    pub indices: &'a BTreeMap<DefId, Index<'ast>>,
    pub helpers: &'a StaticHelpers,
    pub budget: &'a Budget,
}

#[derive(Clone, Copy)]
enum Slot<'a> {
    Parameter(usize),
    Result,
    MeaningInput,
    Input(usize, &'a BinderKey),
    Output(usize, &'a BinderKey),
}

struct Path<'a> {
    parent: Option<&'a Path<'a>>,
    child: TypeChild,
    length: usize,
}

struct Reader<'a, 'ast> {
    context: InterfaceNaturalContext<'a, 'ast>,
    index: &'a Index<'ast>,
    interface: &'a Interface,
}

/// Call during the original program's finish callback, before consuming any
/// Index. Capture is followed by an independent source-order validation pass.
pub(in crate::frontend) fn capture_interface_naturals_budgeted(
    context: InterfaceNaturalContext<'_, '_>,
) -> Result<InterfaceNaturals> {
    context.budget.charge(context.declaration.span, 1)?;
    let index = context.indices.get(&context.owner).ok_or_else(|| {
        SourceError::new(
            "source",
            context.declaration.span,
            "missing original interface index",
        )
    })?;
    context.budget.charge(context.declaration.span, 1)?;
    let interface = context.interfaces.get(&context.owner).ok_or_else(|| {
        SourceError::new(
            "source",
            context.declaration.span,
            "missing original checked interface",
        )
    })?;
    let reader = Reader {
        context,
        index,
        interface,
    };
    reader.header()?;
    let mut count = 0usize;
    reader.types(&mut |_, ty| {
        let roots = reader.preflight_type(ty, 1, &mut 0)?;
        count = count
            .checked_add(roots)
            .ok_or_else(|| reader.failure(ty.span))?;
        Ok(())
    })?;
    // Scope's fresh binding counter and its shared handle precede allocation.
    reader
        .context
        .budget
        .charge(reader.context.declaration.span, 2)?;
    let scope = crate::frontend::check::declarations::scope(
        interface,
        reader.context.helpers,
        reader.context.budget,
        reader.context.declaration.span,
    )?;
    let environment = environment(
        reader.context.owner,
        reader
            .context
            .resolution
            .declaration(reader.context.owner)
            .module,
        &scope,
        &BTreeMap::new(),
        &[],
        reader.context.declaration.span,
        reader.context.budget,
    )?;
    reader
        .context
        .budget
        .charge(reader.context.declaration.span, count.saturating_add(1))?;
    let mut roots = Vec::with_capacity(count);
    reader.types(&mut |slot, ty| reader.capture_type(slot, ty, None, &mut roots))?;
    let retained = InterfaceNaturals { environment, roots };
    reader.validate(&retained)?;
    Ok(retained)
}

impl Reader<'_, '_> {
    fn failure(&self, span: Span) -> SourceError {
        SourceError::new(
            "source",
            span,
            "retained interface natural differs from its original collection",
        )
    }

    fn validation(&self) -> Validation<'_, '_> {
        Validation {
            indices: self.context.indices,
            helpers: self.context.helpers,
            interfaces: self.context.interfaces,
            resolution: self.context.resolution,
            budget: self.context.budget,
        }
    }

    fn header(&self) -> Result<()> {
        let context = &self.context;
        let declaration = context.declaration;
        context.budget.charge(declaration.span, 1)?;
        let original = context
            .resolution
            .try_declaration(context.owner)
            .ok_or_else(|| self.failure(declaration.span))?;
        let module = context.resolution.module_name(original.module);
        context.budget.charge(
            declaration.span,
            original
                .name
                .1
                .len()
                .saturating_add(declaration.name.text.len())
                .saturating_add(module.len())
                .saturating_add(self.interface.module.len())
                .saturating_add(1),
        )?;
        if original.name.1 != declaration.name.text
            || original.kind != declaration.kind
            || original.ast_index != self.interface.ast_index
            || self.interface.kind != declaration.kind
            || self.interface.module != module
            || self.interface.statics.len() != declaration.static_params.len()
            || self.interface.params.len() != declaration.params.len()
            || self.interface.meaning_domain.is_some() != declaration.meaning_domain.is_some()
        {
            return Err(self.failure(declaration.span));
        }
        context
            .budget
            .charge(declaration.span, declaration.static_params.len())?;
        for (parameter, formal) in declaration
            .static_params
            .iter()
            .zip(&self.interface.statics)
        {
            context.budget.charge(parameter.name.span, 1)?;
            let binder = self
                .index
                .try_binder(&parameter.name)
                .ok_or_else(|| self.failure(parameter.name.span))?;
            let info = self
                .index
                .table
                .try_binder(binder)
                .ok_or_else(|| self.failure(parameter.name.span))?;
            context.budget.charge(
                parameter.name.span,
                formal
                    .key
                    .name
                    .len()
                    .saturating_add(info.key.name.len())
                    .saturating_add(1),
            )?;
            let category = match (&parameter.kind, &formal.kind) {
                (ast::StaticParamKind::Natural, StaticKind::Natural) => BindingKind::StaticNatural,
                (ast::StaticParamKind::Basis, StaticKind::Basis) => BindingKind::StaticBasis,
                (ast::StaticParamKind::Operation { .. }, StaticKind::Operation { .. }) => {
                    BindingKind::StaticOperation
                }
                _ => return Err(self.failure(parameter.name.span)),
            };
            if info.key != formal.key
                || info.kind != category
                || binder.definition() != context.owner
            {
                return Err(self.failure(parameter.name.span));
            }
        }
        Ok(())
    }

    // Source declaration order: static ports, parameters, Meaning domain, result.
    fn types(&self, visit: &mut impl FnMut(Slot<'_>, &ast::Type) -> Result<()>) -> Result<()> {
        let declaration = self.context.declaration;
        self.context
            .budget
            .charge(declaration.span, declaration.static_params.len())?;
        for (ordinal, (parameter, formal)) in declaration
            .static_params
            .iter()
            .zip(&self.interface.statics)
            .enumerate()
        {
            if let ast::StaticParamKind::Operation {
                basis, codomain, ..
            } = &parameter.kind
            {
                visit(Slot::Input(ordinal, &formal.key), basis)?;
                visit(
                    Slot::Output(ordinal, &formal.key),
                    codomain.as_deref().unwrap_or(basis),
                )?;
            }
        }
        self.context
            .budget
            .charge(declaration.span, declaration.params.len().saturating_add(2))?;
        for (ordinal, parameter) in declaration.params.iter().enumerate() {
            visit(Slot::Parameter(ordinal), &parameter.ty)?;
        }
        if declaration.kind == FnKind::Meaning {
            visit(
                Slot::MeaningInput,
                declaration
                    .meaning_domain
                    .as_ref()
                    .unwrap_or(&declaration.return_type),
            )?;
        }
        visit(Slot::Result, &declaration.return_type)
    }

    fn original_type(&self, source: &ast::Type) -> Result<NodeId> {
        self.context.budget.charge(source.span, 1)?;
        let node = self
            .index
            .try_node_id_ty(source)
            .ok_or_else(|| self.failure(source.span))?;
        self.context.budget.charge(source.span, 1)?;
        let Some(OriginalNode::Type(original)) = self.index.original_node(node) else {
            return Err(self.failure(source.span));
        };
        if node.definition() != self.context.owner || !std::ptr::eq(source, original) {
            return Err(self.failure(source.span));
        }
        Ok(node)
    }

    fn original_name(&self, name: &ast::Ident) -> Result<ResolvedUse> {
        self.context.budget.charge(name.span, 1)?;
        let site = self
            .index
            .try_usage(name)
            .ok_or_else(|| self.failure(name.span))?;
        self.context.budget.charge(name.span, 1)?;
        let usage = self
            .index
            .table
            .try_usage(site)
            .ok_or_else(|| self.failure(name.span))?;
        if site.definition() != self.context.owner {
            return Err(self.failure(name.span));
        }
        Ok(usage.target)
    }

    fn preflight_natural(&self, source: &ast::Natural, depth: usize) -> Result<()> {
        self.context.budget.charge(source.span, 1)?;
        if depth > 128 {
            return Err(SourceError::new(
                "limit",
                source.span,
                "retained natural plan exceeds depth 128",
            ));
        }
        let node = self
            .index
            .try_node_id_natural(source)
            .ok_or_else(|| self.failure(source.span))?;
        self.context.budget.charge(source.span, 1)?;
        let Some(OriginalNode::Natural(original)) = self.index.original_node(node) else {
            return Err(self.failure(source.span));
        };
        if node.definition() != self.context.owner || !std::ptr::eq(source, original) {
            return Err(self.failure(source.span));
        }
        match &source.kind {
            ast::NatKind::Number(_) => {}
            ast::NatKind::Name(_) => {
                self.context.budget.charge(source.span, 1)?;
                let site = self
                    .index
                    .try_natural_usage(source)
                    .ok_or_else(|| self.failure(source.span))?;
                self.context.budget.charge(source.span, 1)?;
                let usage = self
                    .index
                    .table
                    .try_usage(site)
                    .ok_or_else(|| self.failure(source.span))?;
                let ResolvedUse::Local(id) = usage.target else {
                    return Err(self.failure(source.span));
                };
                self.context.budget.charge(source.span, 1)?;
                if site.definition() != self.context.owner
                    || self
                        .index
                        .table
                        .try_binder(id)
                        .is_none_or(|info| info.kind != BindingKind::StaticNatural)
                {
                    return Err(self.failure(source.span));
                }
            }
            ast::NatKind::Call { callee, arguments } => {
                let ResolvedUse::Global(resolve::Target::Declaration(id)) =
                    self.original_name(callee)?
                else {
                    return Err(self.failure(source.span));
                };
                self.context.budget.charge(source.span, 1)?;
                let helper = self
                    .context
                    .helpers
                    .get(&id)
                    .ok_or_else(|| self.failure(source.span))?;
                if helper.parameters.len() != arguments.len() {
                    return Err(self.failure(source.span));
                }
                self.context.budget.charge(source.span, arguments.len())?;
                for argument in arguments {
                    self.preflight_natural(argument, depth + 1)?;
                }
            }
            ast::NatKind::Add(left, right)
            | ast::NatKind::Sub(left, right)
            | ast::NatKind::Mul(left, right) => {
                self.context.budget.charge(source.span, 2)?;
                self.preflight_natural(left, depth + 1)?;
                self.preflight_natural(right, depth + 1)?;
            }
        }
        Ok(())
    }

    fn preflight_type(&self, source: &ast::Type, depth: usize, nodes: &mut usize) -> Result<usize> {
        self.original_type(source)?;
        if depth > 64 {
            return Err(SourceError::new(
                "limit",
                source.span,
                "type exceeds depth 64",
            ));
        }
        // Same stored-depth/cell convention as check::Budget::ty: Q's owner
        // wrapper is transparent, but its actual visit and path are retained.
        if !matches!(source.kind, ast::TypeKind::Q(_)) {
            *nodes = nodes
                .checked_add(1)
                .ok_or_else(|| self.failure(source.span))?;
            if *nodes > 4096 {
                return Err(SourceError::new(
                    "limit",
                    source.span,
                    "type exceeds 4096 cells",
                ));
            }
        }
        match &source.kind {
            ast::TypeKind::Bits(natural) => {
                self.preflight_natural(natural, 1)?;
                Ok(1)
            }
            ast::TypeKind::Q(child) => {
                self.context.budget.charge(source.span, 1)?;
                self.preflight_type(child, depth, nodes)
            }
            ast::TypeKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(SourceError::new(
                        "limit",
                        source.span,
                        "type tuple exceeds 64 fields",
                    ));
                }
                self.context.budget.charge(source.span, fields.len())?;
                let mut count = 0usize;
                for field in fields {
                    count = count
                        .checked_add(self.preflight_type(field, depth + 1, nodes)?)
                        .ok_or_else(|| self.failure(field.span))?;
                }
                Ok(count)
            }
            ast::TypeKind::Named(name) => {
                let ResolvedUse::Local(id) = self.original_name(name)? else {
                    return Err(self.failure(name.span));
                };
                self.context.budget.charge(name.span, 1)?;
                if self
                    .index
                    .table
                    .try_binder(id)
                    .is_none_or(|info| info.kind != BindingKind::StaticBasis)
                {
                    return Err(self.failure(name.span));
                }
                Ok(0)
            }
            ast::TypeKind::Unit | ast::TypeKind::Bit => Ok(0),
        }
    }

    fn slot(&self, slot: Slot<'_>, span: Span) -> Result<InterfaceSlot> {
        Ok(match slot {
            Slot::Parameter(index) => InterfaceSlot::Parameter(index),
            Slot::Result => InterfaceSlot::Result,
            Slot::MeaningInput => InterfaceSlot::MeaningInput,
            Slot::Input(ordinal, key) => InterfaceSlot::OperationInput {
                ordinal,
                formal: self.context.budget.key(span, key)?,
            },
            Slot::Output(ordinal, key) => InterfaceSlot::OperationOutput {
                ordinal,
                formal: self.context.budget.key(span, key)?,
            },
        })
    }

    fn capture_type(
        &self,
        slot: Slot<'_>,
        source: &ast::Type,
        path: Option<&Path<'_>>,
        roots: &mut Vec<InterfaceNatural>,
    ) -> Result<()> {
        self.context.budget.charge(source.span, 1)?;
        match &source.kind {
            ast::TypeKind::Bits(natural) => {
                self.context.budget.charge(source.span, 1)?;
                if roots.len() >= roots.capacity() {
                    return Err(self.failure(source.span));
                }
                let length = path.map_or(0, |path| path.length);
                // Vector allocation, borrowed traversal/copy and reversal all
                // precede their work. Path links themselves use stack frames.
                self.context
                    .budget
                    .charge(source.span, length.saturating_mul(4).saturating_add(3))?;
                let mut retained_path = Vec::with_capacity(length);
                let mut cursor = path;
                while let Some(link) = cursor {
                    retained_path.push(link.child);
                    cursor = link.parent;
                }
                retained_path.reverse();
                let type_node = self.original_type(source)?;
                let slot = self.slot(slot, source.span)?;
                let capture = Capture {
                    index: self.index,
                    helpers: self.context.helpers,
                    budget: self.context.budget,
                };
                let natural = capture.natural(natural)?;
                self.context.budget.charge(source.span, 1)?;
                roots.push(InterfaceNatural {
                    owner: self.context.owner,
                    slot,
                    path: retained_path,
                    type_node,
                    natural: Arc::new(natural),
                });
            }
            ast::TypeKind::Q(child) => {
                self.context.budget.charge(source.span, 1)?;
                let next = Path {
                    parent: path,
                    child: TypeChild::Quantum,
                    length: path.map_or(1, |path| path.length + 1),
                };
                self.capture_type(slot, child, Some(&next), roots)?;
            }
            ast::TypeKind::Tuple(fields) => {
                self.context.budget.charge(source.span, fields.len())?;
                for (ordinal, field) in fields.iter().enumerate() {
                    self.context.budget.charge(field.span, 1)?;
                    let next = Path {
                        parent: path,
                        child: TypeChild::Tuple(ordinal),
                        length: path.map_or(1, |path| path.length + 1),
                    };
                    self.capture_type(slot, field, Some(&next), roots)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn validate(&self, retained: &InterfaceNaturals) -> Result<()> {
        self.validate_environment(&retained.environment)?;
        let mut roots = retained.roots.iter();
        // Independently enumerate every original slot; this does not reuse the
        // capture's root iterator or count to decide completeness or ordering.
        let declaration = self.context.declaration;
        self.context
            .budget
            .charge(declaration.span, declaration.static_params.len())?;
        for (ordinal, parameter) in declaration.static_params.iter().enumerate() {
            if let ast::StaticParamKind::Operation {
                basis, codomain, ..
            } = &parameter.kind
            {
                let key = &self.interface.statics[ordinal].key;
                self.validate_type(Slot::Input(ordinal, key), basis, None, &mut roots)?;
                self.validate_type(
                    Slot::Output(ordinal, key),
                    codomain.as_deref().unwrap_or(basis),
                    None,
                    &mut roots,
                )?;
            }
        }
        self.context
            .budget
            .charge(declaration.span, declaration.params.len().saturating_add(2))?;
        for (ordinal, parameter) in declaration.params.iter().enumerate() {
            self.validate_type(Slot::Parameter(ordinal), &parameter.ty, None, &mut roots)?;
        }
        if declaration.kind == FnKind::Meaning {
            self.validate_type(
                Slot::MeaningInput,
                declaration
                    .meaning_domain
                    .as_ref()
                    .unwrap_or(&declaration.return_type),
                None,
                &mut roots,
            )?;
        }
        self.validate_type(Slot::Result, &declaration.return_type, None, &mut roots)?;
        self.context.budget.charge(declaration.span, 1)?;
        if roots.next().is_some() {
            return Err(self.failure(declaration.span));
        }
        Ok(())
    }

    fn same_slot(&self, original: Slot<'_>, retained: &InterfaceSlot, span: Span) -> Result<bool> {
        self.context.budget.charge(span, 1)?;
        Ok(match (original, retained) {
            (Slot::Parameter(a), InterfaceSlot::Parameter(b)) => a == *b,
            (Slot::Result, InterfaceSlot::Result)
            | (Slot::MeaningInput, InterfaceSlot::MeaningInput) => true,
            (Slot::Input(a, key), InterfaceSlot::OperationInput { ordinal: b, formal })
            | (Slot::Output(a, key), InterfaceSlot::OperationOutput { ordinal: b, formal }) => {
                self.context.budget.charge(
                    span,
                    key.name
                        .len()
                        .saturating_add(formal.name.len())
                        .saturating_add(1),
                )?;
                a == *b && key == formal
            }
            _ => false,
        })
    }

    fn validate_type(
        &self,
        slot: Slot<'_>,
        source: &ast::Type,
        path: Option<&Path<'_>>,
        roots: &mut std::slice::Iter<'_, InterfaceNatural>,
    ) -> Result<()> {
        let type_node = self.original_type(source)?;
        match &source.kind {
            ast::TypeKind::Bits(natural) => {
                self.context.budget.charge(source.span, 1)?;
                let retained = roots.next().ok_or_else(|| self.failure(source.span))?;
                let length = path.map_or(0, |path| path.length);
                self.context.budget.charge(
                    source.span,
                    retained.path.len().saturating_add(length).saturating_add(1),
                )?;
                if retained.owner != self.context.owner
                    || retained.type_node != type_node
                    || retained.path.len() != length
                    || !self.same_slot(slot, &retained.slot, source.span)?
                {
                    return Err(self.failure(source.span));
                }
                let mut current = path;
                for child in retained.path.iter().rev() {
                    let Some(original) = current else {
                        return Err(self.failure(source.span));
                    };
                    if original.child != *child {
                        return Err(self.failure(source.span));
                    }
                    current = original.parent;
                }
                self.validation()
                    .natural_at(self.context.owner, natural, &retained.natural, 1)?;
            }
            ast::TypeKind::Q(child) => {
                self.context.budget.charge(source.span, 1)?;
                let next = Path {
                    parent: path,
                    child: TypeChild::Quantum,
                    length: path.map_or(1, |path| path.length + 1),
                };
                self.validate_type(slot, child, Some(&next), roots)?;
            }
            ast::TypeKind::Tuple(fields) => {
                self.context.budget.charge(source.span, fields.len())?;
                for (ordinal, field) in fields.iter().enumerate() {
                    self.context.budget.charge(field.span, 1)?;
                    let next = Path {
                        parent: path,
                        child: TypeChild::Tuple(ordinal),
                        length: path.map_or(1, |path| path.length + 1),
                    };
                    self.validate_type(slot, field, Some(&next), roots)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn reserve_lookup<T>(
        &self,
        values: &BTreeMap<BinderKey, T>,
        key: &BinderKey,
        span: Span,
    ) -> Result<()> {
        self.context
            .budget
            .charge(span, values.len().saturating_add(1))?;
        for candidate in values.keys() {
            // Reserve every possible UTF-8 key comparison before BTreeMap::get.
            self.context.budget.charge(
                span,
                candidate
                    .name
                    .len()
                    .saturating_add(key.name.len())
                    .saturating_add(1),
            )?;
        }
        Ok(())
    }

    fn same_linear(&self, left: &Linear, right: &Linear, span: Span) -> Result<bool> {
        self.context.budget.charge(
            span,
            left.terms
                .len()
                .saturating_add(right.terms.len())
                .saturating_add(1),
        )?;
        if left.constant != right.constant || left.terms.len() != right.terms.len() {
            return Ok(false);
        }
        for ((a, x), (b, y)) in left.terms.iter().zip(&right.terms) {
            self.context.budget.charge(
                span,
                a.name.len().saturating_add(b.name.len()).saturating_add(1),
            )?;
            if a != b || x != y {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn same_type(&self, left: &Ty, right: &Ty, span: Span) -> Result<bool> {
        self.context.budget.charge(span, 1)?;
        Ok(match (&left.kind, &right.kind) {
            (Kind::Unit, Kind::Unit) | (Kind::Bit, Kind::Bit) => true,
            (Kind::Bits(a), Kind::Bits(b)) => self.same_linear(a, b, span)?,
            (Kind::Parameter(a), Kind::Parameter(b)) => {
                self.context.budget.charge(
                    span,
                    a.name
                        .len()
                        .saturating_add(b.name.len())
                        .saturating_add(a.key.as_ref().map_or(0, |k| k.name.len()))
                        .saturating_add(b.key.as_ref().map_or(0, |k| k.name.len()))
                        .saturating_add(1),
                )?;
                a.name == b.name && a.key == b.key && a.span == b.span
            }
            (Kind::Q(a), Kind::Q(b)) => self.same_type(a, b, span)?,
            (Kind::Tuple(a), Kind::Tuple(b)) if a.len() == b.len() => {
                self.context.budget.charge(span, a.len())?;
                for (a, b) in a.iter().zip(b) {
                    if !self.same_type(a, b, span)? {
                        return Ok(false);
                    }
                }
                true
            }
            _ => false,
        })
    }

    fn validate_environment(&self, environment: &StaticEnvironment) -> Result<()> {
        let span = self.context.declaration.span;
        let validation = self.validation();
        self.context.budget.charge(span, 1)?;
        if environment.owner != self.context.owner
            || environment.module
                != self
                    .context
                    .resolution
                    .declaration(self.context.owner)
                    .module
            || !environment.local_naturals.is_empty()
            || !environment.regions.is_empty()
            || environment
                .naturals
                .len()
                .saturating_add(environment.bases.len())
                .saturating_add(environment.operations.len())
                != self.interface.statics.len()
        {
            return Err(self.failure(span));
        }
        self.context
            .budget
            .charge(span, self.interface.statics.len())?;
        for formal in &self.interface.statics {
            self.context.budget.charge(span, 1)?;
            match &formal.kind {
                StaticKind::Natural => {
                    if validation.key(self.context.owner, &formal.key, span)?
                        != BindingKind::StaticNatural
                    {
                        return Err(self.failure(span));
                    }
                    self.reserve_lookup(&environment.naturals, &formal.key, span)?;
                    let value = environment
                        .naturals
                        .get(&formal.key)
                        .ok_or_else(|| self.failure(span))?;
                    self.context.budget.charge(span, 1)?;
                    let Some((key, coefficient)) = value.terms.first_key_value() else {
                        return Err(self.failure(span));
                    };
                    self.context.budget.charge(
                        span,
                        key.name
                            .len()
                            .saturating_add(formal.key.name.len())
                            .saturating_add(1),
                    )?;
                    if value.constant != 0
                        || value.terms.len() != 1
                        || key != &formal.key
                        || *coefficient != 1
                    {
                        return Err(self.failure(span));
                    }
                }
                StaticKind::Basis => {
                    if validation.key(self.context.owner, &formal.key, span)?
                        != BindingKind::StaticBasis
                    {
                        return Err(self.failure(span));
                    }
                    self.reserve_lookup(&environment.bases, &formal.key, span)?;
                    let value = environment
                        .bases
                        .get(&formal.key)
                        .ok_or_else(|| self.failure(span))?;
                    let Kind::Parameter(parameter) = &value.kind else {
                        return Err(self.failure(span));
                    };
                    self.context.budget.charge(
                        span,
                        formal
                            .key
                            .name
                            .len()
                            .saturating_mul(2)
                            .saturating_add(parameter.name.len())
                            .saturating_add(parameter.key.as_ref().map_or(0, |key| key.name.len()))
                            .saturating_add(1),
                    )?;
                    if parameter.key.as_ref() != Some(&formal.key)
                        || parameter.name != formal.key.name
                        || parameter.span != span
                    {
                        return Err(self.failure(span));
                    }
                }
                StaticKind::Operation {
                    basis,
                    codomain,
                    meaning,
                    access,
                } => {
                    if validation.key(self.context.owner, &formal.key, span)?
                        != BindingKind::StaticOperation
                    {
                        return Err(self.failure(span));
                    }
                    self.reserve_lookup(&environment.operations, &formal.key, span)?;
                    let value = environment
                        .operations
                        .get(&formal.key)
                        .ok_or_else(|| self.failure(span))?;
                    validation.contract(self.context.owner, value, span)?;
                    if !self.same_type(&value.input, basis, span)?
                        || value.codomain.is_some() != codomain.is_some()
                        || value.meaning != *meaning
                        || value.access != *access
                        || value.effect != formal_effect(codomain, access)
                    {
                        return Err(self.failure(span));
                    }
                    if let (Some(a), Some(b)) = (&value.codomain, codomain) {
                        if !self.same_type(a, b, span)? {
                            return Err(self.failure(span));
                        }
                    }
                }
            }
        }
        let actual = &environment.context.alternatives;
        let expected = &self.interface.premises.alternatives;
        self.context.budget.charge(
            span,
            actual
                .len()
                .saturating_add(expected.len())
                .saturating_add(1),
        )?;
        if actual.len() != expected.len() {
            return Err(self.failure(span));
        }
        for (actual, expected) in actual.iter().zip(expected) {
            self.context.budget.charge(
                span,
                actual
                    .len()
                    .saturating_add(expected.len())
                    .saturating_add(1),
            )?;
            if actual.len() != expected.len() {
                return Err(self.failure(span));
            }
            for (a, b) in actual.iter().zip(expected) {
                if !self.same_linear(a, b, span)? {
                    return Err(self.failure(span));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn study<R>(
        source: &str,
        target: &str,
        test: impl FnOnce(&Reader<'_, '_>, &mut InterfaceNaturals) -> Result<R>,
    ) -> Result<R> {
        let module = crate::frontend::parser::parse_module(source).unwrap();
        crate::frontend::check::program_with(
            BTreeMap::from([("main", &module)]),
            SourceLimits::finite(),
            |resolution, interfaces, helpers, _, _, indices, budget| {
                let owner = resolution.qualified(target).unwrap();
                let record = resolution.declaration(owner);
                let declaration = &module.decls[record.ast_index];
                let context = InterfaceNaturalContext {
                    owner,
                    declaration,
                    resolution,
                    interfaces,
                    indices,
                    helpers,
                    budget,
                };
                let mut retained = capture_interface_naturals_budgeted(context)?;
                let reader = Reader {
                    context,
                    index: &indices[&owner],
                    interface: &interfaces[&owner],
                };
                test(&reader, &mut retained)
            },
        )
        .map(|(_, value)| value)
    }

    #[test]
    fn quantum_and_tuple_paths_preserve_original_size_occurrences() {
        study(
            "unitary fn f[const A:Basis,const n:Nat](q:(Q<Bits<n>>,Q<A>))->(Q<Bits<n>>,Q<A>){q}",
            "main::f",
            |reader, retained| {
                assert_eq!(retained.roots.len(), 2);
                assert_eq!(retained.roots[0].slot, InterfaceSlot::Parameter(0));
                assert_eq!(retained.roots[1].slot, InterfaceSlot::Result);
                for root in &retained.roots {
                    assert_eq!(root.path, vec![TypeChild::Tuple(0), TypeChild::Quantum]);
                    assert_eq!(root.owner, reader.context.owner);
                    assert_eq!(root.type_node.definition(), root.owner);
                    assert_eq!(root.natural.node.definition(), root.owner);
                    assert!(matches!(root.natural.kind, ResolvedNaturalKind::Name(_)));
                }
                assert_ne!(retained.roots[0].type_node, retained.roots[1].type_node);
                assert_ne!(
                    retained.roots[0].natural.node,
                    retained.roots[1].natural.node
                );
                assert_eq!(retained.environment.naturals.len(), 1);
                assert_eq!(retained.environment.bases.len(), 1);
                assert!(retained.environment.local_naturals.is_empty());
                assert!(retained.environment.regions.is_empty());
                Ok(())
            },
        )
        .unwrap();
    }

    #[test]
    fn explicit_op_ports_keep_distinct_original_trees_after_normalized_equality() {
        study(
            "static fn next[const n:Nat]()->Nat{n+1}
             unitary fn f[const n:Nat,const U:Op<Bits<next[n]()> -> Bits<n+1>>](q:Q<Bits<n+1>>)->Q<Bits<n+1>> requires Applicable(U){U(q)}",
            "main::f",
            |reader, retained| {
                assert_eq!(retained.roots.len(), 4);
                let input = &retained.roots[0];
                let output = &retained.roots[1];
                assert!(matches!(input.slot, InterfaceSlot::OperationInput { ordinal: 1, .. }));
                assert!(matches!(output.slot, InterfaceSlot::OperationOutput { ordinal: 1, .. }));
                assert!(input.path.is_empty());
                assert!(output.path.is_empty());
                assert_ne!(input.type_node, output.type_node);
                let ResolvedNaturalKind::Helper { callee, template, arguments } = &input.natural.kind else { panic!("original helper"); };
                let ResolvedUse::Global(resolve::Target::Declaration(id)) = callee.target else { panic!("global helper"); };
                assert!(Arc::ptr_eq(template, &reader.context.helpers[&id]));
                assert_eq!(arguments.len(), 1);
                assert!(matches!(output.natural.kind, ResolvedNaturalKind::Add(..)));
                Ok(())
            },
        ).unwrap();
    }

    #[test]
    fn abbreviated_op_retains_both_logical_ports_of_one_source_occurrence() {
        study(
            "unitary fn f[const n:Nat,const U:Op<Bits<n>>](q:Q<Bits<n>>)->Q<Bits<n>> requires Applicable(U){U(q)}",
            "main::f",
            |_, retained| {
                assert_eq!(retained.roots.len(), 4);
                let input = &retained.roots[0];
                let output = &retained.roots[1];
                assert!(matches!(input.slot, InterfaceSlot::OperationInput { .. }));
                assert!(matches!(output.slot, InterfaceSlot::OperationOutput { .. }));
                assert_eq!(input.type_node, output.type_node);
                assert_eq!(input.natural.node, output.natural.node);
                Ok(())
            },
        ).unwrap();
    }

    #[test]
    fn meaning_domains_keep_explicit_and_abbreviated_original_slots() {
        for (source, same_occurrence) in [
            (
                "unitary fn id(q:Q<Bits<0>>)->Q<Bits<0>>{q} meaning M:Bits<0> = reference(id);",
                true,
            ),
            (
                "unitary fn id(q:Q<Bits<0>>)->Q<Bits<0>>{q} meaning M:Bits<0> -> Bits<0> = reference(id);",
                false,
            ),
        ] {
            study(source, "main::M", |_, retained| {
                assert_eq!(retained.roots.len(), 2);
                assert_eq!(retained.roots[0].slot, InterfaceSlot::MeaningInput);
                assert_eq!(retained.roots[1].slot, InterfaceSlot::Result);
                assert_eq!(
                    retained.roots[0].natural.node == retained.roots[1].natural.node,
                    same_occurrence
                );
                Ok(())
            })
            .unwrap();
        }
    }

    #[test]
    fn validator_rejects_omission_duplicates_reordering_wrong_paths_and_foreign_nodes() {
        study(
            "unitary fn f[const n:Nat](q:Q<(Bits<n>,Bits<n>)>)->Q<(Bits<n>,Bits<n>)>{q}",
            "main::f",
            |reader, retained| {
                assert_eq!(retained.roots.len(), 4);
                for mutation in 0..6 {
                    let mut wrong = retained.clone();
                    match mutation {
                        0 => {
                            wrong.roots.pop();
                        }
                        1 => wrong.roots.push(wrong.roots[0].clone()),
                        2 => wrong.roots.swap(0, 1),
                        3 => wrong.roots[0].path[1] = TypeChild::Tuple(1),
                        4 => wrong.roots[0].type_node = wrong.roots[1].type_node,
                        _ => wrong.roots[0].natural = Arc::clone(&wrong.roots[1].natural),
                    }
                    assert_eq!(
                        reader.validate(&wrong).unwrap_err().code,
                        "source",
                        "mutation {mutation}"
                    );
                }
                Ok(())
            },
        )
        .unwrap();
    }

    #[test]
    fn validator_rejects_forged_nat_payload_and_equal_but_unbound_helper_template() {
        study(
            "static fn size[const n:Nat]()->Nat{n+1}
             unitary fn f[const n:Nat](q:Q<Bits<size[n]()>>)->Q<Bits<size[n]()>>{q}",
            "main::f",
            |reader, retained| {
                let mut wrong = retained.clone();
                let natural = Arc::make_mut(&mut wrong.roots[0].natural);
                natural.kind = ResolvedNaturalKind::Number(1);
                assert_eq!(reader.validate(&wrong).unwrap_err().code, "source");
                let mut wrong = retained.clone();
                let natural = Arc::make_mut(&mut wrong.roots[0].natural);
                let ResolvedNaturalKind::Helper { template, .. } = &mut natural.kind else {
                    panic!("helper");
                };
                *template = Arc::new(StaticHelper {
                    parameters: template.parameters.clone(),
                    result: template.result.clone(),
                    requirements: template.requirements.clone(),
                });
                assert_eq!(reader.validate(&wrong).unwrap_err().code, "source");
                Ok(())
            },
        )
        .unwrap();
    }

    #[test]
    fn signature_environment_preserves_premises_categories_and_access_without_body_aliases() {
        study(
            "unitary fn f[const A:Basis,const n:Nat,const U:Op<Bits<n>>](q:Q<Bits<n>>)->Q<Bits<n>> requires n>=1,Applicable(U){static let k=n;U(q)}",
            "main::f",
            |reader, retained| {
                assert_eq!(retained.environment.operations.len(), 1);
                for mutation in 0..3 {
                    let mut wrong = retained.clone();
                    let environment = Arc::make_mut(&mut wrong.environment);
                    match mutation {
                        0 => environment.context.alternatives[0][0].constant += 1,
                        1 => environment.operations.values_mut().next().unwrap().access[2] = true,
                        _ => {
                            let key = environment.naturals.keys().next().unwrap().clone();
                            environment.local_naturals.insert(key, NaturalBindingPlan::Initializer(Arc::clone(&wrong.roots[0].natural)));
                        }
                    }
                    assert_eq!(reader.validate(&wrong).unwrap_err().code, "source", "mutation {mutation}");
                }
                Ok(())
            },
        ).unwrap();
    }

    #[test]
    fn foreign_equal_declaration_is_refused_before_infallible_capture_lookup() {
        study(
            "unitary fn f[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}",
            "main::f",
            |reader, _| {
                let declaration = reader.context.declaration.clone();
                let context = InterfaceNaturalContext {
                    declaration: &declaration,
                    ..reader.context
                };
                assert_eq!(
                    capture_interface_naturals_budgeted(context)
                        .unwrap_err()
                        .code,
                    "source"
                );
                Ok(())
            },
        )
        .unwrap();
    }
}
