//! Untrusted concrete, source-order ownership proposal. No verified IR is made.
use super::ast::{self, *};
use super::primitive::{Primitive, Size, TypeShape};
use super::{Error, Instantiation, ParsedProgram, Result, Span};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CALLS: usize = 1_024;
const MAX_FOLDS: usize = 1_024;
const MAX_DEPTH: usize = 16;
const MAX_STEPS: usize = 10_000;
const MAX_CELLS: usize = 100_000;

use crate::frontend::types::Kind as TypeKind;

/// Concrete exact source tree. Accessors retain the current sized profile's
/// public tags: bit/bits denote quantum owners, cbit/cbits ordinary data.
/// Its private shared representation makes Q explicit; no constructor is public.
pub type SourceType = crate::frontend::types::Type<u32>;
impl SourceType {
    fn value_cells(&self) -> usize {
        self.cells() + 1 + self.fields().iter().map(Self::value_cells).sum::<usize>()
    }
    pub fn kind(&self) -> &'static str {
        match &self.kind {
            TypeKind::Q(basis) => match basis.kind {
                TypeKind::Bit => "bit",
                TypeKind::Bits(_) => "bits",
                _ => unreachable!("sized quantum profile has only Bit/Bits owners"),
            },
            TypeKind::Bit => "cbit",
            TypeKind::Bits(_) => "cbits",
            TypeKind::Tuple(_) => "tuple",
            TypeKind::Unit => unreachable!("sized Unit is not admitted by the profile"),
        }
    }
    pub fn width(&self) -> Option<u32> {
        match &self.kind {
            TypeKind::Bit => Some(1),
            TypeKind::Bits(n) => Some(*n),
            TypeKind::Q(basis) => match basis.kind {
                TypeKind::Bit => Some(1),
                TypeKind::Bits(n) => Some(n),
                _ => unreachable!("sized quantum profile has only Bit/Bits owners"),
            },
            TypeKind::Tuple(_) => None,
            TypeKind::Unit => unreachable!("sized Unit is not admitted by the profile"),
        }
    }
    pub fn fields(&self) -> &[SourceType] {
        self.tuple_fields().unwrap_or(&[])
    }
    pub fn is_quantum(&self) -> bool {
        self.is_quantum_owner()
    }
    fn quantum_width(&self) -> usize {
        if self.is_quantum() {
            self.width().unwrap() as usize
        } else {
            self.fields().iter().map(Self::quantum_width).sum()
        }
    }
    fn cells(&self) -> usize {
        self.owner_shape_size().nodes
    }
}
fn bit() -> SourceType {
    SourceType::quantum(SourceType::bit())
}
fn tuple(fields: Vec<SourceType>) -> SourceType {
    SourceType::tuple(fields)
}

/// Quantum owner or copyable classical value in one definition's local namespace.
/// Tuples retain ordered fields and do not introduce a further owner identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceValue {
    ty: SourceType,
    identity: Option<u32>,
    fields: Vec<SourceValue>,
}
impl SourceValue {
    fn cells(&self) -> usize {
        self.ty.cells() + 1 + self.fields.iter().map(Self::cells).sum::<usize>()
    }
    pub fn ty(&self) -> &SourceType {
        &self.ty
    }
    pub fn identity(&self) -> Option<u32> {
        self.identity
    }
    pub fn fields(&self) -> &[SourceValue] {
        &self.fields
    }
    fn tuple(fields: Vec<Self>) -> Self {
        Self {
            ty: tuple(fields.iter().map(|v| v.ty.clone()).collect()),
            identity: None,
            fields,
        }
    }
}

/// A shared transparent provider, optionally wrapped in retained repetitions.
#[derive(Clone, Debug)]
pub struct SourceOperation {
    kind: OperationKind,
    module: String,
    span: Span,
    repetitions: u32,
}
#[derive(Clone, Debug)]
enum OperationKind {
    Definition(usize),
    Repeat(u32, Box<SourceOperation>),
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum OperationKey {
    Definition(usize),
    Repeat(u32, Box<OperationKey>),
}
impl SourceOperation {
    pub fn definition(&self) -> Option<usize> {
        match self.kind {
            OperationKind::Definition(id) => Some(id),
            _ => None,
        }
    }
    pub fn repeat_count(&self) -> Option<u32> {
        match self.kind {
            OperationKind::Repeat(n, _) => Some(n),
            _ => None,
        }
    }
    pub fn child(&self) -> Option<&Self> {
        match &self.kind {
            OperationKind::Repeat(_, child) => Some(child),
            _ => None,
        }
    }
    pub fn module(&self) -> &str {
        &self.module
    }
    pub fn span(&self) -> Span {
        self.span
    }
    fn target(&self) -> usize {
        match &self.kind {
            OperationKind::Definition(id) => *id,
            OperationKind::Repeat(_, child) => child.target(),
        }
    }
    fn key(&self) -> OperationKey {
        match &self.kind {
            OperationKind::Definition(id) => OperationKey::Definition(*id),
            OperationKind::Repeat(n, child) => OperationKey::Repeat(*n, Box::new(child.key())),
        }
    }
}

/// One ordered source operation. Names are exact primitive identities or step
/// categories; call/provider references always select retained actual definitions.
#[derive(Clone, Debug)]
pub struct SourceStep {
    module: String,
    span: Span,
    kind: StepKind,
    inputs: Vec<SourceValue>,
    output: SourceValue,
    effect: Effect,
}
#[derive(Clone, Debug)]
enum StepKind {
    Primitive(Primitive, Vec<u32>),
    Call {
        definition: usize,
        operations: BTreeMap<String, SourceOperation>,
    },
    Apply(SourceOperation),
    Adjoint(SourceOperation),
    Controlled(SourceOperation),
}
impl SourceStep {
    pub fn kind(&self) -> &'static str {
        match self.kind {
            StepKind::Primitive(..) => "primitive",
            StepKind::Call { .. } => "call",
            StepKind::Apply(_) => "apply",
            StepKind::Adjoint(_) => "adjoint",
            StepKind::Controlled(_) => "controlled",
        }
    }
    pub fn primitive(&self) -> Option<&str> {
        match &self.kind {
            StepKind::Primitive(name, _) => Some(name.signature().path),
            _ => None,
        }
    }
    pub(super) fn primitive_kind(&self) -> Option<Primitive> {
        match self.kind {
            StepKind::Primitive(name, _) => Some(name),
            _ => None,
        }
    }
    pub fn natural_arguments(&self) -> &[u32] {
        match &self.kind {
            StepKind::Primitive(_, ns) => ns,
            _ => &[],
        }
    }
    pub fn called_definition(&self) -> Option<usize> {
        match self.kind {
            StepKind::Call { definition, .. } => Some(definition),
            _ => None,
        }
    }
    pub fn operation(&self) -> Option<&SourceOperation> {
        match &self.kind {
            StepKind::Apply(op) | StepKind::Adjoint(op) | StepKind::Controlled(op) => Some(op),
            _ => None,
        }
    }
    pub fn operation_bindings(&self) -> Option<&BTreeMap<String, SourceOperation>> {
        match &self.kind {
            StepKind::Call { operations, .. } => Some(operations),
            _ => None,
        }
    }
    pub fn inputs(&self) -> &[SourceValue] {
        &self.inputs
    }
    pub fn output(&self) -> &SourceValue {
        &self.output
    }
    pub fn module(&self) -> &str {
        &self.module
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn effect(&self) -> &'static str {
        effect_name(self.effect)
    }
}

/// One specialized source function, with a sequential body and local identities.
#[derive(Clone, Debug)]
pub struct SourceDefinition {
    path: String,
    naturals: BTreeMap<String, u32>,
    operations: BTreeMap<String, SourceOperation>,
    inputs: Vec<SourceValue>,
    output: SourceValue,
    steps: Vec<SourceStep>,
    effect: Effect,
    span: Span,
    peak_quantum: usize,
}
impl SourceDefinition {
    pub fn path(&self) -> &str {
        &self.path
    }
    pub fn naturals(&self) -> &BTreeMap<String, u32> {
        &self.naturals
    }
    pub fn operations(&self) -> &BTreeMap<String, SourceOperation> {
        &self.operations
    }
    pub fn inputs(&self) -> &[SourceValue] {
        &self.inputs
    }
    pub fn output(&self) -> &SourceValue {
        &self.output
    }
    pub fn steps(&self) -> &[SourceStep] {
        &self.steps
    }
    pub fn effect(&self) -> &'static str {
        effect_name(self.effect)
    }
    pub fn span(&self) -> Span {
        self.span
    }
    /// Diagnostic peak for this bounded source-order proposal, not a proved
    /// runtime/resource-safety certificate.
    pub fn peak_quantum_width(&self) -> usize {
        self.peak_quantum
    }
}

/// Opaque concrete source proposal. Neither this type nor its inspection views
/// authorizes execution or claims a source-preservation theorem.
#[derive(Clone, Debug)]
pub struct ElaboratedProgram {
    instance: Instantiation,
    definitions: Vec<SourceDefinition>,
    root: usize,
    calls: usize,
    folds: usize,
}
impl ElaboratedProgram {
    /// Preflight the root signature and declared effect against the selected
    /// hierarchical transport profile. Generic source checking is separate;
    /// `lower` performs body and operation-specific capability checks before
    /// generating a proposal. This preflight issues no acceptance evidence.
    pub fn check_lowering_profile(&self) -> Result<()> {
        super::lower::check_profile(self)
    }
    /// Check the root profile, body and operation capabilities, then produce
    /// bounded untrusted hierarchical transport. This performs no native
    /// acceptance and retains this source-order program for preservation checks.
    pub fn lower(&self) -> Result<super::HierarchyProposal> {
        super::lower::lower(self)
    }
    pub fn instantiation(&self) -> &Instantiation {
        &self.instance
    }
    pub fn definitions(&self) -> &[SourceDefinition] {
        &self.definitions
    }
    pub fn root(&self) -> usize {
        self.root
    }
    pub fn call_instances(&self) -> usize {
        self.calls
    }
    pub fn fold_iterations(&self) -> usize {
        self.folds
    }
}
fn effect_name(effect: Effect) -> &'static str {
    match effect {
        Effect::Unitary => "unitary",
        Effect::Iso => "iso",
        Effect::Observe => "observe",
    }
}
fn error(code: &'static str, span: Span, message: impl Into<String>) -> Error {
    Error::new(code, span, message)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Key {
    path: String,
    naturals: BTreeMap<String, u32>,
    operations: BTreeMap<String, OperationKey>,
}
struct Builder<'a> {
    program: &'a ParsedProgram,
    definitions: Vec<SourceDefinition>,
    cache: BTreeMap<Key, usize>,
    active: BTreeSet<Key>,
    calls: usize,
    folds: usize,
    steps: usize,
    cells: usize,
    active_frames: usize,
}
#[derive(Clone)]
struct Binding {
    identity: usize,
    value: SourceValue,
}
#[derive(Clone)]
struct Scope {
    naturals: BTreeMap<String, u32>,
    operations: BTreeMap<String, SourceOperation>,
    values: BTreeMap<String, Binding>,
    shadows: BTreeSet<String>,
    moved: BTreeSet<usize>,
}
struct Frame {
    module: String,
    imports: BTreeMap<String, String>,
    effect: Effect,
    steps: Vec<SourceStep>,
    next_value: u32,
    next_binding: usize,
    live_quantum: BTreeMap<u32, usize>,
    peak: usize,
}

pub(super) fn elaborate(instance: &Instantiation) -> Result<ElaboratedProgram> {
    let mut builder = Builder {
        program: &instance.program,
        definitions: Vec::new(),
        cache: BTreeMap::new(),
        active: BTreeSet::new(),
        calls: 0,
        folds: 0,
        steps: 0,
        cells: 0,
        active_frames: 0,
    };
    let mut operations = BTreeMap::new();
    // Eager validation prevents an unused entry operation from concealing an
    // invalid concrete source body, even if no executable step invokes it.
    for (name, binding) in &instance.operations {
        let id = builder.function(
            &binding.definition,
            binding.naturals.clone(),
            BTreeMap::new(),
            0,
        )?;
        builder.provider_type(id, Span::default())?;
        operations.insert(
            name.clone(),
            SourceOperation {
                kind: OperationKind::Definition(id),
                module: instance.entry.rsplit_once("::").unwrap().0.into(),
                span: Span::default(),
                repetitions: 1,
            },
        );
    }
    let root = builder.function(&instance.entry, instance.naturals.clone(), operations, 0)?;
    Ok(ElaboratedProgram {
        instance: instance.clone(),
        definitions: builder.definitions,
        root,
        calls: builder.calls,
        folds: builder.folds,
    })
}

fn natural(n: &Natural, values: &BTreeMap<String, u32>) -> Result<u32> {
    let fail = || {
        error(
            "limit",
            n.span,
            "concrete natural arithmetic exceeds u32 or has negative subtraction",
        )
    };
    match &n.kind {
        NatKind::Number(n) => u32::try_from(*n).map_err(|_| fail()),
        NatKind::Name(name) => values
            .get(name)
            .copied()
            .ok_or_else(|| error("static", n.span, format!("missing concrete natural {name}"))),
        NatKind::Add(a, b) => natural(a, values)?
            .checked_add(natural(b, values)?)
            .ok_or_else(fail),
        NatKind::Sub(a, b) => natural(a, values)?
            .checked_sub(natural(b, values)?)
            .ok_or_else(fail),
        NatKind::Mul(a, b) => natural(a, values)?
            .checked_mul(natural(b, values)?)
            .ok_or_else(fail),
    }
}
fn predicate(p: &Predicate, values: &BTreeMap<String, u32>) -> Result<bool> {
    let a = natural(&p.left, values)?;
    let b = natural(&p.right, values)?;
    Ok(match p.comparison {
        Compare::Eq => a == b,
        Compare::Ne => a != b,
        Compare::Lt => a < b,
        Compare::Le => a <= b,
        Compare::Gt => a > b,
        Compare::Ge => a >= b,
    })
}
fn concrete_type(t: &ast::Type, values: &BTreeMap<String, u32>, span: Span) -> Result<SourceType> {
    let ty = SourceType {
        kind: match t {
            ast::Type::Quantum(Basis::Bit) => TypeKind::Q(Box::new(SourceType::bit())),
            ast::Type::Quantum(Basis::Bits(n)) => {
                TypeKind::Q(Box::new(SourceType::bits(natural(n, values)?)))
            }
            ast::Type::CBit => TypeKind::Bit,
            ast::Type::CBits(n) => TypeKind::Bits(natural(n, values)?),
            ast::Type::Tuple(fields) => TypeKind::Tuple(
                fields
                    .iter()
                    .map(|t| concrete_type(t, values, span))
                    .collect::<Result<_>>()?,
            ),
        },
    };
    if ty.width().is_some_and(|n| n > 8) {
        return Err(error(
            "limit",
            span,
            "concrete register/classical sequence exceeds eight bits",
        ));
    }
    Ok(ty)
}
fn expected(value: &SourceValue, ty: &SourceType, span: Span) -> Result<()> {
    if &value.ty == ty {
        Ok(())
    } else {
        Err(error(
            "type",
            span,
            "concrete type/size or tuple shape mismatch",
        ))
    }
}

impl Builder<'_> {
    fn enter(&mut self, span: Span) -> Result<()> {
        if self.active_frames >= 64 {
            return Err(error(
                "limit",
                span,
                "combined concrete traversal depth exceeds 64",
            ));
        }
        self.active_frames += 1;
        Ok(())
    }
    fn charge_cells(&mut self, n: usize, span: Span) -> Result<()> {
        self.cells = self
            .cells
            .checked_add(n)
            .ok_or_else(|| error("limit", span, "source value accounting overflow"))?;
        if self.cells > MAX_CELLS {
            return Err(error(
                "limit",
                span,
                "source proposal exceeds 100000 retained value cells",
            ));
        }
        Ok(())
    }
    fn declaration(&self, path: &str) -> Result<(String, Function)> {
        let (module, name) = path
            .rsplit_once("::")
            .ok_or_else(|| error("module", Span::default(), "invalid concrete function path"))?;
        let parsed =
            self.program.modules.get(module).ok_or_else(|| {
                error("module", Span::default(), "missing concrete source module")
            })?;
        if parsed.function.name != name {
            return Err(error("name", Span::default(), "missing concrete function"));
        }
        Ok((module.into(), parsed.function.clone()))
    }
    fn function(
        &mut self,
        path: &str,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, SourceOperation>,
        depth: usize,
    ) -> Result<usize> {
        self.enter(Span::default())?;
        let result = self.function_inner(path, naturals, operations, depth);
        self.active_frames -= 1;
        result
    }
    fn function_inner(
        &mut self,
        path: &str,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, SourceOperation>,
        depth: usize,
    ) -> Result<usize> {
        self.calls = self
            .calls
            .checked_add(1)
            .ok_or_else(|| error("limit", Span::default(), "call accounting overflow"))?;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(error(
                "limit",
                Span::default(),
                "concrete source exceeds 1024 calls or depth 16",
            ));
        }
        let key = Key {
            path: path.into(),
            naturals: naturals.clone(),
            operations: operations
                .iter()
                .map(|(name, op)| (name.clone(), op.key()))
                .collect(),
        };
        if let Some(id) = self.cache.get(&key) {
            return Ok(*id);
        }
        if !self.active.insert(key.clone()) {
            return Err(error(
                "cycle",
                Span::default(),
                "concrete source recursion does not decrease",
            ));
        }
        let (module, function) = self.declaration(path)?;
        let result = (|| {
            let expected_naturals: BTreeSet<_> = function
                .parameters
                .iter()
                .filter_map(|p| {
                    if let Parameter::Natural(n) = p {
                        Some(n)
                    } else {
                        None
                    }
                })
                .collect();
            let expected_operations: BTreeSet<_> = function
                .parameters
                .iter()
                .filter_map(|p| {
                    if let Parameter::Operation(n, _) = p {
                        Some(n)
                    } else {
                        None
                    }
                })
                .collect();
            if naturals.keys().collect::<BTreeSet<_>>() != expected_naturals
                || operations.keys().collect::<BTreeSet<_>>() != expected_operations
            {
                return Err(error(
                    "static",
                    function.span,
                    "concrete bindings do not match declaration",
                ));
            }
            for requirement in &function.requires {
                if let Requirement::Predicate(p) = requirement {
                    if !predicate(p, &naturals)? {
                        return Err(error(
                            "size",
                            p.left.span,
                            "concrete function premise is false",
                        ));
                    }
                }
            }
            for p in &function.parameters {
                if let Parameter::Operation(name, basis) = p {
                    let target_type =
                        self.provider_type(operations[name].target(), function.span)?;
                    let required = concrete_type(
                        &ast::Type::Quantum(basis.clone()),
                        &naturals,
                        function.span,
                    )?;
                    if target_type != required {
                        return Err(error(
                            "type",
                            function.span,
                            "concrete provider width/type mismatch",
                        ));
                    }
                }
            }
            let mut imports: BTreeMap<_, _> = self.program.modules[&module]
                .imports
                .iter()
                .map(|(path, _)| (path.rsplit("::").next().unwrap().into(), path.clone()))
                .collect();
            imports.insert(function.name.clone(), path.into());
            let mut frame = Frame {
                module: module.clone(),
                imports,
                effect: function.effect,
                steps: Vec::new(),
                next_value: 0,
                next_binding: 0,
                live_quantum: BTreeMap::new(),
                peak: 0,
            };
            let mut scope = Scope {
                naturals: naturals.clone(),
                operations: operations.clone(),
                values: BTreeMap::new(),
                shadows: BTreeSet::new(),
                moved: BTreeSet::new(),
            };
            let mut inputs = Vec::new();
            for (name, ty, span) in &function.arguments {
                let value = frame.fresh(&concrete_type(ty, &naturals, *span)?, *span)?;
                bind_name(name, value.clone(), *span, &mut scope, &mut frame)?;
                inputs.push(value);
            }
            self.charge_cells(inputs.iter().map(SourceValue::cells).sum(), function.span)?;
            let output = self.block(&function.body, &mut scope, &mut frame, depth)?;
            expected(
                &output,
                &concrete_type(&function.result, &naturals, function.span)?,
                function.body.span,
            )?;
            if scope.values.values().any(|b| b.value.ty.linear()) {
                return Err(error(
                    "ownership",
                    function.body.span,
                    "concrete function leaves live quantum bindings",
                ));
            }
            let output_owners = quantum_ids(&output);
            if frame.live_quantum.keys().copied().collect::<BTreeSet<_>>() != output_owners {
                return Err(error(
                    "ownership",
                    function.body.span,
                    "concrete function output does not contain every live owner",
                ));
            }
            self.charge_cells(output.cells(), function.span)?;
            let definition = SourceDefinition {
                path: path.into(),
                naturals,
                operations,
                inputs,
                output,
                steps: frame.steps,
                effect: function.effect,
                span: function.span,
                peak_quantum: frame.peak,
            };
            let id = self.definitions.len();
            self.definitions.push(definition);
            self.cache.insert(key.clone(), id);
            Ok(id)
        })();
        self.active.remove(&key);
        result.map_err(|e| e.in_module(&module))
    }
    fn provider_type(&self, id: usize, span: Span) -> Result<SourceType> {
        let definition = &self.definitions[id];
        let group = match definition.inputs.as_slice() {
            [input] => input.ty.clone(),
            inputs => tuple(inputs.iter().map(|input| input.ty.clone()).collect()),
        };
        if definition.effect != Effect::Unitary
            || definition.inputs.is_empty()
            || !group.quantum_group()
            || group != definition.output.ty
        {
            return Err(error(
                "type",
                span,
                "provider must be unitary and preserve its complete quantum input group",
            ));
        }
        Ok(definition.output.ty.clone())
    }
    fn resolve(&self, name: &str, scope: &Scope, frame: &Frame, span: Span) -> Result<String> {
        if scope.shadows.contains(name)
            || scope.naturals.contains_key(name)
            || scope.operations.contains_key(name)
        {
            return Err(error(
                "name",
                span,
                "concrete function name is lexically shadowed",
            ));
        }
        frame
            .imports
            .get(name)
            .cloned()
            .ok_or_else(|| error("name", span, "unresolved concrete function"))
    }
    fn arguments(
        &mut self,
        path: &str,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<(BTreeMap<String, u32>, BTreeMap<String, SourceOperation>)> {
        self.enter(span)?;
        let result = self.arguments_inner(path, arguments, scope, frame, depth, span);
        self.active_frames -= 1;
        result
    }
    fn arguments_inner(
        &mut self,
        path: &str,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<(BTreeMap<String, u32>, BTreeMap<String, SourceOperation>)> {
        let (_, function) = self.declaration(path)?;
        if arguments.len() != function.parameters.len() {
            return Err(error(
                "static",
                span,
                "concrete static argument arity mismatch",
            ));
        }
        let mut naturals = BTreeMap::new();
        let mut operations = BTreeMap::new();
        for (p, a) in function.parameters.iter().zip(arguments) {
            match p {
                Parameter::Natural(name) => {
                    let Argument::Natural(n) = a else {
                        return Err(error("static", span, "expected concrete natural"));
                    };
                    naturals.insert(name.clone(), natural(n, &scope.naturals)?);
                }
                Parameter::Operation(name, _) => {
                    operations.insert(name.clone(), self.operation(a, scope, frame, depth, span)?);
                }
            }
        }
        Ok((naturals, operations))
    }
    fn operation(
        &mut self,
        argument: &Argument,
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        self.enter(span)?;
        let result = self.operation_inner(argument, scope, frame, depth, span);
        self.active_frames -= 1;
        result
    }
    fn operation_inner(
        &mut self,
        argument: &Argument,
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        match argument {
            Argument::Natural(Natural {
                kind: NatKind::Name(name),
                ..
            }) if scope.operations.contains_key(name) => Ok(scope.operations[name].clone()),
            Argument::Natural(Natural {
                kind: NatKind::Name(name),
                span,
                ..
            }) => self.provider(name, &[], scope, frame, depth, *span),
            Argument::Definition(name, arguments, span) => {
                self.provider(name, arguments, scope, frame, depth, *span)
            }
            Argument::Repeat(count, child, span) => {
                let child = self.operation(child, scope, frame, depth, *span)?;
                let count = match count {
                    Count::Natural(n) => natural(n, &scope.naturals)?,
                    Count::Power(n) => {
                        let e = natural(n, &scope.naturals)?;
                        if e > 8 {
                            return Err(error("limit", *span, "repeat exponent exceeds eight"));
                        }
                        1u32 << e
                    }
                };
                let repetitions = count
                    .checked_mul(child.repetitions)
                    .ok_or_else(|| error("limit", *span, "repeat multiplicity overflow"))?;
                if count > 256 || repetitions > 256 {
                    return Err(error("limit", *span, "repeat count/product exceeds 256"));
                }
                Ok(SourceOperation {
                    kind: OperationKind::Repeat(count, Box::new(child)),
                    module: frame.module.clone(),
                    span: *span,
                    repetitions,
                })
            }
            _ => Err(error(
                "static",
                span,
                "expected concrete operation provider",
            )),
        }
    }
    fn provider(
        &mut self,
        name: &str,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        self.enter(span)?;
        let result = self.provider_inner(name, arguments, scope, frame, depth, span);
        self.active_frames -= 1;
        result
    }
    fn provider_inner(
        &mut self,
        name: &str,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        let path = self.resolve(name, scope, frame, span)?;
        let (naturals, operations) = self.arguments(&path, arguments, scope, frame, depth, span)?;
        let id = self.function(&path, naturals, operations, depth + 1)?;
        self.provider_type(id, span)?;
        Ok(SourceOperation {
            kind: OperationKind::Definition(id),
            module: frame.module.clone(),
            span,
            repetitions: 1,
        })
    }
    fn block(
        &mut self,
        block: &Block,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        self.enter(block.span)?;
        let result = self.block_inner(block, scope, frame, depth);
        self.active_frames -= 1;
        result
    }
    fn block_inner(
        &mut self,
        block: &Block,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        let initial = scope.values.clone();
        let shadows = scope.shadows.clone();
        let initial_ids: BTreeSet<_> = initial.values().map(|b| b.identity).collect();
        for statement in &block.statements {
            match statement {
                Statement::Let(pattern, expr) => {
                    let value = self.expr(expr, scope, frame, depth)?;
                    bind(pattern, value, scope, frame)?;
                }
                Statement::Drop(expr) => {
                    if self.expr(expr, scope, frame, depth)?.ty.linear() {
                        return Err(error(
                            "ownership",
                            expr.span,
                            "concrete expression discards quantum owner",
                        ));
                    }
                }
            }
        }
        let result = self.expr(&block.result, scope, frame, depth)?;
        if scope
            .values
            .values()
            .any(|b| !initial_ids.contains(&b.identity) && b.value.ty.linear())
        {
            return Err(error(
                "ownership",
                block.span,
                "concrete local quantum owner escapes its lexical block",
            ));
        }
        scope.values = initial
            .into_iter()
            .filter(|(_, b)| !scope.moved.contains(&b.identity))
            .collect();
        scope.shadows = shadows;
        Ok(result)
    }
    fn expr(
        &mut self,
        expr: &Expr,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        self.enter(expr.span)?;
        let result = self.expr_inner(expr, scope, frame, depth);
        self.active_frames -= 1;
        result
    }
    fn expr_inner(
        &mut self,
        expr: &Expr,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Name(name) => {
                let b = scope.values.get(name).cloned().ok_or_else(|| {
                    error(
                        "ownership",
                        span,
                        "concrete binding is unavailable or moved",
                    )
                })?;
                if b.value.ty.linear() {
                    scope.values.remove(name);
                    scope.moved.insert(b.identity);
                }
                Ok(b.value)
            }
            ExprKind::Tuple(fields) => {
                let mut values = Vec::new();
                let mut cells = 2usize;
                for field in fields {
                    let value = self.expr(field, scope, frame, depth)?;
                    cells = cells
                        .saturating_add(value.cells())
                        .saturating_add(value.ty.cells());
                    if cells > 4096 {
                        return Err(error(
                            "limit",
                            span,
                            "inferred concrete value exceeds 4096 cells",
                        ));
                    }
                    values.push(value);
                }
                Ok(SourceValue::tuple(values))
            }
            ExprKind::Call(name, arguments, inputs) => {
                if let Some(op) = scope.operations.get(name).cloned() {
                    let values = inputs
                        .iter()
                        .map(|e| self.expr(e, scope, frame, depth))
                        .collect::<Result<_>>()?;
                    return self.operation_step(StepKind::Apply(op), values, frame, span);
                }
                let path = self.resolve(name, scope, frame, span)?;
                if let Some(kind) = Primitive::lookup(&path) {
                    let naturals = arguments
                        .iter()
                        .map(|a| {
                            let Argument::Natural(n) = a else {
                                return Err(error(
                                    "static",
                                    span,
                                    "primitive requires natural arguments",
                                ));
                            };
                            natural(n, &scope.naturals)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let values = inputs
                        .iter()
                        .map(|e| self.expr(e, scope, frame, depth))
                        .collect::<Result<_>>()?;
                    let (types, output, effect) = primitive(kind, &naturals, span)?;
                    self.step(
                        StepKind::Primitive(kind, naturals),
                        types,
                        output,
                        effect,
                        values,
                        frame,
                        span,
                        0,
                    )
                } else {
                    let (naturals, operations) =
                        self.arguments(&path, arguments, scope, frame, depth, span)?;
                    let id = self.function(&path, naturals, operations.clone(), depth + 1)?;
                    let definition = &self.definitions[id];
                    let types = definition.inputs.iter().map(|v| v.ty.clone()).collect();
                    let output = definition.output.ty.clone();
                    let effect = definition.effect;
                    let peak = definition.peak_quantum;
                    let values = inputs
                        .iter()
                        .map(|e| self.expr(e, scope, frame, depth))
                        .collect::<Result<_>>()?;
                    self.step(
                        StepKind::Call {
                            definition: id,
                            operations,
                        },
                        types,
                        output,
                        effect,
                        values,
                        frame,
                        span,
                        peak,
                    )
                }
            }
            ExprKind::Adjoint(argument, input) => {
                let op = self.operation(argument, scope, frame, depth, span)?;
                let value = self.expr(input, scope, frame, depth)?;
                self.operation_step(StepKind::Adjoint(op), vec![value], frame, span)
            }
            ExprKind::Controlled(argument, inputs) => {
                let op = self.operation(argument, scope, frame, depth, span)?;
                let values = inputs
                    .iter()
                    .map(|e| self.expr(e, scope, frame, depth))
                    .collect::<Result<_>>()?;
                self.operation_step(StepKind::Controlled(op), values, frame, span)
            }
            ExprKind::If(condition, yes, no) => {
                let branch = if predicate(condition, &scope.naturals)? {
                    yes
                } else {
                    no
                };
                self.block(branch, scope, frame, depth)
            }
            ExprKind::Fold {
                index,
                start,
                end,
                carry,
                initial,
                body,
            } => {
                let start = natural(start, &scope.naturals)?;
                let end = natural(end, &scope.naturals)?;
                let count = end
                    .checked_sub(start)
                    .ok_or_else(|| error("size", span, "negative concrete fold range"))?;
                self.folds = self
                    .folds
                    .checked_add(count as usize)
                    .ok_or_else(|| error("limit", span, "fold accounting overflow"))?;
                if self.folds > MAX_FOLDS {
                    return Err(error(
                        "limit",
                        span,
                        "concrete source exceeds 1024 aggregate fold iterations",
                    ));
                }
                let mut value = self.expr(initial, scope, frame, depth)?;
                let carry_type = value.ty.clone();
                for index_value in start..end {
                    let mut inner = scope.clone();
                    inner.values.retain(|_, b| !b.value.ty.linear());
                    inner.naturals.insert(index.clone(), index_value);
                    bind(carry, value, &mut inner, frame)?;
                    value = self.block(body, &mut inner, frame, depth)?;
                    expected(&value, &carry_type, body.span)?;
                    if inner.values.values().any(|b| b.value.ty.linear()) {
                        return Err(error(
                            "ownership",
                            body.span,
                            "concrete fold leaves carry owner live",
                        ));
                    }
                }
                Ok(value)
            }
        }
    }
    fn operation_step(
        &mut self,
        kind: StepKind,
        inputs: Vec<SourceValue>,
        frame: &mut Frame,
        span: Span,
    ) -> Result<SourceValue> {
        let (op, controlled) = match &kind {
            StepKind::Apply(op) | StepKind::Adjoint(op) => (op, false),
            StepKind::Controlled(op) => (op, true),
            _ => unreachable!(),
        };
        let target = self.provider_type(op.target(), span)?;
        let (types, output) = if controlled {
            (vec![bit(), target.clone()], tuple(vec![bit(), target]))
        } else {
            (vec![target.clone()], target)
        };
        let peak = self.definitions[op.target()].peak_quantum + usize::from(controlled);
        self.step(
            kind,
            types,
            output,
            Effect::Unitary,
            inputs,
            frame,
            span,
            peak,
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn step(
        &mut self,
        kind: StepKind,
        types: Vec<SourceType>,
        output_type: SourceType,
        effect: Effect,
        inputs: Vec<SourceValue>,
        frame: &mut Frame,
        span: Span,
        child_peak: usize,
    ) -> Result<SourceValue> {
        if effect > frame.effect {
            return Err(error(
                "effect",
                span,
                "concrete operation exceeds declared effect",
            ));
        }
        if inputs.len() != types.len() {
            return Err(error("type", span, "concrete operation arity mismatch"));
        }
        for (v, ty) in inputs.iter().zip(types) {
            expected(v, &ty, span)?;
        }
        let before: usize = frame.live_quantum.values().sum();
        let input_width: usize = inputs.iter().map(|v| v.ty.quantum_width()).sum();
        if child_peak > 0 {
            frame.observe_width(
                before
                    .checked_sub(input_width)
                    .and_then(|n| n.checked_add(child_peak))
                    .ok_or_else(|| error("limit", span, "concrete width accounting overflow"))?,
                span,
            )?;
        }
        let mut consumed = BTreeSet::new();
        for input in &inputs {
            for id in quantum_ids(input) {
                if !consumed.insert(id) || frame.live_quantum.remove(&id).is_none() {
                    return Err(error(
                        "ownership",
                        span,
                        "concrete source step aliases or consumes an unavailable owner",
                    ));
                }
            }
        }
        self.steps = self
            .steps
            .checked_add(1)
            .ok_or_else(|| error("limit", span, "source step count overflow"))?;
        if self.steps > MAX_STEPS {
            return Err(error(
                "limit",
                span,
                "source proposal exceeds 10000 ordered steps",
            ));
        }
        self.charge_cells(
            inputs
                .iter()
                .map(SourceValue::cells)
                .sum::<usize>()
                .checked_add(output_type.value_cells())
                .ok_or_else(|| error("limit", span, "value cell accounting overflow"))?,
            span,
        )?;
        let output = frame.fresh(&output_type, span)?;
        frame.steps.push(SourceStep {
            module: frame.module.clone(),
            span,
            kind,
            inputs,
            output: output.clone(),
            effect,
        });
        Ok(output)
    }
}
impl Frame {
    fn observe_width(&mut self, width: usize, span: Span) -> Result<()> {
        if width > 16 {
            return Err(error(
                "limit",
                span,
                "concrete source exceeds 16 live quantum wires",
            ));
        }
        self.peak = self.peak.max(width);
        Ok(())
    }
    fn fresh(&mut self, ty: &SourceType, span: Span) -> Result<SourceValue> {
        if ty.value_cells() > 4096 {
            return Err(error("limit", span, "concrete value exceeds 4096 cells"));
        }
        if let TypeKind::Tuple(fields) = &ty.kind {
            return Ok(SourceValue::tuple(
                fields
                    .iter()
                    .map(|t| self.fresh(t, span))
                    .collect::<Result<_>>()?,
            ));
        }
        let identity = self.next_value;
        self.next_value = identity
            .checked_add(1)
            .ok_or_else(|| error("limit", span, "source value identity exhausted"))?;
        if ty.is_quantum() {
            self.live_quantum.insert(identity, ty.quantum_width());
            self.observe_width(self.live_quantum.values().sum(), span)?;
        }
        Ok(SourceValue {
            ty: ty.clone(),
            identity: Some(identity),
            fields: Vec::new(),
        })
    }
}
fn quantum_ids(value: &SourceValue) -> BTreeSet<u32> {
    if value.ty.is_quantum() {
        BTreeSet::from([value.identity.unwrap()])
    } else {
        value.fields.iter().flat_map(quantum_ids).collect()
    }
}
fn bind_name(
    name: &str,
    value: SourceValue,
    span: Span,
    scope: &mut Scope,
    frame: &mut Frame,
) -> Result<()> {
    let retained: usize = scope
        .values
        .iter()
        .filter(|(key, _)| key.as_str() != name)
        .map(|(_, b)| b.value.cells())
        .sum();
    if retained.saturating_add(value.cells()) > 16_384 {
        return Err(error(
            "limit",
            span,
            "concrete scope exceeds 16384 retained value cells",
        ));
    }
    if scope.naturals.contains_key(name)
        || scope.operations.contains_key(name)
        || scope.values.get(name).is_some_and(|b| b.value.ty.linear())
    {
        return Err(error(
            "ownership",
            span,
            "concrete binding shadows a static name or live quantum owner",
        ));
    }
    let identity = frame.next_binding;
    frame.next_binding = identity
        .checked_add(1)
        .ok_or_else(|| error("limit", span, "binding identity exhausted"))?;
    scope
        .values
        .insert(name.into(), Binding { identity, value });
    scope.shadows.insert(name.into());
    Ok(())
}
fn bind(pattern: &Pattern, value: SourceValue, scope: &mut Scope, frame: &mut Frame) -> Result<()> {
    match pattern {
        Pattern::Name(name, span) => bind_name(name, value, *span, scope, frame),
        Pattern::Tuple(patterns, span) => {
            if !matches!(value.ty.kind, TypeKind::Tuple(_)) || patterns.len() != value.fields.len()
            {
                return Err(error(
                    "type",
                    *span,
                    "concrete pattern does not preserve tuple shape",
                ));
            }
            for (p, v) in patterns.iter().zip(value.fields) {
                bind(p, v, scope, frame)?;
            }
            Ok(())
        }
    }
}
fn primitive(
    kind: Primitive,
    ns: &[u32],
    span: Span,
) -> Result<(Vec<SourceType>, SourceType, Effect)> {
    let signature = kind.signature();
    if ns.len() != signature.natural_arity {
        return Err(error(
            "static",
            span,
            "concrete primitive natural arity mismatch",
        ));
    }
    // These are concrete preparation capacities, not generic source premises.
    match kind {
        Primitive::Phase | Primitive::ControlledPhase => {
            if ns[1] > 8 || ns[0] >= (1u32 << ns[1]) {
                return Err(error(
                    "limit",
                    span,
                    "dyadic phase requires k <= 8 and j < 2^k",
                ));
            }
        }
        Primitive::TakeBit | Primitive::PutBit => {
            if ns[0] > 8 || ns[1] >= ns[0] {
                return Err(error("size", span, "concrete register requires k < n <= 8"));
            }
        }
        Primitive::PrependBit => {
            if ns[0] >= 8 {
                return Err(error("limit", span, "classical pack exceeds eight bits"));
            }
        }
        Primitive::H
        | Primitive::X
        | Primitive::Cnot
        | Primitive::Init0
        | Primitive::MeasureZ
        | Primitive::Empty
        | Primitive::ConsumeEmpty
        | Primitive::EmptyBits => {}
    }
    fn size(size: Size, ns: &[u32], span: Span) -> Result<u32> {
        match size {
            Size::Constant(n) => Ok(n),
            Size::Argument(index, offset) => ns[index]
                .checked_add_signed(i32::from(offset))
                .ok_or_else(|| error("limit", span, "concrete primitive register size overflow")),
        }
    }
    fn shape(t: TypeShape, ns: &[u32], span: Span) -> Result<SourceType> {
        Ok(SourceType {
            kind: match t {
                TypeShape::Bit => TypeKind::Q(Box::new(SourceType::bit())),
                TypeShape::CBit => TypeKind::Bit,
                TypeShape::Bits(n) => TypeKind::Q(Box::new(SourceType::bits(size(n, ns, span)?))),
                TypeShape::CBits(n) => TypeKind::Bits(size(n, ns, span)?),
                TypeShape::Tuple(fields) => TypeKind::Tuple(
                    fields
                        .iter()
                        .map(|t| shape(*t, ns, span))
                        .collect::<Result<_>>()?,
                ),
            },
        })
    }
    Ok((
        signature
            .inputs
            .iter()
            .map(|t| shape(*t, ns, span))
            .collect::<Result<_>>()?,
        shape(signature.output, ns, span)?,
        signature.effect,
    ))
}
