import QleisliKernel.SourceTypes.StaticOperation
import QleisliKernel.SourceTypes.StaticApplication
import QleisliKernel.SourceTypes.SourceOperationProvenance

/-! Original static operation-expression transfer. Constructor syntax, counts,
formal ordinals and all provider actuals produce a retained descriptor which is
independently checked. No wrapper source declaration or closed AST is invented.
Body/control equations remain mandatory at the enclosing native source gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceOperation
open Finite OperationDescription

-- These proof-only instances retain the existing structural BEq algorithms.
private instance : LawfulBEq Semantics.FiniteCarrier.Origin := ⟨by deriving_LawfulEq_tactic⟩
private instance : LawfulBEq Semantics.FiniteCarrier.Atom := ⟨by deriving_LawfulEq_tactic⟩
private instance : ReflBEq OperationDescription.Primitive := ⟨by deriving_ReflEq_tactic⟩
private instance : LawfulBEq OperationDescription.Primitive := ⟨by deriving_LawfulEq_tactic⟩
private instance : ReflBEq OperationDescription.Node := ⟨by deriving_ReflEq_tactic⟩
private instance : LawfulBEq OperationDescription.Node := ⟨by deriving_LawfulEq_tactic⟩
private instance : ReflBEq Description := ⟨by deriving_ReflEq_tactic⟩
private instance : LawfulBEq Description := ⟨by deriving_LawfulEq_tactic⟩

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def candidateResolution {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option Resolved :=
  match candidate.decision with
  | .named resolution | .prelude _ _ _ _ _ _ _ _ resolution => some resolution.result
  | _ => none

private def count (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (environment : LexicalNatural.Environment entries) (scope : List String)
    (validate : Semantics.SourceNatural.Expr → WorkM Unit)
    (tokens : List LocatedToken) : WorkM Nat := do
  if (tokens.take 2).map (·.text) == ["2","^"] then
    let expression ← adapt (StaticBindings.natural (tokens.drop 2))
    validate expression.expression
    let exponent ← LexicalNatural.read sources caller entries environment scope expression.expression
    guard (exponent.result.value ≤ 31) .limit
    pure (2^exponent.result.value)
  else
    let expression ← adapt (StaticBindings.natural tokens)
    validate expression.expression
    pure (← LexicalNatural.read sources caller entries environment scope expression.expression).result.value

def countValue {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (tokens : List LocatedToken) : WorkM Nat :=
  count sources caller entries environment scope
    (StaticApplication.validateNatural instantiation genericState scope) tokens

def countRows (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (scope : List String) (tokens : List LocatedToken) : WorkM (List (String × String)) := do
  let texts := if (tokens.take 2).map (·.text) == ["2","^"] then tokens.drop 2 else tokens
  let expression ← adapt (StaticBindings.natural texts)
  NaturalRows.expression sources caller entries scope expression.expression

structure Count {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  value : Nat
  genericState : Option (GenericLexicalNatural.SomeEnvironment sources)
  original : ∃ before after,
    (countValue instantiation entries environment scope genericState tokens).run before = (.ok value,after)
  rows : List (String × String)
  rowsRead : ∃ before after,(countRows sources caller entries scope tokens).run before = (.ok rows,after)

/-- Shared original count reader for static descriptions and direct runtime
group transforms. Zero counts still retain their original syntax/helper rows;
operand traversal and requested access remain the enclosing rule's duties. -/
def readCount {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none) :
    WorkM (Count instantiation entries environment scope tokens) := do
  let value ← NaturalAffine.witness (countValue instantiation entries environment scope genericState tokens)
  let rows ← NaturalAffine.witness (countRows sources caller entries scope tokens)
  pure ⟨value.val,genericState,by with_reducible exact value.property,rows.val,by with_reducible exact rows.property⟩

/-- Every constructor child is visited before its graph is assembled, including
zero-power children and unused actuals of a provider. The same callback handles
operation arguments recursively; it is never a producer-supplied path flag. -/
def buildWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → List LocatedToken → WorkM Description :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
    exactWork (Exact.charge (32*(bytes+(tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    let description ← if tokens.getLast?.map (·.text) == some ")" then do
        let call ← adapt (CallSyntax.read tokens)
        let [constructor] := call.call.callee.map (·.text) | throw .request
        match constructor,call.call.arguments with
        | "adjoint",[child] => return (← next child.tokens).unary .inverse
        | "controlled",[child] => return (← next child.tokens).unary .controlled
        | "power",[child,amount] =>
          let child ← next child.tokens
          let count ← countValue instantiation entries environment scope genericState amount.tokens
          return child.unary (fun index => .power index count)
        | "then_op",[left,right] => return Description.binary .thenOp (← next left.tokens) (← next right.tokens)
        | "tensor_op",[left,right] => return Description.binary .tensor (← next left.tokens) (← next right.tokens)
        | "conjugate_op",[outer,middle] =>
          return Description.binary .conjugate (← next outer.tokens) (← next middle.tokens)
        | "checked_op",[child,meaning] =>
          let _ ← adapt (CallName.readName child.tokens)
          let child ← next child.tokens
          let selected ← SourceMeaning.selectName sources caller scope (meaning.tokens.map (·.text))
          return child.unary (fun index => .requested index selected.resolution.moduleName selected.resolution.declaration.name)
        | _,_ => throw .request
      else do
        let written ← adapt (StaticApplication.readSyntax tokens)
        let candidate ← CallName.read sources caller scope written.callee
        match candidate.decision with
        | .lexical name _ _ =>
          guard written.arguments.isEmpty .request
          match instantiation with
          | .closed _ => throw .request
          | .static arguments staticEnvironment _ =>
            let some formal := staticEnvironment.numeric.original.header.formals.find? (·.name == name)
              | throw .request
            let .operation _ := formal.kind | throw .request
            pure (OperationDescription.formal caller callerName arguments.bases arguments.naturals
              arguments.operations formal.ordinal)
        | _ =>
          let some resolution := candidateResolution candidate | throw .request
          let actuals ← StaticApplication.read instantiation entries environment scope written
            resolution.moduleName resolution.declaration.name next genericState
          pure (OperationDescription.provider resolution.moduleName resolution.declaration.name
            actuals.arguments.bases actuals.arguments.naturals actuals.arguments.operations)
    guard (description.nodes.length ≤ 4096) .limit
    exactWork (Exact.charge (16*(description.nodes.length+1)^2))
    guard description.complete .request
    pure description)

def buildWithGeneric {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → List LocatedToken → WorkM Description :=
  buildWithInstantiation signature.instantiation entries environment scope genericState

def build {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) : Nat → List LocatedToken → WorkM Description :=
  buildWithGeneric signature entries environment scope none

def primitiveKind {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option OperationDescription.Primitive :=
  match candidate.decision with
  | .primitive _ _ _ _ _ _ .h _ => some .h
  | .primitive _ _ _ _ _ _ .globalPhaseEighth _ => some .globalPhaseEighth
  | _ => none

/-- Existing direct contextual targets and runtime adjoint/control accept sealed unary gates using
the actual complete target type. Static provider arguments and nested static
constructor leaves do not gain this contextual exception. -/
private def runtimePrimitive (sources : Sources) (caller : String) (scope : List String)
    (target : Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) :
    WorkM (Option (Description × List (String × String))) := do
  if (CallName.readName tokens).isOk then
    let candidate ← CallName.read sources caller scope tokens
    match primitiveKind candidate with
    | some kind =>
      guard (kind == .globalPhaseEighth || target == [.bit]) .request
      pure (some (⟨[.primitive kind target],0⟩,CallName.sourceRows candidate))
    | none => pure none
  else
    match CallSyntax.read tokens with
    | .error _ => pure none
    | .ok call =>
      match call.call.callee.map (·.text),call.call.arguments with
      | [constructor],[argument] =>
        if constructor != "adjoint" && constructor != "controlled" then pure none else
          match CallName.readName argument.tokens with
          | .error _ => pure none
          | .ok _ => do
            let candidate ← CallName.read sources caller scope argument.tokens
            match primitiveKind candidate with
            | none => pure none
            | some kind =>
              guard (kind == .globalPhaseEighth || target == [.bit]) .request
              let child : Description := ⟨[.primitive kind target],0⟩
              let description := if constructor == "adjoint" then child.unary .inverse else child.unary .controlled
              pure (some (description,CallName.sourceRows candidate))
      | _,_ => pure none

def proposalWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) : WorkM Description := do
  let primitive ← match target with
    | none => pure none
    | some basis => runtimePrimitive sources caller scope basis tokens
  match primitive with
  | some (description,_) => pure description
  | none => buildWithInstantiation instantiation entries environment scope genericState 65 tokens

/-- Retain exact source lookup and type-actual routes in addition to the
canonical descriptor. Reexports used only to select a provider or an unused
Basis actual remain relevant; canonical names alone cannot cover those rows. -/
private def underEdge {sources caller scope childTokens tokens}
    (edge : Edge) (value : Provenance sources caller scope childTokens) :
    WorkM (Provenance sources caller scope tokens) := do
  -- Pay before mapping paths and copying the returned marker spine. Original
  -- row/source/query work retains its existing separate reservation.
  exactWork (Exact.charge (8*(value.markers.length+1)))
  return ⟨value.rows,value.markers.map fun marker => {marker with path := edge :: marker.path}⟩

/-- The EXISTING original row traversal also retains each actual checked_op
query and source path. It does not reparse a body or read a Meaning graph. -/
def readProvenanceWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → (tokens : List LocatedToken) → WorkM (Provenance sources caller scope tokens) :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
    exactWork (Exact.charge (32*(bytes+(tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    if tokens.getLast?.map (·.text) == some ")" then
      let call ← adapt (CallSyntax.read tokens)
      match checkedOp : call.call.callee.map (·.text),arguments : call.call.arguments with
      | ["adjoint"],[child] | ["controlled"],[child] | ["power"],[child,_] =>
        underEdge (tokens := tokens) (.child 0) (← next child.tokens)
      | ["then_op"],[left,right] | ["tensor_op"],[left,right] | ["conjugate_op"],[left,right] => do
        let left ← underEdge (tokens := tokens) (.child 0) (← next left.tokens)
        let right ← underEdge (tokens := tokens) (.child 1) (← next right.tokens)
        return ⟨left.rows ++ right.rows,left.markers ++ right.markers⟩
      | ["checked_op"],[child,meaning] => do
        let childName ← adapt (CallName.readName child.tokens)
        let selected ← NaturalAffine.witness
          (SourceMeaning.selectName sources caller scope (meaning.tokens.map (·.text)))
        let inherited ← underEdge (tokens := tokens) (.child 0) (← next child.tokens)
        let marker : Marker sources caller scope :=
          ⟨[],tokens,call,child,meaning,checkedOp,arguments,childName,selected.val,
            by with_reducible exact selected.property⟩
        return ⟨inherited.rows ++ selected.val.queryRows,inherited.markers ++ [marker]⟩
      | _,_ => throw .request
    else
      let written ← adapt (StaticApplication.readSyntax tokens)
      let candidate ← CallName.read sources caller scope written.callee
      match candidate.decision with
      | .lexical .. => pure ⟨CallName.sourceRows candidate,[]⟩
      | _ =>
        let some resolution := candidateResolution candidate | throw .request
        let actuals ← StaticApplication.read instantiation entries environment scope written
          resolution.moduleName resolution.declaration.name
          (buildWithInstantiation instantiation entries environment scope genericState 65) genericState
        let children ← actuals.actuals.mapM fun actual => do
          match actual.formal.kind with
          | .operation _ => underEdge (tokens := tokens) (.actual actual.formal.ordinal) (← next actual.argument.tokens)
          | _ => pure (⟨[],[]⟩ : Provenance sources caller scope tokens)
        exactWork (Exact.charge (8*((children.map fun child => child.markers.length).sum+children.length+1)))
        return ⟨CallName.sourceRows candidate ++ actuals.actuals.flatMap StaticApplication.Actual.sourceRows ++
          children.flatMap (·.rows),children.flatMap (·.markers)⟩)

/-- Compatibility projection of the one shared provenance traversal. New
marker/path work is charged; no old remaining-work equivalence is claimed. -/
def readRowsWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (fuel : Nat) (tokens : List LocatedToken) : WorkM (List (String × String)) := do
  return (← readProvenanceWithInstantiation instantiation entries environment scope genericState fuel tokens).rows

def proposalProvenanceWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) :
    WorkM (Provenance sources caller scope tokens) := do
  let primitive ← match target with
    | none => pure none
    | some basis => runtimePrimitive sources caller scope basis tokens
  match primitive with
  | some (_,rows) => pure ⟨rows,[]⟩
  | none => readProvenanceWithInstantiation instantiation entries environment scope genericState 65 tokens

def proposalRowsWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) : WorkM (List (String × String)) := do
  return (← proposalProvenanceWithInstantiation instantiation entries environment scope genericState target tokens).rows

/-- Marker provenance is indexed by this SAME original builder receipt. It
supplies no native graph alignment, invocation, substitution or duty discharge. -/
structure BoundProvenance {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (description : Description)
    (_builder : ∃ before after,
      (proposalWithInstantiation instantiation entries environment scope genericState target tokens).run before = (.ok description,after))
    extends Provenance sources caller scope tokens where
  original : ∃ before after,
    (proposalProvenanceWithInstantiation instantiation entries environment scope genericState target tokens).run before = (.ok toProvenance,after)

private theorem provenance_rows {sources caller callerName original}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    {entries : List NaturalHelpers.Entry} {environment : LexicalNatural.Environment entries}
    {scope : List String} {genericState : Option (GenericLexicalNatural.SomeEnvironment sources)}
    {target : Option Semantics.FiniteCarrier.Basis} {tokens : List LocatedToken}
    {value : Provenance sources caller scope tokens}
    (read : ∃ before after,
      (proposalProvenanceWithInstantiation (instantiation := instantiation) entries environment scope genericState target tokens).run before =
        (.ok value,after)) :
    ∃ before after,
      (proposalRowsWithInstantiation (instantiation := instantiation) entries environment scope genericState target tokens).run before =
        (.ok value.rows,after) := by
  obtain ⟨before,after,read⟩ := read
  refine ⟨before,after,?_⟩
  unfold proposalRowsWithInstantiation
  rw [Finite.bind_run,read]
  rfl

structure CheckedWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  description : Description
  genericState : Option (GenericLexicalNatural.SomeEnvironment sources)
  target : Option Semantics.FiniteCarrier.Basis
  supply : Option (StaticOperation.Supply instantiation)
  original : ∃ before after,
    (proposalWithInstantiation instantiation entries environment scope genericState target tokens).run before = (.ok description,after)
  graph : StaticOperation.CheckedGraph sources (.source caller) description
  rows : List (String × String)
  rowsRead : ∃ before after,
    (proposalRowsWithInstantiation instantiation entries environment scope genericState target tokens).run before = (.ok rows,after)
  provenance : BoundProvenance instantiation entries environment scope tokens genericState target description original
  sameRows : provenance.rows = rows

/-- An already performed original proposal read, indexed by every source and
static-context input. It carries no graph, capability or body-check result. -/
structure Proposal {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) where
  description : Description
  original : ∃ before after,
    (proposalWithInstantiation instantiation entries environment scope genericState target tokens).run before =
      (.ok description,after)

/-- Only proposal construction is shared. The supplying context, complete
graph, capabilities, original rows and all assertion markers are checked now. -/
def readFromProposal {sources caller callerName original instantiation entries environment scope genericState target tokens}
    (proposal : @Proposal sources caller callerName original instantiation entries environment scope genericState target tokens)
    (supply : Option (StaticOperation.Supply instantiation) := none) :
    WorkM (CheckedWithInstantiation instantiation entries environment scope tokens) := do
  let graph ← match supply with
    | none => StaticOperation.check sources (.source caller) proposal.description
    | some supply => StaticOperation.checkWithSupply supply proposal.description
  let provenance ← NaturalAffine.witness
    (proposalProvenanceWithInstantiation instantiation entries environment scope genericState target tokens)
  have provenanceRead : ∃ before after,
      (proposalProvenanceWithInstantiation instantiation entries environment scope genericState target tokens).run before =
        (.ok provenance.val,after) := by
    with_reducible exact provenance.property
  pure ⟨proposal.description,genericState,target,supply,proposal.original,graph,provenance.val.rows,
    provenance_rows provenanceRead,⟨provenance.val,provenanceRead⟩,rfl⟩

def readWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none)
    (target : Option Semantics.FiniteCarrier.Basis := none)
    (supply : Option (StaticOperation.Supply instantiation) := none) :
    WorkM (CheckedWithInstantiation instantiation entries environment scope tokens) := do
  let description ← NaturalAffine.witness (proposalWithInstantiation instantiation entries environment scope genericState target tokens)
  let proposal : Proposal instantiation entries environment scope genericState target tokens :=
    ⟨description.val,by with_reducible exact description.property⟩
  readFromProposal proposal supply

abbrev Checked {sources caller callerName} (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) :=
  CheckedWithInstantiation signature.instantiation entries environment scope tokens

def read {sources caller callerName} (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none)
    (target : Option Semantics.FiniteCarrier.Basis := none)
    (supply : Option (StaticOperation.Supply signature.instantiation) := none) :
    WorkM (Checked signature entries environment scope tokens) :=
  readWithInstantiation signature.instantiation entries environment scope tokens genericState target supply

/-- The fresh and retained branches record different actual actions. Retaining
a proposal never asserts that the fresh whole source reader was rerun. -/
inductive ProposalInput {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (tokens : List LocatedToken) where
  | fresh
  | retained (proposal : Proposal instantiation entries environment scope genericState none tokens)

def readInput {sources caller callerName original instantiation entries environment scope genericState tokens}
    (input : @ProposalInput sources caller callerName original instantiation entries environment scope genericState tokens)
    (supply : StaticOperation.Supply instantiation) :
    WorkM (CheckedWithInstantiation instantiation entries environment scope tokens) :=
  match input with
  | .fresh => readWithInstantiation instantiation entries environment scope tokens genericState none (some supply)
  | .retained proposal => readFromProposal proposal (some supply)

/-- A call creator may identify the exact source builder it actually supplied.
An arbitrary OperationReader keeps the existing fresh path. This identity is
not inferred by comparing names, descriptions, ports or closed values. -/
inductive BuilderReuse {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName) where
  | fresh
  | retained (sameReader : operationReader =
      buildWithInstantiation instantiation entries environment scope application.genericState 65)

private def inputOfValue {sources caller callerName original entries environment scope operationReader genericState tokens kind}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (sameReader : operationReader =
      buildWithInstantiation instantiation entries environment scope genericState 65)
    (value : StaticApplication.Value instantiation entries environment scope operationReader tokens kind) :
    WorkM (ProposalInput instantiation entries environment scope genericState tokens) :=
  match value with
  | .basis .. | .natural .. => throw .request
  | .operation description _ original =>
    let proposal : Proposal instantiation entries environment scope genericState none tokens :=
      ⟨description,by
        change ∃ before after,
          (buildWithInstantiation instantiation entries environment scope genericState 65 tokens).run before =
            (.ok description,after)
        simpa only [sameReader] using original⟩
    pure (.retained proposal)

private def inputOfActual {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (reuse : BuilderReuse application)
    (actual : StaticApplication.Actual instantiation entries environment scope operationReader) :
    WorkM (ProposalInput instantiation entries environment scope application.genericState actual.argument.tokens) :=
  match reuse with
  | .fresh => pure .fresh
  | .retained sameReader => inputOfValue sameReader actual.value

/-- One already-computed operation actual at its exact original position.
The mixed formal and argument tokens remain on actual; this supplies no native
occurrence alignment or GenericDutyQueue invocation/substitution association. -/
structure ActualSource {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) where
  index : Fin application.actuals.length
  actual : StaticApplication.Actual instantiation entries environment scope operationReader
  atIndex : actual = application.actuals[index.val]'index.isLt
  name : String
  description : Description
  operation : actual.operations = [(name,description)]
  checked : CheckedWithInstantiation instantiation entries environment scope actual.argument.tokens
  sameDescription : checked.description = description
  input : ProposalInput instantiation entries environment scope application.genericState actual.argument.tokens
  original : ∃ before after,
    (readInput input supply).run before = (.ok checked,after)

def ActualSource.native {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName
    instantiation application supply}
    (source : @ActualSource sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName
      instantiation application supply) : Sigma (StaticOperation.Actual sources (.source caller)) :=
  ⟨(source.name,source.checked.description),⟨source.checked.graph⟩⟩

structure ApplicationActualsResult {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) where
  actuals : List (Sigma (StaticOperation.Actual sources (.source caller)))
  rows : List (String × String)
  sourceActuals : List (ActualSource application supply)
  sameActuals : actuals = sourceActuals.map ActualSource.native
  sameRows : rows = sourceActuals.flatMap (fun source => source.checked.rows)

def readApplicationActualsWith {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) (reuse : BuilderReuse application) :
    WorkM (ApplicationActualsResult application supply) := do
  -- The finite range, linked-list selections, retained source cells and final
  -- projections are new work. This debit precedes those indexed traversals.
  exactWork (Exact.charge (16*(application.actuals.length+1)^2))
  let retained ← (List.finRange application.actuals.length).mapM fun index => do
    let actual := application.actuals[index.val]'index.isLt
    match operation : actual.operations with
    | [] => pure none
    | [(name,description)] =>
      let input ← inputOfActual application reuse actual
      let checked ← NaturalAffine.witness (readInput input supply)
      let compared ← NaturalAffine.witness (guard (checked.val.description == description) .request)
      have sameDescription : checked.val.description = description := by
        obtain ⟨before,after,read⟩ := compared.property
        have unit : compared.val = () := by cases compared.val; rfl
        rw [unit] at read
        exact beq_iff_eq.mp (guard_success _ _ _ _ read).1
      let source : ActualSource application supply :=
        ⟨index,actual,rfl,name,description,operation,checked.val,sameDescription,input,
          by with_reducible exact checked.property⟩
      pure (some source)
    | _ => throw .request
  let sourceActuals := retained.filterMap id
  return ⟨sourceActuals.map ActualSource.native,sourceActuals.flatMap (fun source => source.checked.rows),sourceActuals,rfl,rfl⟩

def readApplicationActuals {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) : WorkM (ApplicationActualsResult application supply) :=
  readApplicationActualsWith application supply .fresh

/-- Original application tokens authenticate both native graph projections and
these SAME source reads. Original mixed positions and source order are retained
by the actual computation; callee binding checks still run independently. -/
structure ApplicationActuals {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) extends ApplicationActualsResult application supply where
  reuse : BuilderReuse application
  original : ∃ before after,
    (readApplicationActualsWith application supply reuse).run before = (.ok toApplicationActualsResult,after)

def checkApplicationActuals {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) : WorkM (ApplicationActuals application supply) := do
  let checked ← NaturalAffine.witness (readApplicationActuals application supply)
  pure ⟨checked.val,.fresh,by simpa only [readApplicationActuals] using checked.property⟩

/-- Reuse the genuine per-actual proposal receipt retained by StaticApplication.
Native/source graph and complete provenance reads still run for every actual,
including unused ones and zero-power children. -/
def checkApplicationActualsWithBuilder {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation)
    (sameReader : operationReader =
      buildWithInstantiation instantiation entries environment scope application.genericState 65) :
    WorkM (ApplicationActuals application supply) := do
  let checked ← NaturalAffine.witness (readApplicationActualsWith application supply (.retained sameReader))
  pure ⟨checked.val,.retained sameReader,by with_reducible exact checked.property⟩

end QleisliKernel.SourceTypes.SourceOperation
