import QleisliKernel.SourceTypes.QuantumMatch
import QleisliKernel.SourceTypes.StaticSelection
import QleisliKernel.SourceTypes.PhaseApplication

/-! Original exact-label qmatch table and source-function arm headers.
Actual arm/control bodies, source/runtime preservation and native/QDV binding
remain separate obligations. These reads issue no handle or control capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumArms
open Semantics.FiniteCarrier Semantics.Raw Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

structure Label (sources : Sources) where
  ordinal : Nat
  typeQuery : Option (TypeRead sources)

def Label.sourceRows {sources : Sources} (label : @Label sources) : List (String × String) :=
  match label.typeQuery with | none => [] | some query => query.sourceRows

def readLabel (sources : Sources) (caller : String) (selector : Basis) (tokens : List LocatedToken) :
    WorkM (@Label sources) := do
  match selector with
  | [.unit] | [.bit] | [.bits _] =>
    let [literal] := tokens | throw .request
    let ordinal ← adapt (NaturalSyntax.decimal literal.text)
    guard (ordinal ≤ 4294967295) .request
    return ⟨ordinal,none⟩
  | [.enumeration _ variants] =>
    let some variant := tokens.getLast? | throw .request
    guard (tokens.length ≥ 3 && (tokens[tokens.length-2]?.map (·.text)) == some "::") .request
    let ty ← typeExpressionWithSources sources caller ((tokens.dropLast.dropLast).map (·.text))
    guard (ty.basis == selector && variants.contains variant.text) .request
    return ⟨variants.idxOf variant.text,some ty⟩
  | _ => throw .request

def primitiveKind {sources owner scope tokens}
    (candidate : CallName.Checked sources owner scope tokens) : Option OperationDescription.Primitive :=
  match candidate.decision with
  | .primitive _ _ _ _ _ _ .h _ => some .h
  | .primitive _ _ _ _ _ _ .globalPhaseEighth _ => some .globalPhaseEighth
  | _ => none

inductive OperationOrigin (sources : Sources) (owner : String) (tokens : List LocatedToken)
    (description : OperationDescription.Description)
    (graph : StaticOperation.CheckedGraph sources (.source owner) description) where
  | named (selected : QuantumSignature.OperationSelection sources owner tokens)
      (original : description = OperationDescription.provider selected.resolution.moduleName
        selected.resolution.declaration.name selected.signature.staticArguments.bases
        selected.signature.staticArguments.naturals selected.signature.staticArguments.operations)
  | source (callerName : String) (signature : QuantumSignature.Checked sources owner callerName)
      (naturals : PhaseApplication.Naturals sources) (scope : List String)
      (read : SourceOperation.Checked signature.toChecked naturals.helpers.val naturals.environment scope tokens)
      (sameDescription : description = read.description) (sameGraph : HEq graph read.graph)
  | primitive (scope : List String) (candidate : CallName.Checked sources owner scope tokens)
      (kind : OperationDescription.Primitive) (selected : primitiveKind candidate = some kind)
      (target : Basis) (original : description = ⟨[.primitive kind target],0⟩)

/-- Every original provider and constructor remains in this exact graph. A
composed operation has no representative function name or invented signature.
The native continuation binds each provider's actual subject separately. -/
structure Operation (sources : Sources) (owner : String) (tokens : List LocatedToken) where
  description : OperationDescription.Description
  graph : StaticOperation.CheckedGraph sources (.source owner) description
  original : OperationOrigin sources owner tokens description graph

def Operation.providers {sources owner tokens} (operation : Operation sources owner tokens) :
    List (StaticOperation.Provider sources) := operation.graph.providers

def Operation.sourceRows {sources owner tokens} (operation : Operation sources owner tokens) :
    List (String × String) :=
  operation.graph.sourceRows ++ match operation.original with
    | .named selected _ => ResolutionProvenance.sourceRows selected.resolution ++ selected.signature.sourceRows
    | .source _ signature _ _ _ _ _ => signature.sourceRows
    | .primitive .. => []

structure BoundArm (sources : Sources) (owner : String) (selector target : Basis) where
  written : QuantumMatch.Arm
  label : @Label sources
  originalLabel : ∃ before after,
    (readLabel sources owner selector written.label).run before = (.ok label,after)
  operation : Operation sources owner written.operation
  input : operation.graph.root.input = target
  output : operation.graph.root.output = target
  effect : operation.graph.root.effect = .unitary
  controlled : operation.graph.root.paths.controllable = true

/-- Header-only module resolution. The enclosing original-body gate must first
check lexical shadowing, including consumed names; this function does not
authorize a source occurrence or replace that persistent-scope check. -/
def readArm (sources : Sources) (owner : String) (selector target : Basis) (written : QuantumMatch.Arm) :
    WorkM (BoundArm sources owner selector target) := do
  let label ← NaturalAffine.witness (readLabel sources owner selector written.label)
  let selected ← QuantumSignature.select sources owner (written.operation.map (·.text))
  let selected := QuantumSignature.OperationSelection.closed selected
  -- This standalone legacy metadata reader has no independent body inference.
  -- Keep its annotation refusal; the complete source continuation below may
  -- retain an internal inference obligation for the actual native body gate.
  guard (selected.signature.original.parsedHeader.effect == none ||
    selected.signature.original.parsedHeader.effect == some .unitary) .request
  let description := OperationDescription.provider selected.resolution.moduleName selected.resolution.declaration.name
    selected.signature.staticArguments.bases selected.signature.staticArguments.naturals selected.signature.staticArguments.operations
  let graph ← StaticOperation.check sources (.source owner) description
  let operation : Operation sources owner written.operation := ⟨description,graph,.named selected rfl⟩
  if input : operation.graph.root.input = target then
    if output : operation.graph.root.output = target then
      if effect : operation.graph.root.effect = .unitary then
        if controlled : operation.graph.root.paths.controllable = true then
          return ⟨written,label.val,by with_reducible exact label.property,operation,input,output,effect,controlled⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Resolve original positional specializations in their actual caller static
environment. The body traversal supplies persistent lexical names, including
consumed runtime binders and body-local Nat aliases. -/
def readArmWithSignature {sources owner name}
    (signature : QuantumSignature.Checked sources owner name)
    (naturals : PhaseApplication.Naturals sources) (scope : List String)
    (selector target : Basis) (written : QuantumMatch.Arm) :
    WorkM (BoundArm sources owner selector target) := do
  let label ← NaturalAffine.witness (readLabel sources owner selector written.label)
  let operation : Operation sources owner written.operation ←
    match CallName.readName written.operation with
    | .ok _ => do
      let candidate ← CallName.read sources owner scope written.operation
      match selected : primitiveKind candidate with
      | some kind =>
        let description : OperationDescription.Description := ⟨[.primitive kind target],0⟩
        let graph ← StaticOperation.check sources (.source owner) description
        return ⟨description,graph,.primitive scope candidate kind selected target rfl⟩
      | none => do
        let source ← SourceOperation.read signature.toChecked naturals.helpers.val naturals.environment scope written.operation
        return ⟨source.description,source.graph,.source name signature naturals scope source rfl HEq.rfl⟩
    | .error _ => do
      let source ← SourceOperation.read signature.toChecked naturals.helpers.val naturals.environment scope written.operation
      return ⟨source.description,source.graph,.source name signature naturals scope source rfl HEq.rfl⟩
  if input : operation.graph.root.input = target then
    if output : operation.graph.root.output = target then
      if effect : operation.graph.root.effect = .unitary then
        if controlled : operation.graph.root.paths.controllable = true then
          return ⟨written,label.val,by with_reducible exact label.property,operation,input,output,effect,controlled⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

def BoundArm.sourceRows {sources owner selector target} (arm : BoundArm sources owner selector target) :
    List (String × String) :=
  arm.label.sourceRows ++ arm.operation.sourceRows

def partition {sources owner selector target} (count : Nat) (arms : List (BoundArm sources owner selector target)) : Bool :=
  let labels := arms.map (·.label.ordinal)
  labels.length == count && labels.all (· < count) && labels.eraseDups.length == labels.length

/-- Original arm headers and label coverage, not an enclosing lexical-scope
judgment. Current native admission also requires QuantumSequence.read. -/
structure Table (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) where
  site : QuantumMatch.Site sources owner name offset
  layout : Semantics.FiniteCarrier.Layout
  originalTypes : ∃ before after, (SourceTypes.checkMany sources [selector,target]).run before = (.ok (),after)
  selectorLayout : Semantics.FiniteCarrier.layout selector = some layout
  arms : List (BoundArm sources owner selector target)
  originalArms : arms.map (·.written) = site.parsed.arms
  complete : partition layout.labels.length arms = true

/-- Reuse the exact already-read caller; all arm, source-type and partition
checks remain in this shared continuation. No alternate source body is supplied. -/
def readArms {sources owner name}
    (originalCaller : OrdinarySignature.Original sources owner name)
    (offset : Nat) (selector target : Basis) :
    WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite originalCaller offset
  let original ← NaturalAffine.witness (SourceTypes.checkMany sources [selector,target])
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let arms ← site.parsed.arms.mapM (readArm sources owner selector target)
  exactWork (Exact.charge (256*(site.parsed.tokens.length+1)*(arms.length+1)))
  if same : arms.map (·.written) = site.parsed.arms then
    if complete : partition layout.val.labels.length arms = true then
      return ⟨site,layout.val,by with_reducible exact original.property,
        by obtain ⟨before,after,ran⟩ := layout.property
           exact FiniteCarrier.read_reference _ _ _ _ ran,
        arms,same,complete⟩
    else throw .request
  else throw .request

def read (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) :
    WorkM (Table sources owner name offset selector target) := do
  let original ← OrdinarySignature.readOriginal sources owner name
  readArms original offset selector target

/-- Read the unchanged original site using the same checked caller instance as
its complete source trace. Supplying no event environment seeds the original
header actuals; complete source traversal supplies local aliases when present. -/
def readArmsWithSignature {sources owner name}
    (signature : QuantumSignature.Checked sources owner name)
    (offset : Nat) (selector target : Basis)
    (eventNaturals : Option (PhaseApplication.Naturals sources) := none)
    (eventScope : List String := []) : WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite signature.original offset
  let original ← NaturalAffine.witness (SourceTypes.checkMany sources [selector,target])
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let naturals ← match eventNaturals with
    | some naturals => pure naturals
    | none => PhaseApplication.prepareWithSignature signature
  let scope := signature.staticNames ++ eventScope
  let arms ← site.parsed.arms.mapM (readArmWithSignature signature naturals scope selector target)
  exactWork (Exact.charge (256*(site.parsed.tokens.length+1)*(arms.length+1)))
  if same : arms.map (·.written) = site.parsed.arms then
    if complete : partition layout.val.labels.length arms = true then
      return ⟨site,layout.val,by with_reducible exact original.property,
        by obtain ⟨before,after,ran⟩ := layout.property
           exact FiniteCarrier.read_reference _ _ _ _ ran,
        arms,same,complete⟩
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.QuantumArms
