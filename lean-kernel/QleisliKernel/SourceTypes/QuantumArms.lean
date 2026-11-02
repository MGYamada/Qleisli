import QleisliKernel.SourceTypes.QuantumMatch
import QleisliKernel.SourceTypes.StaticSelection
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.QuantumLabels
import QleisliKernel.SourceTypes.SourceRows

/-! Original exact-label qmatch table and source-function arm headers.
Actual arm/control bodies, source/runtime preservation and native/QDV binding
remain separate obligations. These reads issue no handle or control capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumArms
open Semantics.FiniteCarrier Semantics.Raw Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

abbrev Label := QuantumLabels.Label
def Label.sourceRows {sources : Sources} (label : Label sources) : List (String × String) :=
  QuantumLabels.Label.sourceRows label
abbrev readLabel := QuantumLabels.read

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
  | instantiated (callerName : String) (original : OrdinarySignature.Original sources owner callerName)
      (instantiation : StaticInstantiation.Checked original) (supply : StaticOperation.Supply instantiation)
      (naturals : PhaseApplication.Naturals sources) (scope : List String)
      (read : SourceOperation.CheckedWithInstantiation instantiation naturals.helpers.val naturals.environment scope tokens)
      (sameDescription : description = read.description) (sameGraph : HEq graph read.graph)
  | primitive (scope : List String) (candidate : CallName.Checked sources owner scope tokens)
      (kind : OperationDescription.Primitive) (selected : primitiveKind candidate = some kind)
      (target : Basis) (original : description = ⟨[.primitive kind target],0⟩)

def operationSourceRows {sources owner tokens description}
    (graph : StaticOperation.CheckedGraph sources (.source owner) description)
    (original : OperationOrigin sources owner tokens description graph) : List SourceRows.Row :=
  graph.sourceRows ++ match original with
    | .named selected _ => ResolutionProvenance.sourceRows selected.resolution ++ selected.signature.sourceRows
    | .source _ signature naturals _ read _ _ => signature.sourceRows ++ naturals.sourceRows ++ read.rows
    | .instantiated _ original _ supply naturals _ read _ _ =>
      [(owner,original.source)] ++ supply.arguments.sourceRows ++ naturals.sourceRows ++ read.rows
    | .primitive _ candidate .. => CallName.sourceRows candidate

/-- Every original provider and constructor remains in this exact graph. A
composed operation has no representative function name or invented signature.
Only repeated relevance rows are shared; every original route remains available
in graph/original and in the retained row index. -/
structure Operation (sources : Sources) (owner : String) (tokens : List LocatedToken) where
  description : OperationDescription.Description
  graph : StaticOperation.CheckedGraph sources (.source owner) description
  original : OperationOrigin sources owner tokens description graph
  relevance : SourceRows.Retained (operationSourceRows graph original)

def Operation.providers {sources owner tokens} (operation : Operation sources owner tokens) :
    List (StaticOperation.Provider sources) := operation.graph.providers

def Operation.rawSourceRows {sources owner tokens} (operation : Operation sources owner tokens) :
    List SourceRows.Row := operationSourceRows operation.graph operation.original

def Operation.sourceRows {sources owner tokens} (operation : Operation sources owner tokens) :
    List SourceRows.Row := operation.relevance.rows

theorem Operation.sourceRows_canonical {sources owner tokens} (operation : Operation sources owner tokens) :
    operation.sourceRows = operation.rawSourceRows.eraseDups := operation.relevance.canonical

theorem Operation.sourceRows_members {sources owner tokens} (operation : Operation sources owner tokens)
    (row : SourceRows.Row) : row ∈ operation.sourceRows ↔ row ∈ operation.rawSourceRows :=
  operation.relevance.members row

private def retainOperation {sources owner tokens description}
    (graph : StaticOperation.CheckedGraph sources (.source owner) description)
    (original : OperationOrigin sources owner tokens description graph) : WorkM (Operation sources owner tokens) := do
  let relevance ← SourceRows.read (operationSourceRows graph original)
  pure ⟨description,graph,original,relevance⟩

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
  let operation : Operation sources owner written.operation ← retainOperation graph (.named selected rfl)
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
        retainOperation graph (.primitive scope candidate kind selected target rfl)
      | none => do
        let source ← SourceOperation.read signature.toChecked naturals.helpers.val naturals.environment scope written.operation naturals.generic
          none (some signature.supply)
        retainOperation source.graph (.source name signature naturals scope source rfl HEq.rfl)
    | .error _ => do
      let source ← SourceOperation.read signature.toChecked naturals.helpers.val naturals.environment scope written.operation naturals.generic
        none (some signature.supply)
      retainOperation source.graph (.source name signature naturals scope source rfl HEq.rfl)
  if input : operation.graph.root.input = target then
    if output : operation.graph.root.output = target then
      if effect : operation.graph.root.effect = .unitary then
        if controlled : operation.graph.root.paths.controllable = true then
          return ⟨written,label.val,by with_reducible exact label.property,operation,input,output,effect,controlled⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- The same operation/body contract for an original ordinary or mixed caller.
Its exact instantiation and argument receipts replace no source signature. -/
def readArmWithInstantiation {sources owner name}
    (original : OrdinarySignature.Original sources owner name) (instantiation : StaticInstantiation.Checked original)
    (supply : StaticOperation.Supply instantiation)
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
        retainOperation graph (.primitive scope candidate kind selected target rfl)
      | none => do
        let source ← SourceOperation.readWithInstantiation instantiation naturals.helpers.val naturals.environment
          scope written.operation naturals.generic none (some supply)
        retainOperation source.graph (.instantiated name original instantiation supply naturals scope source rfl HEq.rfl)
    | .error _ => do
      let source ← SourceOperation.readWithInstantiation instantiation naturals.helpers.val naturals.environment
        scope written.operation naturals.generic none (some supply)
      retainOperation source.graph (.instantiated name original instantiation supply naturals scope source rfl HEq.rfl)
  if input : operation.graph.root.input = target then
    if output : operation.graph.root.output = target then
      if effect : operation.graph.root.effect = .unitary then
        if controlled : operation.graph.root.paths.controllable = true then
          pure ⟨written,label.val,by with_reducible exact label.property,operation,input,output,effect,controlled⟩
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
  selectorKind : QuantumMatch.acceptsSelector site.parsed selector = true

/-- Reuse the exact already-read caller; all arm, source-type and partition
checks remain in this shared continuation. No alternate source body is supplied. -/
def readArms {sources owner name}
    (originalCaller : OrdinarySignature.Original sources owner name)
    (offset : Nat) (selector target : Basis) :
    WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite originalCaller offset
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
  let original ← NaturalAffine.witness (SourceTypes.checkMany sources [selector,target])
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let arms ← site.parsed.arms.mapM (readArm sources owner selector target)
  exactWork (Exact.charge (256*(site.parsed.tokens.length+1)*(arms.length+1)))
  if same : arms.map (·.written) = site.parsed.arms then
    if complete : partition layout.val.labels.length arms = true then
      return ⟨site,layout.val,by with_reducible exact original.property,
        by obtain ⟨before,after,ran⟩ := layout.property
           exact FiniteCarrier.read_reference _ _ _ _ ran,
        arms,same,complete,selectorKind.down⟩
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
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
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
        arms,same,complete,selectorKind.down⟩
    else throw .request
  else throw .request

def readArmsWithInstantiation {sources owner name}
    (originalCaller : OrdinarySignature.Original sources owner name)
    (instantiation : StaticInstantiation.Checked originalCaller) (supply : StaticOperation.Supply instantiation)
    (offset : Nat) (selector target : Basis)
    (eventNaturals : Option (PhaseApplication.Naturals sources) := none)
    (eventScope : List String := []) : WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite originalCaller offset
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
  let original ← NaturalAffine.witness (SourceTypes.checkMany sources [selector,target])
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let naturals ← match eventNaturals with
    | some naturals => pure naturals
    | none => PhaseApplication.prepareWithInstantiation instantiation
  let scope := instantiation.names ++ eventScope
  let arms ← site.parsed.arms.mapM
    (readArmWithInstantiation originalCaller instantiation supply naturals scope selector target)
  exactWork (Exact.charge (256*(site.parsed.tokens.length+1)*(arms.length+1)))
  if same : arms.map (·.written) = site.parsed.arms then
    if complete : partition layout.val.labels.length arms = true then
      pure ⟨site,layout.val,by with_reducible exact original.property,
        by obtain ⟨before,after,ran⟩ := layout.property
           exact FiniteCarrier.read_reference _ _ _ _ ran,
        arms,same,complete,selectorKind.down⟩
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.QuantumArms
