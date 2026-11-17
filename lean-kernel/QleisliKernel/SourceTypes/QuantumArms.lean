import QleisliKernel.SourceTypes.SourceRuntimeTrace
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

private def readArmUsing {sources owner name} {State : Type}
    (original : OrdinarySignature.Original sources owner name) (instantiation : StaticInstantiation.Checked original)
    (supply : StaticOperation.Supply instantiation)
    (naturals : PhaseApplication.Naturals sources) (scope : List String)
    (selector target : Basis) (written : QuantumMatch.Arm)
    (readSource : (tokens : List LocatedToken) → State →
      WorkM (SourceOperation.CheckedWithInstantiation instantiation naturals.helpers.val
        naturals.environment scope tokens × State)) (state : State) :
    WorkM (BoundArm sources owner selector target × State) := do
  let label ← NaturalAffine.witness (readLabel sources owner selector written.label)
  let named : WorkM (Operation sources owner written.operation × State) := do
    let (source,next) ← readSource written.operation state
    let operation ← retainOperation source.graph (.instantiated name original instantiation supply naturals scope source rfl HEq.rfl)
    return (operation,next)
  let (operation,next) ← match CallName.readName written.operation with
    | .ok _ => do
      let candidate ← CallName.read sources owner scope written.operation
      match selected : primitiveKind candidate with
      | some kind =>
        let description : OperationDescription.Description := ⟨[.primitive kind target],0⟩
        let graph ← StaticOperation.check sources (.source owner) description
        let operation ← retainOperation graph (.primitive scope candidate kind selected target rfl)
        pure (operation,state)
      | none => named
    | .error _ => named
  if input : operation.graph.root.input = target then
    if output : operation.graph.root.output = target then
      if effect : operation.graph.root.effect = .unitary then
        if controlled : operation.graph.root.paths.controllable = true then
          return (⟨written,label.val,by with_reducible exact label.property,operation,input,output,effect,controlled⟩,next)
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Resolve an original arm under its exact instantiated caller. -/
def readArmWithInstantiation {sources owner name}
    (original : OrdinarySignature.Original sources owner name) (instantiation : StaticInstantiation.Checked original)
    (supply : StaticOperation.Supply instantiation)
    (naturals : PhaseApplication.Naturals sources) (scope : List String)
    (selector target : Basis) (written : QuantumMatch.Arm) :
    WorkM (BoundArm sources owner selector target) := do
  let (arm,_) ← readArmUsing original instantiation supply naturals scope selector target written
    (fun tokens (_ : Unit) => do
      let source ← SourceOperation.readWithInstantiation instantiation naturals.helpers.val naturals.environment
        scope tokens naturals.generic none (some supply)
      return (source,())) ()
  return arm

def BoundArm.sourceRows {sources owner selector target} (arm : BoundArm sources owner selector target) :
    List (String × String) :=
  arm.label.sourceRows ++ arm.operation.sourceRows

def partitionWith {Arm : Type} (ordinal : Arm → Nat) (count : Nat) (arms : List Arm) : Bool :=
  let labels := arms.map ordinal
  labels.length == count && labels.all (· < count) && labels.eraseDups.length == labels.length

def partition {sources owner selector target} (count : Nat) (arms : List (BoundArm sources owner selector target)) : Bool :=
  partitionWith (·.label.ordinal) count arms

/-- Original arm headers and label coverage, not an enclosing lexical-scope
judgment. Current native admission also requires QuantumSequence.read. -/
structure TableWith (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis)
    (Arm : Type) (written : Arm → QuantumMatch.Arm) (ordinal : Arm → Nat) where
  site : QuantumMatch.Site sources owner name offset
  layout : Semantics.FiniteCarrier.Layout
  originalTypes : SourceTypes.ManyRead sources [selector,target]
  selectorLayout : Semantics.FiniteCarrier.layout selector = some layout
  arms : List Arm
  originalArms : arms.map written = site.parsed.arms
  complete : partitionWith ordinal layout.labels.length arms = true
  selectorKind : QuantumMatch.acceptsSelector site.parsed selector = true

abbrev Table (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) :=
  TableWith sources owner name offset selector target (BoundArm sources owner selector target)
    BoundArm.written (·.label.ordinal)

private def finishTable {sources owner name offset selector target Arm written ordinal}
    (site : QuantumMatch.Site sources owner name offset)
    (originalTypes : SourceTypes.ManyRead sources [selector,target])
    (layout : Semantics.FiniteCarrier.Layout)
    (selectorLayout : Semantics.FiniteCarrier.layout selector = some layout)
    (selectorKind : QuantumMatch.acceptsSelector site.parsed selector = true)
    (arms : List Arm) : WorkM (TableWith sources owner name offset selector target Arm written ordinal) := do
  exactWork (Exact.charge (256*(site.parsed.tokens.length+1)*(arms.length+1)))
  if same : arms.map written = site.parsed.arms then
    if complete : partitionWith ordinal layout.labels.length arms = true then
      return ⟨site,layout,originalTypes,selectorLayout,arms,same,complete,selectorKind⟩
    else throw .request
  else throw .request

/-- Reuse the exact already-read caller; all arm, source-type and partition
checks remain in this shared continuation. No alternate source body is supplied. -/
def readArms {sources owner name}
    (originalCaller : OrdinarySignature.Original sources owner name)
    (offset : Nat) (selector target : Basis) :
    WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite originalCaller offset
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
  let original ← SourceTypes.readMany sources [selector,target]
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let arms ← site.parsed.arms.mapM (readArm sources owner selector target)
  finishTable site original layout.val
    (by obtain ⟨before,after,ran⟩ := layout.property; exact FiniteCarrier.read_reference _ _ _ _ ran)
    selectorKind.down arms

def read (sources : Sources) (owner name : String) (offset : Nat) (selector target : Basis) :
    WorkM (Table sources owner name offset selector target) := do
  let original ← OrdinarySignature.readOriginal sources owner name
  readArms original offset selector target

/-- A standalone signature lookup must recover the original lexical names at
the requested event, including binders consumed before the selection. -/
private def scopeAt {sources owner name} (signature : QuantumSignature.Checked sources owner name)
    (offset : Nat) : WorkM (List String) := do
  let runtime ← SourceRuntimeContext.fromQuantumCore signature.toChecked signature.context signature.operations
  let body ← SourceRuntimeTrace.readBodyWithSignature runtime.signature
  let some scope := body.checked.events.findSome? (fun
    | .selection event => if event.parsed.keyword.span.startByte == offset then some event.scope else none
    | _ => none) | throw .request
  return scope

/-- Use the selected caller's header actuals and original lexical scope.
Complete traversal supplies local aliases. A standalone lookup recovers the
scope at this byte offset from the same instantiated caller body. -/
def readArmsWithSignature {sources owner name}
    (signature : QuantumSignature.Checked sources owner name)
    (offset : Nat) (selector target : Basis)
    (eventNaturals : Option (PhaseApplication.Naturals sources) := none)
    (eventScope : Option (List String) := none) : WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite signature.original offset
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
  let original ← SourceTypes.readMany sources [selector,target]
    (signature.operations.catalogue.map (·.helpers))
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let naturals ← match eventNaturals with
    | some naturals => pure naturals
    | none => PhaseApplication.prepareWithSignature signature
  let locals ← match eventScope with | some names => pure names | none => scopeAt signature offset
  let scope := signature.staticNames ++ locals
  let arms ← site.parsed.arms.mapM (readArmWithSignature signature naturals scope selector target)
  finishTable site original layout.val
    (by obtain ⟨before,after,ran⟩ := layout.property; exact FiniteCarrier.read_reference _ _ _ _ ran)
    selectorKind.down arms

private def readArmRetainingGraphs {sources owner name}
    (original : OrdinarySignature.Original sources owner name)
    (instantiation : StaticInstantiation.Checked original) (supply : StaticOperation.Supply instantiation)
    (naturals : PhaseApplication.Naturals sources) (scope : List String)
    (selector target : Basis) (written : QuantumMatch.Arm) :
    StateT (List (StaticOperation.SuppliedGraphEntry supply)) WorkM (BoundArm sources owner selector target) :=
  fun previous => readArmUsing original instantiation supply naturals scope selector target written
    (fun tokens => SourceOperation.readWithSharedGraphs instantiation naturals.helpers.val
      naturals.environment scope tokens naturals.generic supply) previous

def readArmsWithInstantiation {sources owner name}
    (originalCaller : OrdinarySignature.Original sources owner name)
    (instantiation : StaticInstantiation.Checked originalCaller) (supply : StaticOperation.Supply instantiation)
    (offset : Nat) (selector target : Basis)
    (eventNaturals : Option (PhaseApplication.Naturals sources))
    (eventScope : List String) : WorkM (Table sources owner name offset selector target) := do
  let site ← QuantumMatch.readSite originalCaller offset
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
  let original ← SourceTypes.readMany sources [selector,target]
    (supply.arguments.catalogue.map (·.helpers))
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let naturals ← match eventNaturals with
    | some naturals => pure naturals
    | none => PhaseApplication.prepareWithInstantiation instantiation
  let scope := instantiation.names ++ eventScope
  let readArm := readArmRetainingGraphs originalCaller instantiation supply naturals scope selector target
  let (arms,_) ← (site.parsed.arms.mapM readArm).run []
  finishTable site original layout.val
    (by obtain ⟨before,after,ran⟩ := layout.property; exact FiniteCarrier.read_reference _ _ _ _ ran)
    selectorKind.down arms

inductive RuntimeArm {sources owner} (event : SourceRuntimeContext.SelectionEvent sources owner)
    (selector target : Basis) where
  | operation (arm : BoundArm sources owner selector target)
  | inline {index : Nat} (arm : SourceRuntimeTrace.InlineArmBody event index)
      (replayed : ∃ before after,
        (SourceRuntimeTrace.readInlineArmBody event index).run before = (.ok arm,after))
      (ports : event.selector.basis = selector ∧ event.target.basis = target)
      (label : Label sources)
      (originalLabel : ∃ before after,
        (readLabel sources owner selector (event.parsed.arms.get ⟨index,arm.armIndex⟩).label).run before = (.ok label,after))

def RuntimeArm.written {sources owner event selector target} :
    @RuntimeArm sources owner event selector target → QuantumMatch.Arm
  | .operation arm => arm.written
  | .inline arm .. => event.parsed.arms.get ⟨_,arm.armIndex⟩

def RuntimeArm.ordinal {sources owner event selector target} :
    @RuntimeArm sources owner event selector target → Nat
  | .operation arm => arm.label.ordinal
  | .inline _ _ _ label _ => label.ordinal

def RuntimeArm.sourceRows {sources owner event selector target} :
    @RuntimeArm sources owner event selector target → List SourceRows.Row
  | .operation arm => arm.sourceRows
  | .inline arm _ _ label _ => label.sourceRows ++ arm.result.staticRows

abbrev RuntimeTable {sources owner} (event : SourceRuntimeContext.SelectionEvent sources owner)
    (offset : Nat) (selector target : Basis) :=
  TableWith sources owner event.callerName offset selector target (RuntimeArm event selector target)
    RuntimeArm.written RuntimeArm.ordinal

/-- Read every arm of the retained runtime event in written order. The table
shares source, type, and label coverage checks with the static-operation table. -/
def readRuntimeArms {sources owner} (event : SourceRuntimeContext.SelectionEvent sources owner)
    (offset : Nat) (selector target : Basis) : WorkM (RuntimeTable event offset selector target) := do
  guard (offset == event.parsed.keyword.span.startByte) .request
  let caller := event.signature.original
  let instantiation := event.signature.instantiation
  let supply := event.signature.supply
  let site ← QuantumMatch.readSite caller offset
  guard (site.parsed == event.parsed) .request
  let selectorKind ← QuantumMatch.checkSelector site.parsed selector
  let originalTypes ← SourceTypes.readMany sources [selector,target] (supply.arguments.catalogue.map (·.helpers))
  let layout ← NaturalAffine.witness (FiniteCarrier.read selector)
  let scope := instantiation.names ++ event.scope
  if ports : event.selector.basis = selector ∧ event.target.basis = target then
    let readArm (index : Fin site.parsed.arms.length) :
        StateT (List (StaticOperation.SuppliedGraphEntry supply)) WorkM (RuntimeArm event selector target) :=
      fun previous => do
        let written := site.parsed.arms[index]
        if written.operation.head?.map (·.text) == some "{" then
          let arm ← NaturalAffine.witness (SourceRuntimeTrace.readInlineArmBody event index.val)
          let label ← NaturalAffine.witness
            (readLabel sources owner selector (event.parsed.arms.get ⟨index.val,arm.val.armIndex⟩).label)
          return (.inline arm.val (by with_reducible exact arm.property) ports label.val
            (by with_reducible exact label.property),previous)
        else
          let (arm,next) ← (readArmRetainingGraphs caller instantiation supply event.naturals scope selector target written).run previous
          return (.operation arm,next)
    let (arms,_) ← ((List.finRange site.parsed.arms.length).mapM readArm).run []
    finishTable site originalTypes layout.val
      (by obtain ⟨before,after,ran⟩ := layout.property; exact FiniteCarrier.read_reference _ _ _ _ ran)
      selectorKind.down arms
  else throw .request

end QleisliKernel.SourceTypes.QuantumArms
