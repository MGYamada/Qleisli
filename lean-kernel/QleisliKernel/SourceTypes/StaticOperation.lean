import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.SourceTypes.StaticKinds
import QleisliKernel.SourceTypes.SourceMeaning
import QleisliKernel.SourceTypes.SymbolicTypes

/-! Checked topological operation descriptions and original formal bindings.
Paths below describe implementation obligations. Fresh original provider-body,
inverse/control and literal constructed-body equations remain mandatory at the
enclosing native graph gate; this metadata issues no operation or runtime handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticOperation
open Finite Semantics.FiniteCarrier Semantics.Raw OperationDescription

inductive Context where
  | external
  | source (moduleName : String)
  deriving BEq, DecidableEq, Repr

def Context.visible (context : Context) (owner : String) (isPublic : Bool) : Bool :=
  isPublic || match context with | .external => false | .source caller => owner == caller

def Context.internal (context : Context) (owner : String) : Bool :=
  match context with | .external => false | .source caller => owner == caller

structure Paths where
  applicable : Bool
  adjointable : Bool
  controllable : Bool
  deriving BEq, DecidableEq, Repr

def Paths.meet (left right : Paths) : Paths :=
  ⟨left.applicable && right.applicable,left.adjointable && right.adjointable,
    left.controllable && right.controllable⟩

private def joinEffect : Effect → Effect → Effect
  | .observe,_ | _,.observe => .observe
  | .iso,_ | _,.iso => .iso
  | .unitary,.unitary => .unitary

structure Provider (sources : Sources) where
  moduleName : String
  declarationName : String
  signature : QuantumSignatureCore.Checked sources moduleName declarationName
  expectedEffect : Effect
  internalInference : Bool

structure Result (sources : Sources) where
  input : Basis
  output : Basis
  effect : Effect
  paths : Paths
  provider : Option (Provider sources) := none
  formal : Option (Provider sources) := none
  kindRows : List (String × String) := []
  requirements : List (Nat × SourceMeaning.Request sources) := []

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

def ports (tokens : List String) : Except String (List String × List String) := do
  let parsed ← OperationPorts.read tokens
  return (parsed.input,parsed.output)

structure FormalContract (sources : Sources) where
  input : Basis
  output : Basis
  originalPorts : SymbolicTypes.Ports sources
  effect : Effect
  requirement : Option (SourceMeaning.Request sources)
  symbolic : Option (SymbolicTypes.SomeRefinement sources)

/-- The Meaning query belongs to the original kind's module and preceding
scope. Closing Basis actuals cannot replace either exact Meaning port. The
returned request still needs an independent equation against the actual body. -/
def formalContract {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) (formal : StaticHeaders.Formal) :
    WorkM (FormalContract sources) := do
  let .operation tokens := formal.kind | throw .request
  exactWork (Exact.charge (32*(tokens.length+1)*(environment.numeric.original.header.formals.length+1)))
  let parsed ← adapt (OperationPorts.read tokens)
  let input ← StaticKinds.readType environment formal.ordinal parsed.input
  let output ← StaticKinds.readType environment formal.ordinal parsed.output
  let scope := (environment.numeric.original.header.formals.filter (·.ordinal < formal.ordinal)).map (·.name)
  let state : GenericLexicalNatural.SomeEnvironment sources :=
    ⟨owner,name,environment.numeric,GenericLexicalNatural.initial environment.numeric⟩
  let originalPorts ← SymbolicTypes.readPorts state scope formal.ordinal parsed.input parsed.output
  let adjointable := environment.numeric.original.header.access.contains (.adjointable,formal.name)
  let controllable := environment.numeric.original.header.access.contains (.controllable,formal.name)
  guard (!controllable || originalPorts.same.isSome) .request
  let effect := if originalPorts.same.isSome || adjointable || controllable then Effect.unitary else .iso
  let (requirement,symbolic) ← match parsed.meaning with
    | none => pure (none,none)
    | some tokens => do
      let selected ← SourceMeaning.select sources owner scope tokens
      let symbolic ← SymbolicTypes.checkRefinement state scope formal.ordinal parsed.input parsed.output
        selected.meaning.graph.input selected.meaning.graph.output
      guard (selected.meaning.graph.input == input.basis && selected.meaning.graph.output == output.basis) .request
      pure (some selected.request,some (⟨state,scope,formal.ordinal,parsed.input,parsed.output,
        selected.meaning.graph.input,selected.meaning.graph.output,symbolic⟩ : SymbolicTypes.SomeRefinement sources))
  return ⟨input.basis,output.basis,originalPorts,effect,requirement,symbolic⟩

def formalPorts {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) (formal : StaticHeaders.Formal) :
    WorkM (Basis × Basis) := do
  let contract ← formalContract environment formal
  return (contract.input,contract.output)

def requirementsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) :
    WorkM (List (String × SourceMeaning.Request sources)) := do
  match instantiation with
  | .closed _ => pure []
  | .static _ environment _ =>
    let rows ← environment.numeric.original.header.formals.mapM fun formal => do
      match formal.kind with
      | .operation _ =>
        let contract ← formalContract environment formal
        pure (contract.requirement.toList.map fun request => (formal.name,request))
      | _ => pure []
    pure rows.flatten

private def indexedRequirements {sources : Sources} (operations : List (String × Nat))
    (requirements : List (String × SourceMeaning.Request sources)) :
    WorkM (List (Nat × SourceMeaning.Request sources)) := requirements.mapM fun (name,request) => do
  let some (_,index) := operations.find? (·.1 == name) | throw .request
  pure (index,request)

def kindRowsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) : WorkM (List (String × String)) := do
  match instantiation with
  | .closed _ => pure []
  | .static _ environment _ =>
    let rows ← environment.numeric.original.header.formals.mapM fun formal => do
      match formal.kind with
      | .operation tokens =>
        let (input,output) ← adapt (ports tokens)
        return (← StaticKinds.readRows environment formal.ordinal input) ++
          (← StaticKinds.readRows environment formal.ordinal output)
      | _ => pure []
    pure rows.flatten

private def required (access : List (StaticHeaders.Access × String)) (name : String) : Paths :=
  ⟨access.contains (.applicable,name),access.contains (.adjointable,name),access.contains (.controllable,name)⟩

private def satisfies (actual required : Paths) : Bool :=
  (!required.applicable || actual.applicable) && (!required.adjointable || actual.adjointable) &&
    (!required.controllable || actual.controllable)

private def namedResults {sources : Sources} (arguments : List (String × Description))
    (results : List (String × Result sources)) : Bool :=
  arguments.map (·.1) == results.map (·.1)

structure Bindings (sources : Sources) where
  contracts : List (String × FormalContract sources)

def Bindings.requirements {sources : Sources} (bindings : Bindings sources) : List (String × SourceMeaning.Request sources) :=
  bindings.contracts.flatMap fun (name,contract) => contract.requirement.toList.map (name,·)

/-- Check every original operation formal and actual, including unused ones.
The signature core supplies original mixed-kind identities and ordered Nat
premises; equal width cannot replace either exact operation port. -/
def bindArgumentsWithContracts {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (results : List (String × Result sources)) : WorkM (Bindings sources) := do
  let arguments := instantiation.arguments
  exactWork (Exact.charge (32*(results.length+1)*(original.occurrence.header.length+1)))
  guard (namedResults arguments.operations results) .request
  match instantiation with
  | .closed _ =>
    guard results.isEmpty .request
    pure ⟨[]⟩
  | .static _ environment _ =>
    let formals := environment.numeric.original.header.formals.filter fun formal =>
      match formal.kind with | .operation _ => true | _ => false
    guard (formals.length == results.length) .request
    let contracts ← formals.mapM fun formal => do
      let some (_,actual) := results.find? (·.1 == formal.name) | throw .request
      let contract ← formalContract environment formal
      guard (actual.input == contract.input && actual.output == contract.output &&
        actual.effect != .observe && (contract.effect != .unitary || actual.effect == .unitary) &&
        satisfies actual.paths (required environment.numeric.original.header.access formal.name)) .request
      pure (formal.name,contract)
    pure ⟨contracts⟩

def bindArgumentsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (results : List (String × Result sources)) : WorkM Unit :=
  bindArgumentsWithContracts instantiation results >>= fun _ => pure ()

def bindArgumentsWithRequirements {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (results : List (String × Result sources)) : WorkM (List (String × SourceMeaning.Request sources)) :=
  bindArgumentsWithContracts instantiation results >>= fun bindings => pure bindings.requirements

private theorem bindingProjection {α β : Type} (action : WorkM α) (projection : α → β)
    (value : α) (before after : Nat) (ran : action.run before = (.ok value,after)) :
    (action >>= fun value => pure (projection value)).run before = (.ok (projection value),after) := by
  rw [Finite.bind_run,ran]
  rfl

def bindArguments {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name)
    (results : List (String × Result sources)) : WorkM Unit :=
  bindArgumentsWithInstantiation signature.instantiation results

private def result {sources : Sources} (input output : Basis) (effect : Effect) (paths : Paths)
    (provider : Option (Provider sources) := none) (formal : Option (Provider sources) := none)
    (kindRows : List (String × String) := [])
    (requirements : List (Nat × SourceMeaning.Request sources) := []) : WorkM (Result sources) := do
  let _ ← FiniteCarrier.read input
  let _ ← FiniteCarrier.read output
  pure ⟨input,output,effect,paths,provider,formal,kindRows,requirements⟩

private def child {sources : Sources} (previous : List (Result sources)) (index : Nat) : WorkM (Result sources) :=
  match previous[index]? with | none => throw .request | some result => pure result

private def readProvider (sources : Sources) (context : Context) (description : Description)
    (previous : List (Result sources)) (owner name : String) (bases : List (String × Basis))
    (naturals : List (String × Nat)) (operations : List (String × Nat)) : WorkM (Result sources) := do
  let actuals ← operations.mapM fun (name,index) => do
    let some description := description.select index | throw .request
    return (name,description)
  let signature ← QuantumSignatureCore.prepareWithArguments sources owner name {bases,naturals,operations := actuals}
  guard (context.visible owner signature.original.declaration.isPublic) .request
  let originalResults ← operations.mapM fun (name,index) => do return (name,← child previous index)
  let bindings ← bindArgumentsWithContracts signature.instantiation originalResults
  let kindRows ← kindRowsWithInstantiation signature.instantiation
  let staticRows ← StaticInstantiation.readRowsWithTypes signature.instantiation (signature.inputs ++ signature.outputs)
  let kindRows := kindRows ++ staticRows
  let requirements ← indexedRequirements operations bindings.requirements
  let [input] := signature.inputs | throw .request
  let [output] := signature.outputs | throw .request
  guard (match signature.parts with | .owner _ => true | _ => false) .request
  let internal := context.internal owner
  -- Internal purity is a deferred body obligation, not a fact inferred from
  -- an annotation. The native body gate must prove this bound for each leaf.
  -- External/host selection always retains the public effect unchanged.
  let visible := if internal then none else signature.original.parsedHeader.effect
  guard (visible != some .observe) .request
  let endomorphic := input == output
  let reversible := visible == none || visible == some .unitary
  let reverseArgs := originalResults.all fun (_,actual) => actual.paths.applicable && actual.paths.adjointable
  let controlArgs := originalResults.all fun (_,actual) =>
    actual.paths.applicable && actual.paths.adjointable && actual.paths.controllable
  let expected := visible.getD (if endomorphic then .unitary else .iso)
  result input output expected
    ⟨true,reversible && reverseArgs,reversible && endomorphic && controlArgs⟩
    (some ⟨owner,name,signature,expected,internal⟩) none kindRows requirements

def readNode (sources : Sources) (context : Context) (description : Description)
    (previous : List (Result sources)) (node : Node) : WorkM (Result sources) := do
  match node with
  | .primitive kind target =>
    guard (context != .external) .request
    guard (kind == .globalPhaseEighth || target == [.bit]) .request
    result target target .unitary ⟨true,true,true⟩
  | .provider owner name bases naturals operations =>
    readProvider sources context description previous owner name bases naturals operations
  | .formal owner name bases naturals operations ordinal =>
    let actuals ← operations.mapM fun (name,index) => do
      let some description := description.select index | throw .request
      return (name,description)
    let signature ← QuantumSignatureCore.prepareWithArguments sources owner name {bases,naturals,operations := actuals}
    let originalResults ← operations.mapM fun (name,index) => do return (name,← child previous index)
    let bindings ← bindArgumentsWithContracts signature.instantiation originalResults
    let kindRows ← kindRowsWithInstantiation signature.instantiation
    let staticRows ← StaticInstantiation.readRowsWithTypes signature.instantiation (signature.inputs ++ signature.outputs)
    let kindRows := kindRows ++ staticRows
    let requirements ← indexedRequirements operations bindings.requirements
    match signature.instantiation with
    | .closed _ => throw .request
    | .static _ environment _ =>
      let some formal := environment.numeric.original.header.formals[ordinal]? | throw .request
      guard (formal.ordinal == ordinal) .request
      let some (_,contract) := bindings.contracts.find? (·.1 == formal.name) | throw .request
      let input := contract.input
      let output := contract.output
      let some (_,actual) := originalResults.find? (·.1 == formal.name) | throw .request
      let paths := actual.paths.meet (required environment.numeric.original.header.access formal.name)
      let effect := contract.effect
      result input output effect paths none (some ⟨owner,name,signature,effect,false⟩) kindRows requirements
  | .inverse index =>
    let c ← child previous index
    guard c.paths.adjointable .request
    result c.output c.input c.effect ⟨c.paths.adjointable,c.paths.applicable,c.paths.controllable⟩
  | .controlled index =>
    let c ← child previous index
    guard (c.input == c.output) .request
    result (.pair :: .bit :: c.input) (.pair :: .bit :: c.output) .unitary
      ⟨c.paths.controllable,c.paths.controllable,c.paths.controllable⟩
  | .power index count =>
    let c ← child previous index
    guard (c.input == c.output && count ≤ 4294967295) .request
    result c.input c.output c.effect c.paths
  | .thenOp left right =>
    let a ← child previous left
    let b ← child previous right
    guard (a.output == b.input) .request
    result a.input b.output (joinEffect a.effect b.effect) (a.paths.meet b.paths)
  | .tensor left right =>
    let a ← child previous left
    let b ← child previous right
    result (.pair :: a.input ++ b.input) (.pair :: a.output ++ b.output)
      (joinEffect a.effect b.effect) (a.paths.meet b.paths)
  | .conjugate outer middle =>
    let a ← child previous outer
    let b ← child previous middle
    guard (b.input == a.input && b.output == a.input) .request
    result a.output a.output (joinEffect a.effect b.effect)
      ⟨a.paths.applicable && a.paths.adjointable && b.paths.applicable,
        a.paths.applicable && a.paths.adjointable && b.paths.adjointable,
        a.paths.applicable && a.paths.adjointable && b.paths.controllable⟩
  | .requested index owner name =>
    let c ← child previous index
    let some operand := description.nodes[index]? | throw .request
    -- checked_op accepts an original name, never an explicitly specialized
    -- provider or a constructed operand. An original formal keeps its full
    -- caller instance because those fields authenticate the lexical binding.
    guard (match operand with
      | .provider _ _ bases naturals operations => bases.isEmpty && naturals.isEmpty && operations.isEmpty
      | .formal .. => true
      | _ => false) .request
    let caller := match context with | .external => none | .source caller => some caller
    let requirement ← SourceMeaning.request sources caller owner name
    guard (requirement.meaning.graph.input == c.input && requirement.meaning.graph.output == c.output) .request
    result c.input c.output c.effect c.paths none none [] [(index,requirement)]

def readOccurrences (description : Description) : WorkM (List Nat) := do
  -- Reserve both capped topological scans before entering their pure readers.
  exactWork (Exact.charge (64*(description.nodes.length+1)^2))
  let count ← adapt description.treeSize
  exactWork (Exact.charge (8*(count+1)^2))
  adapt description.occurrences

def readNodes (sources : Sources) (context : Context) (description : Description) :
    WorkM (List (Result sources)) := do
  guard description.complete .request
  let _ ← readOccurrences description
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  exactWork (Exact.charge (64*(bytes+1)*(description.nodes.length+1)^2))
  description.nodes.foldlM (fun previous node => do
    let next ← readNode sources context description previous node
    pure (previous ++ [next])) []

structure GraphData (sources : Sources) where
  description : Description
  results : List (Result sources)
  contexts : List Context
  count : results.length = description.nodes.length
  contextCount : contexts.length = description.nodes.length
  complete : description.complete = true
  root : Result sources
  selected : results[description.root]? = some root

/-- A complete original argument receipt before its recursive graph proofs are
attached. Exact descriptor order and the checked formal binding are retained. -/
structure SupplyData (sources : Sources) where
  owner : String
  name : String
  original : OrdinarySignature.Original sources owner name
  instantiation : StaticInstantiation.Checked original
  context : Context
  actuals : List (String × GraphData sources)
  ordered : actuals.map (fun (name,graph) => (name,graph.description)) = instantiation.arguments.operations
  bound : ∃ before after,
    (bindArgumentsWithInstantiation instantiation (actuals.map fun (name,graph) => (name,graph.root))).run before = (.ok (),after)

private def remapResult {sources : Sources} (mapping : Nat → Option Nat) (value : Result sources) :
    Option (Result sources) := do
  let requirements ← value.requirements.mapM fun (index,request) => do
    let index ← mapping index
    pure (index,request)
  pure {value with requirements}

def selectData {sources : Sources} (data : GraphData sources) (index : Nat) : Option (GraphData sources) := do
  let (indices,description) ← data.description.selection index
  let results ← indices.mapM fun sourceIndex => do
    let value ← data.results[sourceIndex]?
    remapResult (fun old => if indices.contains old then some (indices.idxOf old) else none) value
  let contexts ← indices.mapM (data.contexts[·]?)
  if count : results.length = description.nodes.length then
    if contextCount : contexts.length = description.nodes.length then
      if complete : description.complete = true then
        match selected : results[description.root]? with
        | none => none
        | some root => some ⟨description,results,contexts,count,contextCount,complete,root,selected⟩
      else none
    else none
  else none

private structure Borrowed where
  destination : Nat
  actual : Nat
  sourceIndex : Nat
  occurrence : Nat

private def insertBorrowed (previous : List Borrowed) (next : Borrowed) : WorkM (List Borrowed) := do
  exactWork (Exact.charge (previous.length+1))
  match previous.find? (·.destination == next.destination) with
  | none => pure (previous ++ [next])
  | some existing =>
    guard (existing.actual == next.actual && existing.sourceIndex == next.sourceIndex &&
      existing.occurrence == next.occurrence) .request
    pure previous

private def originalFormal {sources : Sources} (supply : SupplyData sources) (description : Description) (node : Node) :
    WorkM (Option (List (String × Nat))) := do
  match node with
  | .formal owner name bases naturals operations ordinal =>
    guard (owner == supply.owner && name == supply.name &&
      bases == supply.instantiation.arguments.bases && naturals == supply.instantiation.arguments.naturals) .request
    let actuals ← operations.mapM fun (name,index) => do
      let some child := description.select index | throw .request
      pure (name,child)
    guard (actuals == supply.instantiation.arguments.operations) .request
    match supply.instantiation with
    | .closed _ => throw .request
    | .static _ environment _ =>
      let some formal := environment.numeric.original.header.formals[ordinal]? | throw .request
      guard (formal.ordinal == ordinal && match formal.kind with | .operation _ => true | _ => false) .request
      pure (some operations)
  | _ => pure none

private def borrowPlan {sources : Sources} (supply : SupplyData sources) (description : Description) : WorkM (List Borrowed) := do
  exactWork (Exact.charge (16*(description.nodes.length+1)^2))
  description.nodes.zipIdx.reverse.foldlM (fun plan (node,occurrence) => do
    if plan.any (·.destination == occurrence) then pure plan else
    match node with
    | .formal owner name .. =>
      if owner != supply.owner || name != supply.name then pure plan else
        let some operations ← originalFormal supply description node | throw .request
        operations.foldlM (fun plan (name,index) => do
          let some actual := (supply.actuals.zipIdx).find? (fun (actual,_) => actual.1 == name) | throw .request
          let some (indices,selected) := description.selection index | throw .request
          guard (selected == actual.1.2.description && indices.length == actual.1.2.results.length) .request
          (indices.zipIdx).foldlM (fun plan (destination,sourceIndex) =>
            insertBorrowed plan ⟨destination,actual.2,sourceIndex,occurrence⟩) plan) plan
    | _ => pure plan) []

private def borrowedValue {sources : Sources} (supply : SupplyData sources) (description : Description)
    (plan : List Borrowed) (entry : Borrowed) : WorkM (Result sources × Context) := do
  let some (_,actual) := supply.actuals[entry.actual]? | throw .request
  let some value := actual.results[entry.sourceIndex]? | throw .request
  let some context := actual.contexts[entry.sourceIndex]? | throw .request
  let some value := remapResult (fun sourceIndex =>
    (plan.find? fun other => other.occurrence == entry.occurrence && other.actual == entry.actual &&
      other.sourceIndex == sourceIndex).map (·.destination)) value
    | throw .request
  guard (entry.destination < description.nodes.length) .request
  pure (value,context)

def readSuppliedData {sources : Sources} (supply : SupplyData sources) (description : Description) : WorkM (GraphData sources) := do
  guard description.complete .request
  let _ ← readOccurrences description
  let plan ← borrowPlan supply description
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  exactWork (Exact.charge (64*(bytes+1)*(description.nodes.length+1)^2))
  let (results,contexts) ← description.nodes.zipIdx.foldlM (fun (previous,contexts) (node,index) => do
    let (value,context) ← match plan.find? (·.destination == index) with
      | some entry => borrowedValue supply description plan entry
      | none => do
        let _ ← originalFormal supply description node
        let value ← readNode sources (.source supply.owner) description previous node
        pure (value,Context.source supply.owner)
    pure (previous ++ [value],contexts ++ [context])) ([],[])
  if count : results.length = description.nodes.length then
    if contextCount : contexts.length = description.nodes.length then
      if complete : description.complete = true then
        match selected : results[description.root]? with
        | none => throw .request
        | some root => pure ⟨description,results,contexts,count,contextCount,complete,root,selected⟩
      else throw .request
    else throw .request
  else throw .request

/-- Actual reader provenance. An inherited read matches complete original
formal instances; selecting a closure keeps its parent receipts. -/
inductive GraphReadProof (sources : Sources) : GraphData sources → Type where
  | fresh (data : GraphData sources) (context : Context)
      (read : ∃ before after,(readNodes sources context data.description).run before = (.ok data.results,after))
      (contexts : data.contexts = List.replicate data.results.length context) : GraphReadProof sources data
  | inherited (supply : SupplyData sources)
      (actuals : ∀ index : Fin supply.actuals.length,
        GraphReadProof sources (supply.actuals[index.val]'index.isLt).2)
      (data : GraphData sources)
      (read : ∃ before after,(readSuppliedData supply data.description).run before = (.ok data,after)) :
      GraphReadProof sources data
  | selected (parent : GraphData sources) (proof : GraphReadProof sources parent) (index : Nat)
      (data : GraphData sources) (read : selectData parent index = some data) : GraphReadProof sources data

structure CheckedGraph (sources : Sources) (context : Context) (description : Description) where
  results : List (Result sources)
  contexts : List Context
  count : results.length = description.nodes.length
  contextCount : contexts.length = description.nodes.length
  complete : description.complete = true
  root : Result sources
  selected : results[description.root]? = some root
  read : GraphReadProof sources ⟨description,results,contexts,count,contextCount,complete,root,selected⟩

def CheckedGraph.data {sources context description} (graph : CheckedGraph sources context description) : GraphData sources :=
  ⟨description,graph.results,graph.contexts,graph.count,graph.contextCount,graph.complete,graph.root,graph.selected⟩

def ofData {sources : Sources} (context : Context) (data : GraphData sources) (proof : GraphReadProof sources data) :
    CheckedGraph sources context data.description :=
  ⟨data.results,data.contexts,data.count,data.contextCount,data.complete,data.root,data.selected,proof⟩

def check (sources : Sources) (context : Context) (description : Description) :
    WorkM (CheckedGraph sources context description) := do
  let results ← NaturalAffine.witness (readNodes sources context description)
  if complete : description.complete = true then
    if count : results.val.length = description.nodes.length then
      match selected : results.val[description.root]? with
      | none => throw .request
      | some root =>
        let contexts := List.replicate results.val.length context
        let data : GraphData sources :=
          ⟨description,results.val,contexts,count,by
            change (List.replicate results.val.length context).length = description.nodes.length
            rw [List.length_replicate]
            exact count,complete,root,selected⟩
        pure (ofData context data (.fresh data context (by with_reducible exact results.property) rfl))
    else throw .request
  else throw .request

def CheckedGraph.select {sources context description} (graph : CheckedGraph sources context description)
    (index : Nat) (selectedContext : Context := context) :
    WorkM (Sigma (CheckedGraph sources selectedContext)) := do
  exactWork (Exact.charge (16*(description.nodes.length+1)^2))
  match selected : selectData graph.data index with
  | none => throw .request
  | some data => pure ⟨data.description,ofData selectedContext data (.selected graph.data graph.read index data selected)⟩

def CheckedGraph.providers {sources context description} (graph : CheckedGraph sources context description) :
    List (Provider sources) := graph.results.filterMap (·.provider)

def CheckedGraph.sourceRows {sources context description} (graph : CheckedGraph sources context description) :
    List (String × String) := graph.results.flatMap fun result =>
  result.kindRows ++ ((result.provider.toList ++ result.formal.toList).flatMap fun provider => provider.signature.sourceRows) ++
    (result.requirements.flatMap fun (_,request) => request.sourceRows)

/-- Local requests in original node order. Descendant requests remain separate
under inverses, controls and zero powers; no ancestor copies or erases them. -/
def CheckedGraph.requirements {sources context description} (graph : CheckedGraph sources context description) :
    List (Nat × SourceMeaning.Request sources) := graph.results.flatMap (·.requirements)

def CheckedGraph.hasMeaningRequirements {sources context description} (graph : CheckedGraph sources context description) : Bool :=
  !graph.requirements.isEmpty

structure Actual (sources : Sources) (context : Context) (argument : String × Description) where
  graph : CheckedGraph sources context argument.2

structure ArgumentsCheckedWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) (context : Context) where
  actuals : List (Sigma (Actual sources context))
  ordered : actuals.map (·.1) = instantiation.arguments.operations
  bound : ∃ before after,
    (bindArgumentsWithInstantiation instantiation (actuals.map fun actual => (actual.1.1,actual.2.graph.root))).run before = (.ok (),after)
  kindRows : List (String × String)
  kindRowsRead : ∃ before after,
    (kindRowsWithInstantiation instantiation).run before = (.ok kindRows,after)
  rootRequirements : List (String × SourceMeaning.Request sources)
  rootRequirementsRead : ∃ before after,
    (bindArgumentsWithRequirements instantiation (actuals.map fun actual => (actual.1.1,actual.2.graph.root))).run before = (.ok rootRequirements,after)

def checkArgumentsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) : WorkM (ArgumentsCheckedWithInstantiation instantiation context) := do
  let actuals ← instantiation.arguments.operations.mapM fun argument => do
    let graph ← check sources context argument.2
    pure (⟨argument,⟨graph⟩⟩ : Sigma (Actual sources context))
  if ordered : actuals.map (·.1) = instantiation.arguments.operations then
    let bindings ← NaturalAffine.witness (bindArgumentsWithContracts instantiation
      (actuals.map fun actual => (actual.1.1,actual.2.graph.root)))
    let rows ← NaturalAffine.witness (kindRowsWithInstantiation instantiation)
    return ⟨actuals,ordered,by
      obtain ⟨before,after,ran⟩ := bindings.property
      exact ⟨before,after,bindingProjection _ (fun _ => ()) _ _ _ ran⟩,
      rows.val,by with_reducible exact rows.property,bindings.val.requirements,by
        obtain ⟨before,after,ran⟩ := bindings.property
        exact ⟨before,after,bindingProjection _ Bindings.requirements _ _ _ ran⟩⟩
  else throw .request

/-- Rebind checked actual graphs without rereading a provider under a different
module. This repeats the original formal/actual obligations, including unused
actuals and refinements, while retaining every graph receipt. -/
def checkArgumentsFromWithActuals {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) (actuals : List (Sigma (Actual sources context))) :
    WorkM {checked : ArgumentsCheckedWithInstantiation instantiation context // checked.actuals = actuals} := do
  if ordered : actuals.map (·.1) = instantiation.arguments.operations then
    let bindings ← NaturalAffine.witness (bindArgumentsWithContracts instantiation
      (actuals.map fun actual => (actual.1.1,actual.2.graph.root)))
    let rows ← NaturalAffine.witness (kindRowsWithInstantiation instantiation)
    pure ⟨⟨actuals,ordered,by
      obtain ⟨before,after,ran⟩ := bindings.property
      exact ⟨before,after,bindingProjection _ (fun _ => ()) _ _ _ ran⟩,
      rows.val,by with_reducible exact rows.property,bindings.val.requirements,by
        obtain ⟨before,after,ran⟩ := bindings.property
        exact ⟨before,after,bindingProjection _ Bindings.requirements _ _ _ ran⟩⟩,rfl⟩
  else throw .request

def checkArgumentsFrom {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) (actuals : List (Sigma (Actual sources context))) :
    WorkM (ArgumentsCheckedWithInstantiation instantiation context) := do
  pure (← checkArgumentsFromWithActuals instantiation context actuals).val

structure Supply {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) where
  context : Context
  arguments : ArgumentsCheckedWithInstantiation instantiation context

def Supply.data {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) : SupplyData sources :=
  ⟨owner,name,original,instantiation,supply.context,
    supply.arguments.actuals.map (fun actual => (actual.1.1,actual.2.graph.data)),by
      simpa only [List.map_map,Function.comp_def,CheckedGraph.data] using supply.arguments.ordered,
    by simpa only [List.map_map,Function.comp_def,CheckedGraph.data] using supply.arguments.bound⟩

def Supply.valid {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) :
    ∀ index : Fin supply.data.actuals.length,
      GraphReadProof sources (supply.data.actuals[index.val]'index.isLt).2 := by
  intro index
  have bound : index.val < supply.arguments.actuals.length := by
    simpa only [Supply.data,List.length_map] using index.isLt
  let packed := supply.arguments.actuals[index.val]'bound
  simpa only [Supply.data,List.getElem_map] using packed.2.graph.read

def checkWithSupply {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) (description : Description) :
    WorkM (CheckedGraph sources (.source owner) description) := do
  let data ← NaturalAffine.witness (readSuppliedData supply.data description)
  if same : data.val.description = description then
    have read : ∃ before after,(readSuppliedData supply.data data.val.description).run before = (.ok data.val,after) := by
      rw [same]
      with_reducible exact data.property
    let checked := ofData (.source owner) data.val
      (.inherited supply.data supply.valid data.val read)
    pure (same ▸ checked)
  else throw .request

structure ProviderInstance {sources siteContext description}
    (graph : CheckedGraph sources siteContext description) (index : Nat) where
  result : Result sources
  selected : graph.results[index]? = some result
  provider : Provider sources
  originalProvider : result.provider = some provider
  context : Context
  contextRead : graph.contexts[index]? = some context
  arguments : ArgumentsCheckedWithInstantiation provider.signature.instantiation context

/-- Recover the provider's exact original actuals and their inherited contexts
at this occurrence. The returned context is the original supplying site; it is
never reconstructed from the provider's declaration module. -/
def argumentsAt {sources context description} (graph : CheckedGraph sources context description) (index : Nat) :
    WorkM (ProviderInstance graph index) := do
  let some node := description.nodes[index]? | throw .request
  let .provider owner name bases naturals operations := node | throw .request
  match selected : graph.results[index]? with
  | none => throw .request
  | some result =>
    match found : result.provider with
    | none => throw .request
    | some provider =>
      guard (provider.moduleName == owner && provider.declarationName == name &&
        provider.signature.staticArguments.bases == bases && provider.signature.staticArguments.naturals == naturals) .request
      match contextRead : graph.contexts[index]? with
      | none => throw .request
      | some originalContext =>
        let actuals ← operations.mapM fun (name,index) => do
          let selected ← graph.select index originalContext
          pure (⟨(name,selected.1),⟨selected.2⟩⟩ : Sigma (Actual sources originalContext))
        let arguments ← checkArgumentsFrom provider.signature.instantiation originalContext actuals
        pure ⟨result,selected,provider,found,originalContext,contextRead,arguments⟩

def ArgumentsCheckedWithInstantiation.sourceRows {sources owner name original instantiation context}
    (checked : @ArgumentsCheckedWithInstantiation sources owner name original instantiation context) :
    List (String × String) := checked.kindRows ++ checked.actuals.flatMap (fun actual => actual.2.graph.sourceRows) ++
      checked.rootRequirements.flatMap (fun (_,request) => request.sourceRows)

def ArgumentsCheckedWithInstantiation.hasMeaningRequirements {sources owner name original instantiation context}
    (checked : @ArgumentsCheckedWithInstantiation sources owner name original instantiation context) : Bool :=
  !checked.rootRequirements.isEmpty || checked.actuals.any (fun actual => actual.2.graph.hasMeaningRequirements)

abbrev ArgumentsChecked {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) (context : Context) :=
  ArgumentsCheckedWithInstantiation signature.instantiation context

def checkArguments {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name)
    (context : Context) : WorkM (ArgumentsChecked signature context) :=
  checkArgumentsWithInstantiation signature.instantiation context

end QleisliKernel.SourceTypes.StaticOperation
