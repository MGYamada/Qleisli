import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.SourceTypes.StaticKinds
import QleisliKernel.SourceTypes.SourceMeaning
import QleisliKernel.SourceTypes.SymbolicTypes
import QleisliKernel.SourceTypes.OperationPaths
import QleisliKernel.SourceTypes.GenericCatalogue

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

abbrev Paths := OperationPaths.Paths
def Paths.meet (left right : Paths) : Paths := OperationPaths.Paths.meet left right

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
  generic : Option (GenericCatalogue.Inference signature.original) := none

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

private def selectActuals (description : Description) (operations : List (String × Nat)) :
    WorkM (List (String × Description)) := operations.mapM fun (name,index) => do
  let some actual := description.select index | throw .request
  pure (name,actual)

private def readProvider (sources : Sources) (context : Context)
    (readChild : Nat → WorkM (Result sources)) (actuals : List (String × Description))
    (owner name : String) (bases : List (String × Basis)) (naturals : List (String × Nat))
    (operations : List (String × Nat)) (catalogue : Option (GenericCatalogue.Checked sources)) : WorkM (Result sources) := do
  let signature ← QuantumSignatureCore.prepareWithArguments sources owner name {bases,naturals,operations := actuals}
    (catalogue.map (·.originals)) (catalogue.map (·.helpers))
  guard (context.visible owner signature.original.declaration.isPublic) .request
  let generic ← GenericCatalogue.inferOriginal signature.original catalogue
  let originalResults ← operations.mapM fun (name,index) => do return (name,← readChild index)
  let bindings ← bindArgumentsWithContracts signature.instantiation originalResults
  let kindRows ← kindRowsWithInstantiation signature.instantiation
  let staticRows ← StaticInstantiation.readRowsWithTypes signature.instantiation (signature.inputs ++ signature.outputs)
  let kindRows := kindRows ++ staticRows
  let requirements ← indexedRequirements operations bindings.requirements
  let [input] := signature.inputs | throw .request
  let [output] := signature.outputs | throw .request
  guard (match signature.parts with | .owner _ => true | _ => false) .request
  let internal := context.internal owner
  -- Eligibility uses the independently checked ORIGINAL body, before closing
  -- any convenient Basis/Nat values. Actual native body/Gram and J/C paths
  -- remain separate obligations. External selection keeps the public bound.
  let visible := if internal then generic.inferredEffect
    else signature.original.parsedHeader.effect.getD .observe
  guard (visible != .observe) .request
  let endomorphic := input == output
  let reversible := visible == .unitary
  let reverseArgs := originalResults.all fun (_,actual) => actual.paths.applicable && actual.paths.adjointable
  let controlArgs := originalResults.all fun (_,actual) =>
    actual.paths.applicable && actual.paths.adjointable && actual.paths.controllable
  let expected := visible
  result input output expected
    ⟨true,reversible && reverseArgs,reversible && endomorphic && controlArgs⟩
    (some ⟨owner,name,signature,expected,internal,some generic⟩) none kindRows requirements

private def readNodeWith (sources : Sources) (context : Context) (description : Description)
    (readChild : Nat → WorkM (Result sources))
    (select : List (String × Nat) → WorkM (List (String × Description))) (node : Node)
    (catalogue : Option (GenericCatalogue.Checked sources) := none) : WorkM (Result sources) := do
  match node with
  | .primitive kind target =>
    guard (context != .external) .request
    guard (kind == .globalPhaseEighth || target == [.bit]) .request
    result target target .unitary ⟨true,true,true⟩
  | .provider owner name bases naturals operations =>
    readProvider sources context readChild (← select operations) owner name bases naturals operations catalogue
  | .formal owner name bases naturals operations ordinal =>
    guard (context == .source owner) .request
    let actuals ← select operations
    let signature ← QuantumSignatureCore.prepareWithArguments sources owner name {bases,naturals,operations := actuals}
      (catalogue.map (·.originals)) (catalogue.map (·.helpers))
    let originalResults ← operations.mapM fun (name,index) => do return (name,← readChild index)
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
      result input output effect paths none (some ⟨owner,name,signature,effect,false,none⟩) kindRows requirements
  | .inverse index =>
    let c ← readChild index
    guard (c.effect == .unitary && c.paths.adjointable) .request
    result c.output c.input c.effect ⟨c.paths.adjointable,c.paths.applicable,c.paths.controllable⟩
  | .controlled index =>
    let c ← readChild index
    guard (c.effect == .unitary && c.input == c.output) .request
    result (.pair :: .bit :: c.input) (.pair :: .bit :: c.output) .unitary
      ⟨c.paths.controllable,c.paths.controllable,c.paths.controllable⟩
  | .power index count =>
    let c ← readChild index
    guard (c.input == c.output && count ≤ 4294967295) .request
    result c.input c.output c.effect c.paths
  | .thenOp left right =>
    let a ← readChild left
    let b ← readChild right
    guard (a.output == b.input) .request
    result a.input b.output (joinEffect a.effect b.effect) (a.paths.meet b.paths)
  | .tensor left right =>
    let a ← readChild left
    let b ← readChild right
    result (.pair :: a.input ++ b.input) (.pair :: a.output ++ b.output)
      (joinEffect a.effect b.effect) (a.paths.meet b.paths)
  | .conjugate outer middle =>
    let a ← readChild outer
    let b ← readChild middle
    guard (a.effect == .unitary && b.input == a.input && b.output == a.input) .request
    result a.output a.output (joinEffect a.effect b.effect)
      ⟨a.paths.applicable && a.paths.adjointable && b.paths.applicable,
        a.paths.applicable && a.paths.adjointable && b.paths.adjointable,
        a.paths.applicable && a.paths.adjointable && b.paths.controllable⟩
  | .requested index owner name =>
    let c ← readChild index
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

def readNode (sources : Sources) (context : Context) (description : Description)
    (previous : List (Result sources)) (node : Node)
    (catalogue : Option (GenericCatalogue.Checked sources) := none) : WorkM (Result sources) :=
  readNodeWith sources context description (child previous) (selectActuals description) node catalogue

def readOccurrences (description : Description) : WorkM (List Nat) := do
  -- Reserve both capped topological scans before entering their pure readers.
  exactWork (Exact.charge (64*(description.nodes.length+1)^2))
  let count ← adapt description.treeSize
  exactWork (Exact.charge (8*(count+1)^2))
  adapt description.occurrences

private def natFields (n : Nat) : Nat := 1+n.log2/8

private def basisFields (basis : Basis) : Nat := basis.foldl (fun total atom => total+match atom with
  | .enumeration origin names | .record origin names =>
    origin.moduleName.utf8ByteSize+origin.declarationName.utf8ByteSize+origin.source.utf8ByteSize+
      names.foldl (fun n name => n+name.utf8ByteSize+1) 4
  | .bits n | .tuple n => natFields n+1
  | _ => 1) 0

private def basisArguments (bases : List (String × Basis)) : Nat :=
  bases.foldl (fun total (name,basis) => total+name.utf8ByteSize+basisFields basis+1) 0

private def namedIndices (values : List (String × Nat)) : Nat :=
  values.foldl (fun total (name,index) => total+name.utf8ByteSize+natFields index+1) 0

private def applicationFields (owner name : String) (bases : List (String × Basis))
    (naturals operations : List (String × Nat)) : Nat :=
  owner.utf8ByteSize+name.utf8ByteSize+basisArguments bases+namedIndices naturals+namedIndices operations+8

private def nodeFields : Node → Nat
  | .primitive _ target => basisFields target+2
  | .provider owner name bases naturals operations => applicationFields owner name bases naturals operations
  | .formal owner name bases naturals operations ordinal =>
    applicationFields owner name bases naturals operations+natFields ordinal
  | .requested i owner name => natFields i+owner.utf8ByteSize+name.utf8ByteSize+3
  | .power i count => natFields i+natFields count+2
  | node => node.children.foldl (fun total i => total+natFields i) 1

private def descriptionFields (description : Description) : Nat :=
  description.nodes.foldl (fun total node => total+nodeFields node) (natFields description.root)

private structure GraphWork where
  shape : Nat
  payload : Nat
  sourceBytes : Nat

private def graphWork (sources : Sources) (description : Description) : GraphWork :=
  ⟨description.nodes.foldl (fun total node => total+node.children.length+1) 1,descriptionFields description,
    sources.foldl (fun total (owner,text) => total+owner.utf8ByteSize+text.utf8ByteSize+1) 1⟩

-- The canonical selectors scan the graph and its reachability lists, remap
-- each retained edge and recheck completeness. Charge separately per request.
private def selectionWork (work : GraphWork) : Nat := 32*work.shape^2+16*(work.payload+1)

private def freshNode {sources} (context : Context) (description : Description) (work : GraphWork)
    (previous : Array (Result sources)) (node : Node) (catalogue : Option (GenericCatalogue.Checked sources))
    (prepared : Option (List (String × Description)) := none) : WorkM (Result sources) := do
  let operands := node.children.foldl (fun total index => total+match previous[index]? with
    | some value => basisFields value.input+basisFields value.output+1
    | none => 1) 0
  let fields := nodeFields node
  let sourceWork := match node with
    | .provider .. | .formal .. | .requested .. => 64*work.sourceBytes
    | _ => 0
  exactWork (Exact.charge (16*(fields+operands+work.shape+1)+sourceWork))
  readNodeWith sources context description (fun i => lift (readOption previous[i]?))
    (fun operations => match prepared with
      | some actuals => pure actuals
      | none => do
        exactWork (Exact.charge (operations.length*selectionWork work))
        selectActuals description operations) node catalogue

def readNodes (sources : Sources) (context : Context) (description : Description)
    (catalogue : Option (GenericCatalogue.Checked sources) := none) :
    WorkM (List (Result sources)) := do
  let work := graphWork sources description
  exactWork (Exact.charge (16*(sources.size+work.shape^2+work.payload+1)))
  guard description.complete .request
  let _ ← readOccurrences description
  let results ← description.nodes.foldlM (init := #[]) fun previous node => do
    let value ← freshNode context description work previous node catalogue
    pure (previous.push value)
  pure results.toList

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
  catalogue : Option (GenericCatalogue.Checked sources)

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

private structure Loan where
  occurrence : Nat
  actual : Nat
  sourceIndex : Nat
  deriving BEq

private inductive Planned (sources : Sources) where
  | fresh
  | formal (arguments : List (String × Description))
  | borrowed (loan : Loan) (value : Result sources) (context : Context)

-- A borrowed result keeps its actual supplying context and redirects each
-- local Meaning request through this wrapper's original destination map.
private def installLoan {sources} (plan : Array (Planned sources)) (graph : GraphData sources)
    (occurrence actual : Nat) (indices : List Nat) (mapping : Array Nat) : WorkM (Array (Planned sources)) := do
  exactWork (Exact.charge (16*(indices.length+graph.results.length+graph.contexts.length+1)))
  let results := graph.results.toArray
  let contexts := graph.contexts.toArray
  indices.zipIdx.foldlM (init := plan) fun slots (destination,sourceIndex) => do
    let loan := ⟨occurrence,actual,sourceIndex⟩
    match slots[destination]? with
    | none | some (.formal _) => throw .request
    | some (.borrowed earlier _ _) =>
      guard (earlier == loan) .request
      pure slots
    | some .fresh =>
      let some value := results[sourceIndex]? | throw .request
      let some context := contexts[sourceIndex]? | throw .request
      exactWork (Exact.charge (16*(value.requirements.length+1)))
      let some value := remapResult (fun i => mapping[i]?) value | throw .request
      pure (slots.setIfInBounds destination (.borrowed loan value context))

-- The exact selected descriptors serve both original-argument comparison
-- and the later common formal reader. Validate all arguments in written order.
private def planFormal {sources} (supply : SupplyData sources) (description : Description) (work : GraphWork)
    (actuals : List ((String × GraphData sources) × Nat)) (plan : Array (Planned sources)) (occurrence : Nat)
    (owner name : String) (bases : List (String × Basis)) (naturals operations : List (String × Nat))
    (ordinal : Nat) : WorkM (Array (Planned sources)) := do
  let expected := supply.instantiation.arguments
  exactWork (Exact.charge (16*(owner.utf8ByteSize+name.utf8ByteSize+supply.owner.utf8ByteSize+supply.name.utf8ByteSize+
    basisArguments bases+basisArguments expected.bases+namedIndices naturals+namedIndices expected.naturals+
    natFields ordinal+supply.original.occurrence.header.length+1)))
  guard (owner == supply.owner && name == supply.name && bases == expected.bases && naturals == expected.naturals) .request
  match supply.instantiation with
  | .closed _ => throw .request
  | .static _ environment _ =>
    let some formal := environment.numeric.original.header.formals[ordinal]? | throw .request
    guard (formal.ordinal == ordinal && match formal.kind with | .operation _ => true | _ => false) .request
  let keyFields := actuals.foldl (fun total entry => total+entry.1.1.utf8ByteSize+1) 0
  let initial : Array (Planned sources) × List (Nat × Array Nat) × List (String × Description) := (plan,[],[])
  let (slots,_,reverseArgs) ← operations.foldlM (init := initial) fun (slots,maps,args) (key,index) => do
    exactWork (Exact.charge (selectionWork work+16*(keyFields+key.utf8ByteSize+maps.length+1)))
    let some ((_,actual),id) := actuals.find? (fun entry => entry.1.1 == key) | throw .request
    let some (indices,selected) := description.selection index | throw .request
    exactWork (Exact.charge (16*(descriptionFields selected+descriptionFields actual.description+indices.length+1)))
    guard (selected == actual.description && indices.length == actual.results.length) .request
    -- For a repeated reference to the same actual at this wrapper the first
    -- destination list remains the remapping used for its local requirements.
    let (mapping,maps) := match maps.find? (·.1 == id) with
      | some (_,mapping) => (mapping,maps)
      | none => let mapping := indices.toArray; (mapping,(id,mapping) :: maps)
    let slots ← installLoan slots actual occurrence id indices mapping
    pure (slots,maps,(key,selected) :: args)
  let arguments := reverseArgs.reverse
  let fields := fun (rows : List (String × Description)) =>
    rows.foldl (fun total (key,graph) => total+key.utf8ByteSize+descriptionFields graph+1) 0
  exactWork (Exact.charge (16*(fields arguments+fields expected.operations+1)))
  guard (arguments == expected.operations) .request
  pure (slots.setIfInBounds occurrence (.formal arguments))

private def borrowPlan {sources} (supply : SupplyData sources) (description : Description) (work : GraphWork) :
    WorkM (Array (Planned sources)) := do
  exactWork (Exact.charge (16*(description.nodes.length+supply.actuals.length+1)))
  let actuals := supply.actuals.zipIdx
  description.nodes.zipIdx.reverse.foldlM (init := Array.replicate description.nodes.length .fresh) fun plan (node,index) => do
    match plan[index]?,node with
    | some .fresh,.formal owner name bases naturals operations ordinal =>
      planFormal supply description work actuals plan index owner name bases naturals operations ordinal
    | none,_ => throw .request
    | _,_ => pure plan

private def readInheritedData {sources : Sources} (supply : SupplyData sources) (description : Description) : WorkM (GraphData sources) := do
  let work := graphWork sources description
  exactWork (Exact.charge (16*(sources.size+work.shape^2+work.payload+1)))
  guard description.complete .request
  let _ ← readOccurrences description
  let plan ← borrowPlan supply description work
  let initial : Array (Result sources) × Array Context := (#[],#[])
  let (values,places) ← description.nodes.zipIdx.foldlM (init := initial) fun (previous,contexts) (node,index) => do
    let (value,context) ← match plan[index]? with
      | some (.borrowed _ value context) => pure (value,context)
      | some (.formal arguments) => do
        let value ← freshNode (.source supply.owner) description work previous node supply.catalogue (some arguments)
        pure (value,Context.source supply.owner)
      | some .fresh => do
        let value ← freshNode (.source supply.owner) description work previous node supply.catalogue
        pure (value,Context.source supply.owner)
      | none => throw .request
    pure (previous.push value,contexts.push context)
  let results := values.toList
  let contexts := places.toList
  if count : results.length = description.nodes.length then
    if contextCount : contexts.length = description.nodes.length then
      if complete : description.complete = true then
        match selected : results[description.root]? with
        | none => throw .request
        | some root => pure ⟨description,results,contexts,count,contextCount,complete,root,selected⟩
      else throw .request
    else throw .request
  else throw .request

/-- This exact shape has no child edges or formal occurrence to borrow. The
original supplying scope still selects the provider's visibility/effect, and
the common readNode still checks its complete original signature and body
inference. General graphs retain the inherited traversal below. -/
def isFreshLeaf (description : Description) : Bool :=
  match description.nodes,description.root with
  | [.provider _ _ _ _ []],0 => true
  | _,_ => false

/-- A constant-size graph driver for one actual source leaf and an already
checked original catalogue. It performs no supply search, descriptor copying,
index remapping, linked-list accumulation or pairwise graph comparison. The
reservation covers the keys/list cells actually inspected by this driver;
readNode pays for every original type/actual/effect/access check itself. -/
def readFreshLeafData (sources : Sources) (context : Context)
    (catalogue : GenericCatalogue.Checked sources) (description : Description) : WorkM (GraphData sources) := do
  match nodes : description.nodes with
  | [.provider owner name bases naturals []] =>
    if atRoot : description.root = 0 then
      if complete : description.complete = true then
        let _ ← readOccurrences description
        exactWork (Exact.charge (64*(applicationFields owner name bases naturals []+1)))
        let value ← readNode sources context description [] (.provider owner name bases naturals []) (some catalogue)
        pure ⟨description,[value],[context],by simp only [nodes,List.length_singleton],
          by simp only [nodes,List.length_singleton],complete,value,by simp only [atRoot,List.getElem?_cons_zero]⟩
      else throw .request
    else throw .request
  | _ => throw .request

/-- A provider leaf cannot reference any inherited actual. This is a
structural dispatch, never a retry after a failed reader. The same supplied
reader receipt retains the complete original instance and every unused actual.
Cold or non-leaf graphs keep the original general traversal. -/
def readSuppliedData {sources : Sources} (supply : SupplyData sources) (description : Description) : WorkM (GraphData sources) :=
  match supply.catalogue with
  | some catalogue =>
    if isFreshLeaf description then readFreshLeafData sources (.source supply.owner) catalogue description
    else readInheritedData supply description
  | none => readInheritedData supply description

/-- Actual reader provenance. An inherited read matches complete original
formal instances; selecting a closure keeps its parent receipts. -/
inductive GraphReadProof (sources : Sources) : GraphData sources → Type where
  | fresh (data : GraphData sources) (context : Context) (catalogue : Option (GenericCatalogue.Checked sources))
      (read : ∃ before after,(readNodes sources context data.description catalogue).run before = (.ok data.results,after))
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

def check (sources : Sources) (context : Context) (description : Description)
    (catalogue : Option (GenericCatalogue.Checked sources) := none) :
    WorkM (CheckedGraph sources context description) := do
  let results ← NaturalAffine.witness (readNodes sources context description catalogue)
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
        pure (ofData context data (.fresh data context catalogue (by with_reducible exact results.property) rfl))
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
  result.kindRows ++ ((result.provider.toList ++ result.formal.toList).flatMap fun provider =>
    provider.signature.sourceRows ++ (provider.generic.map (·.sourceRows) |>.getD [])) ++
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
  catalogue : Option (GenericCatalogue.Checked sources)

def checkArgumentsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) (catalogue : Option (GenericCatalogue.Checked sources) := none) :
    WorkM (ArgumentsCheckedWithInstantiation instantiation context) := do
  let actuals ← instantiation.arguments.operations.mapM fun argument => do
    let graph ← check sources context argument.2 catalogue
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
        exact ⟨before,after,bindingProjection _ Bindings.requirements _ _ _ ran⟩,catalogue⟩
  else throw .request

/-- Rebind checked actual graphs without rereading a provider under a different
module. This repeats the original formal/actual obligations, including unused
actuals and refinements, while retaining every graph receipt. -/
def checkArgumentsFromWithActuals {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) (actuals : List (Sigma (Actual sources context)))
    (catalogue : Option (GenericCatalogue.Checked sources) := none) :
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
        exact ⟨before,after,bindingProjection _ Bindings.requirements _ _ _ ran⟩,catalogue⟩,rfl⟩
  else throw .request

def checkArgumentsFrom {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) (actuals : List (Sigma (Actual sources context)))
    (catalogue : Option (GenericCatalogue.Checked sources) := none) :
    WorkM (ArgumentsCheckedWithInstantiation instantiation context) := do
  pure (← checkArgumentsFromWithActuals instantiation context actuals catalogue).val

structure Supply {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) where
  context : Context
  arguments : ArgumentsCheckedWithInstantiation instantiation context

def Supply.data {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) : SupplyData sources :=
  ⟨owner,name,original,instantiation,supply.context,
    supply.arguments.actuals.map (fun actual => (actual.1.1,actual.2.graph.data)),by
      simpa only [List.map_map,Function.comp_def,CheckedGraph.data] using supply.arguments.ordered,
    by simpa only [List.map_map,Function.comp_def,CheckedGraph.data] using supply.arguments.bound,
    supply.arguments.catalogue⟩

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

/-- A successful graph read is indexed by the exact original supply and the
independently reconstructed operation description. -/
structure SuppliedGraph {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) (description : Description) where
  graph : CheckedGraph sources (.source owner) description
  checked : ∃ before after, (checkWithSupply supply description).run before = (.ok graph,after)

structure SuppliedGraphEntry {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) where
  description : Description
  fields : Nat
  exactFields : fields = descriptionFields description
  graph : SuppliedGraph supply description

private def findSuppliedGraph {sources owner name original instantiation}
    {supply : @Supply sources owner name original instantiation}
    (description : Description) (fields : Nat) (previous : List (SuppliedGraphEntry supply)) :
    WorkM (Option (SuppliedGraph supply description)) :=
  previous.findSomeM? fun first => do
    exactWork (Exact.charge (16*(fields+first.fields+1)))
    if same : first.description = description then
      pure (some (same ▸ first.graph))
    else pure none

/-- Reuse only the static graph. Each caller still reads its own original
expression, including provider actuals, source rows and assertion markers. -/
def checkSharedSupply {sources owner name original instantiation}
    (supply : @Supply sources owner name original instantiation) (description : Description)
    (previous : List (SuppliedGraphEntry supply)) :
    WorkM (SuppliedGraph supply description × List (SuppliedGraphEntry supply)) := do
  let fields := descriptionFields description
  exactWork (Exact.charge (4*(fields+1)))
  match ← findSuppliedGraph description fields previous with
  | some graph => return (graph,previous)
  | none =>
    let read ← NaturalAffine.witness (checkWithSupply supply description)
    let graph : SuppliedGraph supply description := ⟨read.val,by with_reducible exact read.property⟩
    return (graph,⟨description,fields,rfl,graph⟩::previous)

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
          (match provider.generic with | some (.catalogued catalogue _) => some catalogue | _ => none)
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
    (context : Context) (catalogue : Option (GenericCatalogue.Checked sources) := none) : WorkM (ArgumentsChecked signature context) :=
  checkArgumentsWithInstantiation signature.instantiation context catalogue

end QleisliKernel.SourceTypes.StaticOperation
