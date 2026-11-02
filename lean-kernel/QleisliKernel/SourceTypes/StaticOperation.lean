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
  let (requirement,symbolic) ← match parsed.meaning with
    | none => pure (none,none)
    | some tokens => do
      let scope := (environment.numeric.original.header.formals.filter (·.ordinal < formal.ordinal)).map (·.name)
      let selected ← SourceMeaning.select sources owner scope tokens
      let state : GenericLexicalNatural.SomeEnvironment sources :=
        ⟨owner,name,environment.numeric,GenericLexicalNatural.initial environment.numeric⟩
      let symbolic ← SymbolicTypes.checkRefinement state scope formal.ordinal parsed.input parsed.output
        selected.meaning.graph.input selected.meaning.graph.output
      guard (selected.meaning.graph.input == input.basis && selected.meaning.graph.output == output.basis) .request
      pure (some selected.request,some (⟨state,scope,formal.ordinal,parsed.input,parsed.output,
        selected.meaning.graph.input,selected.meaning.graph.output,symbolic⟩ : SymbolicTypes.SomeRefinement sources))
  return ⟨input.basis,output.basis,requirement,symbolic⟩

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
        actual.effect != .observe && (contract.input != contract.output || actual.effect == .unitary) &&
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
      let effect := if input == output then Effect.unitary else .iso
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

structure CheckedGraph (sources : Sources) (context : Context) (description : Description) where
  results : List (Result sources)
  read : ∃ before after, (readNodes sources context description).run before = (.ok results,after)
  count : results.length = description.nodes.length
  complete : description.complete = true
  root : Result sources
  selected : results[description.root]? = some root

def check (sources : Sources) (context : Context) (description : Description) :
    WorkM (CheckedGraph sources context description) := do
  let results ← NaturalAffine.witness (readNodes sources context description)
  if complete : description.complete = true then
    if count : results.val.length = description.nodes.length then
      match selected : results.val[description.root]? with
      | none => throw .request
      | some root => return ⟨results.val,by with_reducible exact results.property,count,complete,root,selected⟩
    else throw .request
  else throw .request

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
