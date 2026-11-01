import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.SourceTypes.StaticKinds

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

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private structure Ports where
  input : List String := []
  output : List String := []
  stack : List String := []
  arrow : Bool := false
  afterArrow : Bool := false

private def portToken (state : Ports) (token : String) : Except String Ports := do
  if state.arrow then
    if token != ">" then throw "incomplete original operation arrow"
    return {state with arrow := false,afterArrow := true}
  if state.stack.isEmpty && token == "," then
    throw "operation Meaning refinement requires its separate original equality gate"
  if state.stack.isEmpty && token == "-" then
    if state.afterArrow then throw "multiple original operation arrows"
    return {state with arrow := true}
  let stack ← if ["(","<","["].contains token then
      pure ((if token == "(" then ")" else if token == "<" then ">" else "]") :: state.stack)
    else if [")",">","]"].contains token then do
      let expected :: rest := state.stack | throw "unmatched operation kind delimiter"
      if token != expected then throw "mismatched operation kind delimiter"
      pure rest
    else pure state.stack
  return if state.afterArrow then {state with stack,output := state.output ++ [token]}
    else {state with stack,input := state.input ++ [token]}

def ports (tokens : List String) : Except String (List String × List String) := do
  let state ← tokens.foldlM portToken {}
  if state.input.isEmpty || !state.stack.isEmpty || state.arrow then throw "incomplete original operation kind"
  if state.afterArrow && state.output.isEmpty then throw "missing original operation codomain"
  return (state.input,if state.afterArrow then state.output else state.input)

def formalPorts {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) (formal : StaticHeaders.Formal) :
    WorkM (Basis × Basis) := do
  let .operation tokens := formal.kind | throw .request
  exactWork (Exact.charge (32*(tokens.length+1)*(environment.numeric.original.header.formals.length+1)))
  let (input,output) ← adapt (ports tokens)
  let input ← StaticKinds.readType environment formal.ordinal input
  let output ← StaticKinds.readType environment formal.ordinal output
  return (input.basis,output.basis)

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

/-- Check every original operation formal and actual, including unused ones.
The signature core supplies original mixed-kind identities and ordered Nat
premises; equal width cannot replace either exact operation port. -/
def bindArgumentsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (results : List (String × Result sources)) : WorkM Unit := do
  let arguments := instantiation.arguments
  exactWork (Exact.charge (32*(results.length+1)*(original.occurrence.header.length+1)))
  guard (namedResults arguments.operations results) .request
  match instantiation with
  | .closed _ => guard results.isEmpty .request
  | .static _ environment _ =>
    let formals := environment.numeric.original.header.formals.filter fun formal =>
      match formal.kind with | .operation _ => true | _ => false
    guard (formals.length == results.length) .request
    for formal in formals do
      let some (_,actual) := results.find? (·.1 == formal.name) | throw .request
      let (input,output) ← formalPorts environment formal
      guard (actual.input == input && actual.output == output &&
        actual.effect != .observe && (input != output || actual.effect == .unitary) &&
        satisfies actual.paths (required environment.numeric.original.header.access formal.name)) .request

def bindArguments {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name)
    (results : List (String × Result sources)) : WorkM Unit :=
  bindArgumentsWithInstantiation signature.instantiation results

private def result {sources : Sources} (input output : Basis) (effect : Effect) (paths : Paths)
    (provider : Option (Provider sources) := none) (formal : Option (Provider sources) := none)
    (kindRows : List (String × String) := []) : WorkM (Result sources) := do
  let _ ← FiniteCarrier.read input
  let _ ← FiniteCarrier.read output
  pure ⟨input,output,effect,paths,provider,formal,kindRows⟩

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
  bindArguments signature originalResults
  let kindRows ← kindRowsWithInstantiation signature.instantiation
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
    (some ⟨owner,name,signature,expected,internal⟩) none kindRows

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
    bindArguments signature originalResults
    let kindRows ← kindRowsWithInstantiation signature.instantiation
    match signature.instantiation with
    | .closed _ => throw .request
    | .static _ environment _ =>
      let some formal := environment.numeric.original.header.formals[ordinal]? | throw .request
      guard (formal.ordinal == ordinal) .request
      let (input,output) ← formalPorts environment formal
      let some (_,actual) := originalResults.find? (·.1 == formal.name) | throw .request
      let paths := actual.paths.meet (required environment.numeric.original.header.access formal.name)
      let effect := if input == output then Effect.unitary else .iso
      result input output effect paths none (some ⟨owner,name,signature,effect,false⟩) kindRows
  | .inverse index =>
    let c ← child previous index
    guard c.paths.adjointable .request
    result c.output c.input c.effect ⟨c.paths.adjointable,c.paths.applicable,c.paths.controllable⟩
  | .controlled index =>
    let c ← child previous index
    guard (c.input == c.output && c.paths.controllable) .request
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

def readNodes (sources : Sources) (context : Context) (description : Description) :
    WorkM (List (Result sources)) := do
  guard description.complete .request
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
  result.kindRows ++ (result.provider.toList ++ result.formal.toList).flatMap fun provider => provider.signature.sourceRows

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

def checkArgumentsWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (context : Context) : WorkM (ArgumentsCheckedWithInstantiation instantiation context) := do
  let actuals ← instantiation.arguments.operations.mapM fun argument => do
    let graph ← check sources context argument.2
    pure (⟨argument,⟨graph⟩⟩ : Sigma (Actual sources context))
  if ordered : actuals.map (·.1) = instantiation.arguments.operations then
    let bound ← NaturalAffine.witness (bindArgumentsWithInstantiation instantiation
      (actuals.map fun actual => (actual.1.1,actual.2.graph.root)))
    have same : bound.val = () := by cases bound.val; rfl
    let rows ← NaturalAffine.witness (kindRowsWithInstantiation instantiation)
    return ⟨actuals,ordered,by with_reducible simpa only [same] using bound.property,
      rows.val,by with_reducible exact rows.property⟩
  else throw .request

def ArgumentsCheckedWithInstantiation.sourceRows {sources owner name original instantiation context}
    (checked : @ArgumentsCheckedWithInstantiation sources owner name original instantiation context) :
    List (String × String) := checked.kindRows ++ checked.actuals.flatMap (fun actual => actual.2.graph.sourceRows)

abbrev ArgumentsChecked {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) (context : Context) :=
  ArgumentsCheckedWithInstantiation signature.instantiation context

def checkArguments {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name)
    (context : Context) : WorkM (ArgumentsChecked signature context) :=
  checkArgumentsWithInstantiation signature.instantiation context

end QleisliKernel.SourceTypes.StaticOperation
