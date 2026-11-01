import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.SourceTypes.OperationPorts
import QleisliKernel.SourceTypes.CallSyntax

/-! Original declared Meaning graphs. Reference and classical specification
functions retain their exact source queries, full types and original bodies.
No matrix, provider equality, path or success flag is supplied by a producer;
actual reference bodies and requested equations remain final native duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceMeaning
open Finite Semantics.FiniteCarrier Semantics.Raw

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def expect (text : String) (tokens : List LocatedToken) : Except String (LocatedToken × List LocatedToken) := do
  let first :: rest := tokens | throw "missing original Meaning token"
  if first.text != text then throw "unexpected original Meaning token"
  return (first,rest)

private def pieces : Nat → Nat → List LocatedToken → List LocatedToken → List (List LocatedToken) →
    Except String (List (List LocatedToken)) :=
  Nat.rec (fun _ _ _ _ => throw "original Meaning traversal capacity")
    (fun _ next depth prefix tokens previous => do
      match tokens with
      | [] => if depth == 0 then pure previous.reverse else throw "incomplete original source body"
      | first :: rest =>
        if depth > 0 then
          next (if first.text == "{" then depth+1 else if first.text == "}" then depth-1 else depth) [] rest previous
        else if first.text == "meaning" then
          let (body,ending) := rest.span (·.text != ";")
          let terminator :: tail := ending | throw "missing original Meaning terminator"
          next 0 [] tail ((prefix ++ [first] ++ body ++ [terminator]) :: previous)
        else if first.text == "{" then next 1 [] rest previous
        else if first.text == "}" then throw "unmatched original source body"
        else if first.text == ";" then next 0 [] rest previous
        else next 0 (prefix ++ [first]) rest previous)

def declarations (source : String) : Except String (List (List LocatedToken)) := do
  let tokens ← lexLocated source
  pieces (tokens.length+1) 0 [] tokens []

structure Header where
  name : LocatedToken
  typeTokens : List LocatedToken
  ports : OperationPorts.Parsed
  portRead : OperationPorts.read (typeTokens.map (·.text)) = .ok ports
  noNestedMeaning : ports.meaning = none
  bodyTokens : List LocatedToken
  body : CallSyntax.Checked bodyTokens

def header (source : String) (declaration : Declaration) (tokens : List LocatedToken) : Except String Header := do
  let projected ← ModuleHeader.project source tokens
  let tokens ← if declaration.isPublic then do
      let (_,rest) ← expect "pub" projected.tokens
      pure rest
    else pure projected.tokens
  let (_,tokens) ← expect "meaning" tokens
  let (name,tokens) ← expect declaration.name tokens
  let (_,tokens) ← expect ":" tokens
  let (types,ending) := tokens.span (·.text != "=")
  let (_,body) ← expect "=" ending
  if body.getLast?.map (·.text) != some ";" then throw "incomplete original Meaning declaration"
  match portRead : OperationPorts.read (types.map (·.text)) with
  | .error error => throw error
  | .ok ports =>
    if noNestedMeaning : ports.meaning = none then
      let expression ← CallSyntax.read body.dropLast
      return ⟨name,types,ports,portRead,noNestedMeaning,body.dropLast,expression⟩
    else throw "a Meaning declaration cannot have a Meaning refinement"

structure Original (sources : Sources) (owner name : String) where
  source : String
  declaration : Declaration
  bound : originalBinding sources owner name = .ok (source,declaration)
  category : declaration.kind = "meaning"
  tokens : List LocatedToken
  parsed : Header
  reading : header source declaration tokens = .ok parsed
  catalogue : ∃ all, declarations source = .ok all ∧ tokens ∈ all
  bytes : LocatedFacts.OrderedSlices source.toUTF8 0 tokens

def readOriginal (sources : Sources) (owner name : String) : WorkM (Original sources owner name) := do
  guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  exactWork (Exact.charge (512*(bytes+1)+1))
  match bound : originalBinding sources owner name with
  | .error _ => throw .request
  | .ok (source,declaration) =>
    if category : declaration.kind = "meaning" then
      let tokens ← adapt (lexLocated source)
      exactWork (Exact.charge (32*(tokens.length+1)^2))
      match readAll : declarations source with
      | .error _ => throw .request
      | .ok all =>
        let candidates := all.filter fun tokens => (header source declaration tokens).isOk
        match selected : candidates with
        | [tokens] =>
          have present : tokens ∈ all := by
            have member : tokens ∈ candidates := by rw [selected]; exact List.mem_cons_self
            exact (List.mem_filter.mp member).1
          match reading : header source declaration tokens with
          | .error _ => throw .request
          | .ok parsed =>
            if bytes : LocatedFacts.checkOrdered source.toUTF8 0 tokens = true then
              return ⟨source,declaration,bound,category,tokens,parsed,reading,⟨all,readAll,present⟩,
                LocatedFacts.checkOrdered_sound _ _ _ bytes⟩
            else throw .request
        | _ => throw .request
    else throw .request

structure QuantumReference (sources : Sources) where
  caller : String
  tokens : List LocatedToken
  resolution : CallName.Resolution sources caller (tokens.map (·.text))
  signature : QuantumSignatureCore.Checked sources resolution.result.moduleName resolution.result.declaration.name
  original : signature.original.source = resolution.result.source ∧ signature.original.declaration = resolution.result.declaration
  expectedEffect : Effect
  internalInference : Bool
  staticRows : List (String × String)
  rowsRead : ∃ before after,
    (StaticInstantiation.readRows signature.instantiation).run before = (.ok staticRows,after)

structure ClassicalReference (sources : Sources) where
  caller : String
  tokens : List LocatedToken
  resolution : CallName.Resolution sources caller (tokens.map (·.text))
  signature : OrdinarySignature.Checked sources resolution.result.moduleName resolution.result.declaration.name
  original : signature.original.source = resolution.result.source ∧ signature.original.declaration = resolution.result.declaration
  classical : signature.original.parsedHeader.ordinaryOnly = true
  instantiation : StaticInstantiation.Checked signature.original
  staticRows : List (String × String)
  rowsRead : ∃ before after,
    (StaticInstantiation.readRows instantiation).run before = (.ok staticRows,after)

inductive Action (sources : Sources) where
  | reference (function : QuantumReference sources)
  | permutation (function : ClassicalReference sources)
  | phase (function : ClassicalReference sources)
  | compose (left right : Nat)
  | tensor (left right : Nat)

def Action.remap {sources} (mapping : Nat → Nat) : Action sources → Action sources
  | .reference function => .reference function
  | .permutation function => .permutation function
  | .phase function => .phase function
  | .compose left right => .compose (mapping left) (mapping right)
  | .tensor left right => .tensor (mapping left) (mapping right)

structure Node (sources : Sources) where
  owner : String
  name : String
  original : Original sources owner name
  input : TypeRead sources
  output : TypeRead sources
  inputRead : ∃ before after,
    (typeExpressionWithSources sources owner original.parsed.ports.input).run before = (.ok input,after)
  outputRead : ∃ before after,
    (typeExpressionWithSources sources owner original.parsed.ports.output).run before = (.ok output,after)
  action : Action sources
  queryRows : List (String × String)

structure Graph (sources : Sources) where
  nodes : List (Node sources)
  root : Nat
  input : Basis
  output : Basis

def Graph.sourceRows {sources} (graph : Graph sources) : List (String × String) := graph.nodes.flatMap fun node =>
  (node.owner,node.original.source) :: node.input.sourceRows ++ node.output.sourceRows ++ node.queryRows

def Graph.references {sources} (graph : Graph sources) : List (QuantumReference sources) :=
  graph.nodes.filterMap fun node => match node.action with | .reference function => some function | _ => none

def Graph.classical {sources} (graph : Graph sources) : List (ClassicalReference sources) :=
  graph.nodes.filterMap fun node => match node.action with
    | .permutation function | .phase function => some function | _ => none

private def quantum (sources : Sources) (caller : String) (tokens : List LocatedToken)
    (input output : Basis) : WorkM (QuantumReference sources) := do
  let resolution ← CallName.resolve sources caller (tokens.map (·.text))
  let signature ← QuantumSignatureCore.prepareWithArguments sources resolution.result.moduleName resolution.result.declaration.name {}
  guard (signature.inputs == [input] && signature.outputs == [output] &&
    (match signature.parts with | .owner _ => true | _ => false)) .request
  let internal := resolution.result.moduleName == caller
  let effect := if input == output then Effect.unitary else .iso
  guard (internal || (signature.original.parsedHeader.effect == some .unitary ||
    (effect == .iso && signature.original.parsedHeader.effect == some .iso))) .request
  if original : signature.original.source = resolution.result.source ∧ signature.original.declaration = resolution.result.declaration then
    let rows ← NaturalAffine.witness (StaticInstantiation.readRows signature.instantiation)
    pure ⟨caller,tokens,resolution,signature,original,effect,internal,rows.val,
      by with_reducible exact rows.property⟩
  else throw .request

private def classical (sources : Sources) (caller : String) (tokens : List LocatedToken)
    (input output : Basis) : WorkM (ClassicalReference sources) := do
  let resolution ← CallName.resolve sources caller (tokens.map (·.text))
  let environment ← StaticTypes.prepare sources resolution.result.moduleName resolution.result.declaration.name {}
  let original := environment.numeric.original.envelope
  let inputs ← NaturalAffine.witness (OrdinarySignature.inputTypesWithSources sources resolution.result.moduleName
    original.parsedHeader.parameterTypes)
  let result ← NaturalAffine.witness (typeExpressionWithSources sources resolution.result.moduleName
    (original.parsedHeader.resultTokens.map (·.text)))
  let signature : OrdinarySignature.Checked sources resolution.result.moduleName resolution.result.declaration.name :=
    ⟨original,inputs.val,result.val,by with_reducible exact inputs.property,by with_reducible exact result.property⟩
  guard (signature.inputs == [input] && signature.basis == output) .request
  if original : signature.original.source = resolution.result.source ∧ signature.original.declaration = resolution.result.declaration then
    if classical : signature.original.parsedHeader.ordinaryOnly = true then
      let instantiation : StaticInstantiation.Checked signature.original := .static {} environment rfl
      let rows ← NaturalAffine.witness (StaticInstantiation.readRows instantiation)
      pure ⟨caller,tokens,resolution,signature,original,classical,instantiation,rows.val,
        by with_reducible exact rows.property⟩
    else throw .request
  else throw .request

def readGraph : Nat → (sources : Sources) → Option String → String → String → List (String × String) → WorkM (Graph sources) :=
  Nat.rec (fun _ _ _ _ _ => throw .limit) (fun _ next sources caller owner name active => do
    guard (!active.contains (owner,name)) .request
    let original ← readOriginal sources owner name
    guard (original.declaration.isPublic || caller == some owner) .request
    let input ← NaturalAffine.witness (typeExpressionWithSources sources owner original.parsed.ports.input)
    let output ← NaturalAffine.witness (typeExpressionWithSources sources owner original.parsed.ports.output)
    let _ ← FiniteCarrier.read input.val.basis
    let _ ← FiniteCarrier.read output.val.basis
    let make (action : Action sources) (rows : List (String × String)) : Node sources :=
      ⟨owner,name,original,input.val,output.val,by with_reducible exact input.property,
        by with_reducible exact output.property,action,rows⟩
    let call := original.parsed.body.call
    let [constructor] := call.callee.map (·.text) | throw .request
    match constructor,call.arguments with
    | "reference",[argument] =>
      let function ← quantum sources owner argument.tokens input.val.basis output.val.basis
      return ⟨[make (.reference function) (ResolutionProvenance.sourceRows function.resolution.result ++ function.signature.sourceRows ++ function.staticRows)],
        0,input.val.basis,output.val.basis⟩
    | "permutation_by",[argument] =>
      guard (input.val.basis == output.val.basis) .request
      let function ← classical sources owner argument.tokens input.val.basis output.val.basis
      return ⟨[make (.permutation function) (ResolutionProvenance.sourceRows function.resolution.result ++ function.signature.sourceRows ++ function.staticRows)],
        0,input.val.basis,output.val.basis⟩
    | "phase_by",[argument] =>
      guard (input.val.basis == output.val.basis) .request
      let function ← classical sources owner argument.tokens input.val.basis [.pair,.bit,.pair,.bit,.bit]
      return ⟨[make (.phase function) (ResolutionProvenance.sourceRows function.resolution.result ++ function.signature.sourceRows ++ function.staticRows)],
        0,input.val.basis,output.val.basis⟩
    | "compose",[first,second] | "tensor",[first,second] =>
      let leftResolution ← CallName.resolve sources owner (first.tokens.map (·.text))
      let rightResolution ← CallName.resolve sources owner (second.tokens.map (·.text))
      guard (leftResolution.result.declaration.kind == "meaning" && rightResolution.result.declaration.kind == "meaning") .request
      let left ← next sources (some owner) leftResolution.result.moduleName leftResolution.result.declaration.name ((owner,name)::active)
      let right ← next sources (some owner) rightResolution.result.moduleName rightResolution.result.declaration.name ((owner,name)::active)
      let tensor := constructor == "tensor"
      guard (if tensor then input.val.basis == .pair :: left.input ++ right.input &&
          output.val.basis == .pair :: left.output ++ right.output
        else input.val.basis == left.input && left.output == right.input && output.val.basis == right.output) .request
      guard (left.nodes.length+right.nodes.length+1 ≤ 4096) .limit
      exactWork (Exact.charge (32*(left.nodes.length+right.nodes.length+1)^2))
      let rightNodes := right.nodes.map fun node => {node with action := node.action.remap (·+left.nodes.length)}
      let action := if tensor then Action.tensor left.root (right.root+left.nodes.length)
        else Action.compose left.root (right.root+left.nodes.length)
      let rows := ResolutionProvenance.sourceRows leftResolution.result ++ ResolutionProvenance.sourceRows rightResolution.result
      pure ⟨left.nodes ++ rightNodes ++ [make action rows],left.nodes.length+right.nodes.length,input.val.basis,output.val.basis⟩
    | _,_ => throw .request)

structure Checked (sources : Sources) (caller : Option String) (owner name : String) where
  graph : Graph sources
  original : ∃ before after, (readGraph 65 sources caller owner name []).run before = (.ok graph,after)

def read (sources : Sources) (caller : Option String) (owner name : String) : WorkM (Checked sources caller owner name) := do
  let graph ← NaturalAffine.witness (readGraph 65 sources caller owner name [])
  pure ⟨graph.val,by with_reducible exact graph.property⟩

def decisionResolution {sources caller scope tokens} (decision : CallName.Decision sources caller scope tokens) : Option Resolved :=
  match decision with
  | .named resolution | .prelude _ _ _ _ _ _ _ _ resolution => some resolution.result
  | _ => none

structure Selected (sources : Sources) (caller : String) (scope tokens : List String) where
  decision : CallName.Decision sources caller scope tokens
  resolution : Resolved
  selected : decisionResolution decision = some resolution
  meaning : Checked sources (some caller) resolution.moduleName resolution.declaration.name
  queryRows : List (String × String)
  root : Node sources
  originalRoot : meaning.graph.nodes[meaning.graph.root]? = some root
  original : root.owner = resolution.moduleName ∧ root.name = resolution.declaration.name ∧
    root.original.source = resolution.source ∧ root.original.declaration = resolution.declaration

def select (sources : Sources) (caller : String) (scope tokens : List String) : WorkM (Selected sources caller scope tokens) := do
  let decision ← CallName.readTexts sources caller scope tokens
  match selected : decisionResolution decision with
  | none => throw .request
  | some resolution =>
    guard (resolution.declaration.kind == "meaning") .request
    let meaning ← read sources (some caller) resolution.moduleName resolution.declaration.name
    match originalRoot : meaning.graph.nodes[meaning.graph.root]? with
    | none => throw .request
    | some root =>
      if original : root.owner = resolution.moduleName ∧ root.name = resolution.declaration.name ∧
          root.original.source = resolution.source ∧ root.original.declaration = resolution.declaration then
        let rows := match decision with
          | .named resolution => ResolutionProvenance.sourceRows resolution.result
          | .prelude _ _ _ localMissing _ _ lookup _ resolution =>
            (caller,localMissing.lookup.source) :: ("std::prelude",lookup.source) :: ResolutionProvenance.sourceRows resolution.result
          | _ => []
        pure ⟨decision,resolution,selected,meaning,rows,root,originalRoot,original⟩
      else throw .request

end QleisliKernel.SourceTypes.SourceMeaning
