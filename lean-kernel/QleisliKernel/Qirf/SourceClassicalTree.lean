import QleisliKernel.Semantics.SourceClassical
import QleisliKernel.SourceTypes.SourceRuntimeContext
import QleisliKernel.SourceTypes.SourceNominal
import QleisliKernel.SourceTypes.SourceMatchLabels
import QleisliKernel.SourceTypes.SourceStaticSelection

/-! Fresh original ordinary syntax for the independent tree interpreter.
Every declaration, lexical call, parameter pattern, nominal member and static
condition is read from the actual original sources. No SourceRuntimeTrace
summary or producer result supplies a program node. A retained preparation
execution binds the resulting interpreter program to these reads; final
per-input agreement and Meaning/native equations remain mandatory callers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceClassicalTree
open QleisliKernel Finite SourceTypes
open Semantics.FiniteCarrier

private def adapt {α : Type} (action : Except String α) : WorkM α :=
  lift (action.mapError fun _ => .request)

def ordinaryBasis (tree : Semantics.RuntimeType.Tree) : Except String Basis :=
  tree.mapM fun atom => match atom with
    | .finite finite => pure finite
    | .quantum => throw "quantum marker in an ordinary interpreter interface"

def pattern (tokens : List String) : Except String Semantics.SourceClassical.Pattern := do
  let original ← QuantumMoves.parsePattern 65 tokens
  return original.map fun atom => match atom with
    | .name name => .name name
    | .wildcard => .wildcard
    | .tuple arity => .tuple arity

structure Original {sources} (catalogue : GenericCatalogue.Checked sources)
    (owner name caller : String) where
  signature : SourceRuntimeContext.Signature sources owner name
  signatureRead : ∃ before after,
    (SourceRuntimeContext.readSignature sources owner name {} (.source caller) (some catalogue)).run before =
      (.ok signature,after)
  tree : SourceSyntax.Tree signature.original.occurrence.body
  parsed : SourceSyntax.read (signature.original.occurrence.body.length+1) 0 true
    signature.original.occurrence.body = .ok tree
  rawPatterns : List (List String)
  parameters : QuantumOperands.parameterPatterns signature.original = .ok rawPatterns
  patterns : List Semantics.SourceClassical.Pattern
  patternsRead : rawPatterns.mapM pattern = .ok patterns
  inputs : List Basis
  inputRead : (signature.parameters.map (·.tree)).mapM ordinaryBasis = .ok inputs
  output : Basis
  outputRead : ordinaryBasis signature.result.tree = .ok output

structure Definition {sources} (catalogue : GenericCatalogue.Checked sources) where
  owner : String
  name : String
  caller : String
  original : Original catalogue owner name caller
  function : Semantics.SourceClassical.Function
  rows : List (String × String)

structure State {sources} (catalogue : GenericCatalogue.Checked sources) where
  definitions : List (Definition catalogue) := []

def State.functions {sources catalogue} (state : @State sources catalogue) : List Semantics.SourceClassical.Function :=
  state.definitions.map (·.function)

structure Accumulator {sources} (catalogue : GenericCatalogue.Checked sources) where
  state : State catalogue
  nodes : List Semantics.SourceClassical.Node := []
  rows : List (String × String) := []

private def add {sources catalogue} (accumulator : @Accumulator sources catalogue)
    (node : Semantics.SourceClassical.Node) (basis : Basis) : WorkM (Accumulator catalogue × Nat × Basis) := do
  exactWork (Exact.charge (16*(accumulator.nodes.length+node.children.length+basis.length+1)))
  guard (node.children.all (· < accumulator.nodes.length)) .request
  return ({accumulator with nodes := accumulator.nodes ++ [node]},accumulator.nodes.length,basis)

private def names (pattern : Semantics.SourceClassical.Pattern) : List String := pattern.filterMap fun atom => match atom with
  | .name name => some name
  | _ => none

private def parameterTypes (patterns : List Semantics.SourceClassical.Pattern) (types : List Basis) :
    Except String (List (String × Basis)) := do
  if patterns.length != types.length then throw "original ordinary parameter count"
  let bound := patterns.flatMap names
  if !decide bound.Nodup then throw "duplicate original ordinary parameter binding"
  (patterns.zip types).foldlM (fun environment (pattern,basis) =>
    Semantics.SourceClassical.bindTypes pattern basis environment) []

private def tupleBasis (fields : List Basis) : Basis :=
  (if fields.length == 2 then Atom.pair else .tuple fields.length) :: fields.flatten

private def readTerm {sources catalogue} (environment : List (String × Basis)) :
    Nat → QuantumMoves.Term → Accumulator catalogue →
      WorkM (QuantumMoves.Term × Accumulator catalogue × Nat × Basis) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next term accumulator => do
    let first :: rest := term | throw .request
    match first with
    | .wildcard => throw .request
    | .name name =>
      let some (_,basis) := environment.find? (·.1 == name) | throw .request
      let (accumulator,index,basis) ← add accumulator (.variable name) basis
      return (rest,accumulator,index,basis)
    | .tuple 0 =>
      let (accumulator,index,basis) ← add accumulator .unit [.unit]
      return (rest,accumulator,index,basis)
    | .tuple arity =>
      let (remaining,accumulator,indices,bases) ← (List.range arity).foldlM
        (fun (remaining,accumulator,indices,bases) _ => do
          let (remaining,accumulator,index,basis) ← next remaining accumulator
          return (remaining,accumulator,indices ++ [index],bases ++ [basis])) (rest,accumulator,[],[])
      let (accumulator,index,basis) ← add accumulator (.tuple indices) (tupleBasis bases)
      return (remaining,accumulator,index,basis))

/-- The callback freshly reads the exact original callee; ordinary argument
evaluation order and caller lexical scope stay in the original syntax tree. -/
def readTree {sources owner name} (catalogue : GenericCatalogue.Checked sources)
    (signature : SourceRuntimeContext.Signature sources owner name)
    (callee : String → String → String → State catalogue → WorkM (State catalogue × Nat)) :
    Nat → PhaseApplication.Naturals sources → List (String × Basis) →
    {tokens : List LocatedToken} → SourceSyntax.Tree tokens → Accumulator catalogue →
    WorkM (Accumulator catalogue × Nat × Basis) :=
  Nat.rec (fun _ _ {_} _ _ => throw .limit)
    (fun _ next naturals environment {tokens} tree accumulator => do
      exactWork (Exact.charge (16*((tokens.map fun token => token.text.utf8ByteSize+4).sum+
        (environment.map fun (name,basis) => name.utf8ByteSize+basis.length).sum+1)))
      let scope := signature.staticNames ++ environment.map (·.1)
      let children (trees : List (Sigma SourceSyntax.Tree)) (accumulator : Accumulator catalogue) :=
        trees.foldlM (fun (accumulator,indices,bases) child => do
          let (accumulator,index,basis) ← next naturals environment child.2 accumulator
          return (accumulator,indices ++ [index],bases ++ [basis])) (accumulator,[],[])
      match tree with
      | .empty .. => add accumulator .unit [.unit]
      | .literal _ value _ => add accumulator (.bit value) [.bit]
      | .move _ term _ =>
        let (rest,accumulator,index,basis) ← readTerm environment (term.length+1) term accumulator
        guard rest.isEmpty .request
        pure (accumulator,index,basis)
      | .group group trees =>
        let (accumulator,indices,bases) ← children trees.trees accumulator
        if indices.isEmpty then add accumulator .unit [.unit]
        else if indices.length == 1 && (group.group.arguments.head?.bind (·.followingComma)).isNone then
          return (accumulator,← lift (readOption indices.head?),← lift (readOption bases.head?))
        else add accumulator (.tuple indices) (tupleBasis bases)
      | .boolean written trees =>
        let (accumulator,indices,bases) ← children trees.trees accumulator
        guard (bases.all (· == [.bit])) .request
        match written.operator,indices with
        | .not,[child] => add accumulator (.not child) [.bit]
        | .xor,[first,second] => add accumulator (.xor first second) [.bit]
        | .and,[first,second] => add accumulator (.and first second) [.bit]
        | _,_ => throw .request
      | .binding written expression rest =>
        let (accumulator,first,basis) ← next naturals environment expression accumulator
        let bound ← adapt (pattern (written.statement.pattern.map (·.text)))
        guard ((names bound).all fun name => !naturals.staticNames.contains name) .request
        let after ← adapt (Semantics.SourceClassical.bindTypes bound basis environment)
        let (accumulator,last,result) ← next naturals after rest accumulator
        add accumulator (.binding bound first last) result
      | .sequence _ expression rest =>
        let (accumulator,first,_) ← next naturals environment expression accumulator
        let (accumulator,last,basis) ← next naturals environment rest accumulator
        add accumulator (.sequence first last) basis
      | .staticBindings leading _ rest =>
        let (naturals,_) ← PhaseApplication.extend sources owner leading naturals scope
        let accumulator := {accumulator with rows := accumulator.rows ++ naturals.sourceRows}
        next naturals environment rest accumulator
      | .conditional _ condition left right =>
        let (accumulator,condition,conditionType) ← next naturals environment condition accumulator
        guard (conditionType == [.bit]) .request
        let (accumulator,left,leftType) ← next naturals environment left accumulator
        let (accumulator,right,rightType) ← next naturals environment right accumulator
        guard (leftType == rightType) .request
        add accumulator (.conditional condition left right) leftType
      | .staticConditional written left right =>
        let selected ← SourceStaticSelection.read sources owner naturals scope written
        let (accumulator,left,leftType) ← next selected.naturals environment left accumulator
        let (accumulator,right,rightType) ← next selected.naturals environment right accumulator
        guard (leftType == rightType) .request
        let accumulator := {accumulator with rows := accumulator.rows ++ selected.naturals.sourceRows}
        add accumulator (.staticConditional selected.selected left right) leftType
      | .variant written =>
        let reference ← SourceNominal.readVariant sources owner scope written
        let rows ← NaturalRows.typeRead sources owner naturals.helpers.val scope
          (written.typeTokens.map (·.text)) reference.nominal.query
        add {accumulator with rows := accumulator.rows ++ rows}
          (.variant reference.nominal.query.basis reference.ordinal) reference.nominal.query.basis
      | .record written trees =>
        let reference ← SourceNominal.readRecord sources owner scope written
        let (accumulator,indices,bases) ← children trees.trees accumulator
        guard (bases == reference.fields.map (·.basis)) .request
        let original : Semantics.SourceClassical.Record := ⟨reference.nominal.query.basis,
          reference.definition.fields.map fun field => (field.member.name.text,field.basis)⟩
        let rows ← NaturalRows.typeRead sources owner naturals.helpers.val scope
          (written.typeTokens.map (·.text)) reference.nominal.query
        add {accumulator with rows := accumulator.rows ++ rows}
          (.record original ((written.initializers.map (·.name.text)).zip indices)) reference.nominal.query.basis
      | .projection written receiver =>
        let (accumulator,index,basis) ← next naturals environment receiver accumulator
        let reference ← SourceNominal.readProjection sources owner basis written
        let original : Semantics.SourceClassical.Record := ⟨basis,
          reference.definition.fields.map fun field => (field.member.name.text,field.basis)⟩
        let rows ← NaturalRows.nominalOrigins sources naturals.helpers.val basis
        add {accumulator with rows := accumulator.rows ++ rows}
          (.projection original reference.index index) reference.field.basis
      | .matching written scrutinee trees =>
        let (accumulator,scrutinee,basis) ← next naturals environment scrutinee accumulator
        let labels ← SourceMatchLabels.read sources owner naturals.helpers.val scope written basis
        let (accumulator,indices,bases) ← children trees.trees accumulator
        let some output := bases.head? | throw .request
        guard (bases.all (· == output)) .request
        add {accumulator with rows := accumulator.rows ++ labels.labels.sourceRows}
          (.matching scrutinee labels.labels.ordinals indices) output
      | .call written trees =>
        let (accumulator,indices,bases) ← children trees.trees accumulator
        let .name _ ← adapt (StaticApplication.readSyntax written.call.callee) | throw .request
        let candidate ← CallName.readWithModules sources (some catalogue.modulesContext) owner scope written.call.callee
        match candidate.decision with
        | .primitive _ _ _ _ _ _ .emptyBits _ =>
          guard indices.isEmpty .request
          add {accumulator with rows := accumulator.rows ++ CallName.sourceRows candidate} .emptyBits [.bits 0]
        | _ =>
          let some resolved := CallName.candidateResolution candidate | throw .request
          let (state,index) ← callee resolved.moduleName resolved.declaration.name owner accumulator.state
          let some target := state.definitions[index]? | throw .request
          guard (target.function.inputs == bases) .request
          add {accumulator with state := state,rows := accumulator.rows ++ CallName.sourceRows candidate}
            (.call index indices) target.function.output
      | _ => throw .request)

/-- Read each actual original body and every callee from the same Sources.
No symbolic source Value, execution result or cached map participates. -/
def readFunction {sources} (catalogue : GenericCatalogue.Checked sources) (fuel : Nat)
    (active : List (String × String)) (owner name caller : String) (state : State catalogue) :
    WorkM (State catalogue × Nat) := do
  match fuel with
  | 0 => throw .limit
  | fuel+1 =>
    guard (!active.contains (owner,name)) .request
    let signature ← NaturalAffine.witness (SourceRuntimeContext.readSignature sources owner name {}
      (.source caller) (some catalogue))
    guard (signature.val.original.declaration.isPublic || caller == owner) .request
    let inferred ← GenericCatalogue.lookup catalogue.toRuntimeChecked signature.val.original
    guard (SourceEffect.visible caller owner signature.val.original.declaration.isPublic
      signature.val.original.parsedHeader.effect inferred.inferred.inferredEffect == .unitary) .request
    let externalPermission := caller != owner && signature.val.original.declaration.isPublic &&
      !signature.val.original.parsedHeader.ordinaryOnly && signature.val.original.parsedHeader.effect.isSome
    guard (!externalPermission && !inferred.inferred.quantumUse) .request
    let tokens := signature.val.original.occurrence.body
    exactWork (Exact.charge (32*(SourceTrace.Meter.tokenFields tokens+1)))
    match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
    | .error _ => throw .request
    | .ok tree =>
      match parameters : QuantumOperands.parameterPatterns signature.val.original with
      | .error _ => throw .request
      | .ok rawPatterns =>
        match patternsRead : rawPatterns.mapM pattern with
        | .error _ => throw .request
        | .ok patterns =>
          match inputRead : (signature.val.parameters.map (·.tree)).mapM ordinaryBasis with
          | .error _ => throw .request
          | .ok inputs =>
            match outputRead : ordinaryBasis signature.val.result.tree with
            | .error _ => throw .request
            | .ok output =>
              let environment ← adapt (parameterTypes patterns inputs)
              let naturals ← signature.val.naturals
              let (built,root,basis) ← readTree catalogue signature.val
                (fun calleeOwner calleeName callingModule state =>
                  readFunction catalogue fuel ((owner,name)::active) calleeOwner calleeName callingModule state)
                (tokens.length+1) naturals environment tree ⟨state,[],[]⟩
              guard (basis == output) .request
              let function : Semantics.SourceClassical.Function := ⟨inputs,output,patterns,built.nodes,root⟩
              let original : Original catalogue owner name caller :=
                ⟨signature.val,by with_reducible exact signature.property,tree,parsed,rawPatterns,parameters,
                  patterns,patternsRead,inputs,inputRead,output,outputRead⟩
              let definition : Definition catalogue :=
                ⟨owner,name,caller,original,function,signature.val.sourceRows ++ naturals.sourceRows ++ built.rows⟩
              return (⟨built.state.definitions ++ [definition]⟩,built.state.definitions.length)
termination_by fuel

structure Prepared {sources} (catalogue : GenericCatalogue.Checked sources) (owner name caller : String) where
  state : State catalogue
  root : Nat
  original : ∃ before after,
    (readFunction catalogue (SourceTrace.sourceFuel sources) [] owner name caller {}).run before = (.ok (state,root),after)

def prepare {sources} (catalogue : GenericCatalogue.Checked sources) (owner name caller : String) :
    WorkM (Prepared catalogue owner name caller) := do
  let program ← NaturalAffine.witness
    (readFunction catalogue (SourceTrace.sourceFuel sources) [] owner name caller {})
  return ⟨program.val.1,program.val.2,by with_reducible exact program.property⟩

def Prepared.sourceRows {sources catalogue owner name caller}
    (prepared : @Prepared sources catalogue owner name caller) : List (String × String) :=
  prepared.state.definitions.flatMap (·.rows)

end QleisliKernel.Qirf.SourceClassicalTree
