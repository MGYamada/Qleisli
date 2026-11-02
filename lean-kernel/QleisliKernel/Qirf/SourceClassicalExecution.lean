import QleisliKernel.Semantics.SourceClassical
import QleisliKernel.FiniteCarrier
import QleisliKernel.Raw.OwnerFlow
import QleisliKernel.SourceTypes.NaturalAffine

/-! Charged execution of the independent ordinary reference program.
The complete original type metadata is retained and checked once. Execution
charges each actual node, environment, binding and call boundary before use;
it does not multiply all nominal source bytes by all port bytes at every row.
Every result retains an equation for the unchanged independent evaluator.
This grants no original-source binding, Meaning equation or execution handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceClassicalExecution
open QleisliKernel Finite Semantics.FiniteCarrier
open Semantics.SourceClassical

abbrev Result {α : Type} (action : Except String α) := {value : α // action = .ok value}

private def runPure {α : Type} (action : Except String α) : WorkM (Result action) :=
  match action with
  | .error _ => throw .request
  | .ok value => pure ⟨value,rfl⟩

/-- Freeze the returned payload while replacing only the first computation.
Rewriting the entire dependent Result type would also abstract its projection. -/
private theorem bindResult {α β : Type} {action : Except String α} (result : Result action)
    (next : α → Except String β) :
    (do let value ← action; next value) = next result.val :=
  congrArg (fun computation : Except String α => computation >>= next) result.property

private theorem nodeAt (nodes : List Node) (callee : Nat → List Value → Except String Value)
    (fuel : Nat) (environment : Environment) (index : Nat) (node : Node)
    (present : nodes[index]? = some node) :
    evaluateNode nodes callee (fuel+1) environment index =
      nodeAction callee (evaluateNode nodes callee fuel) environment node := by
  simp only [evaluateNode_succ,present]

private theorem functionAt (functions : List Function) (fuel index : Nat) (arguments : List Value)
    (function : Function) (present : functions[index]? = some function) :
    evaluate functions (fuel+1) index arguments = functionAction (evaluate functions fuel) function arguments := by
  simp only [evaluate_succ,present]

def basisCells (basis : Basis) : Nat := Raw.OwnerFlow.fields [⟨0,basis⟩]

def valueCells (value : Value) : Nat := value.foldl (fun count atom => count+match atom with
  | .owner owner => Raw.OwnerFlow.fields [owner]
  | .ordinary basis _ => basisCells basis+1
  | .tuple _ => 1) 0

def environmentCells (environment : Environment) : Nat :=
  (environment.map fun (name,value) => name.utf8ByteSize+valueCells value+1).sum

def patternCells (pattern : Pattern) : Nat := pattern.foldl (fun count atom => count+1+match atom with
  | .name name => name.utf8ByteSize
  | .tuple arity => arity
  | _ => 0) 0

def nodeCells (node : Node) : Nat := node.children.length+1+match node with
  | .variable name => name.utf8ByteSize
  | .binding pattern _ _ => patternCells pattern
  | .variant basis _ => basisCells basis
  | .record original written => basisCells original.basis+
      (original.fields.map fun (name,basis) => name.utf8ByteSize+basisCells basis+1).sum+
      (written.map fun (name,_) => name.utf8ByteSize+1).sum
  | .projection original _ _ => basisCells original.basis+
      (original.fields.map fun (name,basis) => name.utf8ByteSize+basisCells basis+1).sum
  | .matching _ labels bodies => (labels.length+1)*(bodies.length+1)
  | _ => 0

private def nodeBases : Node → List Basis
  | .variant basis _ => [basis]
  | .record original _ | .projection original _ _ => original.basis :: original.fields.map (·.2)
  | _ => []

def programBases (functions : List Function) : List Basis := functions.flatMap fun function =>
  function.inputs ++ [function.output] ++ function.nodes.flatMap nodeBases

private def shapeCells (basis : Basis) : Nat := (basis.map fun atom => match atom with
  | .pair => 3
  | .tuple arity => arity+1
  | .record _ fields => fields.length+1
  | _ => 1).sum

private def scalarBasesWith : Nat → Basis → Except String (List Basis) :=
  Nat.rec (fun _ => throw "ordinary metadata traversal capacity") (fun _ next basis => do
    match basis with
    | .pair :: _ | .tuple _ :: _ =>
      return (← (← basisFields basis).mapM next).flatten
    | _ => pure [basis])

def scalarBases (basis : Basis) : Except String (List Basis) :=
  scalarBasesWith (basis.length+1) basis

structure Entry where
  basis : Basis
  code : Layout
  computed : ∃ before after,(FiniteCarrier.read basis).run before = (.ok code,after)

theorem Entry.reference (entry : Entry) : Semantics.FiniteCarrier.layout entry.basis = some entry.code := by
  obtain ⟨before,after,computed⟩ := entry.computed
  exact FiniteCarrier.read_reference _ _ _ _ computed

structure Metadata (functions : List Function) where
  scalars : List Basis
  shapes : ((programBases functions).mapM scalarBases).map List.flatten = .ok scalars
  entries : List Entry
  complete : entries.map (·.basis) = scalars.eraseDups

theorem Metadata.every {functions} (metadata : Metadata functions) (basis : Basis)
    (member : basis ∈ metadata.scalars) :
    ∃ entry ∈ metadata.entries,entry.basis = basis ∧ Semantics.FiniteCarrier.layout basis = some entry.code := by
  have cached : basis ∈ metadata.entries.map (·.basis) := by
    rw [metadata.complete]
    simpa only [List.mem_eraseDups] using member
  obtain ⟨entry,present,same⟩ := List.mem_map.mp cached
  refine ⟨entry,present,same,?_⟩
  rw [← same]
  exact entry.reference

/-- This cache shares only exact immutable type/layout reads. Full original
nominal origins remain in every stored basis, and all raw metadata comparisons
are reserved before eraseDups. Tuple forests retain their full shape but read
their scalar value fields separately, imposing no new joined-width limit.
No source/provider occurrence is deduplicated. -/
def readMetadata (functions : List Function) : WorkM (Metadata functions) := do
  let bases := programBases functions
  exactWork (Exact.charge (32*((bases.map shapeCells).sum+1)*((bases.map basisCells).sum+1)))
  let scalars ← runPure ((bases.mapM scalarBases).map List.flatten)
  let entries ← scalars.val.eraseDups.mapM fun basis => do
    let code ← SourceTypes.NaturalAffine.witness (FiniteCarrier.read basis)
    pure (⟨basis,code.val,by with_reducible exact code.property⟩ : Entry)
  if complete : entries.map (·.basis) = scalars.val.eraseDups then
    return ⟨scalars.val,scalars.property,entries,complete⟩
  else throw .request

def Metadata.codeCells {functions} (metadata : Metadata functions) : Nat :=
  (metadata.entries.map fun entry => (entry.basis.length+1)*(entry.code.bits+1)*(entry.code.labels.length+1)).sum

/-- Bound every scalar layout before valueBasis can enumerate it. Canonical
source inputs and genuine callee arguments use these exact prepared types;
a foreign or malformed scalar cannot trigger an unbounded layout computation.
Tuple markers and zero-width scalar fields remain separate. -/
private def readArguments {functions} (metadata : Metadata functions) (arguments : List Value) : WorkM Unit := do
  let bases := arguments.flatten.filterMap fun atom => match atom with
    | .ordinary basis _ => some basis
    | _ => none
  let stored := metadata.entries.map (·.basis)
  exactWork (Exact.charge (32*(bases.length+1)*
    ((stored.map basisCells).sum+(bases.map basisCells).sum+1)))
  guard (bases.all stored.contains) .request

private def readList {α β : Type} (reference : α → Except String β)
    (action : (value : α) → WorkM (Result (reference value))) :
    (values : List α) → WorkM (Result (values.mapM reference))
  | [] => pure ⟨[],rfl⟩
  | first :: rest => do
    exactWork (Exact.charge 32)
    let head ← action first
    let tail ← readList reference action rest
    return ⟨head.val :: tail.val,by
      simp only [List.mapM_cons]
      exact (bindResult head (fun value => do
        let rest ← rest.mapM reference
        pure (value :: rest))).trans (bindResult tail (fun rest => .ok (head.val :: rest)))⟩

/-- Each recursive call carries the exact independent child equation. The
reservation covers the literal node lookup, complete current value frame,
original node metadata, finite layout work and each immediate child use. -/
def readNode {functions} (metadata : Metadata functions) (nodes : List Node)
    (callee : Nat → List Value → Except String Value)
    (readCallee : (index : Nat) → (arguments : List Value) → WorkM (Result (callee index arguments))) :
    (fuel : Nat) → (environment : Environment) → (index : Nat) →
      WorkM (Result (evaluateNode nodes callee fuel environment index)) :=
  Nat.rec (motive := fun fuel => (environment : Environment) → (index : Nat) →
      WorkM (Result (evaluateNode nodes callee fuel environment index)))
    (fun _ _ => throw .limit) (fun fuel next environment index => do
      exactWork (Exact.charge (32*(nodes.length+1)))
      match present : nodes[index]? with
      | none => throw .request
      | some node =>
        exactWork (Exact.charge (32*(nodeCells node+environmentCells environment+metadata.codeCells+1)*
          (node.children.length+1)))
        let child := next environment
        let reference := evaluateNode nodes callee fuel environment
        match kind : node with
        | .unit | .bit _ | .emptyBits | .variable _ | .variant .. =>
          let result ← runPure (nodeAction callee (evaluateNode nodes callee fuel) environment node)
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((congrArg (nodeAction callee (evaluateNode nodes callee fuel) environment) kind).symm.trans
                result.property)⟩
        | .tuple fields =>
          let values ← readList reference child fields
          return ⟨.tuple fields.length :: values.val.flatten,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              (bindResult values (fun values => .ok ((.tuple fields.length :: values.flatten) : Value)))⟩
        | .not input =>
          let value ← child input
          let result ← runPure (do
            let value ← bitValue value.val
            pure [.ordinary [.bit] (1-value)])
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult value (fun value => do
                let value ← bitValue value
                pure [.ordinary [.bit] (1-value)])).trans result.property)⟩
        | .xor first second =>
          let first ← child first
          let a ← runPure (bitValue first.val)
          let second ← child second
          let b ← runPure (bitValue second.val)
          return ⟨[.ordinary [.bit] (if a.val == b.val then 0 else 1)],by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult first (fun first => do
                let a ← bitValue first
                let second ← reference _
                let b ← bitValue second
                pure [.ordinary [.bit] (if a == b then 0 else 1)])).trans
              ((bindResult a (fun a => do
                let second ← reference _
                let b ← bitValue second
                pure [.ordinary [.bit] (if a == b then 0 else 1)])).trans
              ((bindResult second (fun second => do
                let b ← bitValue second
                pure [.ordinary [.bit] (if a.val == b then 0 else 1)])).trans
                (bindResult b (fun b => .ok [.ordinary [.bit] (if a.val == b then 0 else 1)])))))⟩
        | .and first second =>
          let first ← child first
          let a ← runPure (bitValue first.val)
          let second ← child second
          let b ← runPure (bitValue second.val)
          return ⟨[.ordinary [.bit] (if a.val == 1 && b.val == 1 then 1 else 0)],by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult first (fun first => do
                let a ← bitValue first
                let second ← reference _
                let b ← bitValue second
                pure [.ordinary [.bit] (if a == 1 && b == 1 then 1 else 0)])).trans
              ((bindResult a (fun a => do
                let second ← reference _
                let b ← bitValue second
                pure [.ordinary [.bit] (if a == 1 && b == 1 then 1 else 0)])).trans
              ((bindResult second (fun second => do
                let b ← bitValue second
                pure [.ordinary [.bit] (if a.val == 1 && b == 1 then 1 else 0)])).trans
                (bindResult b (fun b => .ok [.ordinary [.bit] (if a.val == 1 && b == 1 then 1 else 0)])))))⟩
        | .conditional condition left right =>
          let condition ← child condition
          let selected ← runPure (bitValue condition.val)
          let result ← child (if selected.val == 1 then left else right)
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult condition (fun condition => do
                let selected ← bitValue condition
                reference (if selected == 1 then left else right))).trans
              ((bindResult selected (fun selected => reference (if selected == 1 then left else right))).trans
                result.property))⟩
        | .staticConditional selected left right =>
          let result ← child (if selected then left else right)
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans result.property⟩
        | .binding pattern value rest =>
          let value ← child value
          exactWork (Exact.charge (32*(patternCells pattern+1)*
            (valueCells value.val+environmentCells environment+1)))
          let bound ← runPure (bind pattern value.val environment)
          let result ← next bound.val rest
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult value (fun value => do
                let bound ← bind pattern value environment
                evaluateNode nodes callee fuel bound rest)).trans
              ((bindResult bound (fun bound => evaluateNode nodes callee fuel bound rest)).trans result.property))⟩
        | .sequence first rest =>
          let first ← child first
          let result ← child rest
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult first (fun _ => reference rest)).trans result.property)⟩
        | .record original written =>
          let values ← readList (fun (name,index) => do return (name,← reference index))
            (fun (name,index) => do
              let value ← child index
              return ⟨(name,value.val),bindResult value (fun value => .ok (name,value))⟩) written
          let result ← runPure (construct original values.val)
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult values (construct original)).trans result.property)⟩
        | .projection original field receiver =>
          let receiver ← child receiver
          let result ← runPure (project original field receiver.val)
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult receiver (project original field)).trans result.property)⟩
        | .matching scrutinee labels bodies =>
          let scrutinee ← child scrutinee
          let selected ← runPure (selectMatch labels bodies scrutinee.val)
          let result ← child selected.val
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult scrutinee (fun scrutinee => do
                let selected ← selectMatch labels bodies scrutinee
                reference selected)).trans
              ((bindResult selected reference).trans result.property))⟩
        | .call function arguments =>
          let arguments ← readList reference child arguments
          let result ← readCallee function arguments.val
          return ⟨result.val,by
            exact (nodeAt nodes callee fuel environment index _ present).trans
              ((bindResult arguments (callee function)).trans result.property)⟩)

/-- Actual ordinary calls retain complete source types and fresh local pattern
bindings. The shared type cache is unchanged across every canonical input. -/
def read {functions} (metadata : Metadata functions) :
    (fuel index : Nat) → (arguments : List Value) → WorkM (Result (evaluate functions fuel index arguments)) :=
  Nat.rec (motive := fun fuel => (index : Nat) → (arguments : List Value) →
      WorkM (Result (evaluate functions fuel index arguments)))
    (fun _ _ => throw .limit) (fun fuel next index arguments => do
      exactWork (Exact.charge (32*(functions.length+1)))
      match present : functions[index]? with
      | none => throw .request
      | some function =>
        let argumentCells := (arguments.map valueCells).sum
        let patterns := (function.patterns.map patternCells).sum
        exactWork (Exact.charge (32*(argumentCells+(function.inputs.map basisCells).sum+
          metadata.codeCells+1)*(patterns+1)))
        readArguments metadata arguments
        let environment ← runPure (bindArguments function arguments)
        let result ← readNode metadata function.nodes (evaluate functions fuel)
          next (function.nodes.length+1) environment.val function.root
        exactWork (Exact.charge (32*(valueCells result.val+basisCells function.output+metadata.codeCells+1)))
        let checked ← runPure (checkResult function.output result.val)
        return ⟨checked.val,by
          exact (functionAt functions fuel index arguments function present).trans
            ((bindResult environment (fun environment => do
              let result ← evaluateNode function.nodes (evaluate functions fuel) (function.nodes.length+1)
                environment function.root
              checkResult function.output result)).trans
            ((bindResult result (checkResult function.output)).trans checked.property))⟩)

end QleisliKernel.Qirf.SourceClassicalExecution
