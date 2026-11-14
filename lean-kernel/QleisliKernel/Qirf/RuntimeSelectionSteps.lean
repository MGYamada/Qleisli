import QleisliKernel.Qirf.RuntimeSelectionWitness

/-! Literal witnesses on the original ordered mixed-body steps.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeSelectionSteps
open QleisliKernel Finite RuntimePureBody

/-- The ordinal is the position inside this exact body or branch. A pure
step keeps its ordinal when entered as a node. Child bodies start at zero. -/
inductive Item (dependencies : List Semantics.Finite.Dependency) where
  | node {program block} (ordinal : Nat) (value : Node dependencies program block)
  | nodes {program block} (ordinal : Nat) (value : Nodes dependencies program block)
  | step {program block} (ordinal : Nat) (value : Step dependencies program block)
  | steps {program block} (ordinal : Nat) (value : Steps dependencies program block)

-- This relation occurs only in proofs. In particular there is no executable
-- function computing a sizeOf over an indexed source body or its receipts.
private def Smaller {dependencies} (left right : Item dependencies) : Prop :=
  let rank : Item dependencies → Nat := fun item => match item with
    | .node _ v => sizeOf v | .nodes _ vs => sizeOf vs
    | .step _ v => sizeOf v | .steps _ vs => sizeOf vs
  rank left < rank right

private theorem smallerWF {dependencies} : WellFounded (@Smaller dependencies) :=
  (measure (fun item : Item dependencies => match item with
    | .node _ v => sizeOf v | .nodes _ vs => sizeOf vs
    | .step _ v => sizeOf v | .steps _ vs => sizeOf vs)).wf

inductive Edge where
  | atOrdinal (ordinal : Nat)
  | nextOrdinal (ordinal : Nat)
  | pureStep (ordinal : Nat)
  | named (ordinal : Nat) (callerOwner callerName : String) (offset : Nat) (owner name : String)
  | transform (ordinal : Nat) (callerOwner callerName : String) (offset : Nat) (owner name : String)
  | thenBranch (ordinal : Nat)
  | elseBranch (ordinal : Nat)
  deriving BEq, Repr

private def namedEdge {sources caller} (ordinal : Nat) (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller) : Edge :=
  .named ordinal caller event.target.callerName event.call.calleeOffset
    event.target.resolution.moduleName event.target.resolution.declaration.name

private inductive View (dependencies : List Semantics.Finite.Dependency) (parent : Item dependencies) where
  | leaf
  | selection {program block} (ordinal : Nat) (value : Node dependencies program block)
  | child (edge : Edge) (one : Item dependencies) (decreases : Smaller one parent)
  | pair (firstEdge : Edge) (first : Item dependencies) (restEdge : Edge) (rest : Item dependencies) (smallerFirst : Smaller first parent)
      (smallerRest : Smaller rest parent)

private def inspect {dependencies} : (item : Item dependencies) → View dependencies item
  | .node ordinal node@(.selection ..) => .selection ordinal node
  | .node ordinal (.named event _ _ _ _ nested) => .child (namedEdge ordinal event) (.nodes 0 nested) (by simp only [Smaller] <;> decreasing_tactic)
  | .node ordinal (.transform (caller := caller) (event := event) _ _ _ _ _ _ _ nested) =>
    .child (.transform ordinal caller event.callerName event.call.calleeOffset
      event.target.resolution.moduleName event.target.resolution.declaration.name) (.nodes 0 nested)
      (by simp only [Smaller] <;> decreasing_tactic)
  | .node _ (.primitive ..) | .node _ (.structural _) | .node _ (.basis ..)
  | .node _ (.computed ..) | .node _ (.certifiedComputed ..) | .node _ (.workspace ..) | .node _ (.operation ..) => .leaf
  | .node _ (.rectangularOperation _) | .node _ (.structuralComputed ..) => .leaf
  | .nodes _ .nil => .leaf
  | .nodes ordinal (.cons first rest) => .pair (.atOrdinal ordinal) (.node ordinal first) (.nextOrdinal (ordinal+1)) (.nodes (ordinal+1) rest)
      (by simp only [Smaller] <;> decreasing_tactic) (by simp only [Smaller] <;> decreasing_tactic)
  | .step ordinal (.pure node) => .child (.pureStep ordinal) (.node ordinal node) (by simp only [Smaller] <;> decreasing_tactic)
  | .step _ (.gap _) | .step _ (.observation _) => .leaf
  | .step ordinal (.named event _ _ _ _ _ nested) => .child (namedEdge ordinal event) (.steps 0 nested) (by simp only [Smaller] <;> decreasing_tactic)
  | .step ordinal (.conditional _ _ _ _ _ _ left right) => .pair (.thenBranch ordinal) (.steps 0 left) (.elseBranch ordinal) (.steps 0 right)
      (by simp only [Smaller] <;> decreasing_tactic) (by simp only [Smaller] <;> decreasing_tactic)
  | .steps _ .nil => .leaf
  | .steps ordinal (.cons first rest) => .pair (.atOrdinal ordinal) (.step ordinal first) (.nextOrdinal (ordinal+1)) (.steps (ordinal+1) rest)
      (by simp only [Smaller] <;> decreasing_tactic) (by simp only [Smaller] <;> decreasing_tactic)

/-- A pair is the ordered head and tail of a source list, or the then and
else children of the actual conditional. Its indices preserve both runs,
even when they contain equal operations or identical selector actions. -/
inductive Witness {dependencies} : Item dependencies → Nat → Type where
  | leaf {item} (original : inspect item = .leaf) : Witness item 0
  | selection {item ordinal program block} {node : Node dependencies program block}
      (original : inspect item = .selection ordinal node)
      (literal : RuntimeSelectionWitness.Checked node)
      (obtained : RuntimeInterval.Computed (RuntimeSelectionWitness.read node) literal) : Witness item 1
  | child {item edge one count decrease} (original : inspect item = .child edge one decrease)
      (nested : Witness one count) : Witness item count
  | pair {item firstEdge first restEdge rest a b smallerFirst smallerRest}
      (original : inspect item = .pair firstEdge first restEdge rest smallerFirst smallerRest)
      (head : Witness first a) (tail : Witness rest b) : Witness item (a+b)

private def read {dependencies} (item : Item dependencies) : WorkM (Σ count,Witness item count) :=
  WellFounded.fix (smallerWF (dependencies := dependencies))
    (C := fun current => WorkM (Σ count,Witness current count))
    (fun current next => do
      exactWork (Exact.charge 8)
      match original : inspect current with
      | .leaf => return ⟨0,.leaf original⟩
      | .selection _ node =>
        let held ← SourceTypes.NaturalAffine.witness (RuntimeSelectionWitness.read node)
        return ⟨1,.selection original held.val (by with_reducible exact held.property)⟩
      | .child _ one smaller =>
        let held ← next one smaller
        return ⟨held.1,.child original held.2⟩
      | .pair _ first _ rest smallerFirst smallerRest =>
        let a ← next first smallerFirst
        let b ← next rest smallerRest
        return ⟨a.1+b.1,.pair original a.2 b.2⟩) item

structure Checked {dependencies program block} (result : BlockResult dependencies program block) where
  count : Nat
  witness : Witness (.steps 0 (Steps.ofList result.steps)) count
  obtained : RuntimeInterval.Computed (read (.steps 0 (Steps.ofList result.steps))) ⟨count,witness⟩

/-- Receives the previously retained BlockResult. Only the mixed steps
contain the complete coverage, including observation/classical-only cases. -/
def readResult {dependencies program block} (result : BlockResult dependencies program block) : WorkM (Checked result) := do
  exactWork (Exact.charge (8*(result.steps.length+1)))
  let held ← SourceTypes.NaturalAffine.witness (read (.steps 0 (Steps.ofList result.steps)))
  return ⟨held.val.1,held.val.2,by with_reducible exact held.property⟩

/-- Locate an actual checked coherent-table interval using the same ordered mixed-body
tree. Merely supplying a position or a physical lift does not satisfy this. -/
private def hasBasis {dependencies} (item : Item dependencies) : WorkM Bool :=
  WellFounded.fix (smallerWF (dependencies := dependencies))
    (C := fun _ => WorkM Bool)
    (fun current next => do
      exactWork (Exact.charge 8)
      match inspect current with
      | .leaf =>
        match current with
        | .node _ (.basis ..) | .node _ (.computed ..) | .node _ (.certifiedComputed ..)
        | .node _ (.workspace ..) | .node _ (.structuralComputed ..) => return true
        | _ => return false
      | .selection .. => return false
      | .child _ one smaller => next one smaller
      | .pair _ first _ rest smallerFirst smallerRest =>
        if ← next first smallerFirst then return true else next rest smallerRest) item

def readBasisResult {dependencies program block} (result : BlockResult dependencies program block) : WorkM Bool := do
  exactWork (Exact.charge (8*(result.steps.length+1)))
  hasBasis (.steps 0 (Steps.ofList result.steps))

/-- The selected node retains the same program, block and complete literal
receipt. Its ordinal is local to its original enclosing body or branch. -/
structure Selection (dependencies : List Semantics.Finite.Dependency) where
  program : Semantics.Observation.Program
  block : RuntimeInterval.Block dependencies program
  ordinal : Nat
  node : Node dependencies program block
  literal : RuntimeSelectionWitness.Checked node
  obtained : RuntimeInterval.Computed (RuntimeSelectionWitness.read node) literal

/-- The rank enumerates selections in source traversal order. The path
records each actual list edge, named-call occurrence and conditional arm.
A right child follows all selections stored in its left sibling. -/
inductive At {dependencies} : {item : Item dependencies} → {count : Nat} →
    Witness item count → Nat → List Edge → Selection dependencies → Prop where
  | selection {item ordinal program block} {node : Node dependencies program block}
      {original : inspect item = .selection ordinal node}
      {literal : RuntimeSelectionWitness.Checked node}
      {obtained : RuntimeInterval.Computed (RuntimeSelectionWitness.read node) literal} :
      At (.selection original literal obtained) 0 [] ⟨program,block,ordinal,node,literal,obtained⟩
  | child {item edge one count decrease rank path found}
      {original : inspect item = .child edge one decrease} {nested : Witness one count}
      (inside : At nested rank path found) :
      At (.child original nested) rank (edge :: path) found
  | first {item firstEdge first restEdge rest a b smallerFirst smallerRest rank path found}
      {original : inspect item = .pair firstEdge first restEdge rest smallerFirst smallerRest}
      {head : Witness first a} {tail : Witness rest b} (inside : At head rank path found) :
      At (.pair original head tail) rank (firstEdge :: path) found
  | rest {item firstEdge first restEdge rest a b smallerFirst smallerRest rank path found}
      {original : inspect item = .pair firstEdge first restEdge rest smallerFirst smallerRest}
      {head : Witness first a} {tail : Witness rest b} (inside : At tail rank path found) :
      At (.pair original head tail) (a+rank) (restEdge :: path) found

structure Located {dependencies item count} (witness : @Witness dependencies item count) (rank : Nat) where
  path : List Edge
  found : Selection dependencies
  original : At witness rank path found

private def atRank {dependencies} (item : Item dependencies) {count : Nat}
    (witness : Witness item count) (index : Fin count) : WorkM (Located witness index.val) :=
  WellFounded.fix (smallerWF (dependencies := dependencies))
    (C := fun current => {n : Nat} → (w : Witness current n) → (i : Fin n) → WorkM (Located w i.val))
    (fun _ next {_} current i => do
      exactWork (Exact.charge 8)
      match current,i with
      | .leaf _,i => False.elim (Nat.not_lt_zero _ i.isLt)
      | .selection (ordinal := ordinal) (node := node) _ literal obtained,i =>
        have zero : 0 = i.val := by have := i.isLt; omega
        return ⟨[],⟨_,_,ordinal,node,literal,obtained⟩,zero ▸ At.selection⟩
      | .child (edge := edge) (decrease := smaller) _ nested,i =>
        let result ← next _ smaller nested i
        return ⟨edge :: result.path,result.found,.child result.original⟩
      | .pair (firstEdge := firstEdge) (restEdge := restEdge) (a := a) (b := b)
          (smallerFirst := smallerFirst) (smallerRest := smallerRest) original head tail,i =>
        if left : i.val < a then
          let result ← next _ smallerFirst head ⟨i.val,left⟩
          return ⟨firstEdge :: result.path,result.found,.first result.original⟩
        else
          have bound : i.val-a < b := by have := i.isLt; omega
          let result ← next _ smallerRest tail ⟨i.val-a,bound⟩
          have indexEq : a+(i.val-a) = i.val := by omega
          let evidence := fun n => At (.pair original head tail) n (restEdge :: result.path) result.found
          return ⟨restEdge :: result.path,result.found,(congrArg evidence indexEq).mp (.rest result.original)⟩)
    item witness index

/-- Extract the literal already read by the witnessed traversal, together
with its path through the same original mixed steps. -/
def locate {dependencies program block result} (checked : @Checked dependencies program block result)
    (index : Fin checked.count) : WorkM (Located checked.witness index.val) :=
  atRank _ checked.witness index

end QleisliKernel.Qirf.RuntimeSelectionSteps
