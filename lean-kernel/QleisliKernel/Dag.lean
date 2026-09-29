import QleisliKernel.Composition

/-! Shared acyclic evaluation and its algebra-independent interpretation law.
Copyright 2026 Masahiko G. Yamada. Apache-2.0. -/

namespace QleisliKernel.Dag

inductive Instruction where
  | leaf (word : Word)
  | call (definition : Nat) (inputPorts outputPorts : List Nat)
  | sequence (definitions : List Nat)
  | repeatOp (count definition : Nat)
  deriving BEq, DecidableEq, Repr

def Instruction.references : Instruction → List Nat
  | .leaf _ => []
  | .call child _ _ => [child]
  | .sequence children => children
  | .repeatOp _ child => [child]

structure Algebra (α : Type) where
  identity : α
  leaf : Word → α
  sequence : α → α → α
  power : Nat → α → α

def evalSequence {α : Type} (ops : Algebra α) (env : Array α)
    (children : List Nat) : Option α :=
  children.foldl (fun acc child =>
    acc.bind (fun first => env[child]?.map (ops.sequence first))) (some ops.identity)

def evalNode {α : Type} (ops : Algebra α) (env : Array α) : Instruction → Option α
  | .leaf word => some (ops.leaf word)
  | .call child _ _ => env[child]?
  | .sequence children => evalSequence ops env children
  | .repeatOp count child => env[child]?.map (ops.power count)

/-- Each definition is interpreted once; references only access prior results. -/
def evaluate {α : Type} (ops : Algebra α) (nodes : List Instruction) : Option (Array α) :=
  nodes.foldl (fun acc node =>
    acc.bind (fun env => (evalNode ops env node).map env.push)) (some #[])

structure Hom {α β : Type} (left : Algebra α) (right : Algebra β) (f : α → β) : Prop where
  identity : f left.identity = right.identity
  leaf : ∀ word, f (left.leaf word) = right.leaf word
  sequence : ∀ a b, f (left.sequence a b) = right.sequence (f a) (f b)
  power : ∀ count a, f (left.power count a) = right.power count (f a)

private theorem map_sequence_fold {α β : Type} (a : Algebra α) (b : Algebra β)
    (f : α → β) (law : Hom a b f) (env : Array α) (children : List Nat)
    (initial : Option α) :
    (children.foldl (fun acc child =>
      acc.bind (fun first => env[child]?.map (a.sequence first))) initial).map f =
    children.foldl (fun acc child =>
      acc.bind (fun first => (env.map f)[child]?.map (b.sequence first))) (initial.map f) := by
  induction children generalizing initial with
  | nil => rfl
  | cons child rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    cases initial <;> simp [Array.getElem?_map, Option.map_map, Function.comp_def, law.sequence]

theorem evalNode_map {α β : Type} (a : Algebra α) (b : Algebra β)
    (f : α → β) (law : Hom a b f) (env : Array α) (node : Instruction) :
    (evalNode a env node).map f = evalNode b (env.map f) node := by
  cases node with
  | leaf word => simp [evalNode, law.leaf]
  | call child input output => simp [evalNode, Array.getElem?_map]
  | sequence children =>
    simp only [evalNode, evalSequence]
    rw [map_sequence_fold a b f law]
    simp [law.identity]
  | repeatOp count child =>
    simp [evalNode, Array.getElem?_map, Option.map_map, Function.comp_def, law.power]

private theorem map_evaluate_fold {α β : Type} (a : Algebra α) (b : Algebra β)
    (f : α → β) (law : Hom a b f) (nodes : List Instruction)
    (initial : Option (Array α)) :
    (nodes.foldl (fun acc node =>
      acc.bind (fun env => (evalNode a env node).map env.push)) initial).map (Array.map f) =
    nodes.foldl (fun acc node =>
      acc.bind (fun env => (evalNode b env node).map env.push)) (initial.map (Array.map f)) := by
  induction nodes generalizing initial with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    cases initial with
    | none => rfl
    | some env =>
      simp only [Option.map_some, Option.bind_some]
      rw [← evalNode_map a b f law]
      simp [Option.map_map, Function.comp_def, Array.map_push]

/-- Any lawful interpretation commutes with actual shared-DAG evaluation. -/
theorem evaluate_map {α β : Type} (a : Algebra α) (b : Algebra β)
    (f : α → β) (law : Hom a b f) (nodes : List Instruction) :
    (evaluate a nodes).map (Array.map f) = evaluate b nodes := by
  unfold evaluate
  rw [map_evaluate_fold a b f law]
  simp

def summaryAlgebra : Algebra Summary :=
  ⟨identitySummary, normalize, compose, powerSummary⟩

def actionAlgebra : Algebra Action :=
  ⟨identitySummary.action, run, thenAction, repeatAction⟩

theorem action_hom : Hom summaryAlgebra actionAlgebra Summary.action where
  identity := rfl
  leaf word := by funext bit phase; exact normalize_correct word bit phase
  sequence := compose_action
  power := powerSummary_action

/-- Actual cached summary evaluation agrees with direct operational actions. -/
theorem evaluate_actions (nodes : List Instruction) :
    (evaluate summaryAlgebra nodes).map (Array.map Summary.action) =
      evaluate actionAlgebra nodes :=
  evaluate_map summaryAlgebra actionAlgebra Summary.action action_hom nodes

end QleisliKernel.Dag
