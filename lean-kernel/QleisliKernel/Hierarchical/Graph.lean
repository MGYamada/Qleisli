import Std

/-! Bounded scheduling of the full hierarchy's combined dependency graph.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
An untrusted adapter proposes an order; this pass checks it against actual edges.
It establishes dependency safety only, never an IR equation or a schema receipt. -/

namespace QleisliKernel.Hierarchical.Graph

abbrev Nodes := Array (List Nat)

inductive Error where
  | limit | invalidIr
  deriving BEq, DecidableEq, Repr

structure Failure where
  kind : Error
  node : Option Nat
  deriving Repr

structure Stats where
  nodes : Nat
  references : Nat
  visits : Nat
  depth : Nat
  deriving BEq, DecidableEq, Repr

structure Schedule where
  order : Array Nat
  ranks : Array Nat
  stats : Stats
  deriving Repr

def dependencies (nodes : Nodes) (node : Nat) : List Nat := nodes[node]?.getD []

def rank (ranks : Array Nat) (node : Nat) : Nat := ranks[node]?.getD ranks.size

/-- The external table order need not be topological. Every proposed index
occurs exactly once; zero-dependency nodes and zero-repeat bodies remain nodes. -/
def makeRanks (size : Nat) (order : Array Nat) : Option (Array Nat) := do
  if order.size != size then none else do
    let state ← order.foldlM (fun (state : Nat × Array Nat) node => do
      let previous ← state.2[node]?
      if previous != size then none
      else some (state.1 + 1, state.2.set! node state.1)) (0, Array.replicate size size)
    return state.2

/-- Rank strictly decreases along each actual dependency, not supplied counts. -/
def topology (nodes : Nodes) (ranks : Array Nat) : Bool :=
  ranks.size == nodes.size && (List.range nodes.size).all (fun parent =>
    (dependencies nodes parent).all (fun child =>
      child < nodes.size && rank ranks child < rank ranks parent))

def depths (nodes : Nodes) (order : Array Nat) : Except Failure (Array Nat) :=
  order.foldlM (fun results parent => do
    let value := 1 + ((dependencies nodes parent).map (fun child => results[child]?.getD 0)).foldl max 0
    if value > 256 then .error ⟨.limit, some parent⟩
    else .ok (results.set! parent value)) (Array.replicate nodes.size 0)

def reachable (nodes : Nodes) (order : Array Nat) (roots : List Nat) : Bool := Id.run do
  let mut seen := Array.replicate nodes.size false
  for root in roots do
    seen := seen.set! root true
  for parent in order.toList.reverse do
    if seen[parent]?.getD false then
      for child in dependencies nodes parent do
        seen := seen.set! child true
  return seen.all id

/-- Conservative shared charge covers input scans, rank/depth arrays, edge
lookups, order checks and reachability. No expanded execution count is visited. -/
def charge (nodes references roots : Nat) : Nat := 10 * nodes + 5 * references + 3 * roots

/-- Stop before visiting the rest of an oversized adjacency list. Computing
all list lengths first would do uncharged work on a rejected input. -/
def countReferencesWithin (nodes : Nodes) (rootCount budget : Nat) : Option Nat :=
  nodes.foldlM (fun count children => children.foldlM (fun current _ =>
    let next := current + 1
    if next > 1000000 || charge nodes.size next rootCount > budget then none
    else some next) count) 0

def countReferences (nodes : Nodes) (rootCount : Nat) : Option Nat :=
  countReferencesWithin nodes rootCount 2000000

/-- All four external tables are flattened by the untrusted adapter. Typed
reference projection and node semantics are checked separately; this pass is
never sufficient to accept an artifact. Its visits debit the enclosing budget. -/
def checkWithBudget (nodes : Nodes) (roots : List Nat) (order : Array Nat)
    (budget : Nat) : Except Failure Schedule :=
  if nodes.isEmpty || nodes.size > 100000 || budget > 2000000 || 10 * nodes.size > budget then
    .error ⟨.limit, none⟩
  else
    let rootCount := (roots.take (nodes.size + 1)).length
    if rootCount = 0 || rootCount > nodes.size || charge nodes.size 0 rootCount > budget then .error ⟨.limit, none⟩
    else match countReferencesWithin nodes rootCount budget with
      | none => .error ⟨.limit, none⟩
      | some references =>
        let visits := charge nodes.size references rootCount
        if references > 1000000 || visits > budget then .error ⟨.limit, none⟩
        else match makeRanks nodes.size order with
          | none => .error ⟨.invalidIr, none⟩
          | some ranks =>
            if !topology nodes ranks || !(roots.all (· < nodes.size)) then .error ⟨.invalidIr, none⟩
            else match depths nodes order with
              | .error failure => .error failure
              | .ok ds =>
                if !reachable nodes order roots then .error ⟨.invalidIr, none⟩
                else .ok ⟨order, ranks, ⟨nodes.size, references, visits, ds.foldl max 0⟩⟩

theorem checkWithBudget_conditions (nodes : Nodes) (roots : List Nat) (order : Array Nat)
    (budget : Nat) (schedule : Schedule) (accepted : checkWithBudget nodes roots order budget = .ok schedule) :
    schedule.order = order ∧ makeRanks nodes.size order = some schedule.ranks ∧
    topology nodes schedule.ranks = true ∧ reachable nodes order roots = true ∧
    schedule.stats.visits ≤ budget := by
  unfold checkWithBudget at accepted
  dsimp only at accepted
  split at accepted
  next invalid => contradiction
  next bounded =>
    split at accepted
    next invalid => contradiction
    next rootsBounded =>
      cases hc : countReferencesWithin nodes (roots.take (nodes.size + 1)).length budget with
      | none => simp only [hc] at accepted; contradiction
      | some references =>
        simp only [hc] at accepted
        split at accepted
        next invalid => contradiction
        next capacity =>
          cases hr : makeRanks nodes.size order with
          | none => simp [hr] at accepted
          | some ranks =>
            simp only [hr] at accepted
            split at accepted
            next invalid => contradiction
            next ordered =>
              cases hd : depths nodes order with
              | error failure => simp [hd] at accepted
              | ok ds =>
                simp only [hd] at accepted
                split at accepted
                next invalid => contradiction
                next reached =>
                  cases Except.ok.inj accepted
                  simp at capacity ordered reached
                  exact ⟨rfl, rfl, ordered.1, reached, by simpa using capacity.2⟩

/-- Standalone callers retain the original full-profile allowance. Integrated
callers use checkWithBudget with the actual remaining shared allowance. -/
def check (nodes : Nodes) (roots : List Nat) (order : Array Nat) : Except Failure Schedule :=
  checkWithBudget nodes roots order 2000000

theorem check_conditions (nodes : Nodes) (roots : List Nat) (order : Array Nat)
    (schedule : Schedule) (accepted : check nodes roots order = .ok schedule) :
    schedule.order = order ∧ makeRanks nodes.size order = some schedule.ranks ∧
    topology nodes schedule.ranks = true ∧ reachable nodes order roots = true ∧
    schedule.stats.visits ≤ 2000000 :=
  checkWithBudget_conditions nodes roots order 2000000 schedule accepted

theorem topology_edge (nodes : Nodes) (ranks : Array Nat)
    (valid : topology nodes ranks = true) (parent child : Nat)
    (inside : parent < nodes.size) (edge : child ∈ dependencies nodes parent) :
    child < nodes.size ∧ rank ranks child < rank ranks parent := by
  simp only [topology, Bool.and_eq_true] at valid
  have h := List.all_eq_true.mp valid.2 parent (List.mem_range.mpr inside)
  have e := List.all_eq_true.mp h child edge
  simpa using e

/-- Nonempty paths in the *actual* graph. There is no assumed DAG premise. -/
inductive Path (nodes : Nodes) : Nat → Nat → Prop where
  | edge {a b : Nat} : a < nodes.size → b ∈ dependencies nodes a → Path nodes a b
  | then {a b c : Nat} : Path nodes a b → Path nodes b c → Path nodes a c

theorem path_decreases (nodes : Nodes) (ranks : Array Nat)
    (valid : topology nodes ranks = true) {a b : Nat} (path : Path nodes a b) :
    rank ranks b < rank ranks a := by
  induction path with
  | edge inside member => exact (topology_edge nodes ranks valid _ _ inside member).2
  | «then» _ _ first second => exact Nat.lt_trans second first

theorem checkWithBudget_acyclic (nodes : Nodes) (roots : List Nat) (order : Array Nat)
    (budget : Nat) (schedule : Schedule)
    (accepted : checkWithBudget nodes roots order budget = .ok schedule) (node : Nat) :
    ¬Path nodes node node := by
  intro cycle
  have valid := (checkWithBudget_conditions nodes roots order budget schedule accepted).2.2.1
  exact Nat.lt_irrefl _ (path_decreases nodes schedule.ranks valid cycle)

/-- Actual acceptance excludes cycles, including a self-dependency hidden in
a zero-repeat body. No recursive semantic expansion is used in this proof. -/
theorem check_acyclic (nodes : Nodes) (roots : List Nat) (order : Array Nat)
    (schedule : Schedule) (accepted : check nodes roots order = .ok schedule) (node : Nat) :
    ¬Path nodes node node := by
  intro cycle
  have valid := (check_conditions nodes roots order schedule accepted).2.2.1
  exact Nat.lt_irrefl _ (path_decreases nodes schedule.ranks valid cycle)

end QleisliKernel.Hierarchical.Graph
