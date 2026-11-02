import QleisliKernel.SourceTypes.SourceEffect
import QleisliKernel.Finite

/-! Original typed-body effect closure. The enclosing original source judgment
supplies typed definitions and exact internal runtime edges. External public
bounds contribute to direct effects; unused provider eligibility obligations
remain separate. No annotation or chosen finite dimension seeds inference.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceEffectClosure
open QleisliKernel Finite Semantics.Raw

abbrev DefId := String × String

structure Formula where
  direct : Effect
  dependencies : List DefId
  deriving BEq, DecidableEq, Repr

structure Entry where
  id : DefId
  formula : Formula
  deriving BEq, DecidableEq, Repr

/-- Paths follow only recorded original internal runtime calls. This reference
does not depend on work fuel, the selected closed instance or the solver. -/
inductive Reach (entries : List Entry) (root : DefId) : DefId → Prop where
  | root : Reach entries root root
  | call (entry : Entry) (original : entry ∈ entries) (caller : Reach entries root entry.id)
      {callee : DefId} (dependency : callee ∈ entry.formula.dependencies) : Reach entries root callee

structure Node (entries : List Entry) (root : DefId) where
  entry : Entry
  original : entry ∈ entries
  reachable : Reach entries root entry.id

private structure Pending (entries : List Entry) (root : DefId) where
  id : DefId
  reachable : Reach entries root id

private def idFields (id : DefId) : Nat := id.1.utf8ByteSize+id.2.utf8ByteSize+2

private def entryFields (entry : Entry) : Nat :=
  idFields entry.id+(entry.formula.dependencies.map idFields).sum+entry.formula.dependencies.length+1

private def walk (entries : List Entry) (root : DefId) : Nat →
    List (Pending entries root) → List (Node entries root) → WorkM (List (Node entries root)) :=
  Nat.rec (fun pending nodes => if pending.isEmpty then pure nodes else throw .limit)
    (fun _ next pending nodes => do
      exactWork (Exact.charge (16*((entries.map entryFields).sum+
        (pending.map fun pending => idFields pending.id).sum+
        (nodes.map fun node => entryFields node.entry).sum+1)))
      match pending with
      | [] => pure nodes
      | first :: rest =>
        if nodes.any (fun node => node.entry.id == first.id) then next rest nodes else do
          let some located := entries.attach.find? (fun entry => entry.val.id == first.id) | throw .request
          if same : located.val.id = first.id then
            have reached : Reach entries root located.val.id := same.symm ▸ first.reachable
            let children := located.val.formula.dependencies.attach.map fun dependency =>
              (⟨dependency.val,.call located.val located.property reached dependency.property⟩ : Pending entries root)
            let node : Node entries root := ⟨located.val,located.property,reached⟩
            next (rest ++ children) (nodes ++ [node])
          else throw .request)

structure Checked (entries : List Entry) (root : DefId) where
  unique : (entries.map (·.id)).Nodup
  internalModules : entries.all (fun entry => entry.formula.dependencies.all
    (fun dependency => dependency.1 == entry.id.1)) = true
  nodes : List (Node entries root)
  rootPresent : root ∈ nodes.map (·.entry.id)
  closed : nodes.all (fun node => node.entry.formula.dependencies.all
    (fun dependency => (nodes.map (·.entry.id)).contains dependency)) = true

def Checked.inferred {entries root} (checked : Checked entries root) : Effect :=
  checked.nodes.foldl (fun effect node => SourceEffect.join effect node.entry.formula.direct) .unitary

def Checked.ids {entries root} (checked : Checked entries root) : List DefId :=
  checked.nodes.map (·.entry.id)

/-- Quantum-use facts supplied by the same original typed records follow the
same runtime reachability. Unit allocation/release cannot disappear by effect. -/
def Checked.quantumUse {entries root} (checked : Checked entries root) (direct : DefId → Bool) : Bool :=
  checked.ids.any direct

/-- Every queued edge is processed, including recursive SCC edges. The bound
comes from the complete original graph rather than a caller token count. An
unknown dependency, external edge or duplicate identity refuses independently.
Effect SCC closure grants no recursive call or termination permission. -/
def read (entries : List Entry) (root : DefId) : WorkM (Checked entries root) := do
  exactWork (Exact.charge (16*(entries.length+1)*((entries.map entryFields).sum+1)))
  if unique : (entries.map (·.id)).Nodup then
    let internalModules : PLift (entries.all (fun entry => entry.formula.dependencies.all
        (fun dependency => dependency.1 == entry.id.1)) = true) ←
      if checked : entries.all (fun entry => entry.formula.dependencies.all
          (fun dependency => dependency.1 == entry.id.1)) = true then
        pure (⟨checked⟩ : PLift (entries.all (fun entry => entry.formula.dependencies.all
          (fun dependency => dependency.1 == entry.id.1)) = true))
      else throw .request
    let fuel := entries.length+(entries.map fun entry => entry.formula.dependencies.length).sum+1
    let nodes ← walk entries root fuel [⟨root,.root⟩] []
    exactWork (Exact.charge (16*(nodes.length+1)*((nodes.map fun node => entryFields node.entry).sum+1)))
    if rootPresent : root ∈ nodes.map (·.entry.id) then
      if closed : nodes.all (fun node => node.entry.formula.dependencies.all
          (fun dependency => (nodes.map (·.entry.id)).contains dependency)) = true then
        return ⟨unique,internalModules.down,nodes,rootPresent,closed⟩
      else throw .request
    else throw .request
  else throw .request

private theorem entry_unique (entries : List Entry) : (entries.map (·.id)).Nodup →
    {first second : Entry} → first ∈ entries → second ∈ entries → first.id = second.id → first = second := by
  induction entries with
  | nil => intro _ _ _ a; simp at a
  | cons head tail ih =>
    intro unique first second a b same
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp a with a | a
    · subst first
      rcases List.mem_cons.mp b with b | b
      · exact b.symm
      · have present : head.id ∈ tail.map (·.id) := by
          rw [same]
          exact List.mem_map.mpr ⟨second,b,rfl⟩
        exact False.elim (unique.1 present)
    · rcases List.mem_cons.mp b with b | b
      · subst second
        have present : head.id ∈ tail.map (·.id) := by
          rw [← same]
          exact List.mem_map.mpr ⟨first,a,rfl⟩
        exact False.elim (unique.1 present)
      · exact ih unique.2 a b same

theorem Checked.reachable_member {entries root} (checked : Checked entries root) {id : DefId}
    (path : Reach entries root id) : ∃ node ∈ checked.nodes,node.entry.id = id := by
  induction path with
  | root =>
    obtain ⟨node,member,same⟩ := List.mem_map.mp checked.rootPresent
    exact ⟨node,member,same⟩
  | call entry original _ dependency ih =>
    obtain ⟨node,member,same⟩ := ih
    have exactEntry : node.entry = entry := entry_unique entries checked.unique node.original original same
    have closed := (List.all_eq_true.mp checked.closed) node member
    rw [exactEntry] at closed
    have contains := (List.all_eq_true.mp closed) _ dependency
    have present : _ ∈ checked.nodes.map (·.entry.id) := List.contains_iff_mem.mp contains
    obtain ⟨target,member,same⟩ := List.mem_map.mp present
    exact ⟨target,member,same⟩

theorem Checked.direct_bound {entries root} (checked : Checked entries root)
    (entry : Entry) (original : entry ∈ entries) (path : Reach entries root entry.id) :
    SourceEffect.rank entry.formula.direct ≤ SourceEffect.rank checked.inferred := by
  obtain ⟨node,member,same⟩ := checked.reachable_member path
  have exactEntry : node.entry = entry := entry_unique entries checked.unique node.original original same
  have bound := SourceEffect.member_accumulate (fun node : Node entries root => node.entry.formula.direct)
    checked.nodes .unitary node member
  simpa only [Checked.inferred,exactEntry] using bound

theorem Checked.quantumUse_reachable {entries root} (checked : Checked entries root)
    (direct : DefId → Bool) {id : DefId} (path : Reach entries root id) (used : direct id = true) :
    checked.quantumUse direct = true := by
  obtain ⟨node,member,same⟩ := checked.reachable_member path
  apply List.any_eq_true.mpr
  refine ⟨id,?_,used⟩
  exact List.mem_map.mpr ⟨node,member,same⟩

/-- A candidate assignment independently bounds each direct original body and
each internal call. Public annotations are not part of this proposition. -/
def Lawful (entries : List Entry) (assignment : DefId → Effect) : Prop :=
  ∀ entry ∈ entries,
    SourceEffect.rank entry.formula.direct ≤ SourceEffect.rank (assignment entry.id) ∧
      ∀ callee ∈ entry.formula.dependencies,
        SourceEffect.rank (assignment callee) ≤ SourceEffect.rank (assignment entry.id)

private theorem path_bound {entries root assignment} (lawful : Lawful entries assignment) {id : DefId}
    (path : Reach entries root id) : SourceEffect.rank (assignment id) ≤ SourceEffect.rank (assignment root) := by
  induction path with
  | root => exact Nat.le_refl _
  | call entry original _ dependency ih =>
    exact Nat.le_trans ((lawful entry original).2 _ dependency) ih

theorem Reach.trans {entries first middle last} (initial : Reach entries first middle)
    (later : Reach entries middle last) : Reach entries first last := by
  induction later with
  | root => exact initial
  | call entry original _ dependency ih => exact .call entry original ih dependency

private theorem join_bound (first second : Effect) (limit : Nat)
    (a : SourceEffect.rank first ≤ limit) (b : SourceEffect.rank second ≤ limit) :
    SourceEffect.rank (SourceEffect.join first second) ≤ limit := by
  unfold SourceEffect.join
  split
  · exact b
  · exact a

private theorem fold_bound {α : Type} (effect : α → Effect) (nodes : List α) (initial : Effect) (limit : Nat)
    (start : SourceEffect.rank initial ≤ limit) (each : ∀ node ∈ nodes,SourceEffect.rank (effect node) ≤ limit) :
    SourceEffect.rank (nodes.foldl (fun current node => SourceEffect.join current (effect node)) initial) ≤ limit := by
  induction nodes generalizing initial with
  | nil => exact start
  | cons first rest ih =>
    exact ih (SourceEffect.join initial (effect first))
      (join_bound _ _ _ start (each first (List.mem_cons_self ..)))
      (fun node member => each node (List.mem_cons_of_mem _ member))

theorem Checked.internal_bound {entries root callee} (checked : Checked entries root)
    (child : Checked entries callee) (path : Reach entries root callee) :
    SourceEffect.rank child.inferred ≤ SourceEffect.rank checked.inferred := by
  apply fold_bound (fun node : Node entries callee => node.entry.formula.direct) child.nodes .unitary
    (SourceEffect.rank checked.inferred) (Nat.zero_le _)
  intro node _
  exact checked.direct_bound node.entry node.original (path.trans node.reachable)

theorem Checked.least {entries root} (checked : Checked entries root) (assignment : DefId → Effect)
    (lawful : Lawful entries assignment) :
    SourceEffect.rank checked.inferred ≤ SourceEffect.rank (assignment root) := by
  apply fold_bound (fun node : Node entries root => node.entry.formula.direct) checked.nodes .unitary
    (SourceEffect.rank (assignment root)) (Nat.zero_le _)
  intro node _
  exact Nat.le_trans ((lawful node.entry node.original).1) (path_bound lawful node.reachable)

theorem Checked.unitary_direct {entries root} (checked : Checked entries root)
    (unitary : checked.inferred = .unitary) (entry : Entry) (original : entry ∈ entries)
    (path : Reach entries root entry.id) : entry.formula.direct = .unitary := by
  have bound := checked.direct_bound entry original path
  rw [unitary] at bound
  cases direct : entry.formula.direct <;> simp_all [SourceEffect.rank]

end QleisliKernel.SourceTypes.SourceEffectClosure
