import Qleisli.HierarchicalFiniteUnitary
import QleisliKernel.Hierarchical.Root

/-! Actual graph pairing binds a checked operator to an independent request.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Only actual finite implementation and finite-description equations remain
premises; no whole-graph semantic environment or supplied conclusion is assumed. -/

namespace Qleisli.HierarchicalRoot
open QleisliKernel.Hierarchical
open Artifact
open HierarchicalSemantics (Algebra logicalCode mapM_members)
open HierarchicalFiniteEvaluation

def requested (request : Root.Request) : Artifact :=
  ⟨#[],request.meanings,#[],#[],⟨0,0⟩⟩

def FiniteEquation {S : Type} (leaves : Leaves S) (pair : Root.FinitePair) : Prop :=
  leaves.meaning pair.actual.interface pair.left = leaves.meaning pair.required.interface pair.right

theorem project_fields (artifact : Artifact) (request : Root.Request) (pairs : Array Root.Pair)
    (pair : Root.Pair) (a r : Meaning) (ps : List Root.Pair)
    (found : Root.project artifact request pairs pair = some (a,r,ps)) :
    artifact.meanings[pair.actual]? = some a ∧ request.meanings[pair.requested]? = some r ∧
      pair.children.toList.mapM (fun i => pairs[i]?) = some ps := by
  unfold Root.project at found
  cases ha : artifact.meanings[pair.actual]? with
  | none => simp [ha] at found
  | some actual =>
    cases hr : request.meanings[pair.requested]? with
    | none => simp [ha,hr] at found
    | some required =>
      cases hp : pair.children.toList.mapM (fun i => pairs[i]?) with
      | none => simp [ha,hr,hp] at found
      | some children =>
        have same : (actual,required,children) = (a,r,ps) := by simpa [ha,hr,hp] using found
        cases same
        exact ⟨rfl,rfl,rfl⟩

def render {S : Type} (algebra : Algebra S) (leaves : Leaves S) (m : Meaning) : List S → Option S :=
  match m.body with
  | .finite bytes => fun _ => leaves.meaning m.interface bytes
  | _ => fun values => do
    let (tag,_) ← logicalCode m
    return algebra.apply m.interface tag values

theorem logical_step_all {S : Type} (algebra : Algebra S) (leaves : Leaves S)
    (artifact : Artifact) (fuel index : Nat) (m : Meaning)
    (found : artifact.meanings[index]? = some m) :
    logical algebra leaves artifact (fuel+1) index =
      ((Root.children m.body).mapM (logical algebra leaves artifact fuel)).bind (render algebra leaves m) := by
  cases body : m.body <;>
    simp [logical,evaluate,meaning,found,render,body,logicalCode,Root.children,
      MeaningBody.references,Function.comp_def,Option.bind_assoc]

theorem render_equal {S : Type} (algebra : Algebra S) (leaves : Leaves S) (a r : Meaning)
    (same : a.interface = r.interface) (shape : Root.shape a.body = Root.shape r.body)
    (finite : ∀ left right, a.body = .finite left → r.body = .finite right →
      leaves.meaning a.interface left = leaves.meaning r.interface right) :
    ∀ values, render algebra leaves a values = render algebra leaves r values := by
  cases ha : a.body <;> cases hr : r.body <;>
    simp_all [Root.shape,render,logicalCode]

theorem pair_mapM {S : Type} (ps : List Root.Pair) (left right : Nat → Option S)
    (same : ∀ p ∈ ps, left p.actual = right p.requested) :
    (ps.map Root.Pair.actual).mapM left = (ps.map Root.Pair.requested).mapM right := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.mapM_cons]
    rw [same p (by simp),ih (fun child member => same child (by simp [member]))]

theorem pairs_denote {S : Type} (algebra : Algebra S) (leaves : Leaves S)
    (artifact : Artifact) (request : Root.Request) (pairs : Array Root.Pair)
    (order : Array Nat) (remaining : Nat) (pending : Root.Pending)
    (accepted : Root.inspect artifact request pairs order remaining = .ok pending)
    (finite : ∀ i ∈ pending.requests, ∀ obligation,
      Root.finitePair artifact request pairs i = some obligation → FiniteEquation leaves obligation) :
    ∀ (fuel i : Nat) (pair : Root.Pair), pairs[i]? = some pair →
      logical algebra leaves artifact fuel pair.actual =
        logical algebra leaves (requested request) fuel pair.requested := by
  have checked := Root.inspect_conditions artifact request pairs order remaining pending accepted
  intro fuel
  induction fuel with
  | zero => intro i pair found; rfl
  | succ fuel ih =>
    intro i pair found
    have member : pair ∈ pairs.toList := by
      obtain ⟨h,equal⟩ := Array.getElem?_eq_some_iff.mp found
      exact Array.mem_toList_iff.mpr (equal ▸ Array.getElem_mem h)
    obtain ⟨a,r,ps,project,header,shape,left,right⟩ :=
      Root.aligned_conditions artifact request pairs pair (checked.2.2.2.2 pair member)
    obtain ⟨ha,hr,hps⟩ := project_fields artifact request pairs pair a r ps project
    rw [logical_step_all algebra leaves artifact fuel pair.actual a ha,
      logical_step_all algebra leaves (requested request) fuel pair.requested r (by exact hr),left,right]
    have mapped := pair_mapM ps (logical algebra leaves artifact fuel)
      (logical algebra leaves (requested request) fuel) (by
        intro child inside
        obtain ⟨index,_,childFound⟩ := mapM_members pair.children.toList ps (fun i => pairs[i]?) hps child inside
        exact ih index child childFound)
    rw [mapped]
    congr 1
    funext values
    apply render_equal algebra leaves a r header shape
    intro x y hx hy
    let obligation : Root.FinitePair := ⟨a,r,x,y⟩
    have projected : Root.finitePair artifact request pairs i = some obligation := by
      simp [Root.finitePair,found,ha,hr,hx,hy,obligation]
    have inside : i ∈ pending.requests := by
      rw [checked.2.1]
      simp only [Root.obligations,List.mem_filter,List.mem_range]
      exact ⟨(Array.getElem?_eq_some_iff.mp found).choose,by simp [projected]⟩
    exact finite i inside obligation projected

theorem root_fields (artifact : Artifact) (request : Root.Request) (pairs : Array Root.Pair)
    (accepted : Root.root artifact request pairs = true) :
    ∃ d p first, artifact.definitions[artifact.entry.implementation]? = some d ∧
      artifact.proofs[artifact.entry.proof]? = some p ∧ pairs[0]? = some first ∧
      p.implementation = artifact.entry.implementation ∧ p.kind = request.kind ∧
      d.effect = request.effect ∧ d.interface = request.interface ∧
      first.actual = p.meaning ∧ first.requested = request.entry := by
  cases hd : artifact.definitions[artifact.entry.implementation]? with
  | none => simp [Root.root,hd] at accepted
  | some d =>
    cases hp : artifact.proofs[artifact.entry.proof]? with
    | none => simp [Root.root,hd,hp] at accepted
    | some p =>
      cases hf : pairs[0]? with
      | none => simp [Root.root,hd,hp,hf] at accepted
      | some first =>
        simp only [Root.root,hd,hp,hf,bind,Option.bind,pure,Option.getD,
          Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at accepted
        exact ⟨d,p,first,rfl,rfl,rfl,accepted.1.1.1.1.1,accepted.1.1.1.1.2,
          accepted.1.1.1.2,accepted.1.1.2,accepted.1.2,accepted.2⟩

theorem checkAll_denotes {S : Type} (algebra : Algebra S) (leaves : Leaves S)
    (artifact : Artifact) (order : Array Nat) (request : Root.Request)
    (pairs : Array Root.Pair) (pairOrder : Array Nat) (checked : Root.Checked)
    (accepted : Root.checkAll artifact order request pairs pairOrder = .ok checked)
    (implementations : ∀ leaf ∈ checked.artifact.state.requests.toList, Equation leaves leaf)
    (meanings : ∀ i ∈ checked.binding.requests, ∀ obligation,
      Root.finitePair artifact request pairs i = some obligation → FiniteEquation leaves obligation) :
    ∃ fuel value, physical algebra leaves artifact fuel artifact.entry.implementation = some value ∧
      logical algebra leaves (requested request) fuel request.entry = some value := by
  obtain ⟨ha,hb⟩ := Root.checkAll_conditions artifact order request pairs pairOrder checked accepted
  obtain ⟨proof,fuel,value,hp,_,physical,logical⟩ :=
    HierarchicalFiniteEvaluation.checkAll_denotes algebra leaves artifact order checked.artifact ha implementations
  have bound := Root.inspect_conditions artifact request pairs pairOrder _ checked.binding hb
  obtain ⟨d,p,first,_,found,hf,_,_,_,_,left,right⟩ := root_fields artifact request pairs bound.2.2.1
  have same : p = proof := Option.some.inj (found.symm.trans hp)
  subst p
  have equal := pairs_denote algebra leaves artifact request pairs pairOrder _ checked.binding hb meanings fuel 0 first hf
  rw [left,right] at equal
  exact ⟨fuel,value,physical,equal ▸ logical⟩

open HierarchicalOperators HierarchicalTyping
open scoped Matrix

/-- The requested graph has the same constructed unitary value, with the
complete independently requested interface and arbitrary reference systems. -/
theorem checkAll_unitary (leaves : Leaves Operator)
    (artifact : Artifact) (order : Array Nat) (request : Root.Request)
    (pairs : Array Root.Pair) (pairOrder : Array Nat) (checked : Root.Checked)
    (accepted : Root.checkAll artifact order request pairs pairOrder = .ok checked)
    (implementations : ∀ leaf ∈ checked.artifact.state.requests.toList,
      HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ checked.binding.requests, ∀ obligation,
      Root.finitePair artifact request pairs i = some obligation → FiniteEquation leaves obligation) :
    ∃ fuel value, physical algebra leaves artifact fuel artifact.entry.implementation = some value ∧
      logical algebra leaves (requested request) fuel request.entry = some value ∧
      UnitaryInterface request.interface value := by
  obtain ⟨ha,hb⟩ := Root.checkAll_conditions artifact order request pairs pairOrder checked accepted
  obtain ⟨proof,parent,fuel,value,hp,hd,_,physical,logical,unitary⟩ :=
    HierarchicalFiniteUnitary.checkAll_unitary leaves artifact order checked.artifact ha implementations
  have bound := Root.inspect_conditions artifact request pairs pairOrder _ checked.binding hb
  obtain ⟨d,p,first,foundD,foundP,hf,_,_,_,header,left,right⟩ := root_fields artifact request pairs bound.2.2.1
  have sameP : p = proof := Option.some.inj (foundP.symm.trans hp)
  have sameD : d = parent := Option.some.inj (foundD.symm.trans hd)
  subst p
  subst d
  have equal := pairs_denote algebra leaves artifact request pairs pairOrder _ checked.binding hb meanings fuel 0 first hf
  rw [left,right] at equal
  exact ⟨fuel,value,physical,equal ▸ logical,header ▸ unitary⟩

theorem checkAll_reference_laws {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves Operator) (artifact : Artifact) (order : Array Nat) (request : Root.Request)
    (pairs : Array Root.Pair) (pairOrder : Array Nat) (checked : Root.Checked)
    (accepted : Root.checkAll artifact order request pairs pairOrder = .ok checked)
    (implementations : ∀ leaf ∈ checked.artifact.state.requests.toList,
      HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ checked.binding.requests, ∀ obligation,
      Root.finitePair artifact request pairs i = some obligation → FiniteEquation leaves obligation) :
    ∃ fuel value, physical algebra leaves artifact fuel artifact.entry.implementation = some value ∧
      logical algebra leaves (requested request) fuel request.entry = some value ∧
      let n := width request.interface.inputs
      let joint := Matrix.kronecker (matrixAt n n value) (1 : Matrix R R ℂ)
      jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 := by
  obtain ⟨fuel,value,hp,hm,unitary⟩ :=
    checkAll_unitary leaves artifact order request pairs pairOrder checked accepted implementations meanings
  exact ⟨fuel,value,hp,hm,HierarchicalUnitary.reference_unitary unitary.1⟩

end Qleisli.HierarchicalRoot
