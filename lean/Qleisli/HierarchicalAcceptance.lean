import Qleisli.HierarchicalTyping

/-! Unitarity of constructed denotations for the accepted internal hierarchy.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Unsupported full-profile bodies still have no denotation in this evaluator.
This adds no production acceptance rule or assumed semantic environment. -/

namespace Qleisli.HierarchicalAcceptance
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalTyping
open HierarchicalEvaluation
open scoped Matrix

theorem apply_unitary (artifact : Artifact) (parent : Definition) (tag : Tag)
    (children : List Nat) (values : Nat → Operator)
    (code : physicalCode parent = some (tag,children))
    (typed : NodeTyping.conditions artifact parent = true)
    (ready : ∀ index ∈ children, ∃ child, artifact.definitions[index]? = some child ∧
      UnitaryInterface child.interface (values index)) :
    UnitaryInterface parent.interface (HierarchicalOperators.apply parent.interface tag (children.map values)) := by
  cases body : parent.body with
  | leaf payload => simp [physicalCode,body] at code
  | call child inputs outputs => simp [physicalCode,body] at code
  | computed compute useOp logical encoding => simp [physicalCode,body] at code
  | observeZ input output => simp [physicalCode,body] at code
  | init0 output => simp [physicalCode,body] at code
  | rewire map =>
    have same : tag = .rewire map.axes.toList ∧ children = [] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    apply unitaryInterface_apply
    apply HierarchicalTyping.rewire_unitary
    simp only [NodeTyping.conditions,body,Bool.and_eq_true] at typed
    exact typed.2.2
  | structural operation =>
    have same : tag = .rewire (Structural.axisMap parent.interface) ∧ children = [] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    apply unitaryInterface_apply
    apply structural_unitary
    simp only [NodeTyping.conditions,body,Bool.and_eq_true] at typed
    exact typed.2.2
  | dyadicPhase owner j k =>
    have same : tag = .phase owner j k ∧ children = [] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    apply unitaryInterface_apply
    apply HierarchicalTyping.phase_unitary
    simp only [NodeTyping.conditions,body,Bool.and_eq_true] at typed
    exact typed.2
  | sequence indices =>
    have same : tag = .sequence ∧ children = indices.toList := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    exact typed_sequence artifact parent indices body typed values ready
  | tensor left right =>
    have same : tag = .tensor ∧ children = [left,right] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    obtain ⟨a,ha,ua⟩ := ready left (by simp)
    obtain ⟨b,hb,ub⟩ := ready right (by simp)
    exact typed_tensor artifact parent a b left right body ha hb typed (values left) (values right) ua ub
  | inverse index =>
    have same : tag = .inverse ∧ children = [index] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    obtain ⟨child,found,h⟩ := ready index (by simp)
    exact typed_inverse artifact parent child index body found typed (values index) h
  | repeatOp count index =>
    have same : tag = .power count ∧ children = [index] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    obtain ⟨child,found,h⟩ := ready index (by simp)
    exact typed_power artifact parent child index count body found typed (values index) h
  | control index polarity =>
    have same : tag = .control polarity ∧ children = [index] := by
      simpa [physicalCode,body,eq_comm] using code
    rcases same with ⟨rfl,rfl⟩
    obtain ⟨child,found,h⟩ := ready index (by simp)
    exact typed_control artifact parent child index polarity body found typed (values index) h

/-- A successful list traversal has actually evaluated every dependency,
including children under zero repetitions. -/
theorem mapM_each {A B : Type} (entries : List A) (f : A → Option B) (values : List B)
    (accepted : entries.mapM f = some values) :
    ∀ index ∈ entries, ∃ value, f index = some value := by
  induction entries generalizing values with
  | nil => simp
  | cons index rest ih =>
    cases hf : f index with
    | none => simp [hf] at accepted
    | some value =>
      cases hr : rest.mapM f with
      | none => simp [hf,hr] at accepted
      | some tail =>
        intro child member
        rcases List.mem_cons.mp member with same | inside
        · subst child; exact ⟨value,hf⟩
        · exact ih tail hr child inside

theorem evaluate_unitary (artifact : Artifact)
    (allTyped : ∀ (index : Nat) parent, artifact.definitions[index]? = some parent →
      NodeTyping.conditions artifact parent = true)
    (fuel index : Nat) (value : Operator)
    (evaluated : HierarchicalEvaluation.physical algebra artifact fuel index = some value) :
    ∃ parent, artifact.definitions[index]? = some parent ∧ UnitaryInterface parent.interface value := by
  induction fuel generalizing index value with
  | zero => simp [HierarchicalEvaluation.physical,evaluate] at evaluated
  | succ fuel ih =>
    cases hd : artifact.definitions[index]? with
    | none => simp [HierarchicalEvaluation.physical,evaluate,definition,hd] at evaluated
    | some parent =>
      cases hc : physicalCode parent with
      | none => simp [HierarchicalEvaluation.physical,evaluate,definition,hd,hc] at evaluated
      | some code =>
        rcases code with ⟨tag,children⟩
        rw [physical_step algebra artifact fuel index parent tag children hd hc] at evaluated
        cases hv : children.mapM (HierarchicalEvaluation.physical algebra artifact fuel) with
        | none => simp [hv] at evaluated
        | some values =>
          have each := mapM_each children (HierarchicalEvaluation.physical algebra artifact fuel) values hv
          let environment := fun i => (HierarchicalEvaluation.physical algebra artifact fuel i).getD (identity 0)
          have ready : ∀ i ∈ children, ∃ child, artifact.definitions[i]? = some child ∧
              UnitaryInterface child.interface (environment i) := by
            intro i member
            obtain ⟨v,found⟩ := each i member
            obtain ⟨child,present,unitary⟩ := ih i v found
            exact ⟨child,present,by simpa [environment,found] using unitary⟩
          have mapped := mapM_getD children (HierarchicalEvaluation.physical algebra artifact fuel) (identity 0)
            (fun i member => by obtain ⟨v,h⟩ := each i member; simp [h])
          have values_eq : values = children.map environment := Option.some.inj (hv.symm.trans mapped)
          have result : HierarchicalOperators.apply parent.interface tag values = value := by
            simpa only [hv,bind,Option.bind,pure,Option.some.injEq] using evaluated
          refine ⟨parent,rfl,?_⟩
          rw [← result,values_eq]
          exact apply_unitary artifact parent tag children environment hc (allTyped index parent hd) ready

theorem checkAll_typed (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked) :
    ∀ (index : Nat) parent, artifact.definitions[index]? = some parent →
      NodeTyping.conditions artifact parent = true := by
  have contracts := (Derivation.checkAll_conditions artifact order checked accepted).1
  have nodes := (ContractTyping.checkAll_conditions artifact order checked.typed contracts).1
  have all := (NodeTyping.checkAll_conditions artifact order checked.typed.nodes nodes).2.2.2
  intro index parent found
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨actual,present,typed⟩ := all index inside
  have same := Option.some.inj (found.symm.trans present)
  subst actual
  exact typed

/-- The actual checker constructs a unitary entry denotation and the same
logical denotation. No caller-provided isometry, environment or cache occurs.
This covers precisely the internal rules supported by `Derivation.checkAll`. -/
theorem checkAll_unitary (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked) :
    ∃ proof parent value,
      artifact.proofs[artifact.entry.proof]? = some proof ∧
      artifact.definitions[artifact.entry.implementation]? = some parent ∧
      proof.implementation = artifact.entry.implementation ∧
      Denotes algebra (definition artifact) artifact.entry.implementation value ∧
      Denotes algebra (meaning artifact) proof.meaning value ∧
      UnitaryInterface parent.interface value := by
  obtain ⟨proof,value,hp,bound,physical,logical⟩ :=
    HierarchicalEvaluation.checkAll_operator artifact order checked accepted
  obtain ⟨fuel,evaluated⟩ := physical
  obtain ⟨parent,found,unitary⟩ := evaluate_unitary artifact
    (checkAll_typed artifact order checked accepted) fuel artifact.entry.implementation value evaluated
  exact ⟨proof,parent,value,hp,found,bound,⟨fuel,evaluated⟩,logical,unitary⟩

/-- The theorem is independent of the fuel chosen to exhibit a denotation. -/
theorem checked_denotation_unitary (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (parent : Definition) (found : artifact.definitions[artifact.entry.implementation]? = some parent)
    (value : Operator) (denotes : Denotes algebra (definition artifact) artifact.entry.implementation value) :
    UnitaryInterface parent.interface value := by
  obtain ⟨fuel,evaluated⟩ := denotes
  obtain ⟨actual,present,unitary⟩ := evaluate_unitary artifact
    (checkAll_typed artifact order checked accepted) fuel artifact.entry.implementation value evaluated
  have same := Option.some.inj (found.symm.trans present)
  subst actual
  exact unitary

theorem checkAll_inverse_laws (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (parent : Definition) (found : artifact.definitions[artifact.entry.implementation]? = some parent)
    (value : Operator) (denotes : Denotes algebra (definition artifact) artifact.entry.implementation value) :
    let n := width parent.interface.inputs
    (matrixAt n n value)ᴴ * matrixAt n n value = 1 ∧
      matrixAt n n value * (matrixAt n n value)ᴴ = 1 :=
  HierarchicalUnitary.unitary_laws
    (checked_denotation_unitary artifact order checked accepted parent found value denotes).1

theorem checkAll_reference_unitary {R : Type} [Fintype R] [DecidableEq R]
    (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (parent : Definition) (found : artifact.definitions[artifact.entry.implementation]? = some parent)
    (value : Operator) (denotes : Denotes algebra (definition artifact) artifact.entry.implementation value) :
    let n := width parent.interface.inputs
    let joint := Matrix.kronecker (matrixAt n n value) (1 : Matrix R R ℂ)
    jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 :=
  HierarchicalUnitary.reference_unitary
    (checked_denotation_unitary artifact order checked accepted parent found value denotes).1

namespace Examples

private def target : Side := ⟨#[⟨0,#[.bit],#[7]⟩],#[]⟩
private def full : Side := ⟨#[⟨1,#[.bit],#[8]⟩,⟨0,#[.bit],#[7]⟩],#[]⟩

/-- A π/8 provider, a shared power and coherent control, with meaning indices
independent of definition indices. The theorem uses actual checker success. -/
private def data : Artifact :=
  {definitions := #[⟨⟨target,target⟩,.unitary,.dyadicPhase 0 1 4⟩,
                    ⟨⟨target,target⟩,.unitary,.repeatOp 2 0⟩,
                    ⟨⟨full,full⟩,.unitary,.control 1 true⟩]
   meanings := #[⟨⟨full,full⟩,.control 2 true⟩,⟨⟨target,target⟩,.phase 1 4⟩,
                 ⟨⟨target,target⟩,.power 1 2⟩]
   encodings := #[⟨target,target,.identity⟩,⟨full,full,.identity⟩]
   proofs := #[⟨.equation,.phase,#[],0,1,0,0,⟨1,#[],#[]⟩⟩,
               ⟨.equation,.schema "controlled-power/1",#[0],2,0,1,1,⟨1,#[1,0],#[]⟩⟩]
   entry := ⟨2,1⟩}

private def order : Array Nat := #[0,1,2,4,5,3,6,7,8,9]

theorem accepted_phase_power_unitary : ∃ value,
    Denotes algebra (definition data) data.entry.implementation value ∧
    HierarchicalUnitary.UnitaryAt 2 value := by
  have accepted : (Derivation.checkAll data order).isOk = true := by decide +kernel
  cases hc : Derivation.checkAll data order with
  | error failure => rw [hc] at accepted; change false = true at accepted; contradiction
  | ok checked =>
    obtain ⟨proof,parent,value,_,found,_,physical,_,unitary⟩ := checkAll_unitary data order checked hc
    have same : parent = ⟨⟨full,full⟩,.unitary,.control 1 true⟩ := by
      change some (⟨⟨full,full⟩,.unitary,.control 1 true⟩ : Definition) = some parent at found
      exact (Option.some.inj found).symm
    subst parent
    exact ⟨value,physical,unitary.1⟩

end Examples

end Qleisli.HierarchicalAcceptance
