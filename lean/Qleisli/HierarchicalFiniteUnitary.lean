import Qleisli.HierarchicalFiniteEvaluation

/-! Propagate bound finite-leaf unitarity through actual conditional derivations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Only reconstructed leaves remain premises. No whole-graph unitary environment
or producer receipt is assumed. Rust/decoder correspondence remains explicit. -/

namespace Qleisli.HierarchicalFiniteUnitary
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalTyping
open HierarchicalSemantics (Tag physicalCode premises_members identity_interfaces
  implementation_stage_data meaning_stage_data)
open HierarchicalFiniteEvaluation
open HierarchicalEvaluation (body_children mapM_getD)
open HierarchicalAcceptance (apply_unitary mapM_each)
open scoped Matrix

/-- The same decoded value must satisfy the exact equation and both endpoint
dimensions. This is a mathematical premise, never a serialized checked flag. -/
def Leaf (leaves : Leaves Operator) (request : QleisliKernel.Hierarchical.Finite.Request) : Prop :=
  ∃ value, leaves.implementation request.physical.interface request.program = some value ∧
    leaves.meaning request.logical.interface request.description = some value ∧
    UnitaryInterface request.physical.interface value

theorem Leaf.equation (leaves : Leaves Operator) (request : QleisliKernel.Hierarchical.Finite.Request)
    (checked : Leaf leaves request) : Equation leaves request := by
  obtain ⟨value,physical,logical,_⟩ := checked
  exact ⟨value,physical,logical⟩

/-- Every successful actual denotation, independent of its witnessing fuel. -/
def At (leaves : Leaves Operator) (artifact : Artifact) (index : Nat) : Prop :=
  ∀ fuel value, physical algebra leaves artifact fuel index = some value →
    ∃ parent, artifact.definitions[index]? = some parent ∧ UnitaryInterface parent.interface value

theorem operation_unitary (leaves : Leaves Operator) (artifact : Artifact)
    (index : Nat) (parent : Definition) (tag : Tag) (children : List Nat)
    (found : artifact.definitions[index]? = some parent)
    (code : physicalCode parent = some (tag,children))
    (typed : NodeTyping.conditions artifact parent = true)
    (ready : ∀ child ∈ children, At leaves artifact child) : At leaves artifact index := by
  intro fuel value evaluated
  cases fuel with
  | zero => simp [physical,evaluate] at evaluated
  | succ fuel =>
    rw [physical_step algebra leaves artifact fuel index parent tag children found code] at evaluated
    cases hv : children.mapM (physical algebra leaves artifact fuel) with
    | none => simp [hv] at evaluated
    | some values =>
      have each := mapM_each children (physical algebra leaves artifact fuel) values hv
      let environment := fun i => (physical algebra leaves artifact fuel i).getD (identity 0)
      have unitary : ∀ i ∈ children, ∃ child, artifact.definitions[i]? = some child ∧
          UnitaryInterface child.interface (environment i) := by
        intro i member
        obtain ⟨v,computed⟩ := each i member
        obtain ⟨child,present,h⟩ := ready i member fuel v computed
        exact ⟨child,present,by simpa [environment,computed] using h⟩
      have mapped := mapM_getD children (physical algebra leaves artifact fuel) (identity 0)
        (fun i member => by obtain ⟨v,h⟩ := each i member; simp [h])
      have values_eq : values = children.map environment := Option.some.inj (hv.symm.trans mapped)
      have result : HierarchicalOperators.apply parent.interface tag values = value := by
        simpa only [hv,bind,Option.bind,pure,Option.some.injEq] using evaluated
      refine ⟨parent,found,?_⟩
      rw [← result,values_eq]
      exact apply_unitary artifact parent tag children environment code typed unitary

theorem ordinary_unitary (leaves : Leaves Operator) (artifact : Artifact) (proof : Proof)
    (premises : ∀ index ∈ proof.premises.toList, ∀ premise,
      artifact.proofs[index]? = some premise → At leaves artifact premise.implementation)
    (accepted : Rule.ordinary artifact proof = true) : At leaves artifact proof.implementation := by
  classical
  cases hd : artifact.definitions[proof.implementation]? with
  | none => simp [Rule.ordinary,hd] at accepted
  | some d =>
    cases hm : artifact.meanings[proof.meaning]? with
    | none => simp [Rule.ordinary,hd,hm] at accepted
    | some m =>
      cases hp : Rule.premises artifact proof with
      | none => simp [Rule.ordinary,hd,hm,hp] at accepted
      | some ps =>
        simp [Rule.ordinary,hd,hm,hp] at accepted
        have identity : Power.identityEquation artifact proof = true := by tauto
        have typed : NodeTyping.conditions artifact d = true := by tauto
        have meaningTyped : ContractTyping.meaningConditions artifact m = true := by tauto
        have matched : Rule.bodies proof d m ps = true := by tauto
        have ready : ∀ premise ∈ ps.toList,
            decide (At leaves artifact premise.implementation) = true ∧ true = true := by
          intro premise member
          obtain ⟨index,inside,found⟩ := premises_members artifact proof ps hp premise member
          exact ⟨decide_eq_true (premises index inside premise found),rfl⟩
        obtain ⟨tag,children,_,_,code,_,ready,_⟩ := body_children artifact proof d m ps
          (fun i => decide (At leaves artifact i)) (fun _ => true)
          (identity_interfaces artifact proof d m hd hm identity) typed meaningTyped ready matched
        exact operation_unitary leaves artifact proof.implementation d tag children hd code typed
          (fun child member => of_decide_eq_true (ready child member))

theorem power_unitary (leaves : Leaves Operator) (artifact : Artifact)
    (index exponent provider remaining : Nat) (pending : Power.Pending)
    (accepted : Power.inspect artifact index exponent provider remaining = .ok pending)
    (ready : At leaves artifact pending.providerProof.implementation) :
    At leaves artifact pending.root.implementation := by
  obtain ⟨_,_,_,physicalStage,logicalStage,shape,_,_,_⟩ :=
    Power.inspect_binding artifact index exponent provider remaining pending accepted
  obtain ⟨implementation,_,_,_⟩ :=
    Power.shape_provider artifact pending.root pending.providerProof pending.actual pending.logical shape
  obtain ⟨d,child,repeated,hd,hdBody,hchild,hrBody⟩ :=
    implementation_stage_data artifact pending.root.implementation pending.actual physicalStage
  obtain ⟨m,logicalChild,powered,hm,hmBody,hmChild,hpBody⟩ :=
    meaning_stage_data artifact pending.root.meaning pending.logical logicalStage
  cases hprovider : artifact.definitions[pending.actual.targetDefinition]? with
  | none => simp [Power.shape,hd,hdBody,hprovider] at shape
  | some u =>
    cases hu : artifact.meanings[pending.logical.provider]? with
    | none => simp [Power.shape,hd,hdBody,hprovider,hm,hmBody,hu] at shape
    | some v =>
      simp [Power.shape,hd,hdBody,hchild,hprovider,hm,hmBody,hmChild,hu] at shape
      have rootTyped : NodeTyping.conditions artifact d = true := by tauto
      have repeatedTyped : NodeTyping.conditions artifact repeated = true := by tauto
      have providerReady : At leaves artifact pending.actual.targetDefinition := by
        simpa only [implementation] using ready
      have repeatedReady : At leaves artifact child :=
        operation_unitary leaves artifact child repeated (.power pending.actual.count)
          [pending.actual.targetDefinition] hchild (by simp [physicalCode,hrBody]) repeatedTyped
          (by
            intro i member
            have same : i = pending.actual.targetDefinition := by simpa using member
            simpa only [same] using providerReady)
      exact operation_unitary leaves artifact pending.root.implementation d (.control pending.actual.whenOne)
        [child] hd (by simp [physicalCode,hdBody]) rootTyped
        (by
          intro i member
          have same : i = child := by simpa using member
          simpa only [same] using repeatedReady)

theorem derives_unitary (leaves : Leaves Operator) (artifact : Artifact) (index : Nat)
    (derived : Conditional.Derives artifact (Leaf leaves) index) :
    ∀ proof, artifact.proofs[index]? = some proof → At leaves artifact proof.implementation := by
  apply Conditional.Derives.induction_on_rules artifact (Leaf leaves)
    (fun index => ∀ proof, artifact.proofs[index]? = some proof → At leaves artifact proof.implementation) ?_ ?_ index derived
  · intro index remaining pending inspected discharged proof found
    have bound := (QleisliKernel.Hierarchical.Finite.inspect_conditions artifact index remaining pending inspected).2.2.2.1
    have same : proof = pending.request.proof := Option.some.inj (found.symm.trans bound.2.1)
    subst proof
    obtain ⟨value,hp,_,unitary⟩ := discharged
    intro fuel actual evaluated
    cases fuel with
    | zero => simp [physical,evaluate] at evaluated
    | succ fuel =>
      have same : value = actual := by
        simpa [physical,evaluate,definition,bound.2.2.1,bound.2.2.2.2.1,hp] using evaluated
      exact ⟨pending.request.physical,bound.2.2.1,by simpa only [same] using unitary⟩
  · intro atIndex root found matched ih proof hp
    have same : proof = root := Option.some.inj (hp.symm.trans found)
    subst proof
    obtain ⟨actual,ha,ordinary | ⟨exponent,provider,remaining,pending,inspected⟩⟩ := matched
    · have same : actual = root := Option.some.inj (ha.symm.trans found)
      subst actual
      exact ordinary_unitary leaves artifact root ih ordinary
    · obtain ⟨actualRoot,singleton,providerFound,_,_,_,_,_,_⟩ :=
        Power.inspect_binding artifact atIndex exponent provider remaining pending inspected
      have same : root = pending.root := Option.some.inj (found.symm.trans actualRoot)
      have ready := ih pending.providerProofIndex (by simp [same,singleton]) pending.providerProof providerFound
      simpa only [same] using power_unitary leaves artifact atIndex exponent provider remaining pending inspected ready

/-- Actual entry success plus only the returned reconstructed leaf obligations
constructs a common unitary denotation. No global unitary environment is assumed. -/
theorem checkAll_unitary (leaves : Leaves Operator) (artifact : Artifact) (order : Array Nat)
    (pending : Conditional.Pending) (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Leaf leaves request) :
    ∃ proof parent fuel value, artifact.proofs[artifact.entry.proof]? = some proof ∧
      artifact.definitions[artifact.entry.implementation]? = some parent ∧
      proof.implementation = artifact.entry.implementation ∧
      physical algebra leaves artifact fuel artifact.entry.implementation = some value ∧
      logical algebra leaves artifact fuel proof.meaning = some value ∧
      UnitaryInterface parent.interface value := by
  have equations := fun request member => Leaf.equation leaves request (discharged request member)
  obtain ⟨proof,fuel,value,found,bound,hp,hm⟩ := checkAll_denotes algebra leaves artifact order pending accepted equations
  have derived := (Conditional.checkAll_conditions artifact order pending accepted).2.2.2.2 (Leaf leaves) discharged
  have ready := derives_unitary leaves artifact artifact.entry.proof derived proof found
  obtain ⟨parent,present,unitary⟩ := ready fuel value (by simpa only [bound] using hp)
  exact ⟨proof,parent,fuel,value,found,by simpa only [bound] using present,bound,hp,hm,unitary⟩

theorem checked_denotation_unitary (leaves : Leaves Operator) (artifact : Artifact) (order : Array Nat)
    (pending : Conditional.Pending) (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Leaf leaves request)
    (parent : Definition) (found : artifact.definitions[artifact.entry.implementation]? = some parent)
    (fuel : Nat) (value : Operator)
    (evaluated : physical algebra leaves artifact fuel artifact.entry.implementation = some value) :
    UnitaryInterface parent.interface value := by
  obtain ⟨proof,actual,depth,result,hp,hd,_,computed,_,unitary⟩ :=
    checkAll_unitary leaves artifact order pending accepted discharged
  have same : actual = parent := Option.some.inj (hd.symm.trans found)
  subst actual
  have equal := evaluate_unique algebra (definition leaves artifact) fuel depth artifact.entry.implementation
    value result evaluated computed
  simpa only [equal] using unitary

theorem checkAll_inverse_laws {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves Operator) (artifact : Artifact) (order : Array Nat)
    (pending : Conditional.Pending) (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Leaf leaves request)
    (parent : Definition) (found : artifact.definitions[artifact.entry.implementation]? = some parent)
    (fuel : Nat) (value : Operator)
    (evaluated : physical algebra leaves artifact fuel artifact.entry.implementation = some value) :
    let n := width parent.interface.inputs
    let joint := Matrix.kronecker (matrixAt n n value) (1 : Matrix R R ℂ)
    jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 :=
  HierarchicalUnitary.reference_unitary
    (checked_denotation_unitary leaves artifact order pending accepted discharged parent found fuel value evaluated).1

end Qleisli.HierarchicalFiniteUnitary
