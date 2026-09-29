import Qleisli.HierarchicalAcceptance
import QleisliKernel.Hierarchical.Conditional

/-! Constructed denotations conditional on actual finite-leaf equations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Leaf readers consume actual bytes and interfaces, independently on each side.
Their equations remain explicit until the transitional Rust correspondence is
established. This mathematical evaluator is not the reference runtime. -/

namespace Qleisli.HierarchicalFiniteEvaluation
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics
open HierarchicalEvaluation (mapM_congr_success mapM_getD body_children eventually_all)
open scoped Matrix

structure Leaves (S : Type) where
  implementation : Interface → ByteArray → Option S
  meaning : Interface → ByteArray → Option S

inductive Node (S : Type) where
  | leaf (value : S)
  | operation (node : HierarchicalEvaluation.Node)

/-- No proof table or producer assertion enters either denotation reader. -/
def definition {S : Type} (leaves : Leaves S) (artifact : Artifact) (index : Nat) : Option (Node S) := do
  let d ← artifact.definitions[index]?
  match d.body with
  | .leaf bytes => return .leaf (← leaves.implementation d.interface bytes)
  | _ =>
    let (tag,children) ← physicalCode d
    return .operation ⟨d.interface,tag,children⟩

def meaning {S : Type} (leaves : Leaves S) (artifact : Artifact) (index : Nat) : Option (Node S) := do
  let m ← artifact.meanings[index]?
  match m.body with
  | .finite bytes => return .leaf (← leaves.meaning m.interface bytes)
  | _ =>
    let (tag,children) ← logicalCode m
    return .operation ⟨m.interface,tag,children⟩

/-- Fuel bounds dependency depth, including actual bodies under zero powers. -/
def evaluate {S : Type} (algebra : Algebra S) (read : Nat → Option (Node S)) : Nat → Nat → Option S
  | 0, _ => none
  | fuel+1, index => do
    let node ← read index
    match node with
    | .leaf value => return value
    | .operation node =>
      let values ← node.children.mapM (evaluate algebra read fuel)
      return algebra.apply node.interface node.tag values

def physical {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact) : Nat → Nat → Option S :=
  evaluate algebra (definition leaves artifact)

def logical {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact) : Nat → Nat → Option S :=
  evaluate algebra (meaning leaves artifact)

theorem physical_ir_only {S : Type} (algebra : Algebra S) (leaves : Leaves S) (a b : Artifact)
    (same : a.definitions = b.definitions) : physical algebra leaves a = physical algebra leaves b := by
  have readers : definition leaves a = definition leaves b := by
    funext index
    simp [definition,same]
  unfold physical
  rw [readers]

theorem logical_ir_only {S : Type} (algebra : Algebra S) (leaves : Leaves S) (a b : Artifact)
    (same : a.meanings = b.meanings) : logical algebra leaves a = logical algebra leaves b := by
  have readers : meaning leaves a = meaning leaves b := by
    funext index
    simp [meaning,same]
  unfold logical
  rw [readers]

def Equation {S : Type} (leaves : Leaves S) (request : QleisliKernel.Hierarchical.Finite.Request) : Prop :=
  ∃ value, leaves.implementation request.physical.interface request.program = some value ∧
    leaves.meaning request.logical.interface request.description = some value

theorem definition_operation {S : Type} (leaves : Leaves S) (artifact : Artifact)
    (index : Nat) (d : Definition) (tag : Tag) (children : List Nat)
    (found : artifact.definitions[index]? = some d) (code : physicalCode d = some (tag,children)) :
    definition leaves artifact index = some (.operation ⟨d.interface,tag,children⟩) := by
  cases body : d.body <;> simp [physicalCode,body] at code <;>
    simp [definition,found,physicalCode,body] <;> simp_all

theorem meaning_operation {S : Type} (leaves : Leaves S) (artifact : Artifact)
    (index : Nat) (m : Meaning) (tag : Tag) (children : List Nat)
    (found : artifact.meanings[index]? = some m) (code : logicalCode m = some (tag,children)) :
    meaning leaves artifact index = some (.operation ⟨m.interface,tag,children⟩) := by
  cases body : m.body <;> simp [logicalCode,body] at code <;>
    simp [meaning,found,logicalCode,body] <;> simp_all

theorem evaluate_more {S : Type} (algebra : Algebra S) (read : Nat → Option (Node S))
    (fuel index : Nat) (value : S) (accepted : evaluate algebra read fuel index = some value) :
    ∀ more, fuel ≤ more → evaluate algebra read more index = some value := by
  induction fuel generalizing index value with
  | zero => simp [evaluate] at accepted
  | succ fuel ih =>
    cases hn : read index with
    | none => simp [evaluate,hn] at accepted
    | some node =>
      cases node with
      | leaf result =>
        have same : result = value := by simpa [evaluate,hn] using accepted
        subst result
        intro more enough
        cases more with
        | zero => omega
        | succ more => simp [evaluate,hn]
      | operation node =>
        cases hc : node.children.mapM (evaluate algebra read fuel) with
        | none => simp [evaluate,hn,hc] at accepted
        | some values =>
          have equal : algebra.apply node.interface node.tag values = value := by
            simpa [evaluate,hn,hc] using accepted
          intro more bound
          cases more with
          | zero => omega
          | succ more =>
            have children := mapM_congr_success node.children (evaluate algebra read fuel)
              (evaluate algebra read more) values hc (fun child _ result checked => ih child result checked more (by omega))
            simp [evaluate,hn,children,equal]

theorem evaluate_unique {S : Type} (algebra : Algebra S) (read : Nat → Option (Node S))
    (fuel more index : Nat) (first second : S)
    (hf : evaluate algebra read fuel index = some first)
    (hs : evaluate algebra read more index = some second) : first = second := by
  have a := evaluate_more algebra read fuel index first hf (max fuel more) (Nat.le_max_left _ _)
  have b := evaluate_more algebra read more index second hs (max fuel more) (Nat.le_max_right _ _)
  exact Option.some.inj (a.symm.trans b)

theorem evaluate_node {S : Type} (algebra : Algebra S) (read : Nat → Option (Node S))
    (fuel index : Nat) (node : HierarchicalEvaluation.Node) (fallback : S)
    (found : read index = some (.operation node))
    (children : ∀ child ∈ node.children, (evaluate algebra read fuel child).isSome = true) :
    evaluate algebra read (fuel+1) index =
      some (algebra.apply node.interface node.tag
        (node.children.map (fun child => (evaluate algebra read fuel child).getD fallback))) := by
  simp [evaluate,found,mapM_getD node.children (evaluate algebra read fuel) fallback children]

theorem ordinary_evaluate {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact) (proof : Proof)
    (fuel : Nat)
    (premises : ∀ index ∈ proof.premises.toList, ∀ premise, artifact.proofs[index]? = some premise →
      ∃ value, physical algebra leaves artifact fuel premise.implementation = some value ∧
        logical algebra leaves artifact fuel premise.meaning = some value)
    (accepted : Rule.ordinary artifact proof = true) :
    ∃ value, physical algebra leaves artifact (fuel+1) proof.implementation = some value ∧
      logical algebra leaves artifact (fuel+1) proof.meaning = some value := by
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
        have interface := identity_interfaces artifact proof d m hd hm identity
        have evaluated : ∀ premise ∈ ps.toList, ∃ value,
            physical algebra leaves artifact fuel premise.implementation = some value ∧
            logical algebra leaves artifact fuel premise.meaning = some value := by
          intro premise member
          obtain ⟨index,inside,found⟩ := premises_members artifact proof ps hp premise member
          exact premises index inside premise found
        have ready : ∀ premise ∈ ps.toList,
            (physical algebra leaves artifact fuel premise.implementation).isSome = true ∧
            (logical algebra leaves artifact fuel premise.meaning).isSome = true := by
          intro premise inside
          obtain ⟨value,he,hl⟩ := evaluated premise inside
          simp [he,hl]
        obtain ⟨pt,pc,mt,mc,ph,mh,pready,mready⟩ :=
          body_children artifact proof d m ps
            (fun i => (physical algebra leaves artifact fuel i).isSome)
            (fun i => (logical algebra leaves artifact fuel i).isSome) interface typed meaningTyped ready matched
        let fallback := algebra.apply d.interface pt []
        let operations := fun index => (physical algebra leaves artifact fuel index).getD fallback
        let meanings := fun index => (logical algebra leaves artifact fuel index).getD fallback
        have equations : ∀ premise ∈ ps.toList,
            operations premise.implementation = meanings premise.meaning := by
          intro premise inside
          obtain ⟨value,he,hl⟩ := evaluated premise inside
          simp [operations,meanings,he,hl]
        have same := bodies_sound algebra artifact proof d m ps operations meanings
          interface typed meaningTyped equations matched
        have actual := evaluate_node algebra (definition leaves artifact) fuel proof.implementation
          ⟨d.interface,pt,pc⟩ fallback (definition_operation leaves artifact _ d pt pc hd ph) pready
        have expected := evaluate_node algebra (meaning leaves artifact) fuel proof.meaning
          ⟨m.interface,mt,mc⟩ fallback (meaning_operation leaves artifact _ m mt mc hm mh) mready
        have eq : algebra.apply d.interface pt (pc.map operations) =
            algebra.apply m.interface mt (mc.map meanings) := by
          simpa [HierarchicalSemantics.physical,HierarchicalSemantics.logical,ph,mh] using same
        refine ⟨algebra.apply d.interface pt (pc.map operations),actual,?_⟩
        change logical algebra leaves artifact (fuel+1) proof.meaning = _
        rw [eq]
        exact expected

theorem physical_step {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact)
    (fuel index : Nat) (d : Definition) (tag : Tag) (children : List Nat)
    (found : artifact.definitions[index]? = some d) (code : physicalCode d = some (tag,children)) :
    physical algebra leaves artifact (fuel+1) index = (do
      let values ← children.mapM (physical algebra leaves artifact fuel)
      return algebra.apply d.interface tag values) := by
  have node := definition_operation leaves artifact index d tag children found code
  simp [physical,evaluate,node]

theorem logical_step {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact)
    (fuel index : Nat) (m : Meaning) (tag : Tag) (children : List Nat)
    (found : artifact.meanings[index]? = some m) (code : logicalCode m = some (tag,children)) :
    logical algebra leaves artifact (fuel+1) index = (do
      let values ← children.mapM (logical algebra leaves artifact fuel)
      return algebra.apply m.interface tag values) := by
  have node := meaning_operation leaves artifact index m tag children found code
  simp [logical,evaluate,node]

theorem power_evaluate {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact)
    (index exponent provider remaining fuel : Nat) (pending : Power.Pending)
    (accepted : Power.inspect artifact index exponent provider remaining = .ok pending)
    (value : S)
    (he : physical algebra leaves artifact fuel pending.providerProof.implementation = some value)
    (hl : logical algebra leaves artifact fuel pending.providerProof.meaning = some value) :
    ∃ result, physical algebra leaves artifact (fuel+2) pending.root.implementation = some result ∧
      logical algebra leaves artifact (fuel+2) pending.root.meaning = some result := by
  obtain ⟨_,_,_,physicalStage,logicalStage,shape,_,_,_⟩ :=
    Power.inspect_binding artifact index exponent provider remaining pending accepted
  obtain ⟨implementation,meaning,count,polarity⟩ :=
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
      have rootIdentity : Power.identityEquation artifact pending.root = true := by tauto
      have providerIdentity : Power.identityEquation artifact pending.providerProof = true := by tauto
      have rt : NodeTyping.conditions artifact repeated = true := by tauto
      have pt : ContractTyping.meaningConditions artifact powered = true := by tauto
      have ri : repeated.interface = u.interface := by
        simp [NodeTyping.conditions,hrBody,hprovider] at rt
        tauto
      have pi : powered.interface = v.interface := by
        simp [ContractTyping.meaningConditions,hpBody,hu] at pt
        tauto
      have ui : u.interface = v.interface := identity_interfaces artifact pending.providerProof u v
        (by simpa only [implementation] using hprovider) (by simpa only [meaning] using hu) providerIdentity
      have sameInterface := identity_interfaces artifact pending.root d m hd hm rootIdentity
      rw [implementation] at he
      rw [meaning] at hl
      have repeatedValue : physical algebra leaves artifact (fuel+1) child =
          some (algebra.apply v.interface (.power pending.logical.count) [value]) := by
        rw [physical_step algebra leaves artifact fuel child repeated (.power pending.actual.count)
          [pending.actual.targetDefinition] hchild (by simp [physicalCode,hrBody])]
        simp [he,ri,ui,count]
      have poweredValue : logical algebra leaves artifact (fuel+1) logicalChild =
          some (algebra.apply v.interface (.power pending.logical.count) [value]) := by
        rw [logical_step algebra leaves artifact fuel logicalChild powered (.power pending.logical.count)
          [pending.logical.provider] hmChild (by simp [logicalCode,hpBody])]
        simp [hl,pi]
      refine ⟨algebra.apply m.interface (.control pending.logical.polarity)
        [algebra.apply v.interface (.power pending.logical.count) [value]],?_,?_⟩
      · rw [physical_step algebra leaves artifact (fuel+1) pending.root.implementation d (.control pending.actual.whenOne)
          [child] hd (by simp [physicalCode,hdBody])]
        simp [repeatedValue,sameInterface,polarity]
      · rw [logical_step algebra leaves artifact (fuel+1) pending.root.meaning m (.control pending.logical.polarity)
          [logicalChild] hm (by simp [logicalCode,hmBody])]
        simp [poweredValue]

theorem derives_evaluate {S : Type} (algebra : Algebra S) (leaves : Leaves S) (artifact : Artifact)
    (index : Nat) (derived : Conditional.Derives artifact (Equation leaves) index) :
    ∀ proof, artifact.proofs[index]? = some proof → ∃ fuel value,
      physical algebra leaves artifact fuel proof.implementation = some value ∧
      logical algebra leaves artifact fuel proof.meaning = some value := by
  induction derived with
  | finite index remaining pending inspected discharged =>
    intro proof found
    have bound := (QleisliKernel.Hierarchical.Finite.inspect_conditions artifact index remaining pending inspected).2.2.2.1
    have same : proof = pending.request.proof := Option.some.inj (found.symm.trans bound.2.1)
    subst proof
    obtain ⟨value,hp,hm⟩ := discharged
    refine ⟨1,value,?_,?_⟩
    · simp [physical,evaluate,definition,bound.2.2.1,bound.2.2.2.2.1,hp]
    · simp [logical,evaluate,meaning,bound.2.2.2.1,bound.2.2.2.2.2,hm]
  | rule atIndex root found matched _ ih =>
    intro proof hp
    have same : proof = root := Option.some.inj (hp.symm.trans found)
    subst proof
    have eventually : ∀ child ∈ root.premises.toList, ∃ bound, ∀ fuel, bound ≤ fuel →
        ∀ premise, artifact.proofs[child]? = some premise → ∃ value,
          physical algebra leaves artifact fuel premise.implementation = some value ∧
          logical algebra leaves artifact fuel premise.meaning = some value := by
      intro child member
      cases hp : artifact.proofs[child]? with
      | none => exact ⟨0,by simp⟩
      | some premise =>
        obtain ⟨fuel,value,he,hl⟩ := ih child member premise hp
        refine ⟨fuel,?_⟩
        intro more enough actual ha
        have same : actual = premise := Option.some.inj ha.symm
        subst actual
        exact ⟨value,evaluate_more algebra (definition leaves artifact) fuel premise.implementation value he more enough,
          evaluate_more algebra (meaning leaves artifact) fuel premise.meaning value hl more enough⟩
    obtain ⟨fuel,ready⟩ := eventually_all root.premises.toList
      (fun child fuel => ∀ premise, artifact.proofs[child]? = some premise → ∃ value,
        physical algebra leaves artifact fuel premise.implementation = some value ∧
        logical algebra leaves artifact fuel premise.meaning = some value) eventually
    obtain ⟨actual,ha,ordinary | ⟨exponent,provider,remaining,pending,inspected⟩⟩ := matched
    · have same : actual = root := Option.some.inj (ha.symm.trans found)
      subst actual
      obtain ⟨value,he,hl⟩ := ordinary_evaluate algebra leaves artifact root fuel (ready fuel (Nat.le_refl _)) ordinary
      exact ⟨fuel+1,value,he,hl⟩
    · obtain ⟨actualRoot,singleton,providerFound,_,_,_,_,_,_⟩ :=
        Power.inspect_binding artifact atIndex exponent provider remaining pending inspected
      have same : root = pending.root := Option.some.inj (found.symm.trans actualRoot)
      obtain ⟨value,he,hl⟩ := ready fuel (Nat.le_refl _) pending.providerProofIndex
        (by simp [same,singleton]) pending.providerProof providerFound
      obtain ⟨result,hp,hm⟩ := power_evaluate algebra leaves artifact atIndex exponent provider remaining fuel pending inspected value he hl
      exact ⟨fuel+2,result,by simpa only [same] using hp,by simpa only [same] using hm⟩


/-- The entry implementation remains bound by actual whole-artifact preparation. -/
theorem checkAll_entry (artifact : Artifact) (order : Array Nat) (pending : Conditional.Pending)
    (accepted : Conditional.checkAll artifact order = .ok pending) :
    ∃ proof, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation := by
  have ht := (Conditional.checkAll_conditions artifact order pending accepted).1
  have hn := (ContractTyping.checkAll_conditions artifact order pending.typed ht).1
  have hp := (NodeTyping.checkAll_conditions artifact order pending.typed.nodes hn).1
  unfold Artifact.prepare at hp
  cases projected : Artifact.project artifact with
  | error failure => simp [projected] at hp
  | ok projection =>
    exact finish_entry artifact projection order pending.typed.nodes.prepared (by simpa only [projected] using hp)

/-- Only the finite request equations remain premises. No interpretation of
an entire producer-selected environment or displayed proof conclusion is assumed. -/
theorem checkAll_denotes {S : Type} (algebra : Algebra S) (leaves : Leaves S)
    (artifact : Artifact) (order : Array Nat) (pending : Conditional.Pending)
    (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Equation leaves request) :
    ∃ proof fuel value, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation ∧
      physical algebra leaves artifact fuel artifact.entry.implementation = some value ∧
      logical algebra leaves artifact fuel proof.meaning = some value := by
  have derived := (Conditional.checkAll_conditions artifact order pending accepted).2.2.2.2
    (Equation leaves) discharged
  obtain ⟨proof,found,bound⟩ := checkAll_entry artifact order pending accepted
  obtain ⟨fuel,value,hp,hm⟩ := derives_evaluate algebra leaves artifact artifact.entry.proof derived proof found
  exact ⟨proof,fuel,value,found,bound,by simpa only [bound] using hp,hm⟩

theorem checkAll_equal {S : Type} (algebra : Algebra S) (leaves : Leaves S)
    (artifact : Artifact) (order : Array Nat) (pending : Conditional.Pending)
    (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Equation leaves request)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (fuel more : Nat) (P M : S)
    (hp : physical algebra leaves artifact fuel artifact.entry.implementation = some P)
    (hm : logical algebra leaves artifact more proof.meaning = some M) : P = M := by
  obtain ⟨actual,depth,value,ha,_,he,hl⟩ := checkAll_denotes algebra leaves artifact order pending accepted discharged
  have same : actual = proof := Option.some.inj (ha.symm.trans found)
  subst actual
  have p := evaluate_unique algebra (definition leaves artifact) fuel depth _ P value hp he
  have m := evaluate_unique algebra (meaning leaves artifact) more depth _ M value hm hl
  exact p.trans m.symm

/-- Exact complete operators, retaining scalar phase; native/Rust correspondence
and leaf-unitarity acceptance are still explicit integration obligations. -/
theorem checkAll_matrix (leaves : Leaves HierarchicalOperators.Operator)
    (artifact : Artifact) (order : Array Nat) (pending : Conditional.Pending)
    (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Equation leaves request)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (fuel more : Nat) (P M : HierarchicalOperators.Operator)
    (hp : physical HierarchicalOperators.algebra leaves artifact fuel artifact.entry.implementation = some P)
    (hm : logical HierarchicalOperators.algebra leaves artifact more proof.meaning = some M)
    (inputWidth outputWidth : Nat) :
    HierarchicalOperators.matrixAt inputWidth outputWidth P =
      HierarchicalOperators.matrixAt inputWidth outputWidth M := by
  rw [checkAll_equal HierarchicalOperators.algebra leaves artifact order pending accepted discharged proof found fuel more P M hp hm]

theorem checkAll_reference {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves HierarchicalOperators.Operator)
    (artifact : Artifact) (order : Array Nat) (pending : Conditional.Pending)
    (accepted : Conditional.checkAll artifact order = .ok pending)
    (discharged : ∀ request ∈ pending.state.requests.toList, Equation leaves request)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (fuel more : Nat) (P M : HierarchicalOperators.Operator)
    (hp : physical HierarchicalOperators.algebra leaves artifact fuel artifact.entry.implementation = some P)
    (hm : logical HierarchicalOperators.algebra leaves artifact more proof.meaning = some M)
    (inputWidth outputWidth : Nat)
    (rho : Matrix ((Fin inputWidth → Bool) × R) ((Fin inputWidth → Bool) × R) ℂ) :
    HierarchicalOperators.referenceMap (HierarchicalOperators.matrixAt inputWidth outputWidth P) rho =
      HierarchicalOperators.referenceMap (HierarchicalOperators.matrixAt inputWidth outputWidth M) rho := by
  rw [checkAll_matrix leaves artifact order pending accepted discharged proof found fuel more P M hp hm inputWidth outputWidth]

end Qleisli.HierarchicalFiniteEvaluation
