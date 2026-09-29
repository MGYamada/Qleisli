import Qleisli.HierarchicalOperators

/-! Constructed partial denotations of actual hierarchical bodies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This mathematical evaluator is separate from resource-bounded verification.
Unsupported bodies and missing children produce no denotation. -/

namespace Qleisli.HierarchicalEvaluation
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics

structure Node where
  interface : Interface
  tag : Tag
  children : List Nat

def definition (artifact : Artifact) (index : Nat) : Option Node := do
  let d ← artifact.definitions[index]?
  let (tag,children) ← physicalCode d
  return ⟨d.interface,tag,children⟩

def meaning (artifact : Artifact) (index : Nat) : Option Node := do
  let m ← artifact.meanings[index]?
  let (tag,children) ← logicalCode m
  return ⟨m.interface,tag,children⟩

/-- Fuel bounds dependency depth, never an operation's repetition count.
Even count zero reads and evaluates its actual child. -/
def evaluate {S : Type} (algebra : Algebra S) (read : Nat → Option Node) : Nat → Nat → Option S
  | 0, _ => none
  | fuel + 1, index => do
    let node ← read index
    let values ← node.children.mapM (evaluate algebra read fuel)
    return algebra.apply node.interface node.tag values

def physical {S : Type} (algebra : Algebra S) (artifact : Artifact) : Nat → Nat → Option S :=
  evaluate algebra (definition artifact)

def logical {S : Type} (algebra : Algebra S) (artifact : Artifact) : Nat → Nat → Option S :=
  evaluate algebra (meaning artifact)

theorem physical_ir_only {S : Type} (algebra : Algebra S) (a b : Artifact)
    (same : a.definitions = b.definitions) : physical algebra a = physical algebra b := by
  have readers : definition a = definition b := by
    funext index
    simp [definition,same]
  unfold physical
  rw [readers]

theorem logical_ir_only {S : Type} (algebra : Algebra S) (a b : Artifact)
    (same : a.meanings = b.meanings) : logical algebra a = logical algebra b := by
  have readers : meaning a = meaning b := by
    funext index
    simp [meaning,same]
  unfold logical
  rw [readers]

theorem mapM_success {A B : Type} (xs : List A) (f : A → Option B)
    (success : ∀ x ∈ xs, (f x).isSome = true) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    cases hx : f x with
    | none => simpa [hx] using success x (by simp)
    | some y =>
      obtain ⟨ys,hy⟩ := ih (fun z member => success z (by simp [member]))
      exact ⟨y::ys,by simp [hx,hy]⟩

theorem mapM_congr_success {A B : Type} (xs : List A) (f g : A → Option B) (ys : List B)
    (accepted : xs.mapM f = some ys)
    (extend : ∀ x ∈ xs, ∀ value, f x = some value → g x = some value) :
    xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil => simpa using accepted
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [hx] at accepted
    | some y =>
      cases hs : xs.mapM f with
      | none => simp [hx,hs] at accepted
      | some rest =>
        have same : y :: rest = ys := by simpa [hx,hs] using accepted
        subst ys
        have head := extend x (by simp) y hx
        have tail := ih rest hs (fun z member value hz => extend z (by simp [member]) value hz)
        simp [head,tail]

theorem evaluate_more {S : Type} (algebra : Algebra S) (read : Nat → Option Node)
    (fuel index : Nat) (value : S) (accepted : evaluate algebra read fuel index = some value) :
    ∀ more, fuel ≤ more → evaluate algebra read more index = some value := by
  induction fuel generalizing index value with
  | zero => simp [evaluate] at accepted
  | succ fuel ih =>
    cases hn : read index with
    | none => simp [evaluate,hn] at accepted
    | some node =>
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

theorem evaluate_unique {S : Type} (algebra : Algebra S) (read : Nat → Option Node)
    (fuel more index : Nat) (first second : S)
    (hf : evaluate algebra read fuel index = some first)
    (hs : evaluate algebra read more index = some second) : first = second := by
  have a := evaluate_more algebra read fuel index first hf (max fuel more) (Nat.le_max_left _ _)
  have b := evaluate_more algebra read more index second hs (max fuel more) (Nat.le_max_right _ _)
  exact Option.some.inj (a.symm.trans b)

theorem mapM_getD {A B : Type} (xs : List A) (f : A → Option B) (fallback : B)
    (success : ∀ x ∈ xs, (f x).isSome = true) :
    xs.mapM f = some (xs.map (fun x => (f x).getD fallback)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simpa [hx] using success x (by simp)
    | some value =>
      have rest := ih (fun z member => success z (by simp [member]))
      simp [hx,rest]

/-- A fallback is used only to state a total lookup environment; success of
every actual child is proved before this equation can apply. -/
theorem evaluate_node {S : Type} (algebra : Algebra S) (read : Nat → Option Node)
    (fuel index : Nat) (node : Node) (fallback : S) (found : read index = some node)
    (children : ∀ child ∈ node.children, (evaluate algebra read fuel child).isSome = true) :
    evaluate algebra read (fuel+1) index =
      some (algebra.apply node.interface node.tag
        (node.children.map (fun child => (evaluate algebra read fuel child).getD fallback))) := by
  simp [evaluate,found,mapM_getD node.children (evaluate algebra read fuel) fallback children]

theorem children_success (ps : Array Proof) (p m : Array Nat) (physical logical : Nat → Bool)
    (matched : Rule.children ps p m = true)
    (ready : ∀ premise ∈ ps.toList, physical premise.implementation = true ∧ logical premise.meaning = true) :
    (∀ child ∈ p.toList, physical child = true) ∧ (∀ child ∈ m.toList, logical child = true) := by
  simp only [Rule.children,Bool.and_eq_true,beq_iff_eq] at matched
  rw [matched.1,matched.2]
  simp only [Array.toList_map]
  constructor
  · intro child member
    obtain ⟨premise,inside,equal⟩ := List.mem_map.mp member
    subst child
    exact (ready premise inside).1
  · intro child member
    obtain ⟨premise,inside,equal⟩ := List.mem_map.mp member
    subst child
    exact (ready premise inside).2

theorem body_children (artifact : Artifact) (proof : Proof) (d : Artifact.Definition) (m : Meaning)
    (ps : Array Proof) (physical logical : Nat → Bool)
    (interface : d.interface = m.interface)
    (typed : NodeTyping.conditions artifact d = true)
    (meaningTyped : ContractTyping.meaningConditions artifact m = true)
    (ready : ∀ premise ∈ ps.toList, physical premise.implementation = true ∧ logical premise.meaning = true)
    (matched : Rule.bodies proof d m ps = true) :
    ∃ pt pc mt mc, physicalCode d = some (pt,pc) ∧ logicalCode m = some (mt,mc) ∧
      (∀ child ∈ pc, physical child = true) ∧ (∀ child ∈ mc, logical child = true) := by
  unfold Rule.bodies at matched
  split at matched
  next p q _ hd hm => simp [physicalCode,logicalCode,hd,hm]
  next p _ hd hm => simp [physicalCode,logicalCode,hd,hm]
  next p q _ hd hm => simp [physicalCode,logicalCode,hd,hm]
  next target j k l h _ hd hm =>
    obtain ⟨port,found,_⟩ := phase_target artifact d m target j k l h hd hm typed meaningTyped interface
    simp [physicalCode,logicalCode,hd,hm,found]
  next p q _ hd hm =>
    have children := children_success ps p q physical logical matched ready
    exact ⟨.sequence,p.toList,.sequence,q.toList,by simp [physicalCode,hd],by simp [logicalCode,hm],children⟩
  next p q a b _ hd hm =>
    have children := children_success ps #[p,q] #[a,b] physical logical matched ready
    exact ⟨.tensor,[p,q],.tensor,[a,b],by simp [physicalCode,hd],by simp [logicalCode,hm],children⟩
  next p q _ hd hm =>
    have children := children_success ps #[p] #[q] physical logical matched ready
    exact ⟨.inverse,[p],.inverse,[q],by simp [physicalCode,hd],by simp [logicalCode,hm],children⟩
  next p b q c _ hd hm =>
    simp only [Bool.and_eq_true] at matched
    have children := children_success ps #[p] #[q] physical logical matched.2 ready
    exact ⟨.control b,[p],.control c,[q],by simp [physicalCode,hd],by simp [logicalCode,hm],children⟩
  next n p q k _ hd hm =>
    simp only [Bool.and_eq_true] at matched
    have children := children_success ps #[p] #[q] physical logical matched.2 ready
    exact ⟨.power n,[p],.power k,[q],by simp [physicalCode,hd],by simp [logicalCode,hm],children⟩
  next => contradiction

theorem ordinary_evaluate {S : Type} (algebra : Algebra S) (artifact : Artifact) (proof : Proof)
    (fuel : Nat)
    (premises : ∀ index ∈ proof.premises.toList, ∀ premise, artifact.proofs[index]? = some premise →
      ∃ value, physical algebra artifact fuel premise.implementation = some value ∧
        logical algebra artifact fuel premise.meaning = some value)
    (accepted : Rule.ordinary artifact proof = true) :
    ∃ value, physical algebra artifact (fuel+1) proof.implementation = some value ∧
      logical algebra artifact (fuel+1) proof.meaning = some value := by
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
            physical algebra artifact fuel premise.implementation = some value ∧
            logical algebra artifact fuel premise.meaning = some value := by
          intro premise member
          obtain ⟨index,inside,found⟩ := premises_members artifact proof ps hp premise member
          exact premises index inside premise found
        have ready : ∀ premise ∈ ps.toList,
            (physical algebra artifact fuel premise.implementation).isSome = true ∧
            (logical algebra artifact fuel premise.meaning).isSome = true := by
          intro premise inside
          obtain ⟨value,he,hl⟩ := evaluated premise inside
          simp [he,hl]
        obtain ⟨pt,pc,mt,mc,ph,mh,pready,mready⟩ :=
          body_children artifact proof d m ps
            (fun i => (physical algebra artifact fuel i).isSome)
            (fun i => (logical algebra artifact fuel i).isSome) interface typed meaningTyped ready matched
        let fallback := algebra.apply d.interface pt []
        let operations := fun index => (physical algebra artifact fuel index).getD fallback
        let meanings := fun index => (logical algebra artifact fuel index).getD fallback
        have equations : ∀ premise ∈ ps.toList,
            operations premise.implementation = meanings premise.meaning := by
          intro premise inside
          obtain ⟨value,he,hl⟩ := evaluated premise inside
          simp [operations,meanings,he,hl]
        have same := bodies_sound algebra artifact proof d m ps operations meanings
          interface typed meaningTyped equations matched
        have actual := evaluate_node algebra (definition artifact) fuel proof.implementation
          ⟨d.interface,pt,pc⟩ fallback (by simp [definition,hd,ph]) pready
        have expected := evaluate_node algebra (meaning artifact) fuel proof.meaning
          ⟨m.interface,mt,mc⟩ fallback (by simp [meaning,hm,mh]) mready
        have eq : algebra.apply d.interface pt (pc.map operations) =
            algebra.apply m.interface mt (mc.map meanings) := by
          simpa [HierarchicalSemantics.physical,HierarchicalSemantics.logical,ph,mh] using same
        refine ⟨algebra.apply d.interface pt (pc.map operations),actual,?_⟩
        change logical algebra artifact (fuel+1) proof.meaning = _
        rw [eq]
        exact expected

theorem physical_step {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (fuel index : Nat) (d : Artifact.Definition) (tag : Tag) (children : List Nat)
    (found : artifact.definitions[index]? = some d) (code : physicalCode d = some (tag,children)) :
    physical algebra artifact (fuel+1) index = (do
      let values ← children.mapM (physical algebra artifact fuel)
      return algebra.apply d.interface tag values) := by
  simp [physical,evaluate,definition,found,code]

theorem logical_step {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (fuel index : Nat) (m : Meaning) (tag : Tag) (children : List Nat)
    (found : artifact.meanings[index]? = some m) (code : logicalCode m = some (tag,children)) :
    logical algebra artifact (fuel+1) index = (do
      let values ← children.mapM (logical algebra artifact fuel)
      return algebra.apply m.interface tag values) := by
  simp [logical,evaluate,meaning,found,code]

theorem power_evaluate {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (index exponent provider remaining fuel : Nat) (pending : Power.Pending)
    (accepted : Power.inspect artifact index exponent provider remaining = .ok pending)
    (value : S)
    (he : physical algebra artifact fuel pending.providerProof.implementation = some value)
    (hl : logical algebra artifact fuel pending.providerProof.meaning = some value) :
    ∃ result, physical algebra artifact (fuel+2) pending.root.implementation = some result ∧
      logical algebra artifact (fuel+2) pending.root.meaning = some result := by
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
      have repeatedValue : physical algebra artifact (fuel+1) child =
          some (algebra.apply v.interface (.power pending.logical.count) [value]) := by
        rw [physical_step algebra artifact fuel child repeated (.power pending.actual.count)
          [pending.actual.targetDefinition] hchild (by simp [physicalCode,hrBody])]
        simp [he,ri,ui,count]
      have poweredValue : logical algebra artifact (fuel+1) logicalChild =
          some (algebra.apply v.interface (.power pending.logical.count) [value]) := by
        rw [logical_step algebra artifact fuel logicalChild powered (.power pending.logical.count)
          [pending.logical.provider] hmChild (by simp [logicalCode,hpBody])]
        simp [hl,pi]
      refine ⟨algebra.apply m.interface (.control pending.logical.polarity)
        [algebra.apply v.interface (.power pending.logical.count) [value]],?_,?_⟩
      · rw [physical_step algebra artifact (fuel+1) pending.root.implementation d (.control pending.actual.whenOne)
          [child] hd (by simp [physicalCode,hdBody])]
        simp [repeatedValue,sameInterface,polarity]
      · rw [logical_step algebra artifact (fuel+1) pending.root.meaning m (.control pending.logical.polarity)
          [logicalChild] hm (by simp [logicalCode,hmBody])]
        simp [poweredValue]

theorem eventually_all (entries : List Nat) (property : Nat → Nat → Prop)
    (eventually : ∀ index ∈ entries, ∃ bound, ∀ fuel, bound ≤ fuel → property index fuel) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ index ∈ entries, property index fuel := by
  induction entries with
  | nil => exact ⟨0,by simp⟩
  | cons index rest ih =>
    obtain ⟨first,hfirst⟩ := eventually index (by simp)
    obtain ⟨following,hrest⟩ := ih (fun child member => eventually child (by simp [member]))
    refine ⟨max first following,?_⟩
    intro fuel enough child member
    rcases List.mem_cons.mp member with equal | followingMember
    · subst child
      exact hfirst fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
    · exact hrest fuel (Nat.le_trans (Nat.le_max_right _ _) enough) child followingMember

/-- A finite derivation constructs a common successful denotation. There is
no assumed environment, quantum equation or caller-provided evaluation cache. -/
theorem derives_evaluate {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (index : Nat) (derived : Derivation.Derives artifact index) :
    ∀ proof, artifact.proofs[index]? = some proof → ∃ fuel value,
      physical algebra artifact fuel proof.implementation = some value ∧
      logical algebra artifact fuel proof.meaning = some value := by
  apply Derivation.Derives.induction_on_rules artifact
    (fun index => ∀ proof, artifact.proofs[index]? = some proof → ∃ fuel value,
      physical algebra artifact fuel proof.implementation = some value ∧
      logical algebra artifact fuel proof.meaning = some value) ?_ index derived
  intro atIndex root found matched ih proof hp
  have same : proof = root := Option.some.inj (hp.symm.trans found)
  subst proof
  have eventually : ∀ child ∈ root.premises.toList, ∃ bound, ∀ fuel, bound ≤ fuel →
      ∀ premise, artifact.proofs[child]? = some premise → ∃ value,
        physical algebra artifact fuel premise.implementation = some value ∧
        logical algebra artifact fuel premise.meaning = some value := by
    intro child member
    cases hp : artifact.proofs[child]? with
    | none => exact ⟨0,by simp⟩
    | some premise =>
      obtain ⟨fuel,value,he,hl⟩ := ih child member premise hp
      refine ⟨fuel,?_⟩
      intro more enough actual ha
      have same : actual = premise := Option.some.inj ha.symm
      subst actual
      exact ⟨value,evaluate_more algebra (definition artifact) fuel premise.implementation value he more enough,
        evaluate_more algebra (meaning artifact) fuel premise.meaning value hl more enough⟩
  obtain ⟨fuel,ready⟩ := eventually_all root.premises.toList
    (fun child fuel => ∀ premise, artifact.proofs[child]? = some premise → ∃ value,
      physical algebra artifact fuel premise.implementation = some value ∧
      logical algebra artifact fuel premise.meaning = some value) eventually
  obtain ⟨actual,ha,ordinary | ⟨exponent,provider,remaining,pending,inspected⟩⟩ := matched
  · have same : actual = root := Option.some.inj (ha.symm.trans found)
    subst actual
    obtain ⟨value,he,hl⟩ := ordinary_evaluate algebra artifact root fuel (ready fuel (Nat.le_refl _)) ordinary
    exact ⟨fuel+1,value,he,hl⟩
  · obtain ⟨actualRoot,singleton,providerFound,_,_,_,_,_,_⟩ :=
      Power.inspect_binding artifact atIndex exponent provider remaining pending inspected
    have same : root = pending.root := Option.some.inj (found.symm.trans actualRoot)
    obtain ⟨value,he,hl⟩ := ready fuel (Nat.le_refl _) pending.providerProofIndex
      (by simp [same,singleton]) pending.providerProof providerFound
    obtain ⟨result,hp,hm⟩ := power_evaluate algebra artifact atIndex exponent provider remaining fuel pending inspected value he hl
    exact ⟨fuel+2,result,by simpa only [same] using hp,by simpa only [same] using hm⟩

/-- Only successful evaluation defines a denotation. Failed or exhausted
evaluation never supplies a default semantic result. -/
def Denotes {S : Type} (algebra : Algebra S) (read : Nat → Option Node) (index : Nat) (value : S) : Prop :=
  ∃ fuel, evaluate algebra read fuel index = some value

theorem denotes_unique {S : Type} (algebra : Algebra S) (read : Nat → Option Node)
    (index : Nat) (first second : S) (hf : Denotes algebra read index first)
    (hs : Denotes algebra read index second) : first = second := by
  obtain ⟨fuel,ha⟩ := hf
  obtain ⟨more,hb⟩ := hs
  exact evaluate_unique algebra read fuel more index first second ha hb

theorem checkAll_denotes {S : Type} (algebra : Algebra S) (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked) :
    ∃ proof value, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation ∧
      Denotes algebra (definition artifact) artifact.entry.implementation value ∧
      Denotes algebra (meaning artifact) proof.meaning value := by
  have derived := (Derivation.checkAll_conditions artifact order checked accepted).2.2.2
  obtain ⟨proof,found,bound⟩ := HierarchicalSemantics.checkAll_entry artifact order checked accepted
  obtain ⟨fuel,value,hp,hm⟩ := derives_evaluate algebra artifact artifact.entry.proof derived proof found
  exact ⟨proof,value,found,bound,⟨fuel,by simpa only [bound] using hp⟩,⟨fuel,hm⟩⟩

/-- Accepted bodies have equal unique complex operators, with no `Interprets`
premise. This is equation soundness for the supported internal rules; unitarity
and the still unsupported full-profile rules are separate obligations. -/
theorem checkAll_operator (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked) :
    ∃ proof value, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation ∧
      Denotes HierarchicalOperators.algebra (definition artifact) artifact.entry.implementation value ∧
      Denotes HierarchicalOperators.algebra (meaning artifact) proof.meaning value :=
  checkAll_denotes HierarchicalOperators.algebra artifact order checked accepted

theorem checkAll_matrix (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (P M : HierarchicalOperators.Operator)
    (hp : Denotes HierarchicalOperators.algebra (definition artifact) artifact.entry.implementation P)
    (hm : Denotes HierarchicalOperators.algebra (meaning artifact) proof.meaning M)
    (inputWidth outputWidth : Nat) :
    HierarchicalOperators.matrixAt inputWidth outputWidth P =
      HierarchicalOperators.matrixAt inputWidth outputWidth M := by
  obtain ⟨actual,value,ha,_,he,hl⟩ := checkAll_operator artifact order checked accepted
  have same : actual = proof := Option.some.inj (ha.symm.trans found)
  subst actual
  have p := denotes_unique HierarchicalOperators.algebra (definition artifact) artifact.entry.implementation P value hp he
  have m := denotes_unique HierarchicalOperators.algebra (meaning artifact) proof.meaning M value hm hl
  rw [p,m]

theorem checkAll_reference {R : Type} [Fintype R] [DecidableEq R]
    (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (P M : HierarchicalOperators.Operator)
    (hp : Denotes HierarchicalOperators.algebra (definition artifact) artifact.entry.implementation P)
    (hm : Denotes HierarchicalOperators.algebra (meaning artifact) proof.meaning M)
    (inputWidth outputWidth : Nat)
    (rho : Matrix ((Fin inputWidth → Bool) × R) ((Fin inputWidth → Bool) × R) ℂ) :
    HierarchicalOperators.referenceMap (HierarchicalOperators.matrixAt inputWidth outputWidth P) rho =
      HierarchicalOperators.referenceMap (HierarchicalOperators.matrixAt inputWidth outputWidth M) rho := by
  rw [checkAll_matrix artifact order checked accepted proof found P M hp hm inputWidth outputWidth]

namespace Examples

private def target : Side := ⟨#[⟨0,#[.bit],#[7]⟩],#[]⟩
private def full : Side := ⟨#[⟨1,#[.bit],#[8]⟩,⟨0,#[.bit],#[7]⟩],#[]⟩

/-- The meaning table is independently permuted. The phase is π/8, beyond
the unchanged finite ζ8 coefficient domain. -/
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

theorem accepted_phase_power : (Derivation.powerEntry data order 1 0).isOk = true := by decide +kernel
theorem insufficient_depth : (physical HierarchicalOperators.algebra data 2 2).isSome = false := by rfl
theorem sufficient_depth : (physical HierarchicalOperators.algebra data 3 2).isSome = true := by rfl
theorem permuted_meaning : (logical HierarchicalOperators.algebra data 3 0).isSome = true := by rfl
theorem out_of_bounds : physical HierarchicalOperators.algebra data 8 3 = none := by rfl

private def malformedZero : Artifact :=
  {data with definitions := #[⟨⟨target,target⟩,.unitary,.repeatOp 0 99⟩]}
theorem zero_requires_body : physical HierarchicalOperators.algebra malformedZero 8 0 = none := by rfl

private def cyclicZero : Artifact :=
  {data with definitions := #[⟨⟨target,target⟩,.unitary,.repeatOp 0 0⟩]}
theorem zero_cycle_fails : physical HierarchicalOperators.algebra cyclicZero 8 0 = none := by rfl

private def opaqueData : Artifact :=
  {data with definitions := #[⟨⟨target,target⟩,.unitary,.leaf ⟨#[0]⟩⟩]}
theorem unsupported_leaf_fails : physical HierarchicalOperators.algebra opaqueData 8 0 = none := by rfl

theorem constructed_phase_power : ∃ proof value,
    data.proofs[data.entry.proof]? = some proof ∧ proof.implementation = data.entry.implementation ∧
    Denotes HierarchicalOperators.algebra (definition data) data.entry.implementation value ∧
    Denotes HierarchicalOperators.algebra (meaning data) proof.meaning value := by
  have accepted : (Derivation.checkAll data order).isOk = true := by decide +kernel
  cases hc : Derivation.checkAll data order with
  | error failure => rw [hc] at accepted; change false = true at accepted; contradiction
  | ok checked => exact checkAll_operator data order checked hc

end Examples

end Qleisli.HierarchicalEvaluation
