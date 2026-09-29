import QleisliKernel.Hierarchical.Derivation
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Interpretation of actual whole-space equation derivations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Environments obey actual body equations, not proposed proof conclusions.
Concrete complex interpretation is separate from the executable checker. -/

namespace Qleisli.HierarchicalSemantics
open QleisliKernel.Hierarchical
open Artifact

deriving instance ReflBEq, LawfulBEq for QleisliKernel.Layout.TypeAtom
deriving instance ReflBEq, LawfulBEq for QuantumPort
deriving instance ReflBEq, LawfulBEq for ClassicalPort
deriving instance ReflBEq, LawfulBEq for Side
deriving instance ReflBEq, LawfulBEq for Interface

inductive Tag where
  | identity
  | rewire (axes : List Nat)
  | phase (owner j k : Nat)
  | sequence | tensor | inverse
  | control (polarity : Bool)
  | power (count : Nat)
  deriving DecidableEq

structure Algebra (S : Type) where
  apply : Interface → Tag → List S → S
  identity_rewire : ∀ interface map, Rule.identityMap interface map = true →
    apply interface (.rewire map.axes.toList) [] = apply interface .identity []

def physicalCode (definition : Artifact.Definition) : Option (Tag × List Nat) :=
  match definition.body with
  | .rewire map => some (.rewire map.axes.toList,[])
  | .structural _ => some (.rewire (Structural.axisMap definition.interface),[])
  | .dyadicPhase owner j k => some (.phase owner j k,[])
  | .sequence children => some (.sequence,children.toList)
  | .tensor first second => some (.tensor,[first,second])
  | .inverse child => some (.inverse,[child])
  | .control child polarity => some (.control polarity,[child])
  | .repeatOp count child => some (.power count,[child])
  | _ => none

def logicalCode (meaning : Meaning) : Option (Tag × List Nat) :=
  match meaning.body with
  | .identity => some (.identity,[])
  | .rewire map => some (.rewire map.axes.toList,[])
  | .structural _ => some (.rewire (Structural.axisMap meaning.interface),[])
  | .phase j k => do
    let target ← meaning.interface.inputs.quantum[0]?
    return (.phase target.owner j k,[])
  | .sequence children => some (.sequence,children.toList)
  | .tensor first second => some (.tensor,[first,second])
  | .inverse child => some (.inverse,[child])
  | .control child polarity => some (.control polarity,[child])
  | .power child count => some (.power count,[child])
  | _ => none

def physical {S : Type} (algebra : Algebra S) (environment : Nat → S)
    (definition : Artifact.Definition) : Option S := do
  let (tag,children) ← physicalCode definition
  return algebra.apply definition.interface tag (children.map environment)

def logical {S : Type} (algebra : Algebra S) (environment : Nat → S)
    (meaning : Meaning) : Option S := do
  let (tag,children) ← logicalCode meaning
  return algebra.apply meaning.interface tag (children.map environment)

/-- temporary (TP-001): intermediate assumed-environment interface. Retire
with its wrappers after callers use constructed denotations and public-API
migration has been reviewed. Every table node has its actual body interpretation. No proof table or
producer-supplied equality occurs in these equations. Unsupported bodies cannot
be given an interpretation in this slice. -/
structure Interprets {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (operations meanings : Nat → S) : Prop where
  definitions : ∀ index definition, artifact.definitions[index]? = some definition →
    physical algebra operations definition = some (operations index)
  meanings : ∀ index meaning, artifact.meanings[index]? = some meaning →
    logical algebra meanings meaning = some (meanings index)

theorem identity_interfaces (artifact : Artifact) (proof : Proof)
    (definition : Artifact.Definition) (meaning : Meaning)
    (hd : artifact.definitions[proof.implementation]? = some definition)
    (hm : artifact.meanings[proof.meaning]? = some meaning)
    (accepted : Power.identityEquation artifact proof = true) :
    definition.interface = meaning.interface := by
  cases hi : artifact.encodings[proof.inputEncoding]? with
  | none => simp [Power.identityEquation,hi] at accepted
  | some input =>
    cases ho : artifact.encodings[proof.outputEncoding]? with
    | none => simp [Power.identityEquation,hi,ho] at accepted
    | some output =>
      cases hbi : input.body <;> cases hbo : output.body <;>
        simp [Power.identityEquation,hi,ho,hbi,hbo] at accepted
      have endpoints : Artifact.endpoints artifact proof = true := by tauto
      have bound := Artifact.endpoints_bound artifact proof definition meaning input output hd hm hi ho endpoints
      rcases bound with ⟨il,ip,ol,op⟩
      have inputs : definition.interface.inputs = meaning.interface.inputs := by
        simp_all
      have outputs : definition.interface.outputs = meaning.interface.outputs := by
        simp_all
      cases hdif : definition.interface
      cases hmif : meaning.interface
      simp_all

theorem mapM_members {A B : Type} (xs : List A) (ys : List B) (f : A → Option B)
    (accepted : xs.mapM f = some ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    have same : ys = [] := by simpa using accepted
    simp [same]
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [hx] at accepted
    | some y =>
      cases hs : xs.mapM f with
      | none => simp [hx,hs] at accepted
      | some rest =>
        have same : y :: rest = ys := by simpa [hx,hs] using accepted
        subst ys
        intro value member
        rcases List.mem_cons.mp member with equal | following
        · subst value; exact ⟨x,by simp,hx⟩
        · obtain ⟨a,inside,found⟩ := ih rest hs value following
          exact ⟨a,by simp [inside],found⟩

theorem premises_members (artifact : Artifact) (proof : Proof) (ps : Array Proof)
    (accepted : Rule.premises artifact proof = some ps) :
    ∀ premise ∈ ps.toList, ∃ index ∈ proof.premises.toList, artifact.proofs[index]? = some premise := by
  have mapped : proof.premises.toList.mapM (fun index => artifact.proofs[index]?) = some ps.toList := by
    have mapped := congrArg (fun result => Array.toList <$> result) accepted
    change Array.toList <$> proof.premises.mapM (fun index => artifact.proofs[index]?) =
      some ps.toList at mapped
    simpa only [Array.toList_mapM] using mapped
  exact mapM_members _ _ _ mapped

theorem children_images {S : Type} (ps : Array Proof) (p m : Array Nat)
    (operations meanings : Nat → S)
    (accepted : Rule.children ps p m = true)
    (equations : ∀ premise ∈ ps.toList, operations premise.implementation = meanings premise.meaning) :
    p.toList.map operations = m.toList.map meanings := by
  simp only [Rule.children,Bool.and_eq_true,beq_iff_eq] at accepted
  rw [accepted.1,accepted.2]
  simp only [Array.toList_map,List.map_map,Function.comp_def]
  apply List.map_congr_left
  exact equations

theorem singleton_of_get {A : Type} (entries : Array A) (value : A)
    (size : entries.size = 1) (found : entries[0]? = some value) : entries = #[value] := by
  apply Array.ext
  · simpa using size
  · intro i hi hj
    have zero : i = 0 := by omega
    subst i
    exact (Array.getElem?_eq_some_iff.mp found).2

theorem phase_target (artifact : Artifact) (definition : Artifact.Definition) (meaning : Meaning)
    (target j k l h : Nat)
    (hd : definition.body = .dyadicPhase target j k) (hm : meaning.body = .phase l h)
    (typed : NodeTyping.conditions artifact definition = true)
    (meaningTyped : ContractTyping.meaningConditions artifact meaning = true)
    (interface : definition.interface = meaning.interface) :
    ∃ port, meaning.interface.inputs.quantum[0]? = some port ∧ port.owner = target := by
  have one : ContractTyping.onePort meaning.interface.inputs #[.bit] = true := by
    simp only [ContractTyping.meaningConditions,hm,Bool.and_eq_true] at meaningTyped
    tauto
  cases hp : meaning.interface.inputs.quantum[0]? with
  | none => simp [ContractTyping.onePort,hp] at one
  | some port =>
    have size : meaning.interface.inputs.quantum.size = 1 := by
      simp [ContractTyping.onePort,hp] at one
      tauto
    have singleton := singleton_of_get _ port size hp
    have owner : port.owner = target := by
      simp [NodeTyping.conditions,hd,NodeTyping.phase,interface,singleton] at typed
      tauto
    exact ⟨port,rfl,owner⟩

theorem bodies_sound {S : Type} (algebra : Algebra S) (artifact : Artifact) (proof : Proof)
    (definition : Artifact.Definition) (meaning : Meaning) (ps : Array Proof)
    (operations meanings : Nat → S)
    (interface : definition.interface = meaning.interface)
    (typed : NodeTyping.conditions artifact definition = true)
    (meaningTyped : ContractTyping.meaningConditions artifact meaning = true)
    (equations : ∀ premise ∈ ps.toList, operations premise.implementation = meanings premise.meaning)
    (matched : Rule.bodies proof definition meaning ps = true) :
    physical algebra operations definition = logical algebra meanings meaning := by
  unfold Rule.bodies at matched
  split at matched
  next p m _ hd hm =>
    have axes : p.axes = m.axes := by
      simp only [Rule.sameMap,Bool.and_eq_true,beq_iff_eq] at matched
      tauto
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,axes]
  next p _ hd hm =>
    have identity : Rule.identityMap definition.interface p = true := by
      simp only [Bool.and_eq_true] at matched
      exact matched.2
    have same := algebra.identity_rewire definition.interface p identity
    simp only [interface] at same
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,same]
  next p m _ hd hm =>
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface]
  next target j k l h _ hd hm =>
    have angles : j = l ∧ k = h := by
      simp only [Bool.and_eq_true,beq_iff_eq] at matched
      tauto
    obtain ⟨port,hp,owner⟩ := phase_target artifact definition meaning target j k l h hd hm typed meaningTyped interface
    simp [physical,logical,physicalCode,logicalCode,hd,hm,hp,owner,interface,angles.1,angles.2]
  next p m _ hd hm =>
    have same := children_images ps p m operations meanings matched equations
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,same]
  next p q m n _ hd hm =>
    have same := children_images ps #[p,q] #[m,n] operations meanings matched equations
    change [p,q].map operations = [m,n].map meanings at same
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,same]
  next p m _ hd hm =>
    have same := children_images ps #[p] #[m] operations meanings matched equations
    change [p].map operations = [m].map meanings at same
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,same]
  next p b m c _ hd hm =>
    simp only [Bool.and_eq_true,beq_iff_eq] at matched
    have same := children_images ps #[p] #[m] operations meanings matched.2 equations
    change [p].map operations = [m].map meanings at same
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,same,matched.1]
  next n p m k _ hd hm =>
    simp only [Bool.and_eq_true,beq_iff_eq] at matched
    have same := children_images ps #[p] #[m] operations meanings matched.2 equations
    change [p].map operations = [m].map meanings at same
    simp [physical,logical,physicalCode,logicalCode,hd,hm,interface,same,matched.1]
  next => contradiction

/-- temporary (TP-001): assumed-environment wrapper; use `HierarchicalEvaluation.ordinary_evaluate`.
Retire after dependent wrappers migrate and public-API compatibility review. -/
theorem ordinary_sound {S : Type} (algebra : Algebra S) (artifact : Artifact) (proof : Proof)
    (operations meanings : Nat → S) (environment : Interprets algebra artifact operations meanings)
    (premiseEquations : ∀ index ∈ proof.premises.toList, ∀ premise,
      artifact.proofs[index]? = some premise → operations premise.implementation = meanings premise.meaning)
    (accepted : Rule.ordinary artifact proof = true) :
    operations proof.implementation = meanings proof.meaning := by
  cases hd : artifact.definitions[proof.implementation]? with
  | none => simp [Rule.ordinary,hd] at accepted
  | some definition =>
    cases hm : artifact.meanings[proof.meaning]? with
    | none => simp [Rule.ordinary,hd,hm] at accepted
    | some meaning =>
      cases hp : Rule.premises artifact proof with
      | none => simp [Rule.ordinary,hd,hm,hp] at accepted
      | some ps =>
        simp [Rule.ordinary,hd,hm,hp] at accepted
        have identity : Power.identityEquation artifact proof = true := by tauto
        have typed : NodeTyping.conditions artifact definition = true := by tauto
        have meaningTyped : ContractTyping.meaningConditions artifact meaning = true := by tauto
        have matched : Rule.bodies proof definition meaning ps = true := by tauto
        have equations : ∀ premise ∈ ps.toList,
            operations premise.implementation = meanings premise.meaning := by
          intro premise member
          obtain ⟨index,inside,found⟩ := premises_members artifact proof ps hp premise member
          exact premiseEquations index inside premise found
        have same := bodies_sound algebra artifact proof definition meaning ps operations meanings
          (identity_interfaces artifact proof definition meaning hd hm identity) typed meaningTyped equations matched
        rw [environment.definitions _ _ hd,environment.meanings _ _ hm] at same
        exact Option.some.inj same

theorem implementation_stage_data (artifact : Artifact) (index : Nat)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (accepted : Power.implementationStage artifact index = some stage) :
    ∃ root child repeated,
      artifact.definitions[index]? = some root ∧ root.body = .control child stage.whenOne ∧
      artifact.definitions[child]? = some repeated ∧
      repeated.body = .repeatOp stage.count stage.targetDefinition := by
  cases hd : artifact.definitions[index]? with
  | none => simp [Power.implementationStage,hd] at accepted
  | some root =>
    cases hb : root.body <;> simp [Power.implementationStage,hd,hb] at accepted
    rename_i child polarity
    cases hc : artifact.definitions[child]? with
    | none => simp [hc] at accepted
    | some repeated =>
      cases hr : repeated.body <;> simp [hc,hr] at accepted
      rename_i count provider
      subst stage
      exact ⟨root,child,repeated,rfl,hb,hc,hr⟩

theorem meaning_stage_data (artifact : Artifact) (index : Nat) (stage : Power.LogicalStage)
    (accepted : Power.meaningStage artifact index = some stage) :
    ∃ root child powered,
      artifact.meanings[index]? = some root ∧ root.body = .control child stage.polarity ∧
      artifact.meanings[child]? = some powered ∧
      powered.body = .power stage.provider stage.count := by
  cases hm : artifact.meanings[index]? with
  | none => simp [Power.meaningStage,hm] at accepted
  | some root =>
    cases hb : root.body <;> simp [Power.meaningStage,hm,hb] at accepted
    rename_i child polarity
    cases hc : artifact.meanings[child]? with
    | none => simp [hc] at accepted
    | some powered =>
      cases hp : powered.body <;> simp [hc,hp] at accepted
      rename_i provider count
      subst stage
      exact ⟨root,child,powered,rfl,hb,hc,hp⟩

/-- temporary (TP-001): assumed-environment wrapper; use `HierarchicalEvaluation.power_evaluate`.
Retire after dependent wrappers migrate and public-API compatibility review. -/
theorem power_sound {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (index exponent provider remaining : Nat) (pending : Power.Pending)
    (accepted : Power.inspect artifact index exponent provider remaining = .ok pending)
    (operations meanings : Nat → S) (environment : Interprets algebra artifact operations meanings)
    (providerEquation : operations pending.providerProof.implementation = meanings pending.providerProof.meaning) :
    operations pending.root.implementation = meanings pending.root.meaning := by
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
      have equation : operations pending.actual.targetDefinition = meanings pending.logical.provider := by
        simpa only [implementation,meaning] using providerEquation
      have repeats : physical algebra operations repeated = logical algebra meanings powered := by
        simp [physical,logical,physicalCode,logicalCode,hrBody,hpBody,ri,pi,ui,equation,count]
      rw [environment.definitions _ _ hchild,environment.meanings _ _ hmChild] at repeats
      have repeatEquation := Option.some.inj repeats
      have roots : physical algebra operations d = logical algebra meanings m := by
        simp [physical,logical,physicalCode,logicalCode,hdBody,hmBody,sameInterface,repeatEquation,polarity]
      rw [environment.definitions _ _ hd,environment.meanings _ _ hm] at roots
      exact Option.some.inj roots

/-- temporary (TP-001): assumed-environment wrapper; use `HierarchicalEvaluation.derives_evaluate`.
Retire after dependent wrappers migrate and public-API compatibility review. -/
theorem derives_sound {S : Type} (algebra : Algebra S) (artifact : Artifact)
    (operations meanings : Nat → S) (environment : Interprets algebra artifact operations meanings)
    (index : Nat) (derived : Derivation.Derives artifact index) :
    ∀ proof, artifact.proofs[index]? = some proof →
      operations proof.implementation = meanings proof.meaning := by
  apply Derivation.Derives.induction_on_rules artifact
    (fun index => ∀ proof, artifact.proofs[index]? = some proof →
      operations proof.implementation = meanings proof.meaning) ?_ index derived
  intro atIndex root found matched premises proof hp
  have same : root = proof := Option.some.inj (found.symm.trans hp)
  subst proof
  obtain ⟨actual,ha,ordinary | ⟨exponent,provider,remaining,pending,checked⟩⟩ := matched
  · have same : actual = root := Option.some.inj (ha.symm.trans found)
    subst actual
    exact ordinary_sound algebra artifact root operations meanings environment premises ordinary
  · obtain ⟨actualRoot,singleton,hp,_,_,_,_,_,_⟩ :=
      Power.inspect_binding artifact atIndex exponent provider remaining pending checked
    have same : root = pending.root := Option.some.inj (found.symm.trans actualRoot)
    have equation := premises pending.providerProofIndex (by simp [same,singleton]) pending.providerProof hp
    simpa only [same] using power_sound algebra artifact atIndex exponent provider remaining pending
      checked operations meanings environment equation

/-- temporary (TP-001): replaced for supported rules by
`HierarchicalEvaluation.checkAll_denotes`; retire after wrapper callers migrate
and public-API compatibility review. Acceptance starts with the actual empty derivation cache. The only semantic
premise is interpretation of actual bodies, never the proposed proof equations. -/
theorem checkAll_sound {S : Type} (algebra : Algebra S) (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (operations meanings : Nat → S) (environment : Interprets algebra artifact operations meanings)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof) :
    operations proof.implementation = meanings proof.meaning := by
  have derivation := (Derivation.checkAll_conditions artifact order checked accepted).2.2.2
  exact derives_sound algebra artifact operations meanings environment artifact.entry.proof derivation proof found

theorem finish_entry (artifact : Artifact) (projected : Projection) (order : Array Nat)
    (prepared : Prepared) (accepted : Artifact.finish artifact projected order = .ok prepared) :
    ∃ proof, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation := by
  unfold Artifact.finish at accepted
  cases hd : Artifact.index artifact ⟨.definition,artifact.entry.implementation⟩ with
  | none => simp [hd] at accepted
  | some definition =>
    simp only [hd] at accepted
    cases hi : Artifact.index artifact ⟨.proof,artifact.entry.proof⟩ with
    | none => simp [hi] at accepted
    | some proofIndex =>
      simp only [hi] at accepted
      cases hp : artifact.proofs[artifact.entry.proof]? with
      | none => simp [hp] at accepted
      | some proof =>
        simp only [hp] at accepted
        split at accepted
        next wrong => contradiction
        next bound => exact ⟨proof,rfl,by simpa using bound⟩

theorem checkAll_entry (artifact : Artifact) (order : Array Nat) (checked : Derivation.Checked)
    (accepted : Derivation.checkAll artifact order = .ok checked) :
    ∃ proof, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation := by
  have ht := (Derivation.checkAll_conditions artifact order checked accepted).1
  have hn := (ContractTyping.checkAll_conditions artifact order checked.typed ht).1
  have hp := (NodeTyping.checkAll_conditions artifact order checked.typed.nodes hn).1
  unfold Artifact.prepare at hp
  cases projected : Artifact.project artifact with
  | error failure => simp [projected] at hp
  | ok projection =>
    exact finish_entry artifact projection order checked.typed.nodes.prepared (by simpa only [projected] using hp)

/-- temporary (TP-001): assumed-environment entry wrapper, superseded by
`HierarchicalEvaluation.checkAll_denotes`; retire with the other TP-001 wrappers
after public-API compatibility review. Binds the equation to the artifact's actual entry implementation. The
independently requested external contract is an additional, separate boundary. -/
theorem checkAll_entry_sound {S : Type} (algebra : Algebra S) (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (operations meanings : Nat → S) (environment : Interprets algebra artifact operations meanings) :
    ∃ proof, artifact.proofs[artifact.entry.proof]? = some proof ∧
      proof.implementation = artifact.entry.implementation ∧
      operations artifact.entry.implementation = meanings proof.meaning := by
  obtain ⟨proof,found,bound⟩ := checkAll_entry artifact order checked accepted
  exact ⟨proof,found,bound,by simpa only [bound] using
    (checkAll_sound algebra artifact order checked accepted operations meanings environment proof found)⟩

end Qleisli.HierarchicalSemantics
