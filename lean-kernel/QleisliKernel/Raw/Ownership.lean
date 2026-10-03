import QleisliKernel.Raw.Trace
import QleisliKernel.Semantics.Ownership

/-! Structural checking refines independent linear ownership rules.
Only original raw data occurs in the conclusion; no checker decision is a
premise of the reference judgments.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Ownership
open Semantics.Raw Semantics.Finite Finite

def view (state : Raw.State) : Semantics.Ownership.State :=
  ⟨state.live,state.seenTokens,state.seenWires,state.frame⟩

private theorem dedup_facts {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup ∧ xs.eraseDups.Sublist xs := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons]
    have smaller := dedup_facts (xs.filter (fun b => !b == a))
    refine ⟨List.nodup_cons.mpr ⟨?_,smaller.1⟩,List.Sublist.cons_cons a
      (smaller.2.trans (List.filter_sublist))⟩
    intro member
    have filtered := List.mem_eraseDups.mp member
    simp at filtered
termination_by xs.length
 decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem unique_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α)
    (ok : Raw.unique xs = true) : xs.Nodup := by
  have length : xs.eraseDups.length = xs.length := beq_iff_eq.mp ok
  have facts := dedup_facts xs
  exact (facts.2.eq_of_length length) ▸ facts.1

theorem valid (state : Raw.State) (ok : Raw.stateValid state = true) : Semantics.Ownership.Valid (view state) := by
  simp only [Raw.stateValid,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem,beq_iff_eq] at ok
  rcases ok with ⟨⟨⟨⟨⟨⟨⟨⟨owners,tokens⟩,wires⟩,frame⟩,exclusive⟩,ports⟩,issued⟩,count⟩,covered⟩
  exact ⟨unique_nodup _ owners,unique_nodup _ tokens,unique_nodup _ wires,
    unique_nodup _ frame,unique_nodup _ exclusive,
    fun port member => ⟨(ports port member).1.1,(ports port member).2⟩,issued,count,covered⟩

theorem reserve_state (state result : Raw.State) (wires : List Nat)
    (ok : Raw.reserve state wires = .ok result) :
    result = {state with seenWires := state.seenWires ++ wires} := by
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ ok
  exact (Except.ok.inj h).symm

theorem insert_state (state result : Raw.State) (token : Nat) (wires : List Nat)
    (ok : Raw.insert state token wires = .ok result) :
    result = {state with live := state.live ++ [⟨token,wires,wires.length⟩], seenTokens := state.seenTokens ++ [token]} := by
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ ok
  exact (Except.ok.inj h).symm

theorem take_state (state next : Raw.State) (token : Nat) (port : Port)
    (ok : Raw.take state token = .ok (port,next)) :
    state.live.find? (fun p => p.token == token) = some port ∧
    next = {state with live := state.live.filter (fun p => p.token != token)} := by
  obtain ⟨found,hf,h⟩ := except_bind_success _ _ _ ok
  have present : state.live.find? (fun p => p.token == token) = some found := by
    cases original : state.live.find? (fun p => p.token == token) <;> simp_all [readOption]
  have same := Except.ok.inj h
  cases same
  exact ⟨present,rfl⟩

theorem input (state result : Raw.State) (port : Port)
    (ok : Raw.input state port = .ok result) : Semantics.Ownership.Input (view state) port (view result) := by
  obtain ⟨_,hg,h⟩ := except_bind_success _ _ _ ok
  obtain ⟨reserved,hr,h⟩ := except_bind_success _ _ _ h
  obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
  have shape := Raw.require_success _ hg
  simp only [Bool.and_eq_true,beq_iff_eq] at shape
  have freshOwner := (Raw.insert_fresh _ _ _ _ hi).1
  obtain ⟨_,hw,_⟩ := except_bind_success _ _ _ hr
  have freshWires := Raw.require_success _ hw
  simp only [Bool.and_eq_true,List.all_eq_true] at freshWires
  have reservedState := reserve_state _ _ _ hr
  have insertedState := insert_state _ _ _ _ hi
  have same := Except.ok.inj h
  subst result
  refine ⟨shape.1,?_,?_,unique_nodup _ freshWires.1,?_⟩
  · simpa only [reservedState,view] using freshOwner
  · intro wire member
    simpa [view] using (freshWires.2 wire member).2
  · rw [insertedState,reservedState]
    have portShape : Port.mk port.token port.wires port.wires.length = port := by
      cases port
      simp_all
    simp only [view,portShape]

theorem inputs (ports : List Port) (state result : Raw.State)
    (ok : ports.foldlM Raw.input state = .ok result) : Semantics.Ownership.Inputs (view state) ports (view result) := by
  induction ports generalizing state with
  | nil =>
    have same := Except.ok.inj ok
    subst result
    exact .nil _
  | cons port ports ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,rest⟩ := except_bind_success _ _ _ ok
    exact .cons _ _ _ _ _ (input _ _ _ hn) (ih next rest)

private theorem takeTargets_histories (targets : List Target) (ports out : List Port)
    (state result : Raw.State)
    (ok : targets.foldlM (fun (ports,next) target => do
      let (port,next) ← Raw.take next target.input
      Raw.require (port.bits == 1)
      pure (ports ++ [port],next)) (ports,state) = .ok (out,result)) :
    out.length = ports.length + targets.length ∧
    result.seenTokens = state.seenTokens ∧ result.seenWires = state.seenWires := by
  induction targets generalizing ports state with
  | nil =>
    have same := Except.ok.inj ok
    cases same
    simp
  | cons target targets ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,rest⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨port,after⟩,ht,h⟩ := except_bind_success _ _ _ hn
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    have same := Except.ok.inj h
    subst next
    have taken := (take_state _ _ _ _ ht).2
    have tail := ih (ports ++ [port]) after rest
    simp_all [Nat.add_comm,Nat.add_left_comm]

private theorem putTargets_histories (targets : List (Target × Port)) (state result : Raw.State)
    (ok : targets.foldlM (fun next (target,port) => Raw.insert next target.output port.wires) state = .ok result) :
    result.seenTokens = state.seenTokens ++ targets.map (fun pair => pair.1.output) ∧
    result.seenWires = state.seenWires := by
  induction targets generalizing state with
  | nil =>
    have same := Except.ok.inj ok
    subst result
    simp
  | cons pair targets ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hi,rest⟩ := except_bind_success _ _ _ ok
    have inserted := insert_state _ _ _ _ hi
    have tail := ih next rest
    simp_all [List.append_assoc]

/-- Actual dispatch issues exactly the identities declared by its original op.
This connects the independent freshness rule to every pure constructor. -/
theorem dispatch_histories (dependencies : List Basis) (state : Raw.State) (op : Op) (result : Raw.Transition)
    (ok : Raw.dispatch dependencies state op = .ok result) :
    result.state.seenTokens = state.seenTokens ++ Semantics.Ownership.outputs op ∧
    result.state.seenWires = state.seenWires ++ Semantics.Ownership.allocated (view state) op := by
  cases op with
  | init0 output wire =>
    obtain ⟨reserved,hr,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have hrState := reserve_state _ _ _ hr
    have hiState := insert_state _ _ _ _ hi
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated]
  | gate value input output =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have htState := take_state _ _ _ _ ht
    have hiState := insert_state _ _ _ _ hi
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated]
  | cnot control target controlOut targetOut =>
    obtain ⟨⟨c,next⟩,hc,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨t,next'⟩,ht,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outC,hiC,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outT,hiT,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have hcState := take_state _ _ _ _ hc
    have htState := take_state _ _ _ _ ht
    have hiCState := insert_state _ _ _ _ hiC
    have hiTState := insert_state _ _ _ _ hiT
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated,List.append_assoc]
  | toffoli a b target aOut bOut targetOut =>
    obtain ⟨⟨a,next⟩,ha,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨b,next'⟩,hb,h⟩ := except_bind_success _ _ _ h
    obtain ⟨⟨t,next''⟩,ht,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outA,hiA,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outB,hiB,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outT,hiT,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have haState := take_state _ _ _ _ ha
    have hbState := take_state _ _ _ _ hb
    have htState := take_state _ _ _ _ ht
    have hiAState := insert_state _ _ _ _ hiA
    have hiBState := insert_state _ _ _ _ hiB
    have hiTState := insert_state _ _ _ _ hiT
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated,List.append_assoc]
  | quantumIf control target controlOut targetOut zero oneSteps =>
    obtain ⟨⟨c,next⟩,hc,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨t,next'⟩,ht,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outC,hiC,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outT,hiT,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have hcState := take_state _ _ _ _ hc
    have htState := take_state _ _ _ _ ht
    have hiCState := insert_state _ _ _ _ hiC
    have hiTState := insert_state _ _ _ _ hiT
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated,List.append_assoc]
  | split input left right leftBits =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outL,hiL,h⟩ := except_bind_success _ _ _ h
    obtain ⟨outR,hiR,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have htState := take_state _ _ _ _ ht
    have hiLState := insert_state _ _ _ _ hiL
    have hiRState := insert_state _ _ _ _ hiR
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated,List.append_assoc]
  | join left right output =>
    obtain ⟨⟨l,next⟩,hl,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨r,next'⟩,hr,h⟩ := except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have hlState := take_state _ _ _ _ hl
    have hrState := take_state _ _ _ _ hr
    have hiState := insert_state _ _ _ _ hi
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated]
  | liftBasis input output wires table =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨reserved,hr,h⟩ := except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have htState := take_state _ _ _ _ ht
    have hrState := reserve_state _ _ _ hr
    have hiState := insert_state _ _ _ _ hi
    simp_all [view,Semantics.Ownership.outputs,Semantics.Ownership.allocated]
  | applyUnitary input output steps =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have htState := take_state _ _ _ _ ht
    have hiState := insert_state _ _ _ _ hi
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated]
  | certifiedCompute input output ancilla function useSteps logicalSteps =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,hg,h⟩ := except_bind_success _ _ _ h
    obtain ⟨reserved,hr,h⟩ := except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have htState := take_state _ _ _ _ ht
    have hrState := reserve_state _ _ _ hr
    have hiState := insert_state _ _ _ _ hi
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated]
  | computeUseUncompute input output targets ancilla function uses =>
    obtain ⟨⟨source,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨ports,next'⟩,hp,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := except_bind_success _ _ _ h
    obtain ⟨reserved,hr,h⟩ := except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := except_bind_success _ _ _ h
    obtain ⟨final,hf,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have htState := take_state _ _ _ _ ht
    have hrState := reserve_state _ _ _ hr
    have hiState := insert_state _ _ _ _ hi
    have targetStates := takeTargets_histories _ _ _ _ _ hp
    have finalState := putTargets_histories _ _ _ hf
    have length : targets.length ≤ ports.length := by simpa using Nat.le_of_eq targetStates.1.symm
    have targetsBound := List.map_fst_zip length
    have targetsOutput : (targets.zip ports).map (fun pair => pair.1.output) = targets.map (·.output) := by
      simpa only [List.map_map] using congrArg (List.map (fun t : Target => t.output)) targetsBound
    simp_all [Semantics.Ownership.outputs,Semantics.Ownership.allocated,List.append_assoc]

private theorem take_access (state next : Raw.State) (token : Nat) (port : Port)
    (ok : Raw.take state token = .ok (port,next)) :
    Semantics.Ownership.PortAt (view state) token port ∧ next.live ⊆ state.live := by
  have taken := take_state _ _ _ _ ok
  refine ⟨⟨List.mem_of_find?_eq_some taken.1,
    beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == token) taken.1)⟩,?_⟩
  rw [taken.2]
  exact fun _ h => (List.mem_filter.mp h).1

private theorem portAt_mono (before after : Raw.State) (token : Nat) (port : Port)
    (subset : after.live ⊆ before.live) (found : Semantics.Ownership.PortAt (view after) token port) :
    Semantics.Ownership.PortAt (view before) token port := ⟨subset found.1,found.2⟩

private theorem circuit_access (dependencies : List Basis) (bits : Nat) (steps : List Semantics.Finite.Step)
    (ok : Raw.circuitStepsValid dependencies bits steps = true) : Semantics.Ownership.Circuit bits steps := by
  intro step member
  have axes := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp ok) step member)).1
  simp only [Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at axes
  have targets : Finite.targets step.action = Semantics.Ownership.actionAxes step.action := by
    cases step.action <;> rfl
  rw [targets] at axes
  exact ⟨unique_nodup _ axes.2,axes.1.2⟩

private theorem controls_access (source scratch : Nat) (controls : List ProtectedControl)
    (ok : Raw.protectedControlsValid source scratch controls = true) :
    Semantics.Ownership.Controls source scratch controls := by
  have good := Bool.and_eq_true_iff.mp ok
  refine ⟨unique_nodup _ good.2,?_⟩
  intro control member
  simpa only [Raw.protectedValid,Semantics.Ownership.Protected,decide_eq_true_eq] using ((List.all_eq_true.mp good.1) control member)

private theorem uses_access (source scratch targets : Nat) (uses : List Use)
    (ok : Raw.usesValid source scratch targets uses = true) : Semantics.Ownership.Uses source scratch targets uses := by
  intro use member
  have good := (List.all_eq_true.mp ok) use member
  cases use with
  | protectedGate bit gate =>
    simpa only [Raw.protectedValid,Semantics.Ownership.Protected,decide_eq_true_eq] using (Bool.and_eq_true_iff.mp good).1
  | targetGate controls target gate =>
    exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp good).1,controls_access _ _ _ (Bool.and_eq_true_iff.mp good).2⟩
  | phase controls phase => exact controls_access _ _ _ good

private theorem targets_access (targets : List Target) (ports out : List Port) (state result : Raw.State)
    (ok : targets.foldlM (fun (ports,next) target => do
      let (port,next) ← Raw.take next target.input
      Raw.require (port.bits == 1)
      pure (ports ++ [port],next)) (ports,state) = .ok (out,result)) :
    ∀ target ∈ targets, Semantics.Ownership.BitOwner (view state) target.input := by
  induction targets generalizing ports state with
  | nil => simp
  | cons target targets ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,rest⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨port,after⟩,ht,h⟩ := except_bind_success _ _ _ hn
    obtain ⟨_,hg,h⟩ := except_bind_success _ _ _ h
    have same := Except.ok.inj h
    subst next
    have taken := take_access _ _ _ _ ht
    intro item member
    rcases List.mem_cons.mp member with same | member
    · subst item
      exact ⟨port,taken.1,beq_iff_eq.mp (Raw.require_success _ hg)⟩
    · obtain ⟨p,present,bit⟩ := ih (ports ++ [port]) after rest item member
      exact ⟨p,portAt_mono _ _ _ _ taken.2 present,bit⟩

/-- Successful dispatch confines all original local coordinates to the owners
it consumes, including protected source/target/scratch regions. -/
theorem dispatch_access (dependencies : List Basis) (state : Raw.State) (op : Op) (result : Raw.Transition)
    (ok : Raw.dispatch dependencies state op = .ok result) : Semantics.Ownership.Access (view state) op := by
  cases op with
  | init0 output wire | join left right output => trivial
  | gate gate input output =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    exact ⟨port,(take_access _ _ _ _ ht).1,beq_iff_eq.mp (Raw.require_success _ hg)⟩
  | cnot control target controlOut targetOut =>
    obtain ⟨⟨c,next⟩,hc,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨t,next'⟩,ht,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hbc,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hbt,_⟩ := except_bind_success _ _ _ h
    have first := take_access _ _ _ _ hc
    exact ⟨⟨c,first.1,beq_iff_eq.mp (Raw.require_success _ hbc)⟩,
      t,portAt_mono _ _ _ _ first.2 (take_access _ _ _ _ ht).1,beq_iff_eq.mp (Raw.require_success _ hbt)⟩
  | toffoli a b target aOut bOut targetOut =>
    obtain ⟨⟨pa,next⟩,ha,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨pb,next'⟩,hb,h⟩ := except_bind_success _ _ _ h
    obtain ⟨⟨pt,next''⟩,ht,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hba,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hbb,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hbt,_⟩ := except_bind_success _ _ _ h
    have first := take_access _ _ _ _ ha
    have second := take_access _ _ _ _ hb
    exact ⟨⟨pa,first.1,beq_iff_eq.mp (Raw.require_success _ hba)⟩,
      ⟨pb,portAt_mono _ _ _ _ first.2 second.1,beq_iff_eq.mp (Raw.require_success _ hbb)⟩,
      pt,portAt_mono _ _ _ _ (fun p hp => first.2 (second.2 hp)) (take_access _ _ _ _ ht).1,
        beq_iff_eq.mp (Raw.require_success _ hbt)⟩
  | quantumIf control target controlOut targetOut zero oneSteps =>
    obtain ⟨⟨c,next⟩,hc,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨t,next'⟩,ht,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hbc,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    have first := take_access _ _ _ _ hc
    have good := Bool.and_eq_true_iff.mp (Raw.require_success _ hg)
    refine ⟨⟨c,first.1,beq_iff_eq.mp (Raw.require_success _ hbc)⟩,
      t,portAt_mono _ _ _ _ first.2 (take_access _ _ _ _ ht).1,?_,?_⟩
    · simpa only [Raw.unitary_reference] using circuit_access _ _ _ good.1
    · simpa only [Raw.unitary_reference] using circuit_access _ _ _ good.2
  | split input left right leftBits =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    exact ⟨port,(take_access _ _ _ _ ht).1,of_decide_eq_true (Raw.require_success _ hg)⟩
  | liftBasis input output wires table =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    have good := Raw.require_success _ hg
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at good
    exact ⟨port,(take_access _ _ _ _ ht).1,good.1.1.2,good.1.2⟩
  | applyUnitary input output steps =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    exact ⟨port,(take_access _ _ _ _ ht).1,circuit_access _ _ _ (Raw.require_success _ hg)⟩
  | certifiedCompute input output ancilla function useSteps logicalSteps =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    have good := Raw.require_success _ hg
    simp only [Bool.and_eq_true,beq_iff_eq] at good
    refine ⟨port,(take_access _ _ _ _ ht).1,?_,circuit_access _ _ _ good.2⟩
    rw [good.1.1.1]
    exact circuit_access _ _ _ good.1.2
  | computeUseUncompute input output targets ancilla function uses =>
    obtain ⟨⟨source,next⟩,ht,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨⟨ports,next'⟩,hp,h⟩ := except_bind_success _ _ _ h
    obtain ⟨_,hg,_⟩ := except_bind_success _ _ _ h
    have first := take_access _ _ _ _ ht
    refine ⟨source,first.1,?_,uses_access _ _ _ _ (Bool.and_eq_true_iff.mp (Raw.require_success _ hg)).2⟩
    intro target member
    obtain ⟨port,present,bit⟩ := targets_access _ _ _ _ _ hp target member
    exact ⟨port,portAt_mono _ _ _ _ first.2 present,bit⟩

theorem pure (dependencies : List Basis) (state : Raw.State) (op : Op) (result : Raw.Transition)
    (ok : Raw.step dependencies state op = .ok result) :
    Semantics.Ownership.Pure (view state) op (view result.state) := by
  have histories := dispatch_histories _ _ _ _ (Raw.step_conditions _ _ _ _ ok).2.1
  exact ⟨dispatch_access _ _ _ _ (Raw.step_conditions _ _ _ _ ok).2.1,
    ⟨result.events,Raw.step_reference _ _ _ _ ok⟩,histories.1,histories.2⟩

theorem trace_ownership (dependencies : List Basis) (initial final : Raw.State) (ops : List Op)
    (trace : Raw.Trace dependencies initial ops final) (good : Semantics.Ownership.Valid (view initial)) :
    Semantics.Ownership.Run (view initial) (ops.map Semantics.Observation.Op.pure) (view final) := by
  induction trace with
  | nil state => exact .nil _ good
  | cons state op next ops final head tail ih =>
    exact .cons _ _ _ _ _ good (.pure _ _ _ (pure _ _ _ _ head))
      (ih (valid _ (Raw.step_conditions _ _ _ _ head).2.2))

/-- The earlier straight-line raw API reaches the same independent property. -/
theorem prepare_resourceSafe (dependencies : List Basis) (program : Program) (prepared : Raw.Prepared)
    (ok : Raw.prepare dependencies program = .ok prepared) :
    Semantics.Ownership.ResourceSafe (Semantics.Ownership.pureProgram program) := by
  obtain ⟨initial,body,hi,_,ho,same,trace⟩ := Raw.prepare_conditions _ _ _ ok
  have initialized := Raw.inputs_valid _ _ _ (by decide) hi
  have coverage := Raw.output_coverage _ _ ho
  simp only [Raw.outputValid,Bool.and_eq_true,beq_iff_eq] at ho
  refine ⟨view initial,view prepared.state,inputs _ _ _ hi,trace_ownership _ _ _ _ trace (valid _ initialized),?_⟩
  rw [same]
  exact ⟨unique_nodup _ ho.1.1.1.1,ho.1.1.1.2,coverage.1,coverage.2.1⟩

end QleisliKernel.Raw.Ownership
