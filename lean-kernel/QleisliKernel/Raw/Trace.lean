import QleisliKernel.Raw.Structure

/-! Actual raw extraction refines the independent original-operation reader.
All constructor proofs concern the executable dispatch, not an assumed Rust
trace or a proposition defined by checker success.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw
open Semantics.Raw Semantics.Finite

abbrev Reference := Semantics.RawTrace.Interface

def State.reference (state : State) : Reference := ⟨state.live,state.frame⟩
def Prepared.reference (prepared : Prepared) : Semantics.RawTrace.Prepared :=
  ⟨prepared.state.reference,prepared.events,prepared.inputBits⟩

theorem reserve_reference (state result : State) (wires : List Nat)
    (ok : reserve state wires = .ok result) : result.reference = state.reference := by
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ ok
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  rfl

theorem insert_reference (state result : State) (token : Nat) (wires : List Nat)
    (ok : insert state token wires = .ok result) :
    result.reference = Semantics.RawTrace.insert state.reference token wires := by
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ ok
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  rfl

theorem take_reference (state next : State) (token : Nat) (port : Port)
    (ok : take state token = .ok (port,next)) :
    Semantics.RawTrace.take state.reference token = some (port,next.reference) := by
  obtain ⟨found,hf,h⟩ := Finite.except_bind_success _ _ _ ok
  have found_eq : state.live.find? (fun port => port.token == token) = some found := by
    cases he : state.live.find? (fun port => port.token == token) <;> simp_all [Finite.readOption]
  simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  simp [Semantics.RawTrace.take,State.reference,found_eq]

theorem gate_reference (value : Gate) (axis : Nat) : gateStep value axis = Semantics.RawTrace.gate value axis := rfl

theorem unitary_reference (value : UnitaryStep) : unitaryStep value = Semantics.RawTrace.unitary value := by
  cases value <;> rfl

theorem localize_reference (indices : List Nat) (value : Step) : remap indices value = Semantics.RawTrace.localize indices value := rfl

theorem takeTargets_reference (targets : List Target) (ports out : List Port) (state result : State)
    (ok : targets.foldlM (fun (ports,next) target => do
      let (port,next) ← take next target.input
      require (port.bits == 1)
      pure (ports ++ [port],next)) (ports,state) = .ok (out,result)) :
    targets.foldlM (fun (ports,next) target => do
      let (port,next) ← Semantics.RawTrace.take next target.input
      pure (ports ++ [port],next)) (ports,state.reference) = some (out,result.reference) := by
  induction targets generalizing ports state with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at ok
    rcases ok with ⟨rfl,rfl⟩
    rfl
  | cons target targets ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,hrest⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨port,after⟩,ht,h⟩ := Finite.except_bind_success _ _ _ hn
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst next
    simpa [List.foldlM_cons,take_reference _ _ _ _ ht] using ih (ports ++ [port]) after hrest

theorem putTargets_reference (targets : List (Target × Port)) (state result : State)
    (ok : targets.foldlM (fun next (target,port) => insert next target.output port.wires) state = .ok result) :
    targets.foldl (fun next (target,port) => Semantics.RawTrace.insert next target.output port.wires) state.reference = result.reference := by
  induction targets generalizing state with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    rfl
  | cons pair targets ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hi,hrest⟩ := Finite.except_bind_success _ _ _ ok
    simpa [List.foldl_cons,insert_reference _ _ _ _ hi] using ih next hrest

/-- Every accepted original constructor has the same ordered interface and
literal events as the independent reference reader. -/
theorem dispatch_reference (dependencies : List Basis) (state : State) (op : Op) (result : Transition)
    (ok : dispatch dependencies state op = .ok result) :
    Semantics.RawTrace.step state.reference op = some (result.state.reference,result.events) := by
  cases op with
  | packUnit output =>
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨next,inserted,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    cases Except.ok.inj h
    simp [Semantics.RawTrace.step,insert_reference _ _ _ _ inserted]
  | unpackUnit input =>
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨port,next⟩,taken,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,zero,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    cases Except.ok.inj h
    have good := require_success _ zero
    simp only [Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff] at good
    simp [Semantics.RawTrace.step,take_reference _ _ _ _ taken,good.1,good.2]
  | init0 output wire =>
    obtain ⟨reserved,hr,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have r := reserve_reference _ _ _ hr
    have i := insert_reference _ _ _ _ hi
    have live := congrArg Semantics.RawTrace.Interface.live
      (i.trans (congrArg (fun s => Semantics.RawTrace.insert s output [wire]) r))
    simp only [State.reference,Semantics.RawTrace.insert] at live
    simp only [Semantics.RawTrace.step,State.reference,Semantics.RawTrace.insert,live]
    rfl
  | gate value input output =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ht,bind,Option.bind,
      ← insert_reference _ _ _ _ hi,gate_reference]
    rfl
  | cnot control target controlOut targetOut =>
    obtain ⟨⟨c,next⟩,hc,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨t,next'⟩,ht,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outC,hiC,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outT,hiT,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ hc,take_reference _ _ _ _ ht,
      bind,Option.bind,← insert_reference _ _ _ _ hiC,← insert_reference _ _ _ _ hiT,gate_reference]
    rfl
  | toffoli a b target aOut bOut targetOut =>
    obtain ⟨⟨a,next⟩,ha,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨b,next'⟩,hb,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨⟨t,next''⟩,ht,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outA,hiA,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outB,hiB,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outT,hiT,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ha,take_reference _ _ _ _ hb,
      take_reference _ _ _ _ ht,bind,Option.bind,← insert_reference _ _ _ _ hiA,
      ← insert_reference _ _ _ _ hiB,← insert_reference _ _ _ _ hiT,gate_reference]
    rfl
  | quantumIf control target controlOut targetOut zero oneSteps =>
    obtain ⟨⟨c,next⟩,hc,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨t,next'⟩,ht,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outC,hiC,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outT,hiT,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ hc,take_reference _ _ _ _ ht,
      bind,Option.bind,← insert_reference _ _ _ _ hiC,← insert_reference _ _ _ _ hiT,
      unitary_reference,localize_reference]
    rfl
  | split input left right leftBits =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outL,hiL,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨outR,hiR,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ht,bind,Option.bind,
      ← insert_reference _ _ _ _ hiL,← insert_reference _ _ _ _ hiR]
    rfl
  | join left right output =>
    obtain ⟨⟨l,next⟩,hl,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨r,next'⟩,hr,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ hl,take_reference _ _ _ _ hr,
      bind,Option.bind,← insert_reference _ _ _ _ hi]
    rfl
  | liftBasis input output wires table =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨reserved,hr,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have r := reserve_reference _ _ _ hr
    have i := insert_reference _ _ _ _ hi
    have same : inserted.reference = Semantics.RawTrace.insert next.reference output wires :=
      i.trans (congrArg (fun s => Semantics.RawTrace.insert s output wires) r)
    have live := congrArg Semantics.RawTrace.Interface.live same
    simp only [State.reference,Semantics.RawTrace.insert] at live
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ht,bind,Option.bind,pure,live]
    rfl
  | applyUnitary input output steps =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ht,bind,Option.bind,
      ← insert_reference _ _ _ _ hi]
    rfl
  | certifiedCompute input output ancilla function useSteps logicalSteps =>
    obtain ⟨⟨port,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨_,hg,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨reserved,hr,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have r := reserve_reference _ _ _ hr
    have i := insert_reference _ _ _ _ hi
    have same := i.trans (congrArg (fun s => Semantics.RawTrace.insert s output port.wires) r)
    have length : ancilla.length = 1 := by
      have good := require_success _ hg
      simp only [Bool.and_eq_true,beq_iff_eq] at good
      exact good.1.1.1
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ht,bind,Option.bind,← same,length]
    rfl
  | computeUseUncompute input output targets ancilla function uses =>
    obtain ⟨⟨source,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨⟨ports,next'⟩,hp,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨reserved,hr,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
    obtain ⟨final,hf,h⟩ := Finite.except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst result
    have targetsRead := takeTargets_reference targets [] ports next next' hp
    simp only [bind,Option.bind] at targetsRead
    have r := reserve_reference _ _ _ hr
    have i := insert_reference _ _ _ _ hi
    have same := i.trans (congrArg (fun s => Semantics.RawTrace.insert s output source.wires) r)
    have last := putTargets_reference _ _ _ hf
    simp only [Semantics.RawTrace.step,take_reference _ _ _ _ ht,bind,Option.bind,targetsRead,← same,last]
    rfl

/-- Validity and freshness checks strengthen, rather than define, the literal
meaning trace. Meaning-bearing action data and interfaces survive extraction. -/
theorem step_reference (dependencies : List Basis) (state : State) (op : Op) (result : Transition)
    (ok : step dependencies state op = .ok result) :
    Semantics.RawTrace.step state.reference op = some (result.state.reference,result.events) :=
  dispatch_reference _ _ _ _ (step_conditions _ _ _ _ ok).2.1

theorem advance_reference (dependencies : List Basis) (initial result : Prepared) (op : Op)
    (ok : advance dependencies initial op = .ok result) :
    Semantics.RawTrace.advance initial.reference op = some result.reference := by
  obtain ⟨next,hn,h⟩ := Finite.except_bind_success _ _ _ ok
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  simp only [Semantics.RawTrace.advance,Prepared.reference,step_reference _ _ _ _ hn,bind,Option.bind]
  rfl

theorem operations_reference (dependencies : List Basis) (operations : List Op) (initial result : Prepared)
    (ok : operations.foldlM (advance dependencies) initial = .ok result) :
    operations.foldlM Semantics.RawTrace.advance initial.reference = some result.reference := by
  induction operations generalizing initial with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    rfl
  | cons op ops ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,rest⟩ := Finite.except_bind_success _ _ _ ok
    simpa [List.foldlM_cons,advance_reference _ _ _ _ hn] using ih next rest

theorem input_reference (state result : State) (port : Port)
    (ok : input state port = .ok result) :
    result.reference = ⟨state.live ++ [port],state.frame ++ port.wires⟩ := by
  obtain ⟨_,hg,h⟩ := Finite.except_bind_success _ _ _ ok
  obtain ⟨reserved,hr,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨inserted,hi,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  have length : port.bits = port.wires.length := by
    have good := require_success _ hg
    simp only [Bool.and_eq_true,beq_iff_eq] at good
    exact good.1
  have same := (insert_reference _ _ _ _ hi).trans
    (congrArg (fun s => Semantics.RawTrace.insert s port.token port.wires) (reserve_reference _ _ _ hr))
  have live := congrArg Semantics.RawTrace.Interface.live same
  simp only [State.reference,Semantics.RawTrace.insert] at live
  have shape : Port.mk port.token port.wires port.wires.length = port := by
    cases port
    simp_all
  simp only [State.reference,live,shape]

theorem inputs_reference (ports : List Port) (initial result : State)
    (ok : ports.foldlM input initial = .ok result) :
    result.reference = ⟨initial.live ++ ports,initial.frame ++ ports.flatMap (·.wires)⟩ := by
  induction ports generalizing initial with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    simp [State.reference]
  | cons port ports ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,rest⟩ := Finite.except_bind_success _ _ _ ok
    have same := input_reference _ _ _ hn
    have live := congrArg Semantics.RawTrace.Interface.live same
    have frame := congrArg Semantics.RawTrace.Interface.frame same
    change next.live = initial.live ++ [port] at live
    change next.frame = initial.frame ++ port.wires at frame
    simpa [State.reference,live,frame,List.append_assoc] using ih next rest

/-- Every accepted complete raw program has exactly the independent original
trace, input interface and final output permutation. The theorem is unbounded
in program size and wire count; the checker's compatibility limits still apply. -/
theorem prepare_reference (dependencies : List Basis) (program : Program) (result : Prepared)
    (ok : prepare dependencies program = .ok result) :
    Semantics.RawTrace.run program = some result.reference := by
  obtain ⟨initial,hi,h⟩ := Finite.except_bind_success _ _ _ ok
  obtain ⟨body,hb,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  have inputs := inputs_reference _ _ _ hi
  have initial_eq : initial.reference = Semantics.RawTrace.initial program.inputs := by
    simpa [Semantics.RawTrace.initial] using inputs
  have operations := operations_reference _ _ _ _ hb
  simp only [Semantics.RawTrace.run,← initial_eq]
  change (do
    let result ← program.operations.foldlM Semantics.RawTrace.advance
      (Prepared.mk initial [] initial.frame.length).reference
    pure (Semantics.RawTrace.finish program result)) = _
  rw [operations]
  rfl

end QleisliKernel.Raw
