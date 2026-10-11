import QleisliKernel.Raw.Ownership
import QleisliKernel.Semantics.RawUnit

/-! Executable structural Raw Unit maps used by the real dispatcher. The
original-operation ownership/trace proofs and historical semantic transport
connect their structural rules; these local results alone do not establish
source, decoder or runtime preservation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Unit
open Semantics.Raw Finite

/-- Introduce one globally fresh empty owner without allocating a wire. -/
abbrev pack := Raw.packUnit

/-- Consume exactly a live zero-axis owner, retaining all issuance history. -/
abbrev unpack := Raw.unpackUnit

theorem pack_conditions (state : State) (output : Nat) (result : Transition)
    (ok : pack state output = .ok result) :
    stateValid state = true ∧ insert state output [] = .ok result.state ∧
    stateValid result.state = true ∧ result.events = [] := by
  obtain ⟨_,hi,h⟩ := except_bind_success _ _ _ ok
  obtain ⟨next,hn,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,ho,h⟩ := except_bind_success _ _ _ h
  cases Except.ok.inj h
  exact ⟨require_success _ hi,hn,require_success _ ho,rfl⟩

theorem unpack_conditions (state : State) (input : Nat) (result : Transition)
    (ok : unpack state input = .ok result) :
    stateValid state = true ∧ ∃ port,
      take state input = .ok (port,result.state) ∧ port.bits = 0 ∧ port.wires = [] ∧
      stateValid result.state = true ∧ result.events = [] := by
  obtain ⟨_,hi,h⟩ := except_bind_success _ _ _ ok
  obtain ⟨⟨port,next⟩,ht,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,hz,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,ho,h⟩ := except_bind_success _ _ _ h
  cases Except.ok.inj h
  have zero := require_success _ hz
  simp only [Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff] at zero
  exact ⟨require_success _ hi,port,ht,zero.1,zero.2,require_success _ ho,rfl⟩

/-- Actual successful pack transitions satisfy the existing independent input
rule, with a genuine empty logical port and no new physical axes. -/
theorem pack_ownership (state : State) (output : Nat) (result : Transition)
    (ok : pack state output = .ok result) :
    Semantics.Ownership.Valid (Ownership.view state) ∧
    Semantics.Ownership.Input (Ownership.view state) ⟨output,[],0⟩ (Ownership.view result.state) ∧
    Semantics.Ownership.Valid (Ownership.view result.state) := by
  obtain ⟨before,inserted,after,_⟩ := pack_conditions _ _ _ ok
  refine ⟨Ownership.valid _ before,?_,Ownership.valid _ after⟩
  refine ⟨rfl,(insert_fresh _ _ _ _ inserted).1,?_,by simp,?_⟩
  · simp
  · rw [Ownership.insert_state _ _ _ _ inserted]
    simp [Ownership.view]

theorem pack_reference (state : State) (output : Nat) (result : Transition)
    (ok : pack state output = .ok result) :
    result.state.reference = Semantics.RawUnit.pack state.reference output ∧
    result.events = Semantics.RawUnit.events ∧ result.state.iso = state.iso := by
  obtain ⟨_,inserted,_,events⟩ := pack_conditions _ _ _ ok
  refine ⟨insert_reference _ _ _ _ inserted,events,?_⟩
  rw [Ownership.insert_state _ _ _ _ inserted]

theorem unpack_reference (state : State) (input : Nat) (result : Transition)
    (ok : unpack state input = .ok result) :
    Semantics.RawUnit.unpack state.reference input = some result.state.reference ∧
    result.events = Semantics.RawUnit.events ∧
    result.state.seenTokens = state.seenTokens ∧
    result.state.seenWires = state.seenWires ∧ result.state.iso = state.iso := by
  obtain ⟨_,port,taken,zero,empty,_,events⟩ := unpack_conditions _ _ _ ok
  have reference := take_reference _ _ _ _ taken
  have same := (Ownership.take_state _ _ _ _ taken).2
  refine ⟨?_,events,?_,?_,?_⟩
  · simp [Semantics.RawUnit.unpack,reference,zero,empty]
  all_goals simp [same]

/-- Consumption requires the literal live operand and preserves the ordered
physical frame, global histories and validity of every suspended owner. -/
theorem unpack_ownership (state : State) (input : Nat) (result : Transition)
    (ok : unpack state input = .ok result) :
    Semantics.Ownership.Valid (Ownership.view state) ∧
    Semantics.Ownership.Valid (Ownership.view result.state) ∧
    result.state.frame = state.frame ∧ ∃ port,
      port ∈ state.live ∧ port.token = input ∧ port.wires = [] ∧ port.bits = 0 ∧
      result.state.live = state.live.filter (fun p => p.token != input) := by
  obtain ⟨before,port,taken,zero,empty,after,_⟩ := unpack_conditions _ _ _ ok
  obtain ⟨found,same⟩ := Ownership.take_state _ _ _ _ taken
  have member := List.mem_of_find?_eq_some found
  have token := List.find?_some found
  refine ⟨Ownership.valid _ before,Ownership.valid _ after,?_,port,member,?_,empty,zero,?_⟩
  · simp [same]
  · simpa using token
  · simp [same]

/-- A finished identity remains globally issued and cannot be packed again. -/
theorem unpack_no_repack (state : State) (input : Nat) (result second : Transition)
    (ok : unpack state input = .ok result) : pack result.state input ≠ .ok second := by
  intro again
  obtain ⟨valid,_,_,port,present,token,_,_,_⟩ := unpack_ownership _ _ _ ok
  have issued := (valid.ports port present).2
  have histories := (unpack_reference _ _ _ ok).2.2.1
  have fresh := (pack_ownership _ _ _ again).2.1.freshOwner
  apply fresh
  simpa [Ownership.view,histories,token] using issued

/-- Consuming a Unit owner twice is rejected even though it has no wires. -/
theorem unpack_no_second_use (state : State) (input : Nat) (result second : Transition)
    (ok : unpack state input = .ok result) : unpack result.state input ≠ .ok second := by
  intro again
  obtain ⟨_,_,_,_,_,_,_,_,consumed⟩ := unpack_ownership _ _ _ ok
  obtain ⟨_,_,_,port,present,token,_,_,_⟩ := unpack_ownership _ _ _ again
  rw [consumed] at present
  simp [token] at present

/-- A successful round trip restores the exact live owner list and ordered
physical frame. Its one new issued identity is deliberately not forgotten. -/
theorem round_trip (state : State) (token : Nat) (packed finished : Transition)
    (introduced : pack state token = .ok packed)
    (consumed : unpack packed.state token = .ok finished) :
    finished.state = {state with seenTokens := state.seenTokens ++ [token]} := by
  have inserted := (pack_conditions _ _ _ introduced).2.1
  have fresh := (insert_fresh _ _ _ _ inserted).1
  have before := (pack_ownership _ _ _ introduced).1
  have keep : state.live.filter (fun port => port.token != token) = state.live := by
    apply List.filter_eq_self.mpr
    intro port present
    simp only [bne_iff_ne]
    intro same
    apply fresh
    simpa [Ownership.view,same] using (before.ports port present).2
  obtain ⟨_,port,taken,_,_,_,_⟩ := unpack_conditions _ _ _ consumed
  have packedState := Ownership.insert_state _ _ _ _ inserted
  have finishedState := (Ownership.take_state _ _ _ _ taken).2
  simp [finishedState,packedState,List.filter_append,keep]

end QleisliKernel.Raw.Unit
