import QleisliKernel.Qirf.RuntimeInterval
import QleisliKernel.Raw.Sector
import QleisliKernel.Raw.Ownership

/-! The actual local operation fold before its original sector finish event.
Both input/operation receipts are extracted from the same Raw.prepare result.
The retained sector event relation is split exactly at that operation prefix;
its actual final reorder fixes its width, identity axes and empty step piece.
No caller trace, circuit shape, final locality or replacement finish is assumed.
This proof adapter adds no runtime check or acceptance rule.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSectorPrefix
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.Semantics.Finite

/-- The literal output-token lookup used by the original Raw.prepare finish. -/
abbrev outputAxes (program : Semantics.Raw.Program) (body : Raw.Prepared) : List Nat :=
  Raw.axes body.state (program.outputs.flatMap fun token =>
    ((body.state.live.find? (fun port => port.token == token)).map (·.wires)).getD [])

/-- The same preparation receipt contains the actual inputs, no-finish body
fold, output guard and original final output permutation. -/
theorem prepare_prefix (dependencies : List Basis) (program : Semantics.Raw.Program) (prepared : Raw.Prepared)
    (read : Raw.prepare dependencies program = .ok prepared) :
    ∃ (initial : Raw.State) (body : Raw.Prepared),
      program.inputs.foldlM Raw.input {} = .ok initial ∧
      program.operations.foldlM (Raw.advance dependencies) ⟨initial,[],initial.frame.length⟩ = .ok body ∧
      initial.reference = Semantics.RawTrace.initial program.inputs ∧
      Raw.outputValid program body.state = true ∧
      prepared = {body with events := body.events ++ [.reorder body.state.frame.length (outputAxes program body)]} := by
  unfold Raw.prepare at read
  obtain ⟨initial,inputs,h⟩ := except_bind_success _ _ _ read
  obtain ⟨body,operations,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,checked,h⟩ := except_bind_success _ _ _ h
  have reference : initial.reference = Semantics.RawTrace.initial program.inputs := by
    simpa only [Raw.State.reference,Semantics.RawTrace.initial,List.nil_append] using
      Raw.inputs_reference program.inputs {} initial inputs
  exact ⟨initial,body,inputs,operations,reference,Raw.require_success _ checked,(Except.ok.inj h).symm⟩

private theorem pair_values {α : Type} (values : List α) (length : values.length = 2) :
    ∃ first second, values = [first,second] :=
  ⟨_,_,List.eq_getElem_of_length_eq_two values length⟩

private theorem initial_width (selector target : Basis) (program : Semantics.Raw.Program)
    (prepared : Raw.Prepared) (initial : Raw.State)
    (inputs : program.inputs.foldlM Raw.input {} = .ok initial)
    (reference : initial.reference = Semantics.RawTrace.initial program.inputs)
    (counts : (program.effect == .unitary && program.inputs.length == 2 && program.outputs.length == 2) = true)
    (interface : Raw.Sector.ownerInterface selector target program prepared = true) :
    initial.frame.length = width selector + width target := by
  have countFacts := Bool.and_eq_true_iff.mp counts
  obtain ⟨first,second,inputPorts⟩ := pair_values program.inputs
    (beq_iff_eq.mp (Bool.and_eq_true_iff.mp countFacts.1).2)
  obtain ⟨firstOut,secondOut,outputTokens⟩ := pair_values program.outputs (beq_iff_eq.mp countFacts.2)
  have interfaceFacts := interface
  simp only [Raw.Sector.ownerInterface,inputPorts,outputTokens,Bool.and_eq_true,beq_iff_eq] at interfaceFacts
  have firstWidth : first.bits = width selector := interfaceFacts.1.1.1
  have secondWidth : second.bits = width target := interfaceFacts.1.1.2
  have initialLive : initial.live = [first,second] := by
    have live := congrArg Semantics.RawTrace.Interface.live reference
    simpa only [Raw.State.reference,Semantics.RawTrace.initial,inputPorts] using live
  have initialFrame : initial.frame = first.wires ++ second.wires := by
    have frame := congrArg Semantics.RawTrace.Interface.frame reference
    simpa only [Raw.State.reference,Semantics.RawTrace.initial,inputPorts,List.flatMap_cons,List.flatMap_nil,
      List.append_nil] using frame
  have valid := Raw.Ownership.valid initial (Raw.inputs_valid program.inputs {} initial (by decide) inputs)
  have firstPresent : first ∈ initial.live := by
    rw [initialLive]
    exact List.mem_cons_self
  have secondPresent : second ∈ initial.live := by
    rw [initialLive]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have firstShape := (valid.ports first firstPresent).1
  have secondShape := (valid.ports second secondPresent).1
  rw [initialFrame,List.length_append,← firstShape,← secondShape,firstWidth,secondWidth]

private theorem relation_split {α β : Type} (relation : α → β → Prop)
    (first rest : List α) (values : List β)
    (related : Exact.ListRel relation (first ++ rest) values) :
    ∃ firstValues restValues, values = firstValues ++ restValues ∧
      Exact.ListRel relation first firstValues ∧ Exact.ListRel relation rest restValues := by
  induction first generalizing values with
  | nil => exact ⟨[],values,rfl,trivial,related⟩
  | cons head tail ih =>
    cases values with
    | nil => exact False.elim related
    | cons value values =>
      obtain ⟨front,back,same,firstRelated,restRelated⟩ := ih values related.2
      exact ⟨value :: front,back,congrArg (List.cons value) same,⟨related.1,firstRelated⟩,restRelated⟩

private theorem finish_piece (bits width : Nat) (axes : List Nat) (pieces : List (List Step))
    (related : Exact.ListRel (Raw.Sector.EventPiece bits) [.reorder width axes] pieces) :
    pieces = [[]] ∧ width = bits ∧ axes = List.range bits := by
  cases pieces with
  | nil => exact False.elim related
  | cons first rest =>
    have restEmpty : rest = [] := by
      cases rest with
      | nil => rfl
      | cons next tail => exact False.elim related.2
    rcases related.1 with impossible | ⟨same,empty⟩
    · cases impossible
    · have fields := Semantics.Raw.Event.reorder.inj same
      exact ⟨by rw [empty,restEmpty],fields.1,fields.2⟩

private theorem read_facts (dependencies : List Dependency) (selector target : Basis)
    (program : Semantics.Raw.Program) (retained : Raw.Sector.Retained)
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies selector target program) retained) :
    (program.effect == .unitary && program.inputs.length == 2 && program.outputs.length == 2) = true ∧
      Raw.prepare (dependencies.map (·.signature)) program = .ok retained.prepared ∧
      Raw.Sector.ownerInterface selector target program retained.prepared = true ∧
      ∃ pieces : List (List Step), Exact.ListRel (Raw.Sector.EventPiece (width selector + width target))
        retained.prepared.events pieces ∧ retained.steps = pieces.flatten := by
  obtain ⟨work,left,read⟩ := restricted
  have binding : Raw.Sector.ReadBinding dependencies selector target program retained :=
    Raw.Sector.read_bound dependencies selector target program retained work left read
  exact ⟨binding.2.1,binding.2.2.1,binding.2.2.2.2.1,binding.2.2.2.2.2.1⟩

/-- The same retained sector read determines the complete no-finish local
Raw fold and original piece prefix. Only its actual identity finish contributes
an empty piece; every circuit, including an empty one, remains in the prefix. -/
theorem sector_prefix {dependencies : List Dependency} {selector target : Basis}
    {program : Semantics.Raw.Program} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies selector target program) retained) :
    ∃ (initial : Raw.State) (body : Raw.Prepared) (pieces : List (List Step)),
      program.inputs.foldlM Raw.input {} = .ok initial ∧
      program.operations.foldlM (Raw.advance (dependencies.map (·.signature)))
        ⟨initial,[],initial.frame.length⟩ = .ok body ∧
      initial.reference = Semantics.RawTrace.initial program.inputs ∧
      initial.frame.length = width selector + width target ∧
      Raw.outputValid program body.state = true ∧
      retained.prepared = {body with events := body.events ++ [.reorder body.state.frame.length (outputAxes program body)]} ∧
      body.state.frame.length = initial.frame.length ∧ outputAxes program body = List.range initial.frame.length ∧
      Raw.Sector.EventPiece initial.frame.length (.reorder body.state.frame.length (outputAxes program body)) [] ∧
      Exact.ListRel (Raw.Sector.EventPiece initial.frame.length) body.events pieces ∧
      retained.steps = pieces.flatten := by
  obtain ⟨counts,preparation,interface,allPieces,related,flatten⟩ :=
    read_facts dependencies selector target program retained restricted
  unfold Raw.prepare at preparation
  obtain ⟨initial,inputs,afterInputs⟩ := except_bind_success _ _ _ preparation
  obtain ⟨body,operations,afterOperations⟩ := except_bind_success _ _ _ afterInputs
  obtain ⟨_,checked,finished⟩ := except_bind_success _ _ _ afterOperations
  have reference : initial.reference = Semantics.RawTrace.initial program.inputs := by
    simpa only [Raw.State.reference,Semantics.RawTrace.initial,List.nil_append] using
      Raw.inputs_reference program.inputs {} initial inputs
  have outputChecked := Raw.require_success _ checked
  have prepared := (Except.ok.inj finished).symm
  have bits : initial.frame.length = width selector + width target :=
    initial_width selector target program retained.prepared initial inputs reference counts interface
  have prefixAndFinish : Exact.ListRel (Raw.Sector.EventPiece (width selector + width target))
      (body.events ++ [.reorder body.state.frame.length (outputAxes program body)]) allPieces := by
    rw [prepared] at related
    exact related
  obtain ⟨pieces,finishPieces,piecesAppend,prefixRelated,finishRelated⟩ :=
    relation_split (Raw.Sector.EventPiece (width selector + width target)) body.events
      [.reorder body.state.frame.length (outputAxes program body)] allPieces prefixAndFinish
  obtain ⟨finishEmpty,finishWidth,finishAxes⟩ := finish_piece (width selector + width target)
    body.state.frame.length (outputAxes program body) finishPieces finishRelated
  have exactWidth : body.state.frame.length = initial.frame.length := finishWidth.trans bits.symm
  have exactAxes : outputAxes program body = List.range initial.frame.length := by
    rw [bits]
    exact finishAxes
  have exactPiece : Raw.Sector.EventPiece initial.frame.length
      (.reorder body.state.frame.length (outputAxes program body)) [] :=
    Or.inr ⟨by rw [exactWidth,exactAxes],rfl⟩
  have exactPrefix : Exact.ListRel (Raw.Sector.EventPiece initial.frame.length) body.events pieces := by
    rw [bits]
    exact prefixRelated
  have exactFlatten : retained.steps = pieces.flatten := by
    simpa only [piecesAppend,finishEmpty,List.flatten_append,List.flatten_cons,List.flatten_nil,
      List.nil_append,List.append_nil] using flatten
  exact ⟨initial,body,pieces,inputs,operations,reference,bits,outputChecked,prepared,
    exactWidth,exactAxes,exactPiece,exactPrefix,exactFlatten⟩

#print axioms prepare_prefix
#print axioms sector_prefix

end Qleisli.RuntimeSectorPrefix
