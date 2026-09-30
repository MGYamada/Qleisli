import Qleisli.HierarchicalInstrumentComplete

/-! Calibration for complete accepted readout geometry. The examples exercise
nonconsecutive axes, reversed measurement order, a retained multi-bit register,
a retained zero-width owner and pre-existing classical values.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.InstrumentCompleteExamples
open QleisliKernel.Hierarchical
open Artifact

def inputs : Side :=
  ⟨#[⟨10,#[.bit],#[17]⟩,⟨20,#[.bits 2],#[4,9]⟩,
      ⟨22,#[.bits 0],#[]⟩,⟨30,#[.bit],#[2]⟩],#[⟨50,#[.bit]⟩]⟩

def request : Readout.Request := ⟨inputs,#[30,10],60⟩

def afterFirst : Side :=
  ⟨inputs.quantum.filter (fun port => port.owner != 30),inputs.classical.push ⟨70,#[.bit]⟩⟩

def afterSecond : Side :=
  ⟨afterFirst.quantum.filter (fun port => port.owner != 10),afterFirst.classical.push ⟨71,#[.bit]⟩⟩

def packet : Readout.Packet :=
  ⟨#[⟨⟨inputs,afterFirst⟩,.observe,.observeZ 30 70⟩,
     ⟨⟨afterFirst,afterSecond⟩,.observe,.observeZ 10 71⟩],#[70,71],Readout.output request⟩

theorem accepted : Readout.check request packet 2000000 =
    .ok ⟨Readout.workCharge request packet⟩ := by cbv

/-- The actual accepted coordinates contain every output axis exactly once,
even when the requested measurement order differs from physical port order. -/
theorem partition :
    List.Disjoint [2,17] [4,9] ∧ [17,4,9,2].Perm ([2,17]++[4,9]) := by
  obtain ⟨axes,found,_,_,_,disjoint,cover⟩ :=
    HierarchicalInstrument.readout_geometry request packet 2000000 _ accepted
  have actual : axes = #[2,17] := Option.some.inj (found.symm.trans (by cbv))
  subst axes
  simpa [packet,request,inputs,Readout.output,wires] using And.intro disjoint cover

/-- The row equivalence preserves the specified measurement order and the
retained register's internal order; it does not sort physical axis labels. -/
example : List.ofFn (Semantics.Instrument.outputEquiv [17,4,9,2] [2,17] [4,9]
    (by decide) (by decide) (by decide) partition.1 partition.2
    (fun i => i.val == 0, fun i => i.val == 0)) = [false,true,false,true] := by decide

example : packet.outputs.quantum =
    #[⟨20,#[.bits 2],#[4,9]⟩,⟨22,#[.bits 0],#[]⟩] := by cbv

/-- No measured qubits still means one empty outcome and all quantum owners
remain in the residual frame. -/
def emptyRequest : Readout.Request := ⟨inputs,#[],60⟩
def emptyPacket : Readout.Packet := ⟨#[],#[],Readout.output emptyRequest⟩
example : Readout.check emptyRequest emptyPacket 2000000 =
    .ok ⟨Readout.workCharge emptyRequest emptyPacket⟩ := by cbv
example : Fintype.card (Fin 0 → Bool) = 1 := by decide

end Qleisli.InstrumentCompleteExamples
