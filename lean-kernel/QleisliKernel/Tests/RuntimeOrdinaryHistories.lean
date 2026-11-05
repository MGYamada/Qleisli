import QleisliKernel.Qirf.RuntimeOrdinaryHistories

/-! All-input completion through original Body/input/output boundaries and the
actual lazy Instrument run. No quantum instance or dispatcher is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinaryHistories
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open QleisliKernel.Qirf

private def text : String := "#![no_implicit_prelude]\npub fn route(c:Bit)->Bit{not c}"

private def complete (wrong : Bool) : Bool :=
  let action : WorkM Unit := do
    let sources : Sources := #[("main",text)]
    let signature ← SourceRuntimeContext.readSignature sources "main" "route" {}
    let body ← SourceRuntimeTrace.readBodyWithSignature signature
    let program : Semantics.Observation.Program :=
      ⟨[],[2],[if wrong then .constant false 3 else .not 2 3],[],[3],.unitary⟩
    let prepared ← RuntimeInterval.prepare [] program
    let runtime : RuntimeFamily.Request :=
      ⟨.exported,"main","route",signature.parameters.map (·.tree),[[.ordinary [.bit] (.bit 2)]],
        [[false],[true]],signature.result.tree,[.ordinary [.bit] (.bit 3)],.unitary,{}⟩
    let inputs ← RuntimeSourceBoundary.readInputs body prepared runtime.inputStorage
    let initial ← RuntimeOrdinaryInputs.read body prepared runtime inputs
    let before : RuntimeStructuralAction.SourceState := ⟨inputs.owners.bindings,[],0⟩
    let gap ← RuntimeOrdinaryBody.readGap prepared.block 0 1 before initial.ssa
    let owners ← RuntimeOwnerMap.check
      (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary body).value) prepared.whole.state []
    let outputs ← RuntimeSourceBoundary.checkOutputs body prepared.whole.state owners runtime.storage program.outputs
    let _ ← RuntimeOrdinaryHistories.read initial gap.ssa outputs
    pure ()
  (action.run 10000000).1.isOk

#guard complete false
-- Constant zero agrees at input one, but every canonical input is checked.
#guard !complete true

private def zeroHistory : Raw.StreamedInstrument.History :=
  ⟨[(2,false),(3,false)],[1],fun _ _ => pure Semantics.Exact.Scalar.zero⟩

private def zeroOutputRejected : Bool :=
  let ssa : RuntimeOrdinaryBody.State := ⟨[(2,.input 0),(3,.bit false)],[]⟩
  ((RuntimeOrdinaryHistories.readHistories [0] ssa [] [.ordinary [.bit] (.not (.input 0))]
    [.ordinary [.bit] (.bit 3)] [zeroHistory]).run 10000000).1.toOption.isNone

-- This scalar regression is not an authentic history-family witness. It
-- checks that the output reader never exempts even a zero-operator history.
#guard zeroOutputRejected

#print axioms QleisliKernel.Qirf.RuntimeOrdinaryHistories.Histories.every
#print axioms QleisliKernel.Qirf.RuntimeOrdinaryHistories.Rows.every

end QleisliKernel.Tests.RuntimeOrdinaryHistories
