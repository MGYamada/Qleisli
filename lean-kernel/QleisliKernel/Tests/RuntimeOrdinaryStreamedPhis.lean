import QleisliKernel.Qirf.RuntimeOrdinaryStreamedPhis

/-! Actual lazy merge tests on scalar history data. No dense inspection,
quantum instance, sampled outcome selection or accepted request is used.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinaryStreamedPhis
open QleisliKernel QleisliKernel.Finite

private def phis : List Semantics.Observation.ClassicalPhi := [⟨1,2,5⟩,⟨3,4,6⟩]
private def history : Raw.StreamedInstrument.History :=
  ⟨[(1,true),(2,false),(3,true),(4,false)],[0,1,0],fun _ _ => throw .equation⟩

private def snapshot (choice : Bool) : Option (Raw.Instrument.Values × List Nat) :=
  ((Raw.StreamedInstrument.merge choice phis history).run 1000000).1.toOption.map fun result =>
    (result.values,result.hidden)

#guard snapshot true = some ([(1,true),(2,false),(3,true),(4,false),(5,true),(6,true)],[0,1,0])
#guard snapshot false = some ([(1,true),(2,false),(3,true),(4,false),(5,false),(6,false)],[0,1,0])

private def coefficient (choice : Bool) : WorkM Semantics.Exact.Scalar := do
  let result ← Raw.StreamedInstrument.merge choice phis history
  result.operator 0 0

-- The merge never evaluates, replaces or catches the coefficient function.
#guard (coefficient true).run 1000000 = (.error .equation,1000000)
#guard (coefficient false).run 1000000 = (.error .equation,1000000)
#guard ((Raw.StreamedInstrument.merge true [⟨1,2,5⟩,⟨5,5,6⟩] history).run 1000000).1.toOption.isNone

private def zeroHistory : Raw.StreamedInstrument.History :=
  {history with operator := fun _ _ => pure Semantics.Exact.Scalar.zero}

-- A zero operator retains the same complete hidden path and phi processing.
#guard ((Raw.StreamedInstrument.merge true phis zeroHistory).run 1000000).1.toOption.map (·.hidden) = some [0,1,0]

#print axioms QleisliKernel.Qirf.RuntimeOrdinaryStreamedPhis.merge_retains
#print axioms QleisliKernel.Qirf.RuntimeOrdinaryStreamedPhis.MergedAt.coefficient_run

end QleisliKernel.Tests.RuntimeOrdinaryStreamedPhis
