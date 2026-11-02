import QleisliKernel.Qirf.RuntimeMaterialization

/-! Small actual inverse/control programs, including an exact scalar phase.
These equations do not establish original source access or full body checking.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeMaterialization
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open Semantics.Exact

private def scalar : Semantics.Observation.Program :=
  ⟨[⟨0,[],0⟩],[],[.pure (.applyUnitary 0 1 [⟨[],.monomial [] [0] [1]⟩])],
    [1],[],.unitary⟩

private def scalarPaths : WorkM (Matrix × List Matrix) := do
  let forward ← RuntimeMaterialization.readForward [] scalar
  let identity ← lift (arithmetic (Exact.Matrix.identity 1))
  let inverse ← RuntimeMaterialization.readInverse forward identity identity forward.physical
  let controlled ← RuntimeMaterialization.readControlled forward identity identity forward.physical
  return (inverse.physical,controlled.logicals)

#guard (scalarPaths.run 1000000).1.toOption.map (fun result =>
  result.1.entries == [Exact.Scalar.phase 7] &&
    (result.2.map (·.entries)) == [[Exact.Scalar.one],[Exact.Scalar.phase 1]]) == some true

private def identity : Semantics.Observation.Program :=
  ⟨[⟨0,[],0⟩],[],[],[0],[],.unitary⟩

private def zeroOperationForward : WorkM Nat := do
  let forward ← RuntimeMaterialization.readForward [] identity
  return forward.steps.length

#guard (zeroOperationForward.run 1000000).1.toOption == some 0

private def hiddenMeasurement : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],[.measure 0 0],[],[0],.observe⟩

#guard (match (RuntimeMaterialization.readForward [] hiddenMeasurement).run 1000000 with
  | (.error .request,_) => true
  | _ => false)

end QleisliKernel.Tests.RuntimeMaterialization
