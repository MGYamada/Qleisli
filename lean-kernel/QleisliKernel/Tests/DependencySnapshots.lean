import QleisliKernel.Qirf.ContextArmExecution

/-! One-qubit controls for actual dependency sensitivity and inactive branches.
These observations are not a native source-preservation certificate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.DependencySnapshots
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact

def identity : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
def flip : Matrix := ⟨2,2,[Scalar.zero,Scalar.one,Scalar.one,Scalar.zero]⟩
def dependency (meaning : Matrix) : Dependency := ⟨[.bit],meaning⟩
def applyDependency (index input output : Nat) : Semantics.Observation.Op :=
  .pure (.applyUnitary input output [⟨[],.contract [0] index false⟩])
def original : Semantics.Observation.Program :=
  ⟨[⟨10,[7],1⟩],[],[applyDependency 0 10 11],[11],[],.unitary⟩
def branch : Semantics.Observation.Program :=
  ⟨[⟨10,[7],1⟩],[],[.constant true 100,
    .branch 100 [applyDependency 0 10 11] [applyDependency 1 10 12]
      [⟨11,12,13,[8]⟩] []],[13],[],.unitary⟩
def outcome (dependencies : List Dependency) (program : Semantics.Observation.Program := original) :=
  ((Raw.BranchFunction.reconstruct dependencies program).run 1000000).1.toOption

#guard outcome [dependency identity] == some identity
#guard outcome [dependency flip] == some flip
#guard outcome [dependency identity] != outcome [dependency flip]
-- A later unrelated slot need not equal the historical dummy-filled slot.
def observed (dependencies : List Dependency) :=
  let (result,remaining) := (Raw.BranchFunction.reconstruct dependencies original).run 1000000
  (result.toOption,remaining)
#guard observed [dependency identity,dependency identity] == observed [dependency identity,dependency flip]
#guard (outcome []).isNone
#guard (outcome [⟨[.unit],identity⟩]).isNone
-- The actual reference walk accounts for both arms even for a known condition.
#guard Semantics.ObservingFunction.references 65 branch.operations == [0,1]
#guard outcome [dependency identity,dependency flip] branch == some identity
#guard (outcome [dependency identity] branch).isNone

end QleisliKernel.Tests.DependencySnapshots
