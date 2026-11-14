import QleisliKernel.Qirf.StructuralXor

/-! Small literal controlled-X checks for table-free synthesis.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StructuralXor
open QleisliKernel Qirf.StructuralXor Semantics.Finite

private def clauses : List (List Control) := [[⟨0,true⟩,⟨1,false⟩],[⟨1,true⟩]]

private def actual : List Step := [
  ⟨[⟨0,true⟩,⟨1,false⟩],.monomial [2] [1,0] [0,0]⟩,
  ⟨[⟨1,true⟩],.monomial [2] [1,0] [0,0]⟩]

private def failure (target : Nat) (steps : List Step) (work : Nat) : Option Finite.Error :=
  match ((check target clauses steps).run work).1 with
  | .ok _ => none
  | .error error => some error

theorem literal_and_meter : failure 2 actual 168 = none ∧
    failure 2 actual 167 = some (.arithmetic .workLimit) := by decide +kernel

theorem rejects_wrong_phase_and_control :
    failure 2 [⟨[⟨0,true⟩,⟨1,false⟩],.monomial [2] [1,0] [4,4]⟩,
      ⟨[⟨1,true⟩],.monomial [2] [1,0] [0,0]⟩] 168 = some .equation ∧
    failure 2 [⟨[⟨1,true⟩,⟨0,false⟩],.monomial [2] [1,0] [0,0]⟩,
      ⟨[⟨1,true⟩],.monomial [2] [1,0] [0,0]⟩] 168 = some .equation := by decide +kernel

theorem rejects_wrong_target_and_alias :
    failure 2 [⟨[⟨0,true⟩,⟨1,false⟩],.monomial [3] [1,0] [0,0]⟩,
      ⟨[⟨1,true⟩],.monomial [2] [1,0] [0,0]⟩] 168 = some .equation ∧
    failure 1 (clauses.map (toggle 1)) 168 = some .request := by decide +kernel

end QleisliKernel.Tests.StructuralXor
