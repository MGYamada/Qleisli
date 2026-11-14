import QleisliKernel.Raw.Finite

/-! Exact finite workspace equations over the actual body circuit.
The caller must independently bind the source, body and ordered ports.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Workspace
open QleisliKernel Finite Semantics.Finite Semantics.Exact

/-- Data are the low axes and the one-Bit scratch is the high axis. Dirty
checks the complete interface; clean uses the canonical zero embedding. -/
def required (dirty : Bool) (dataBits : Nat) (logical : Matrix) : WorkM Contract := do
  guard (dataBits < 6) .limit
  if dirty then
    let bits := dataBits + 1
    let identity ← Raw.mapping bits bits (List.range (2^bits))
    let basis := Raw.registerBasis bits
    let encoding : Encoding := ⟨basis,basis,identity⟩
    let expected ← Raw.promote bits (List.range dataBits) logical
    return ⟨encoding,encoding,expected⟩
  else
    let encoding ← Raw.zeroEncoding dataBits 1
    return ⟨encoding,encoding,logical⟩

def check (dependencies : List Dependency) (dirty : Bool) (dataBits : Nat)
    (steps : List Step) (logical : Matrix) : WorkM Matrix := do
  let contract ← required dirty dataBits logical
  Finite.check dependencies (Raw.circuit (dataBits+1) steps) contract contract

def checkOriginal (dependencies : List Dependency) (dirty : Bool) (dataBits : Nat)
    (steps : List Step) (logical original : Matrix) : WorkM Matrix := do
  let actual ← check dependencies dirty dataBits steps logical
  exactWork (Exact.charge (actual.entries.length+original.entries.length+1))
  guard (actual == original) .equation
  return actual

theorem check_conditions (dependencies : List Dependency) (dirty : Bool) (dataBits : Nat)
    (steps : List Step) (logical actual : Matrix) (work left : Nat)
    (ok : (check dependencies dirty dataBits steps logical).run work = (.ok actual,left)) :
    ∃ contract middle circuitWork afterCircuit lhs lhsWork rhs rhsWork,
      (required dirty dataBits logical).run work = (.ok contract,middle) ∧
      (circuitMatrix dependencies (Raw.circuit (dataBits+1) steps)).run circuitWork =
        (.ok actual,afterCircuit) ∧
      Exact.Matrix.compose actual contract.input.map afterCircuit = (.ok lhs,lhsWork) ∧
      Exact.Matrix.compose contract.output.map contract.logical lhsWork = (.ok rhs,rhsWork) ∧ lhs = rhs := by
  obtain ⟨contract,middle,prepared,checked⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨circuitWork,afterCircuit,lhs,lhsWork,rhs,rhsWork,conditions⟩ :=
    (Finite.check_conditions _ _ _ _ _ _ _ checked).2.2.2.2.2.2
  exact ⟨contract,middle,circuitWork,afterCircuit,lhs,lhsWork,rhs,rhsWork,prepared,conditions⟩

theorem checkOriginal_bound (dependencies : List Dependency) (dirty : Bool) (dataBits : Nat)
    (steps : List Step) (logical original actual : Matrix) (work left : Nat)
    (ok : (checkOriginal dependencies dirty dataBits steps logical original).run work = (.ok actual,left)) :
    actual = original ∧ ∃ after, (check dependencies dirty dataBits steps logical).run work = (.ok actual,after) := by
  obtain ⟨matrix,after,checked,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,charged,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,guarded,agrees,ret⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ ret).1
  subst actual
  have equal := (guard_success _ _ charged guarded agrees).1
  exact ⟨eq_of_beq equal,after,checked⟩

end QleisliKernel.Raw.Workspace
