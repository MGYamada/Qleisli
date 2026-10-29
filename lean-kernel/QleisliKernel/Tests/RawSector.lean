import QleisliKernel.Raw.Sector
import QleisliKernel.Tests.FiniteRestriction

/-! Small retained theorems for the original Raw-subject sector component.
At most two physical bits. These test the bounded original Raw/frame component,
not original source/arm/nominal binding or a native accepted handle. Raw.Program
has no observing op constructors, so these are not hidden-observation tests.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RawSector
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Raw QleisliKernel.Tests.FiniteRestriction

def subject : Program := {
  inputs := [⟨10,[7],1⟩,⟨11,[91],1⟩]
  operations := [.join 10 11 12,.applyUnitary 12 13 hxSteps,.split 13 14 15 1]
  outputs := [14,15]
  effect := .unitary
}

def outcome (selector target : Basis) (program : Program) (required : List Matrix) :
    Except QleisliKernel.Finite.Error (List Matrix) :=
  ((QleisliKernel.Raw.Sector.check [] selector target program required).run 1000000).1.map (·.sectors)

-- Arbitrary original token/wire identities survive join/apply/split and the
-- independently reconstructed literal final identity permutation.
theorem case1 : (outcome bitBasis bitBasis subject [hadamard,flip] == .ok [hadamard,flip]) = true := by
  decide +kernel

theorem case2 : (outcome bitBasis bitBasis subject [flip,hadamard] == .error .equation) = true := by
  decide +kernel

theorem case3 : (outcome bitBasis bitBasis subject [hadamard] == .error .request) = true := by
  decide +kernel

-- The original body's selector action cannot be dropped by sector extraction.
theorem case4 : (outcome bitBasis bitBasis {subject with operations := [
    .join 10 11 12,.applyUnitary 12 13 [⟨[],.hadamard 0⟩],.split 13 14 15 1]}
    [hadamard,hadamard] == .error .invalid) = true := by decide +kernel

-- Same width does not permit swapping the original physical output owners.
theorem case5 : (outcome bitBasis bitBasis {subject with outputs := [15,14]}
    [hadamard,flip] == .error .request) = true := by decide +kernel

theorem case6 : (outcome bitBasis bitBasis {subject with operations := [
    .join 10 11 12,.applyUnitary 12 10 hxSteps,.split 10 14 15 1]}
    [hadamard,flip] == .error .invalid) = true := by decide +kernel

theorem case7 : (outcome bitBasis bitBasis {subject with effect := .observe}
    [hadamard,flip] == .error .request) = true := by decide +kernel

def zeroSelector : Program := {
  inputs := [⟨10,[],0⟩,⟨11,[91],1⟩]
  operations := [.join 10 11 12,.applyUnitary 12 13 [⟨[],.hadamard 0⟩],.split 13 14 15 0]
  outputs := [14,15]
  effect := .unitary
}

theorem case8 : (outcome unitBasis bitBasis zeroSelector [hadamard] == .ok [hadamard]) = true := by
  decide +kernel

-- This component checks only a physical frame: Unit/Bits<0> identity must be
-- bound by the enclosing original typed forest, not inferred from Raw widths.
theorem case9 : (outcome [.bits 0] bitBasis zeroSelector [hadamard] == .ok [hadamard]) = true := by
  decide +kernel

theorem case10 : (outcome unitBasis bitBasis {zeroSelector with outputs := [15]}
    [hadamard] == .error .request) = true := by decide +kernel

def zeroOwners : Program := {
  inputs := [⟨10,[],0⟩,⟨11,[],0⟩]
  operations := []
  outputs := [10,11]
  effect := .unitary
}

theorem case11 : (outcome unitBasis unitBasis zeroOwners [scalar Scalar.one] ==
    .ok [scalar Scalar.one]) = true := by decide +kernel

def zeroPhase : Program := {zeroOwners with
  operations := [.join 10 11 12,.applyUnitary 12 13 [⟨[],.monomial [] [0] [4]⟩],
    .split 13 14 15 0]
  outputs := [14,15]
}

theorem case12 : (outcome unitBasis unitBasis zeroPhase [scalar negativeOne] ==
    .ok [scalar negativeOne]) = true := by decide +kernel

theorem case13 : (outcome unitBasis unitBasis zeroPhase [scalar Scalar.one] ==
    .error .equation) = true := by decide +kernel

-- Inspect the exact required error for a nonidentity final permutation.
theorem case14 : (match QleisliKernel.Raw.Sector.readEvents 2 [.reorder 2 [1,0]] with
    | .error .request => true
    | _ => false) = true := by decide +kernel

end QleisliKernel.Tests.RawSector
