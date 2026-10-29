import QleisliKernel.Tests.FiniteRestriction

/-! Canonical computed-sector oracles: three joined physical bits at most.
Named theorem constants retain the reduction proofs for compiled audits.
This is informed component evidence, not a source/native qmatch check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ComputedSectors
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.FiniteRestriction QleisliKernel.Tests.FiniteRestriction

theorem hadamard_and_flip : (((readSectors [] bitBasis bitBasis hxCircuit).run 100000).1 ==
    .ok [hadamard,flip]) = true := by decide +kernel

theorem scalar_phase : (((readSectors [] bitBasis unitBasis scalarCircuit).run 100000).1 ==
    .ok [scalar negativeOne,scalar imaginaryOne]) = true := by decide +kernel

theorem zero_width_selector : (((readSectors [] unitBasis bitBasis
    ⟨joinedBasis unitBasis bitBasis,[⟨[],.hadamard 0⟩]⟩).run 100000).1 ==
    .ok [hadamard]) = true := by decide +kernel

theorem complete_conjugation : (((readSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,conjugated⟩).run 100000).1 ==
    .ok [identity,flip]) = true := by decide +kernel

theorem selector_action_refuses : (((readSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,[⟨[],.hadamard 0⟩]⟩).run 100000).1 ==
    .error .invalid) = true := by decide +kernel

theorem malformed_permutation_refuses : (((readSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,[⟨[⟨0,true⟩],.monomial [1] [0,0] [0,0]⟩]⟩).run 100000).1 ==
    .error .request) = true := by decide +kernel

theorem missing_dependency_refuses : (((readSectors [] bitBasis unitBasis
    ⟨joinedBasis bitBasis unitBasis,contractSteps⟩).run 100000).1 ==
    .error .request) = true := by decide +kernel

theorem exact_dependency_adjoint : (((readSectors [⟨unitBasis,scalar imaginaryOne⟩]
    bitBasis unitBasis ⟨joinedBasis bitBasis unitBasis,contractSteps⟩).run 100000).1 ==
    .ok [scalar Scalar.one,scalar negativeImaginary]) = true := by decide +kernel

theorem ordered_axes : (((readSectors [] bitBasis twoTargets
    ⟨joinedBasis bitBasis twoTargets,[⟨[⟨0,true⟩],.monomial [2,1] [0,1,3,2] [0,0,0,0]⟩]⟩).run 1000000).1 ==
    .ok [identity4,firstControlsSecond]) = true := by decide +kernel

theorem original_tree_refuses : (((readSectors [] unitBasis bitBasis
    ⟨joinedBasis [.bits 0] bitBasis,[⟨[],.hadamard 0⟩]⟩).run 100000).1 ==
    .error .request) = true := by decide +kernel

theorem exhausted_work_refuses : (((readSectors [] bitBasis bitBasis hxCircuit).run 0).1 ==
    .error (.arithmetic .workLimit)) = true := by decide +kernel

end QleisliKernel.Tests.ComputedSectors
