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

-- Both active gates are validated, but the flip's payload is not
-- validated again in the sector that executes only the Hadamard.
theorem inactive_payload_does_not_spend_local_validation_work :
    (((readSectors [] bitBasis bitBasis hxCircuit).run 1100).1 ==
      .ok [hadamard,flip]) = true := by decide +kernel

theorem active_payload_still_spends_local_validation_work :
    (((readSectors [] bitBasis bitBasis hxCircuit).run 900).1 ==
      .error (.arithmetic .workLimit)) = true := by decide +kernel

private def repeatedCircuit : Circuit := ⟨joinedBasis [.bits 2] bitBasis,
  [⟨[⟨0,false⟩],.hadamard 2⟩,
   ⟨[⟨0,true⟩],.monomial [2] [1,0] [0,0]⟩]⟩

theorem repeated_tapes_keep_every_physical_ordinal :
    (((readSectors [] [.bits 2] bitBasis repeatedCircuit).run 1220).1 ==
      .ok [hadamard,flip,hadamard,flip]) = true ∧
    (((readSectors [] [.bits 2] bitBasis repeatedCircuit).run 1219).1 ==
      .error (.arithmetic .workLimit)) = true := by decide +kernel

private def distinctPhases : Circuit := ⟨joinedBasis [.bits 2] bitBasis,
  [⟨[⟨0,false⟩],.monomial [2] [1,0] [0,0]⟩,
   ⟨[⟨0,true⟩],.monomial [2] [1,0] [4,4]⟩]⟩

theorem cache_distinguishes_phases_of_the_same_permutation :
    let negativeFlip : Matrix := ⟨2,2,[Scalar.zero,negativeOne,negativeOne,Scalar.zero]⟩
    (((readSectors [] [.bits 2] bitBasis distinctPhases).run 10000).1 ==
      .ok [flip,negativeFlip,flip,negativeFlip]) = true := by decide +kernel

private def phasedFlip : Step := ⟨[],.monomial [0] [1,0] [1,3]⟩

private def phasedFlipMatrix : Matrix := ⟨8,8,(List.range 64).map fun i =>
  let column := i % 8
  if i / 8 == column ^^^ 1 then
    QleisliKernel.Exact.Scalar.phase (if column % 2 = 0 then 1 else 3)
  else Scalar.zero⟩

theorem sparse_sector_keeps_exact_phases_with_less_work :
    (((readSectors [] unitBasis [.bits 3]
      ⟨joinedBasis unitBasis [.bits 3],[phasedFlip]⟩).run 1804).1 ==
      .ok [phasedFlipMatrix]) = true := by decide +kernel

private def fullHadamard : Matrix := ⟨8,8,(List.range 64).map fun i =>
  let common := (i / 8) &&& (i % 8)
  let parity := (List.range 3).foldl (fun value k => value != common.testBit k) false
  ⟨.integer 0,⟨if parity then -1 else 1,2⟩,.integer 0,.integer 0⟩⟩

theorem dense_sector_keeps_its_original_gram_budget :
    (((readSectors [] unitBasis [.bits 3]
      ⟨joinedBasis unitBasis [.bits 3],[⟨[],.hadamard 0⟩,⟨[],.hadamard 1⟩,⟨[],.hadamard 2⟩]⟩).run
      2720).1 == .ok [fullHadamard]) = true := by decide +kernel

private def spentUnit (run : Except QleisliKernel.Finite.Error Unit × Nat) (left : Nat) : Bool :=
  match run.1 with
  | .ok _ => run.2 == left
  | .error _ => false

private def failedUnit (run : Except QleisliKernel.Finite.Error Unit × Nat)
    (error : QleisliKernel.Finite.Error) : Bool :=
  match run.1 with
  | .ok _ => false
  | .error actual => actual == error

theorem measured_gram_retains_the_dense_budget :
    spentUnit ((adaptiveWholeSpace fullHadamard).run 1088) 0 = true ∧
    failedUnit ((adaptiveWholeSpace fullHadamard).run 1087) (.arithmetic .workLimit) = true := by
  decide +kernel

theorem measured_gram_skips_only_when_it_fits_the_smaller_budget :
    spentUnit ((adaptiveWholeSpace phasedFlipMatrix).run 1032) 0 = true ∧
    failedUnit ((adaptiveWholeSpace phasedFlipMatrix).run 1031) (.arithmetic .workLimit) = true := by
  decide +kernel

theorem sparse_gram_charges_every_retained_term :
    spentUnit ((compactSectorSpace phasedFlipMatrix).run 968) 0 = true ∧
    failedUnit ((compactSectorSpace phasedFlipMatrix).run 967) (.arithmetic .workLimit) = true ∧
    failedUnit ((QleisliKernel.Finite.wholeSpace phasedFlipMatrix).run 968) (.arithmetic .workLimit) = true := by
  decide +kernel

private def repeatedColumn : Matrix := ⟨8,8,(List.range 64).map fun i =>
  let column := i % 8
  if i / 8 == (if column == 1 then 0 else column) then Scalar.one else Scalar.zero⟩

theorem sparse_gram_refuses_repeated_columns :
    failedUnit ((compactSectorSpace repeatedColumn).run 2000) .notIsometric = true := by decide +kernel

private def excessiveMagnitude : Matrix := ⟨8,8,(List.range 64).map fun i =>
  if i == 0 then ⟨.integer QleisliKernel.Exact.maxNumerator,.integer 0,.integer 0,.integer 0⟩
  else if i / 8 == i % 8 then Scalar.one else Scalar.zero⟩

theorem sparse_gram_retains_arithmetic_failures :
    failedUnit ((compactSectorSpace excessiveMagnitude).run 2000) (.arithmetic .arithmeticCapacity) = true ∧
    failedUnit ((adaptiveWholeSpace excessiveMagnitude).run 2000) (.arithmetic .arithmeticCapacity) = true ∧
    failedUnit ((QleisliKernel.Finite.wholeSpace excessiveMagnitude).run 2000)
      (.arithmetic .arithmeticCapacity) = true := by
  decide +kernel

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
