import Qleisli.RuntimeTapeAction
import QPTL.FiniteMatrix

/-! Relate the actual native tape to the QPTL direct sum without computing
a joined matrix in the checker. The finite matrices here are denotations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeTapeAction
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.FiniteRestriction
open Qleisli.Semantics.RawAction
open Qleisli.RawFiniteRows (OnRows BoundedEvent)
open scoped Matrix

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      Finset.sum_range_succ,ih]

/-- A mathematical matrix of the literal tape. Its entries are specifications,
not values constructed or supplied to the executable checker. -/
noncomputable def tapeMatrix (dependencies : List Dependency) (bits : Nat) (tape : List Step) :
    Matrix (Fin (2^bits)) (Fin (2^bits)) ℂ :=
  fun row col => circuit dependencies tape (fun input => if input = col.val then 1 else 0) row.val

theorem tapeMatrix_mulVec (dependencies : List Dependency) (bits : Nat) (tape : List Step)
    (bounded : ∀ step ∈ tape, ∀ axis ∈ QleisliKernel.Finite.targets step.action, axis < bits)
    (values : Nat → ℂ) (row : Fin (2^bits)) :
    (tapeMatrix dependencies bits tape *ᵥ (fun col => values col.val)) row =
      circuit dependencies tape values row.val := by
  let columns := List.range (2^bits)
  let weighted := fun col input => (if input = col then (1 : ℂ) else 0) * values col
  let expanded := fun input => (columns.map (fun col => weighted col input)).sum
  have same : OnRows bits expanded values := by
    intro input inside
    have point (col : Nat) : weighted col input = if input = col then values col else 0 := by
      by_cases eq : input = col <;> simp [weighted,eq]
    change (columns.map fun col => weighted col input).sum = values input
    simp only [point,columns]
    exact Qleisli.Exact.range_delta_sum _ _ _ inside
  let term := fun col : Nat =>
    circuit dependencies tape (fun input => if input = col then 1 else 0) row.val * values col
  change (∑ col : Fin (2^bits), term col.val) = _
  rw [Fin.sum_univ_eq_sum_range term, ← range_sum]
  change (columns.map term).sum = _
  calc
    _ = (columns.map fun col => circuit dependencies tape (weighted col) row.val).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro col _
      exact (circuit_scale dependencies tape _ _ row.val).symm
    _ = circuit dependencies tape expanded row.val :=
      (circuit_sum dependencies tape columns weighted row.val).symm
    _ = _ := (BoundedEvent.circuit bits tape bounded).congr dependencies expanded values same row.val row.isLt

/-- The actual native tape matches the mathematical coherent direct sum on
every physical label and reference column. All label matches are required. -/
theorem program_directSum {Reference : Type} (dependencies : List Dependency) (selector target : Basis)
    (program : Semantics.Raw.Program) (tape : Raw.Sector.Tape)
    (binding : Raw.Sector.ForTapeBinding dependencies (.pair selector target) program tape)
    (bounded : ∀ step ∈ tape.steps, ∀ axis ∈ QleisliKernel.Finite.targets step.action,
      axis < width selector + width target)
    (arms : Fin (2^width selector) → List Step)
    (checked : ∀ label : Fin (2^width selector), TapeMatch (width selector) label.val tape.steps (arms label))
    (armBounds : ∀ label, ∀ step ∈ arms label, ∀ axis ∈ QleisliKernel.Finite.targets step.action,
      axis < width target)
    (joint : Nat → Reference → ℂ) (reference : Reference) :
    ∃ actual, Qleisli.Semantics.RawAction.program dependencies program (fun row => joint row reference) = some actual ∧
      ∀ (label : Fin (2^width selector)) (row : Fin (2^width target)),
        actual (pack (width selector) label.val row.val) =
          (Matrix.blockDiagonal' (fun label => tapeMatrix dependencies (width target) (arms label)) *ᵥ
            (fun input => joint (pack (width selector) input.1.val input.2.val) reference)) ⟨label,row⟩ := by
  obtain ⟨actual,read,_⟩ := program_tape dependencies (.pair selector target) program tape
    binding bounded (fun row => joint row reference)
  refine ⟨actual,read,?_⟩
  intro label row
  obtain ⟨selected,selectedRead,action⟩ := program_sector dependencies selector target program tape
    binding bounded (checked label) joint reference
  have same : selected = actual := Option.some.inj (selectedRead.symm.trans read)
  rw [← same,action row.val row.isLt,QPTL.FiniteMatrix.directSum_action]
  exact (tapeMatrix_mulVec dependencies (width target) (arms label) (armBounds label)
    (fun input => joint (pack (width selector) label.val input) reference) row).symm

/-- The original Bit selector fixes the two arm labels. The same native
tape and exact phase-sensitive direct sum used for qmatch also govern qif. -/
theorem program_qif_directSum {Reference : Type} (dependencies : List Dependency) (target : Basis)
    (program : Semantics.Raw.Program) (tape : Raw.Sector.Tape)
    (binding : Raw.Sector.ForTapeBinding dependencies (.pair [.bit] target) program tape)
    (bounded : ∀ step ∈ tape.steps, ∀ axis ∈ QleisliKernel.Finite.targets step.action,
      axis < 1 + width target)
    (zero one : List Step)
    (checkedZero : TapeMatch 1 0 tape.steps zero) (checkedOne : TapeMatch 1 1 tape.steps one)
    (armBounds : ∀ arm ∈ [zero,one], ∀ step ∈ arm, ∀ axis ∈ QleisliKernel.Finite.targets step.action,
      axis < width target)
    (joint : Nat → Reference → ℂ) (reference : Reference) :
    let arms := fun label : Fin 2 => if label.val = 0 then zero else one
    ∃ actual, Qleisli.Semantics.RawAction.program dependencies program (fun row => joint row reference) = some actual ∧
      ∀ (label : Fin 2) (row : Fin (2^width target)),
        actual (pack 1 label.val row.val) =
          (Matrix.blockDiagonal' (fun label => tapeMatrix dependencies (width target) (arms label)) *ᵥ
            (fun input => joint (pack 1 input.1.val input.2.val) reference)) ⟨label,row⟩ := by
  intro arms
  apply program_directSum dependencies [.bit] target program tape binding bounded arms _ _ joint reference
  · intro label
    change TapeMatch 1 label.val tape.steps (arms label)
    by_cases low : label.val = 0
    · simpa only [arms,low,if_true] using checkedZero
    · have high : label.val = 1 := by
        have small : label.val < 2 := label.isLt
        omega
      simpa only [arms,low,high,if_false] using checkedOne
  · intro label
    apply armBounds
    change (if label.val = 0 then zero else one) ∈ [zero,one]
    by_cases low : label.val = 0
    · rw [if_pos low]
      exact List.mem_cons_self
    · rw [if_neg low]
      exact List.mem_cons_of_mem _ List.mem_cons_self

#print axioms program_directSum
#print axioms program_qif_directSum
end Qleisli.RuntimeTapeAction
