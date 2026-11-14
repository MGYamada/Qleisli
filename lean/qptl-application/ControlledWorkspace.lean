import RuntimeWorkspaceRestoration
import Qleisli.RuntimeTapeAction

/-! The checked zero and one restrictions on the original tape lift exact
clean return to a coherent control. The low axis is the control and the
workspace's high scratch axis starts at zero.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeWorkspaceRestoration

open QleisliKernel QleisliKernel.FiniteRestriction
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite Qleisli.Semantics.Exact

/-- A checked clean body can be used on the one sector of an independently
matched original Raw tape. The zero sector is checked against the empty tape,
and the one sector retains the literal body, including its scalar phase.
Every conclusion holds on the same output for arbitrary joint amplitudes of
the control, data and external reference. -/
theorem controlled_clean_action {R : Type} {deps : List Dependency}
    {bits work left : Nat} {steps : List Step} {logical physical : Matrix}
    (clean : (Raw.Workspace.check deps false bits steps logical).run work = (.ok physical,left))
    {program : Semantics.Raw.Program} {tape : Raw.Sector.Tape}
    (binding : Raw.Sector.ForTapeBinding deps (.pair [.bit] [.bits (bits+1)]) program tape)
    (bounded : ∀ step ∈ tape.steps, ∀ axis ∈ Finite.targets step.action, axis < 1 + (bits+1))
    (zero : TapeMatch 1 0 tape.steps []) (one : TapeMatch 1 1 tape.steps steps)
    (joint : Nat → R → ℂ) (reference : R) :
    let padded := fun input ref => if input / 2 < 2^bits then joint input ref else 0
    ∃ actual, Semantics.RawAction.program deps program (fun input => padded input reference) = some actual ∧
      (∀ row, row < 2^(bits+1) →
        actual (pack 1 0 row) = if row < 2^bits then joint (pack 1 0 row) reference else 0) ∧
      (∀ row, row < 2^(bits+1) →
        actual (pack 1 1 row) =
          if row < 2^bits then action logical (fun col ref => joint (pack 1 1 col) ref) row reference else 0) := by
  intro padded
  have targetBounds : ∀ step ∈ tape.steps, ∀ axis ∈ Finite.targets step.action,
      axis < width [.bit] + width [.bits (bits+1)] := bounded
  obtain ⟨actual,read,off⟩ := Qleisli.RuntimeTapeAction.program_sector deps [.bit] [.bits (bits+1)]
    program tape binding targetBounds zero padded reference
  obtain ⟨onResult,onRead,on⟩ := Qleisli.RuntimeTapeAction.program_sector deps [.bit] [.bits (bits+1)]
    program tape binding targetBounds one padded reference
  have same : onResult = actual := Option.some.inj (onRead.symm.trans read)
  have unpackZero (row : Nat) : pack 1 0 row / 2 = row := by
    simp [pack]
  have unpackOne (row : Nat) : pack 1 1 row / 2 = row := by
    simp only [pack,Nat.pow_one]
    omega
  have controlWidth : width [.bit] = 1 := rfl
  rw [controlWidth] at off on
  refine ⟨actual,read,?_,?_⟩
  · intro row inside
    simpa only [Semantics.RawAction.circuit,List.foldl_nil,padded,unpackZero] using off row inside
  · intro row inside
    have selected := on row inside
    rw [same] at selected
    simp only [padded,unpackOne] at selected
    exact selected.trans (clean_action clean (fun col ref => joint (pack 1 1 col) ref) row reference inside)

#print axioms controlled_clean_action
end Qleisli.RuntimeWorkspaceRestoration
