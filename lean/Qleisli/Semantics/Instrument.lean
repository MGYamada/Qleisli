import QleisliKernel.Semantics.Preparation
import QleisliKernel.Semantics.Readout
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! Independent complex coefficient semantics for initialize/unitary/readout.
No acceptance checker, proof table, source producer or hierarchy module is
imported here. The middle operator is supplied as a phase-sensitive coefficient
function; a separate theorem must derive that function from actual IR.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.Instrument
open QleisliKernel.Semantics
open scoped BigOperators

abbrev Coordinates := Nat → Bool
abbrev Coefficient := List Bool → List Bool → ℂ
abbrev State (Reference : Type) := Coordinates → Reference → ℂ
abbrev Input (Reference : Type) := List Bool → Reference → ℂ
abbrev Transform (Reference : Type) := Input Reference → Coordinates → State Reference

/-- Enumerated basis coordinates follow the declared axis order. Other wire
labels are outside this finite state and receive an irrelevant false value. -/
def assignment (axes : List Nat) (bits : Fin axes.length → Bool) : Coordinates :=
  fun axis => (List.ofFn bits)[axes.idxOf axis]?.getD false

/-- The caller's state is read only on its declared old axes; newly allocated
axes and undeclared coordinates cannot influence the original input. -/
def liftInput {Reference : Type} (axes : List Nat) (input : Input Reference) : State Reference :=
  fun state reference => input (axes.map state) reference

/-- Full complex basis-column evolution. The reference coordinate is retained,
so input entanglement requires no product-state premise. -/
noncomputable def evolve {Reference : Type} (inputs outputs : List Nat)
    (operator : Coefficient) (input : State Reference) : State Reference :=
  fun state reference => ∑ basis : Fin inputs.length → Bool,
    operator (outputs.map state) (List.ofFn basis) *
      input (assignment inputs basis) reference

/-- Operational composition of actual zero factors, the full pure operator,
and sequential projective measurement. Sampling and normalization are later
execution operations, not part of the unnormalized branch. -/
noncomputable def execute {Reference : Type} (old fresh inputs outputs measured : List Nat)
    (operator : Coefficient) : Transform Reference :=
  fun input outcome => Readout.sequential measured outcome
    (evolve inputs outputs operator (Preparation.sequential fresh (liftInput old input)))

/-- Independent zero-factor/joint-selection meaning of the requested instrument. -/
noncomputable def specified {Reference : Type} (old fresh inputs outputs measured : List Nat)
    (operator : Coefficient) : Transform Reference :=
  fun input outcome => Readout.branch measured outcome
    (evolve inputs outputs operator (Preparation.zero fresh (liftInput old input)))

theorem execute_specified {Reference : Type} (old fresh inputs outputs measured : List Nat)
    (operator : Coefficient) :
    execute (Reference := Reference) old fresh inputs outputs measured operator =
      specified old fresh inputs outputs measured operator := by
  have prepared (input : Input Reference) :
      Preparation.sequential fresh (liftInput old input) =
        Preparation.zero fresh (liftInput old input) := by
    funext state reference
    exact Preparation.sequential_zero fresh (liftInput old input) state reference
  funext input outcome residual reference
  simp only [execute, specified, prepared, Readout.sequential_branch]

/-- The complete branch coefficient, useful as an independent oracle contract.
All input columns contribute, including their relative phases. -/
theorem specified_coefficient {Reference : Type} (old fresh inputs outputs measured : List Nat)
    (operator : Coefficient) (input : Input Reference) (outcome residual : Coordinates)
    (reference : Reference) :
    specified old fresh inputs outputs measured operator input outcome residual reference =
      ∑ basis : Fin inputs.length → Bool,
        operator (outputs.map (Readout.select measured outcome residual)) (List.ofFn basis) *
          (if fresh.all (fun axis => !assignment inputs basis axis) then
            input (old.map (assignment inputs basis)) reference else 0) := by
  rfl

/-- The public residual frame determines the output matrix rows. The transform
is evaluated on each exact input basis column; outcome bits are little endian. -/
noncomputable def branchMatrix (old residual : List Nat) (precision : Nat)
    (transform : Transform Unit) (outcome : Fin precision → Bool) :
    Matrix (Fin residual.length → Bool) (Fin old.length → Bool) ℂ :=
  fun output input => transform (fun label _ => if label = List.ofFn input then 1 else 0)
    (fun position => (List.ofFn outcome)[position]?.getD false)
    (assignment residual output) ()

/-- Tensor a rectangular branch operator with the unchanged reference. -/
noncomputable def withReference {I O Reference : Type} [DecidableEq Reference]
    (operator : Matrix O I ℂ) : Matrix (O × Reference) (I × Reference) ℂ :=
  fun output input => if output.2 = input.2 then operator output.1 input.1 else 0

/-- The full unnormalized residual/reference density matrix for one outcome;
off-diagonal entries are retained. Trace and sampling are separate operations. -/
noncomputable def density {I O Reference : Type} [Fintype I] [Fintype Reference]
    [DecidableEq Reference] (operator : Matrix O I ℂ)
    (input : Matrix (I × Reference) (I × Reference) ℂ) :
    Matrix (O × Reference) (O × Reference) ℂ :=
  withReference operator * input * (withReference operator).conjTranspose

end Qleisli.Semantics.Instrument
