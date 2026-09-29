import Qleisli.HierarchicalSemantics
import Qleisli.HierarchicalPower

/-! Finite complex interpretation of supported hierarchical bodies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This mathematical interpretation is not executed by the checker. Its sums and
iterations are not an implementation of verification or its resource budget. -/

namespace Qleisli.HierarchicalOperators
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics
open scoped BigOperators Matrix

abbrev Bits := List Bool

/-- The first list element is the least significant, first declared axis.
Values outside the recorded widths have zero coefficients. -/
structure Operator where
  inputWidth : Nat
  outputWidth : Nat
  coefficient : Bits → Bits → ℂ

def width (side : Side) : Nat := (wires side).size

noncomputable def bounded (inputWidth outputWidth : Nat) (f : Bits → Bits → ℂ) : Operator :=
  ⟨inputWidth,outputWidth,fun output input =>
    if output.length = outputWidth ∧ input.length = inputWidth then f output input else 0⟩

noncomputable def identity (n : Nat) : Operator :=
  bounded n n fun output input => if output = input then 1 else 0

/-- Execution order: `before`, then `after`. The intermediate summation is over
the complete basis, not basis probabilities or diagonal density entries. -/
noncomputable def compose (after before : Operator) : Operator :=
  bounded before.inputWidth after.outputWidth fun output input =>
    ∑ middle : Fin after.inputWidth → Bool,
      after.coefficient output (List.ofFn middle) * before.coefficient (List.ofFn middle) input

noncomputable def sequence (inputWidth : Nat) (children : List Operator) : Operator :=
  children.foldl (fun current next => compose next current) (identity inputWidth)

noncomputable def power (child : Operator) (count : Nat) : Operator :=
  Nat.rec (identity child.inputWidth) (fun _ previous => compose child previous) count

def ownerAxis (interface : Interface) (owner : Nat) : Nat :=
  (interface.inputs.quantum.toList.takeWhile (fun port => port.owner != owner)).foldl
    (fun n port => n + port.axes.size) 0

/-- Ideal positive dyadic phase; in particular no quotient by global phase. -/
noncomputable def phase (j k : Nat) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (2 : ℂ)^k)

noncomputable def raw (interface : Interface) : Tag → List Operator → Bits → Bits → ℂ
  | .identity, [] => fun output input => if output = input then 1 else 0
  | .rewire axes, [] => fun output input =>
      if output = axes.map (fun i => input[i]?.getD false) then 1 else 0
  | .phase owner j k, [] => fun output input =>
      if output = input then
        if input[ownerAxis interface owner]?.getD false then phase j k else 1
      else 0
  | .sequence, children => (sequence (width interface.inputs) children).coefficient
  | .tensor, [first,second] => fun output input =>
      first.coefficient (output.take first.outputWidth) (input.take first.inputWidth) *
        second.coefficient (output.drop first.outputWidth) (input.drop first.inputWidth)
  | .inverse, [child] => fun output input => star (child.coefficient input output)
  | .control polarity, [child] => fun output input =>
      if output.head? = input.head? then
        if input.head? = some polarity then child.coefficient output.tail input.tail
        else if output.tail = input.tail then 1 else 0
      else 0
  | .power count, [child] => (power child count).coefficient
  | _, _ => fun _ _ => 0

noncomputable def apply (interface : Interface) (tag : Tag) (children : List Operator) : Operator :=
  bounded (width interface.inputs) (width interface.outputs) (raw interface tag children)

theorem range_select (input : Bits) :
    (List.range input.length).map (fun i => input[i]?.getD false) = input := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [List.getElem?_eq_getElem right]

theorem identity_rewire (interface : Interface) (map : PortMap)
    (accepted : Rule.identityMap interface map = true) :
    apply interface (.rewire map.axes.toList) [] = apply interface .identity [] := by
  have axes : map.axes = Array.range (width interface.inputs) := by
    simp only [Rule.identityMap,Bool.and_eq_true,beq_iff_eq] at accepted
    exact accepted.1.2
  unfold apply bounded
  congr 1
  funext output input
  split
  next sizes =>
    have selected : map.axes.toList.map (fun i => input[i]?.getD false) = input := by
      simpa [axes,← sizes.2] using range_select input
    simp [raw,selected]
  next => rfl

noncomputable def algebra : Algebra Operator := ⟨apply,identity_rewire⟩

/-- Finite matrix extraction keeps the phase of every complex coefficient.
The `Fin n → Bool` basis is little endian, as in `Qpe.bitEquiv`. -/
noncomputable def matrix (operator : Operator) :
    Matrix (Fin operator.outputWidth → Bool) (Fin operator.inputWidth → Bool) ℂ :=
  fun output input => operator.coefficient (List.ofFn output) (List.ofFn input)

/-- Fixed-width extraction is useful when the table's full interface is already
bound. No dimension equality is used as a substitute for that type check. -/
noncomputable def matrixAt (inputWidth outputWidth : Nat) (operator : Operator) :
    Matrix (Fin outputWidth → Bool) (Fin inputWidth → Bool) ℂ :=
  fun output input => operator.coefficient (List.ofFn output) (List.ofFn input)

/-- Rectangular extension of the same joint-map convention used by QPE. -/
noncomputable def referenceMap {I O R : Type} [Fintype I] [Fintype O] [Fintype R] [DecidableEq R]
    (U : Matrix O I ℂ) (rho : Matrix (I × R) (I × R) ℂ) : Matrix (O × R) (O × R) ℂ :=
  let joint := Matrix.kronecker U (1 : Matrix R R ℂ)
  joint * rho * jointᴴ

theorem matrix_compose (after before : Operator) :
    matrixAt before.inputWidth after.outputWidth (compose after before) =
      matrixAt after.inputWidth after.outputWidth after *
        matrixAt before.inputWidth after.inputWidth before := by
  ext output input
  simp [matrixAt,compose,bounded,Matrix.mul_apply]

theorem power_input (child : Operator) (count : Nat) :
    (power child count).inputWidth = child.inputWidth := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

theorem matrix_identity (n : Nat) : matrixAt n n (identity n) = 1 := by
  ext output input
  simp [matrixAt,identity,bounded,Matrix.one_apply,List.ofFn_inj]

/-- Literal operator repetition agrees with independently specified finite
matrix exponentiation. Counts are not replaced by an oracle-use estimate. -/
theorem matrix_power (child : Operator) (n count : Nat)
    (hi : child.inputWidth = n) (ho : child.outputWidth = n) :
    matrixAt n n (power child count) = (matrixAt n n child)^count := by
  induction count with
  | zero => simpa only [power,hi,pow_zero] using matrix_identity n
  | succ count ih =>
    have composed := matrix_compose child (power child count)
    rw [power_input,hi,ho,ih] at composed
    change matrixAt n n (compose child (power child count)) = _
    simpa only [pow_succ'] using composed

namespace Examples

def bitsInterface (n : Nat) : Interface :=
  let side : Side := ⟨#[⟨0,#[.bits n],Array.range n⟩],#[]⟩
  ⟨side,side⟩

def bitInterface : Interface :=
  let side : Side := ⟨#[⟨0,#[.bit],#[0]⟩],#[]⟩
  ⟨side,side⟩

noncomputable def phaseBit (j k : Nat) : Operator := apply bitInterface (.phase 0 j k) []

theorem three_axis_orientation :
    (apply (bitsInterface 3) (.rewire [2,0,1]) []).coefficient
      [false,true,false] [true,false,false] = 1 ∧
    (apply (bitsInterface 3) (.rewire [2,0,1]) []).coefficient
      [false,false,true] [true,false,false] = 0 := by
  norm_num [apply,bounded,raw,bitsInterface,width,wires]

theorem selected_phase (j k : Nat) :
    (phaseBit j k).coefficient [true] [true] = phase j k ∧
    (phaseBit j k).coefficient [false] [false] = 1 ∧
    (phaseBit j k).coefficient [false] [true] = 0 := by
  simp [phaseBit,apply,bounded,raw,bitInterface,width,wires,ownerAxis]

theorem tensor_low_axes (j k : Nat) :
    (apply (bitsInterface 2) .tensor [identity 1,phaseBit j k]).coefficient
      [false,true] [false,true] = phase j k ∧
    (apply (bitsInterface 2) .tensor [identity 1,phaseBit j k]).coefficient
      [true,false] [true,false] = 1 := by
  simp [apply,bounded,raw,bitsInterface,width,wires,identity,phaseBit,bitInterface,ownerAxis]

theorem inverse_phase (j k : Nat) :
    (apply bitInterface .inverse [phaseBit j k]).coefficient [true] [true] = star (phase j k) := by
  simp [apply,bounded,raw,bitInterface,width,wires,phaseBit,ownerAxis]

theorem coherent_control (j k : Nat) :
    (apply (bitsInterface 2) (.control true) [phaseBit j k]).coefficient
      [true,true] [true,true] = phase j k ∧
    (apply (bitsInterface 2) (.control true) [phaseBit j k]).coefficient
      [false,true] [false,true] = 1 ∧
    (apply (bitsInterface 2) (.control true) [phaseBit j k]).coefficient
      [false,true] [true,true] = 0 := by
  simp [apply,bounded,raw,bitsInterface,width,wires,phaseBit,bitInterface,ownerAxis]

/-- A provider's global sign becomes a relative phase under coherent control. -/
theorem controlled_sign_visible :
    let minusIdentity := bounded 1 1 (fun output input => if output = input then (-1 : ℂ) else 0)
    (apply (bitsInterface 2) (.control true) [minusIdentity]).coefficient
      [true,false] [true,false] = -1 ∧
    (apply (bitsInterface 2) (.control true) [minusIdentity]).coefficient
      [false,false] [false,false] = 1 ∧ (-1 : ℂ) ≠ 1 := by
  norm_num [apply,bounded,raw,bitsInterface,width,wires]

end Examples

/-- temporary (TP-001): use `HierarchicalEvaluation.checkAll_operator` with
constructed denotations. Retire after callers migrate and public-API review. -/
theorem checkAll_operator (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (operations meanings : Nat → Operator) (environment : Interprets algebra artifact operations meanings)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof) :
    operations proof.implementation = meanings proof.meaning :=
  HierarchicalSemantics.checkAll_sound algebra artifact order checked accepted operations meanings environment proof found

/-- temporary (TP-001): use `HierarchicalEvaluation.checkAll_matrix` with
constructed denotations. Retire after callers migrate and public-API review. -/
theorem checkAll_matrix (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (operations meanings : Nat → Operator) (environment : Interprets algebra artifact operations meanings)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (inputWidth outputWidth : Nat) :
    matrixAt inputWidth outputWidth (operations proof.implementation) =
      matrixAt inputWidth outputWidth (meanings proof.meaning) := by
  rw [checkAll_operator artifact order checked accepted operations meanings environment proof found]

/-- temporary (TP-001): retire this environment-based entry bridge after
its independently requested power conclusion uses constructed denotations and
public-API compatibility is reviewed. The provider equation formerly assumed by the direct controlled-power
bridge now follows from the actual accepted premise derivation. Interpretation
of actual bodies remains explicit; provider unitarity is a separate theorem. -/
theorem powerEntry_operators (artifact : Artifact) (order : Array Nat) (exponent provider : Nat)
    (checked : Derivation.PowerChecked)
    (accepted : Derivation.powerEntry artifact order exponent provider = .ok checked)
    (operations meanings : Nat → Operator) (environment : Interprets algebra artifact operations meanings)
    (n : Nat) :
    HierarchicalPower.implementationOperator artifact checked.projection.root.implementation
      (fun index => matrixAt n n (operations index)) =
      some (ControlledPowers.controlled ((matrixAt n n (meanings checked.projection.logical.provider))^(2^exponent))) ∧
    HierarchicalPower.meaningOperator artifact checked.projection.root.meaning
      (fun index => matrixAt n n (meanings index)) =
      some (ControlledPowers.controlled ((matrixAt n n (meanings checked.projection.logical.provider))^(2^exponent))) := by
  obtain ⟨derived,_,inspected⟩ := Derivation.powerEntry_provider artifact order exponent provider checked accepted
  have found := (Power.inspect_binding artifact artifact.entry.proof exponent provider _ checked.projection inspected).2.2.1
  have equation := HierarchicalSemantics.derives_sound algebra artifact operations meanings environment
    checked.projection.providerProofIndex derived checked.projection.providerProof found
  exact HierarchicalPower.inspect_operators artifact artifact.entry.proof exponent provider _ checked.projection
    inspected (fun index => matrixAt n n (operations index)) (fun index => matrixAt n n (meanings index))
    (congrArg (matrixAt n n) equation)

/-- temporary (TP-001): use `HierarchicalEvaluation.checkAll_reference`;
retire after callers migrate and public-API review. The entire joint output agrees for every reference system and input matrix,
including off-diagonal coherences. No separability premise is imposed. -/
theorem checkAll_reference {R : Type} [Fintype R] [DecidableEq R]
    (artifact : Artifact) (order : Array Nat)
    (checked : Derivation.Checked) (accepted : Derivation.checkAll artifact order = .ok checked)
    (operations meanings : Nat → Operator) (environment : Interprets algebra artifact operations meanings)
    (proof : Proof) (found : artifact.proofs[artifact.entry.proof]? = some proof)
    (inputWidth outputWidth : Nat)
    (rho : Matrix ((Fin inputWidth → Bool) × R) ((Fin inputWidth → Bool) × R) ℂ) :
    referenceMap (matrixAt inputWidth outputWidth (operations proof.implementation)) rho =
      referenceMap (matrixAt inputWidth outputWidth (meanings proof.meaning)) rho := by
  rw [checkAll_matrix artifact order checked accepted operations meanings environment proof found inputWidth outputWidth]

end Qleisli.HierarchicalOperators
