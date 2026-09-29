import Qleisli.HierarchicalFiniteUnitary
import Qleisli.Interference
import Qleisli.Qft
import QleisliKernel.PhasePolynomial.Operations

/-! Exact diagonal laws for the hierarchy's actual complex operators.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
These proof-only matrix equalities justify sharing controlled phase gradients.
They neither execute dense matrices nor authorize a named Fourier schema. -/

namespace Qleisli.HierarchicalDiagonal
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalSemantics HierarchicalUnitary
open scoped BigOperators Matrix

/-- Dimensions and every complex coefficient, including global phase. -/
def At (n : Nat) (operator : Operator) (values : (Fin n → Bool) → ℂ) : Prop :=
  operator.inputWidth = n ∧ operator.outputWidth = n ∧
    matrixAt n n operator = Matrix.diagonal values

theorem identity_at (n : Nat) : At n (identity n) (fun _ => 1) := by
  exact ⟨rfl,rfl,by simp [matrix_identity]⟩

theorem compose_at {n : Nat} {first second : Operator} {a b : (Fin n → Bool) → ℂ}
    (ha : At n first a) (hb : At n second b) :
    At n (compose second first) (fun bits => b bits * a bits) := by
  refine ⟨ha.1,hb.2.1,?_⟩
  have h := matrix_compose second first
  rw [ha.1,hb.1,hb.2.1,ha.2.2,hb.2.2,Matrix.diagonal_mul_diagonal] at h
  exact h

theorem power_at {n : Nat} {child : Operator} {values : (Fin n → Bool) → ℂ}
    (h : At n child values) (count : Nat) :
    At n (power child count) (fun bits => values bits ^ count) := by
  refine ⟨by simpa [h.1] using power_input child count,
    by simpa [h.1] using power_output child count (h.2.1.trans h.1.symm),?_⟩
  rw [matrix_power child n count h.1 h.2.1,h.2.2,Matrix.diagonal_pow]
  rfl

theorem apply_power_at (interface : Interface) (n count : Nat) (child : Operator)
    (values : (Fin n → Bool) → ℂ)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (ready : At n child values) :
    At n (apply interface (.power count) [child]) (fun bits => values bits ^ count) := by
  refine ⟨hi,ho,?_⟩
  have same : matrixAt n n (apply interface (.power count) [child]) =
      matrixAt n n (power child count) := by
    ext output input
    simp [matrixAt,apply,bounded,raw,hi,ho]
  rw [same]
  exact (power_at ready count).2.2

theorem phase_at (interface : Interface) (n owner j k : Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n) :
    At n (apply interface (.phase owner j k) []) (fun input =>
      if (List.ofFn input)[ownerAxis interface owner]?.getD false then phase j k else 1) := by
  refine ⟨hi,ho,?_⟩
  ext output input
  simp [matrixAt,apply,bounded,raw,hi,ho,Matrix.diagonal_apply,List.ofFn_inj]
  split <;> simp_all

theorem tensor_at (interface : Interface) (m n : Nat) (first second : Operator)
    (a : (Fin m → Bool) → ℂ) (b : (Fin n → Bool) → ℂ)
    (hi : width interface.inputs = m+n) (ho : width interface.outputs = m+n)
    (ha : At m first a) (hb : At n second b) :
    At (m+n) (apply interface .tensor [first,second])
      (fun bits => a (splitEquiv m n bits).1 * b (splitEquiv m n bits).2) := by
  refine ⟨hi,ho,?_⟩
  have matrix : matrixAt (m+n) (m+n) (apply interface .tensor [first,second]) =
      (Matrix.kronecker (matrixAt m m first) (matrixAt n n second)).submatrix
        (splitEquiv m n) (splitEquiv m n) := by
    ext output input
    simp only [matrixAt,apply,bounded,raw,hi,ho,List.length_ofFn,and_self,ite_true,
      ha.1,ha.2.1]
    rw [split_list m n output,split_list m n input]
    simp [Matrix.submatrix,Matrix.kronecker,Matrix.kroneckerMap,matrixAt]
  rw [matrix,ha.2.2,hb.2.2]
  change (Matrix.kroneckerMap (· * ·) (Matrix.diagonal a) (Matrix.diagonal b)).submatrix
    (splitEquiv m n) (splitEquiv m n) = _
  rw [Matrix.diagonal_kronecker_diagonal]
  ext output input
  simp [Matrix.submatrix,Matrix.diagonal_apply]

theorem control_at (interface : Interface) (n : Nat) (polarity : Bool) (child : Operator)
    (values : (Fin n → Bool) → ℂ)
    (hi : width interface.inputs = n+1) (ho : width interface.outputs = n+1)
    (ready : At n child values) :
    At (n+1) (apply interface (.control polarity) [child])
      (fun bits => if bits 0 = polarity then values (fun i => bits i.succ) else 1) := by
  refine ⟨hi,ho,?_⟩
  ext output input
  have childMatrix := congrFun (congrFun ready.2.2 (fun i => output i.succ)) (fun i => input i.succ)
  simp only [matrixAt] at childMatrix
  simp only [matrixAt,apply,bounded,raw,hi,ho,
    List.ofFn_succ,List.head?_cons,List.tail_cons,Option.some.injEq,childMatrix,
    Matrix.diagonal_apply,List.ofFn_inj]
  by_cases same : output = input
  · subst output
    simp
  · have differing : output 0 ≠ input 0 ∨
        (fun i : Fin n => output i.succ) ≠ (fun i : Fin n => input i.succ) := by
      by_contra h
      simp only [not_or,not_not] at h
      apply same
      funext i
      refine Fin.cases h.1 (fun j => congrFun h.2 j) i
    rcases differing with head | tail <;> simp_all

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Consume the actual forward data permutation and its actual inverse.
The phase is pulled back along the route; it is never discarded. -/
theorem conjugate_diagonal (route : I ≃ I) (values : I → ℂ) :
    permutation route.symm * Matrix.diagonal values * permutation route =
      Matrix.diagonal (fun input => values (route input)) := by
  ext output input
  simp [Matrix.mul_apply,permutation,Matrix.diagonal_apply,eq_comm]
  split <;> simp_all

theorem rewire_matrix (interface : Interface) (n : Nat) (forward backward : List Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (routing : QleisliKernel.Layout.Permutation n forward backward) :
    matrixAt n n (apply interface (.rewire forward) []) = permutation (axisEquiv routing) := by
  ext output input
  simp only [matrixAt,apply,bounded,raw,hi,ho,List.length_ofFn,and_self,ite_true]
  rw [← axisEquiv_list routing]
  simp [permutation,List.ofFn_inj]

theorem routed_at (before after : Interface) (n : Nat) (forward backward : List Nat)
    (routing : QleisliKernel.Layout.Permutation n forward backward)
    (bi : width before.inputs = n) (bo : width before.outputs = n)
    (ai : width after.inputs = n) (ao : width after.outputs = n)
    (child : Operator) (values : (Fin n → Bool) → ℂ) (ready : At n child values) :
    At n (compose (apply after (.rewire backward) [])
      (compose child (apply before (.rewire forward) [])))
      (fun bits => values (axisEquiv routing bits)) := by
  have inverse : QleisliKernel.Layout.Permutation n backward forward := by
    refine ⟨routing.2.1,routing.1,?_⟩
    intro i
    exact ⟨(routing.2.2 i).2.1,(routing.2.2 i).1,
      (routing.2.2 i).2.2.2,(routing.2.2 i).2.2.1⟩
  have same : axisEquiv inverse = (axisEquiv routing).symm := by
    apply Equiv.ext
    intro bits
    rfl
  refine ⟨bi,ao,?_⟩
  have first := matrix_compose child (apply before (.rewire forward) [])
  change matrixAt (width before.inputs) child.outputWidth
    (compose child (apply before (.rewire forward) [])) =
      matrixAt child.inputWidth child.outputWidth child *
        matrixAt (width before.inputs) child.inputWidth (apply before (.rewire forward) []) at first
  rw [bi,ready.1,ready.2.1,ready.2.2,rewire_matrix before n forward backward bi bo routing] at first
  have last := matrix_compose (apply after (.rewire backward) [])
    (compose child (apply before (.rewire forward) []))
  change matrixAt (width before.inputs) (width after.outputs) _ =
    matrixAt (width after.inputs) (width after.outputs) _ *
      matrixAt (width before.inputs) (width after.inputs) _ at last
  rw [bi,ai,ao,first,rewire_matrix after n backward forward ai ao inverse,same] at last
  rw [last,← Matrix.mul_assoc,conjugate_diagonal]

theorem phase_power (j precision count : Nat) :
    phase j precision ^ count = phase (j*count) precision := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Lower a dyadic precision through the actual repeated operator, retaining
its absolute phase. Natural subtraction is used only under the stated bound. -/
theorem phase_precision (j precision width : Nat) (enough : width ≤ precision) :
    phase j precision ^ (2^(precision-width)) = phase j width := by
  rw [phase_power]
  unfold phase
  congr 1
  have denominator : (2 : ℂ)^precision = (2 : ℂ)^width * (2 : ℂ)^(precision-width) := by
    rw [← pow_add,Nat.add_sub_of_le enough]
  push_cast
  rw [denominator]
  field_simp

/-- Exact symbolic coefficients describe the actual powered matrix. Counts
may be zero, and terms may cancel modulo 256; neither case skips the child. -/
theorem sparse_power_at (interface : Interface) (n count : Nat) (child : Operator)
    (terms : QleisliKernel.PhasePolynomial.Polynomial)
    (coordinates : (Fin n → Bool) → (Nat → Bool))
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (ready : At n child (fun bits => Interference.complexModel.root ^
      QleisliKernel.PhasePolynomial.evaluate terms (coordinates bits))) :
    At n (apply interface (.power count) [child])
      (fun bits => Interference.complexModel.root ^ QleisliKernel.PhasePolynomial.evaluate
        (QleisliKernel.PhasePolynomial.scale count terms) (coordinates bits)) := by
  have repeated := apply_power_at interface n count child _ hi ho ready
  have equal : (fun bits => (Interference.complexModel.root ^
        QleisliKernel.PhasePolynomial.evaluate terms (coordinates bits)) ^ count) =
      (fun bits => Interference.complexModel.root ^ QleisliKernel.PhasePolynomial.evaluate
        (QleisliKernel.PhasePolynomial.scale count terms) (coordinates bits)) := by
    funext bits
    rw [QleisliKernel.PhasePolynomial.scale_sound,← pow_mul]
    exact pow_eq_pow_mod _ Interference.complexModel.root_period
  rw [equal] at repeated
  exact repeated

theorem shifted_finiteBits (n : Nat) (bits : Fin (n+1) → Bool) :
    (Qft.finiteBits bits ∘ (fun i => i+1)) =
      Qft.finiteBits (fun i : Fin n => bits i.succ) := by
  funext i
  by_cases inside : i < n
  · have shifted : i+1 < n+1 := by omega
    simp [Qft.finiteBits,inside,shifted]
  · have shifted : ¬ i+1 < n+1 := by omega
    simp [Qft.finiteBits,inside,shifted]

/-- A separate low control axis shifts every child coordinate. The complete
complex diagonal follows from the sparse terms, including constant phases. -/
theorem sparse_control_at (interface : Interface) (n : Nat) (child : Operator)
    (terms : QleisliKernel.PhasePolynomial.Polynomial)
    (hi : width interface.inputs = n+1) (ho : width interface.outputs = n+1)
    (ready : At n child (fun bits => Interference.complexModel.root ^
      QleisliKernel.PhasePolynomial.evaluate terms (Qft.finiteBits bits))) :
    At (n+1) (apply interface (.control true) [child])
      (fun bits => Interference.complexModel.root ^ QleisliKernel.PhasePolynomial.evaluate
        (QleisliKernel.PhasePolynomial.controlTrue 0
          (QleisliKernel.PhasePolynomial.remap (fun i => i+1) terms)) (Qft.finiteBits bits)) := by
  have controlled := control_at interface n true child _ hi ho ready
  have equal : (fun bits : Fin (n+1) → Bool => if bits 0 = true then
        Interference.complexModel.root ^ QleisliKernel.PhasePolynomial.evaluate terms
          (Qft.finiteBits (fun i => bits i.succ)) else 1) =
      (fun bits => Interference.complexModel.root ^ QleisliKernel.PhasePolynomial.evaluate
        (QleisliKernel.PhasePolynomial.controlTrue 0
          (QleisliKernel.PhasePolynomial.remap (fun i => i+1) terms)) (Qft.finiteBits bits)) := by
    funext bits
    rw [QleisliKernel.PhasePolynomial.controlTrue_sound,QleisliKernel.PhasePolynomial.remap_sound,
      shifted_finiteBits]
    have first : Qft.finiteBits bits 0 = bits 0 := by simp [Qft.finiteBits]
    rw [first]
    cases bits 0 <;> simp
  rw [equal] at controlled
  exact controlled

theorem sparse_controlled_power_at (powered controlled : Interface) (n count : Nat)
    (child : Operator) (terms : QleisliKernel.PhasePolynomial.Polynomial)
    (hi : width powered.inputs = n) (ho : width powered.outputs = n)
    (ci : width controlled.inputs = n+1) (co : width controlled.outputs = n+1)
    (ready : At n child (fun bits => Interference.complexModel.root ^
      QleisliKernel.PhasePolynomial.evaluate terms (Qft.finiteBits bits))) :
    At (n+1) (apply controlled (.control true) [apply powered (.power count) [child]])
      (fun bits => Interference.complexModel.root ^ QleisliKernel.PhasePolynomial.evaluate
        (QleisliKernel.PhasePolynomial.controlTrue 0
          (QleisliKernel.PhasePolynomial.remap (fun i => i+1)
            (QleisliKernel.PhasePolynomial.scale count terms))) (Qft.finiteBits bits)) :=
  sparse_control_at controlled n _ _ ci co
    (sparse_power_at powered n count child terms Qft.finiteBits hi ho ready)

theorem controlled_gradient (powered controlled : Interface) (n precision : Nat)
    (child : Operator) (value : (Fin n → Bool) → Nat)
    (hi : width powered.inputs = n) (ho : width powered.outputs = n)
    (ci : width controlled.inputs = n+1) (co : width controlled.outputs = n+1)
    (enough : n+1 ≤ precision)
    (gradient : At n child (fun bits => phase (value bits) precision)) :
    At (n+1) (apply controlled (.control true)
      [apply powered (.power (2^(precision-(n+1)))) [child]])
      (fun bits => if bits 0 = true then phase (value (fun i => bits i.succ)) (n+1) else 1) := by
  have repeated := apply_power_at powered n (2^(precision-(n+1))) child _ hi ho gradient
  have phases : (fun bits => phase (value bits) precision ^ (2^(precision-(n+1)))) =
      (fun bits => phase (value bits) (n+1)) :=
    funext (fun bits => phase_precision (value bits) precision (n+1) enough)
  rw [phases] at repeated
  exact control_at controlled n true _ _ ci co repeated

/-- Read the actual repeated/controlled bodies and the actual gradient value.
No proposed whole-graph environment or matrix receipt enters this theorem.
The remaining premise is precisely the diagonal meaning of that child. -/
theorem physical_controlled_gradient
    (leaves : HierarchicalFiniteEvaluation.Leaves Operator) (artifact : Artifact)
    (root repeated child fuel n precision : Nat) (controlled powered : Definition)
    (gradient : Operator) (value : (Fin n → Bool) → Nat)
    (hc : artifact.definitions[root]? = some controlled)
    (hcb : controlled.body = .control repeated true)
    (hp : artifact.definitions[repeated]? = some powered)
    (hpb : powered.body = .repeatOp (2^(precision-(n+1))) child)
    (evaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel child = some gradient)
    (hi : width powered.interface.inputs = n) (ho : width powered.interface.outputs = n)
    (ci : width controlled.interface.inputs = n+1) (co : width controlled.interface.outputs = n+1)
    (enough : n+1 ≤ precision)
    (diagonal : At n gradient (fun bits => phase (value bits) precision)) :
    ∃ actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+2) root = some actual ∧
      At (n+1) actual
        (fun bits => if bits 0 = true then phase (value (fun i => bits i.succ)) (n+1) else 1) := by
  have pcode : physicalCode powered = some (.power (2^(precision-(n+1))),[child]) := by
    simp [physicalCode,hpb]
  have ccode : physicalCode controlled = some (.control true,[repeated]) := by
    simp [physicalCode,hcb]
  have peval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact fuel repeated
    powered _ [child] hp pcode
  simp only [List.mapM_cons,List.mapM_nil,evaluated,bind,Option.bind,pure] at peval
  have ceval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1) root
    controlled _ [repeated] hc ccode
  simp only [List.mapM_cons,List.mapM_nil,peval,bind,Option.bind,pure] at ceval
  exact ⟨_,ceval,controlled_gradient powered.interface controlled.interface n precision
    gradient value hi ho ci co enough diagonal⟩

/-- Arbitrary reference columns, with no separability assumption. -/
theorem joint_amplitude {n : Nat} {operator : Operator} {values : (Fin n → Bool) → ℂ}
    (h : At n operator values) {R : Type}
    (joint : (Fin n → Bool) → R → ℂ) (output : Fin n → Bool) (reference : R) :
    (∑ input, (matrixAt n n operator) output input * joint input reference) =
      values output * joint output reference := by
  rw [h.2.2]
  simp [Matrix.diagonal_apply]

end Qleisli.HierarchicalDiagonal
