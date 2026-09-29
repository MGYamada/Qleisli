import Qleisli.HierarchicalGradient

/-! Fourier coefficients of the hierarchy's actual recursive QFT stages.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The target is defined independently from little-endian integer labels. Matrix
identities are proof-only and retain all phases and reference amplitudes. -/

namespace Qleisli.HierarchicalFourier
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalUnitary
open HierarchicalDiagonal HierarchicalGradient
open scoped BigOperators Matrix

theorem number_sum (n : Nat) (bits : Fin n → Bool) :
    number n bits = ∑ i : Fin n, if bits i then 2^i.val else 0 := by
  induction n with
  | zero => simp [number]
  | succ n ih =>
    rw [number,ih,Fin.sum_univ_castSucc]
    rfl

theorem number_head (n : Nat) (bits : Fin (n+1) → Bool) :
    number (n+1) bits = (if bits 0 then 1 else 0) +
      2 * number n (fun i => bits i.succ) := by
  rw [number_sum,Fin.sum_univ_succ,number_sum,Finset.mul_sum]
  simp only [Fin.val_zero,pow_zero,Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases bits i.succ <;> simp [pow_succ,Nat.mul_comm]

def reverseBits {n : Nat} (bits : Fin n → Bool) : Fin n → Bool := fun i => bits i.rev

theorem reverse_twice {n : Nat} (bits : Fin n → Bool) : reverseBits (reverseBits bits) = bits := by
  funext i
  simp [reverseBits]

theorem reverse_number_succ (n : Nat) (bits : Fin (n+1) → Bool) :
    number (n+1) (reverseBits bits) = (if bits (Fin.last n) then 1 else 0) +
      2 * number n (reverseBits (fun i => bits i.castSucc)) := by
  rw [number_head]
  simp only [reverseBits,Fin.rev_zero,Fin.rev_succ]
  rfl

theorem number_value (n : Nat) (bits : Fin n → Bool) :
    number n bits = Qft.value n (Qft.finiteBits bits) := by
  rw [number_sum,Qft.value,← Fin.sum_univ_eq_sum_range]
  simp [Qft.finiteBits]

theorem phase_zero (n : Nat) : phase 0 n = 1 := by simp [phase]

theorem phase_period (n : Nat) : phase (2^n) n = 1 := by
  unfold phase
  push_cast
  rw [mul_div_cancel_right₀ _ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  exact Complex.exp_two_pi_mul_I

theorem phase_multiple (n k : Nat) : phase (2^n*k) n = 1 := by
  rw [← phase_power,phase_period,one_pow]

theorem phase_double (n a : Nat) : phase (2*a) (n+1) = phase a n := by
  have h := phase_precision a (n+1) n (by omega)
  rw [phase_power] at h
  simpa [Nat.mul_comm] using h

theorem phase_half (n : Nat) : phase (2^n) (n+1) = -1 := by
  unfold phase
  push_cast
  have same : 2 * (Real.pi : ℂ) * Complex.I * 2^n / 2^(n+1) = Real.pi * Complex.I := by
    rw [pow_succ]
    field_simp
  rw [same,Complex.exp_pi_mul_I]

/-- The three factors in a recursive QFT stage, including the H sign. -/
theorem phase_stage (n x z : Nat) (inputHigh outputHigh : Bool) :
    (if inputHigh && outputHigh then (-1 : ℂ) else 1) *
      (if outputHigh then phase x (n+1) else 1) * phase (x*z) n =
    phase ((x + if inputHigh then 2^n else 0) *
      ((if outputHigh then 1 else 0) + 2*z)) (n+1) := by
  cases inputHigh <;> cases outputHigh
  · simp only [Bool.false_and,Bool.false_eq_true,ite_false,Nat.add_zero,one_mul,zero_add]
    rw [show x*(2*z) = 2*(x*z) by ring,phase_double]
  · simp only [Bool.false_and,Bool.false_eq_true,ite_true,ite_false,Nat.add_zero,one_mul]
    rw [show x*(1+2*z) = x + 2*(x*z) by ring,phase_add,phase_double]
  · simp only [Bool.true_and,Bool.false_eq_true,ite_false,ite_true,one_mul,zero_add]
    rw [show (x+2^n)*(2*z) = 2*(x*z) + 2^(n+1)*z by rw [pow_succ]; ring,
      phase_add,phase_double,phase_multiple,mul_one]
  · simp only [Bool.true_and,ite_true]
    rw [show (x+2^n)*(1+2*z) = 2^n + x + 2*(x*z) + 2^(n+1)*z by rw [pow_succ]; ring,
      phase_add,phase_add,phase_add,phase_half,phase_double,phase_multiple,mul_one]

/-- Standard Hadamard coefficients, retaining the negative lower-right entry. -/
noncomputable def hadamard (output input : Bool) : ℂ :=
  Interference.complexModel.halfRoot * if input && output then -1 else 1

/-- Independent desired coefficient before the final explicit data reversal. -/
noncomputable def reversedFourier (n : Nat) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := fun output input =>
  Interference.complexModel.halfRoot^n *
    phase (number n input * number n (reverseBits output)) n

theorem reversedFourier_step (n : Nat) (output input : Fin (n+1) → Bool) :
    hadamard (output (Fin.last n)) (input (Fin.last n)) *
      (if output (Fin.last n) then phase (number n (fun i => input i.castSucc)) (n+1) else 1) *
      reversedFourier n (fun i => output i.castSucc) (fun i => input i.castSucc) =
    reversedFourier (n+1) output input := by
  simp only [hadamard,reversedFourier,pow_succ]
  rw [reverse_number_succ]
  simp only [number]
  rw [show Interference.complexModel.halfRoot *
      (if input (Fin.last n) && output (Fin.last n) then -1 else 1) *
      (if output (Fin.last n) then phase (number n (fun i => input i.castSucc)) (n+1) else 1) *
      (Interference.complexModel.halfRoot^n *
        phase (number n (fun i => input i.castSucc) * number n (reverseBits (fun i => output i.castSucc))) n) =
      (Interference.complexModel.halfRoot^n * Interference.complexModel.halfRoot) *
        ((if input (Fin.last n) && output (Fin.last n) then -1 else 1) *
         (if output (Fin.last n) then phase (number n (fun i => input i.castSucc)) (n+1) else 1) *
         phase (number n (fun i => input i.castSucc) * number n (reverseBits (fun i => output i.castSucc))) n) by ring]
  rw [phase_stage]

theorem sum_head_tail (n : Nat) (f : (Fin (n+1) → Bool) → ℂ) :
    (∑ bits, f bits) = ∑ head : Bool, ∑ tail : Fin n → Bool, f (Fin.cons head tail) := by
  have same : (∑ pair : Bool × (Fin n → Bool), f (Fin.cons pair.1 pair.2)) = ∑ bits, f bits := by
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool))
    intro pair
    rfl
  rw [← same,Fintype.sum_prod_type]

theorem tensor_bit_entry (interface : Interface) (n : Nat) (first second : Operator)
    (hi : width interface.inputs = n+1) (ho : width interface.outputs = n+1)
    (fi : first.inputWidth = 1) (fo : first.outputWidth = 1)
    (output input : Fin (n+1) → Bool) :
    matrixAt (n+1) (n+1) (apply interface .tensor [first,second]) output input =
      matrixAt 1 1 first (fun _ => output 0) (fun _ => input 0) *
        matrixAt n n second (fun i => output i.succ) (fun i => input i.succ) := by
  simp [matrixAt,apply,bounded,raw,hi,ho,fi,fo,List.ofFn_succ]

noncomputable def stage (joint : Interface) (h idleLow gradient idleHigh child : Operator) : Operator :=
  apply joint .sequence [apply joint .tensor [h,idleLow],gradient,apply joint .tensor [idleHigh,child]]

/-- Exact matrix multiplication of the actual tensor/diagonal/tensor stage.
The two intermediate basis sums collapse through the identity factors. -/
theorem stage_entry (joint : Interface) (n : Nat) (h idleLow gradient idleHigh child : Operator)
    (values : (Fin (n+1) → Bool) → ℂ)
    (ji : width joint.inputs = n+1) (jo : width joint.outputs = n+1)
    (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (low : At n idleLow (fun _ => 1)) (high : At 1 idleHigh (fun _ => 1))
    (diagonal : At (n+1) gradient values)
    (output input : Fin (n+1) → Bool) :
    matrixAt (n+1) (n+1) (stage joint h idleLow gradient idleHigh child) output input =
      matrixAt 1 1 h (fun _ => output 0) (fun _ => input 0) *
        values (Fin.cons (output 0) (fun i => input i.succ)) *
        matrixAt n n child (fun i => output i.succ) (fun i => input i.succ) := by
  rw [stage,sequence_three_matrix joint (n+1) _ _ _ ji jo ji jo diagonal.1 diagonal.2.1 ji jo,
    diagonal.2.2]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.diagonal_mul]
  rw [sum_head_tail]
  simp_rw [tensor_bit_entry joint n h idleLow ji jo hi ho,
    tensor_bit_entry joint n idleHigh child ji jo high.1 high.2.1,
    low.2.2,high.2.2]
  have constant_eq (a b : Bool) : ((fun _ : Fin 1 => a) = (fun _ => b)) ↔ a = b := by
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      subst b
      rfl
  simp [Matrix.diagonal_apply,constant_eq,mul_comm]

/-- The inspected gradient supplies the exact dyadic factor of this stage. -/
theorem stage_fourier (joint : Interface) (n : Nat) (h idleLow gradient idleHigh child : Operator)
    (ji : width joint.inputs = n+1) (jo : width joint.outputs = n+1)
    (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (hentry : ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input)
    (low : At n idleLow (fun _ => 1)) (high : At 1 idleHigh (fun _ => 1))
    (diagonal : At (n+1) gradient (fun bits => if bits 0 then
      phase (number n (fun i => bits i.succ)) (n+1) else 1))
    (recursive : matrixAt n n child = reversedFourier n)
    (output input : Fin (n+1) → Bool) :
    matrixAt (n+1) (n+1) (stage joint h idleLow gradient idleHigh child)
      (axisEquiv (Gradient.routing n) output) (axisEquiv (Gradient.routing n) input) =
      reversedFourier (n+1) output input := by
  rw [stage_entry joint n h idleLow gradient idleHigh child _ ji jo hi ho low high diagonal,
    hentry,recursive]
  simp only [Fin.cons_zero,Fin.cons_succ,route_head,route_tail]
  exact reversedFourier_step n output input

theorem sequence_matrix (n : Nat) (children : List Operator)
    (ready : ∀ child ∈ children, child.inputWidth = n ∧ child.outputWidth = n) :
    matrixAt n n (HierarchicalOperators.sequence n children) =
      children.foldl (fun current child => matrixAt n n child * current) 1 := by
  have fold : ∀ start : Operator, start.inputWidth = n → start.outputWidth = n →
      matrixAt n n (children.foldl (fun current child => compose child current) start) =
        children.foldl (fun current child => matrixAt n n child * current) (matrixAt n n start) := by
    induction children with
    | nil => intros; rfl
    | cons child rest ih =>
      intro start si so
      have hc := ready child (by simp)
      have following : ∀ c ∈ rest, c.inputWidth = n ∧ c.outputWidth = n := by
        intro c inside
        exact ready c (by simp [inside])
      simp only [List.foldl_cons]
      rw [ih following (compose child start) si hc.2]
      have first := matrix_compose child start
      rw [si,hc.1,hc.2] at first
      rw [first]
  simpa only [HierarchicalOperators.sequence,matrix_identity] using fold (identity n) rfl rfl

theorem apply_sequence_matrix (interface : Interface) (n : Nat) (children : List Operator)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (ready : ∀ child ∈ children, child.inputWidth = n ∧ child.outputWidth = n) :
    matrixAt n n (apply interface .sequence children) =
      children.foldl (fun current child => matrixAt n n child * current) 1 := by
  have same : matrixAt n n (apply interface .sequence children) =
      matrixAt n n (HierarchicalOperators.sequence n children) := by
    ext output input
    simp [matrixAt,apply,bounded,raw,hi,ho]
  rw [same,sequence_matrix n children ready]

theorem conjugate_entry {I : Type} [Fintype I] [DecidableEq I]
    (route : I ≃ I) (matrix : Matrix I I ℂ) (output input : I) :
    (permutation route.symm * matrix * permutation route) output input =
      matrix (route output) (route input) := by
  have equality (x : I) : output = route.symm x ↔ x = route output := by
    constructor
    · intro equal
      simpa using (congrArg route equal).symm
    · intro equal
      subst x
      simp
  simp [Matrix.mul_apply,permutation,equality]

/-- Actual flat five-node sequence emitted by the shared recursive producer.
The enter/leave routing is explicit, with no tuple/type equality coercion. -/
noncomputable def routedStage (root enter joint leave : Interface)
    (n : Nat) (h idleLow gradient idleHigh child : Operator) : Operator :=
  apply root .sequence [apply enter (.rewire (Gradient.highAxes n)) [],
    apply joint .tensor [h,idleLow],gradient,apply joint .tensor [idleHigh,child],
    apply leave (.rewire (Gradient.lowAxes n)) []]

theorem routed_stage_matrix (root enter joint leave : Interface)
    (n : Nat) (h idleLow gradient idleHigh child : Operator)
    (ri : width root.inputs = n+1) (ro : width root.outputs = n+1)
    (ei : width enter.inputs = n+1) (eo : width enter.outputs = n+1)
    (ji : width joint.inputs = n+1) (jo : width joint.outputs = n+1)
    (li : width leave.inputs = n+1) (lo : width leave.outputs = n+1)
    (gi : gradient.inputWidth = n+1) (go : gradient.outputWidth = n+1)
    (output input : Fin (n+1) → Bool) :
    matrixAt (n+1) (n+1) (routedStage root enter joint leave n h idleLow gradient idleHigh child) output input =
      matrixAt (n+1) (n+1) (stage joint h idleLow gradient idleHigh child)
        (axisEquiv (Gradient.routing n) output) (axisEquiv (Gradient.routing n) input) := by
  have inverse : QleisliKernel.Layout.Permutation (n+1) (Gradient.lowAxes n) (Gradient.highAxes n) := by
    have r := Gradient.routing n
    refine ⟨r.2.1,r.1,?_⟩
    intro i
    exact ⟨(r.2.2 i).2.1,(r.2.2 i).1,(r.2.2 i).2.2.2,(r.2.2 i).2.2.1⟩
  have same : axisEquiv inverse = (axisEquiv (Gradient.routing n)).symm := by
    apply Equiv.ext
    intro bits
    rfl
  have children : ∀ c ∈ [apply enter (.rewire (Gradient.highAxes n)) [],
      apply joint .tensor [h,idleLow],gradient,apply joint .tensor [idleHigh,child],
      apply leave (.rewire (Gradient.lowAxes n)) []], c.inputWidth = n+1 ∧ c.outputWidth = n+1 := by
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ei,eo⟩
    · exact ⟨ji,jo⟩
    · exact ⟨gi,go⟩
    · exact ⟨ji,jo⟩
    · exact ⟨li,lo⟩
  have expression : matrixAt (n+1) (n+1) (routedStage root enter joint leave n h idleLow gradient idleHigh child) =
      permutation (axisEquiv (Gradient.routing n)).symm *
        matrixAt (n+1) (n+1) (stage joint h idleLow gradient idleHigh child) *
          permutation (axisEquiv (Gradient.routing n)) := by
    rw [routedStage,apply_sequence_matrix root (n+1) _ ri ro children,
      stage,sequence_three_matrix joint (n+1) _ _ _ ji jo ji jo gi go ji jo]
    simp only [List.foldl_cons,List.foldl_nil,Matrix.mul_one]
    rw [rewire_matrix enter (n+1) _ _ ei eo (Gradient.routing n),
      rewire_matrix leave (n+1) _ _ li lo inverse,same]
    simp only [Matrix.mul_assoc]
  rw [expression,conjugate_entry]

theorem routed_stage_fourier (root enter joint leave : Interface)
    (n : Nat) (h idleLow gradient idleHigh child : Operator)
    (ri : width root.inputs = n+1) (ro : width root.outputs = n+1)
    (ei : width enter.inputs = n+1) (eo : width enter.outputs = n+1)
    (ji : width joint.inputs = n+1) (jo : width joint.outputs = n+1)
    (li : width leave.inputs = n+1) (lo : width leave.outputs = n+1)
    (hi : h.inputWidth = 1) (ho : h.outputWidth = 1)
    (hentry : ∀ output input : Bool, matrixAt 1 1 h (fun _ => output) (fun _ => input) = hadamard output input)
    (low : At n idleLow (fun _ => 1)) (high : At 1 idleHigh (fun _ => 1))
    (diagonal : At (n+1) gradient (fun bits => if bits 0 then
      phase (number n (fun i => bits i.succ)) (n+1) else 1))
    (recursive : matrixAt n n child = reversedFourier n) :
    matrixAt (n+1) (n+1) (routedStage root enter joint leave n h idleLow gradient idleHigh child) =
      reversedFourier (n+1) := by
  ext output input
  rw [routed_stage_matrix root enter joint leave n h idleLow gradient idleHigh child
    ri ro ei eo ji jo li lo diagonal.1 diagonal.2.1]
  exact stage_fourier joint n h idleLow gradient idleHigh child ji jo hi ho hentry low high diagonal recursive output input

/-- Explicit permutation of data bits, distinct from register reassociation. -/
def reversal (n : Nat) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := reverseBits
  invFun := reverseBits
  left_inv := reverse_twice
  right_inv := reverse_twice

/-- Positive-exponent Fourier convention, defined independently of any circuit. -/
noncomputable def fourier (n : Nat) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := fun output input =>
  Complex.exp (2 * Real.pi * Complex.I *
    (number n input : ℂ) * (number n output : ℂ) / (2 : ℂ)^n) /
    (Real.sqrt ((2 : ℝ)^n) : ℂ)

theorem reverse_fourier (n : Nat) (output input : Fin n → Bool) :
    reversedFourier n (reverseBits output) input = fourier n output input := by
  rw [reversedFourier,reverse_twice,Qft.halfRoot_power]
  simp only [fourier,phase,Nat.cast_mul]
  simp only [← mul_assoc,div_eq_mul_inv]
  rw [mul_comm]

/-- Reversal is an actual output permutation; omitting it changes the matrix. -/
theorem explicit_reversal (n : Nat) :
    permutation (reversal n) * reversedFourier n = fourier n := by
  ext output input
  have equality (x : Fin n → Bool) : output = reverseBits x ↔ x = reverseBits output := by
    constructor
    · intro equal
      simpa only [reverse_twice] using (congrArg reverseBits equal).symm
    · intro equal
      subst x
      exact (reverse_twice output).symm
  simpa [Matrix.mul_apply,permutation,reversal,equality] using reverse_fourier n output input

/-- Composition of a proved recursive body with a proved explicit reversal. -/
theorem compose_fourier (n : Nat) (body reverse : Operator)
    (bi : body.inputWidth = n) (_bo : body.outputWidth = n)
    (ri : reverse.inputWidth = n) (ro : reverse.outputWidth = n)
    (bodyMatrix : matrixAt n n body = reversedFourier n)
    (reverseMatrix : matrixAt n n reverse = permutation (reversal n)) :
    matrixAt n n (compose reverse body) = fourier n := by
  have product := matrix_compose reverse body
  rw [bi,ri,ro] at product
  rw [product,bodyMatrix,reverseMatrix,explicit_reversal]

/-- Coefficient equality applies to arbitrary superpositions and reference
columns. There is no product-state or separability premise. -/
theorem fourier_joint_amplitude (n : Nat) (actual : Operator)
    (matrix : matrixAt n n actual = fourier n) {R : Type}
    (joint : (Fin n → Bool) → R → ℂ) (output : Fin n → Bool) (reference : R) :
    (∑ input, matrixAt n n actual output input * joint input reference) =
      ∑ input, fourier n output input * joint input reference := by rw [matrix]

end Qleisli.HierarchicalFourier
