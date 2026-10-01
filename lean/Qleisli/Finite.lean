import QleisliKernel.Finite
import Qleisli.ExactMatrix
import Qleisli.Semantics.Finite
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin

/-! Actual VM-24 acceptance to phase-sensitive encoded/reference semantics.
Raw-IR extraction, source preservation and native transport remain separate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
open Qleisli.Semantics.Exact

private theorem arithmetic_success {α : Type} (input : Except QleisliKernel.Exact.Error α)
    (value : α) (ok : arithmetic input = .ok value) : input = .ok value := by
  cases input <;> simp_all [arithmetic,Except.mapError]

private theorem readOption_success {α : Type} (input : Option α) (value : α)
    (ok : readOption input = .ok value) : input = some value := by
  cases input <;> simp_all [readOption]

private theorem halfRoot_meaning : scalar QleisliKernel.Finite.halfRoot =
    Qleisli.Semantics.Finite.halfRoot := by
  simp [QleisliKernel.Finite.halfRoot,Qleisli.Semantics.Finite.halfRoot,
    scalar,rational,Coefficient.integer]
  ring

private theorem phase_meaning (k : Nat) : scalar (QleisliKernel.Exact.Scalar.phase k) =
    Qleisli.Semantics.Finite.phase k := by
  have residue : (k : Int) % 8 = (k % 8 : Nat) := by omega
  have bound : k % 8 < 8 := Nat.mod_lt _ (by omega)
  unfold QleisliKernel.Exact.Scalar.phase Qleisli.Semantics.Finite.phase
  rw [residue]
  generalize k % 8 = r at *
  interval_cases r <;>
    simp [scalar,rational,Coefficient.integer,Qleisli.Semantics.Finite.halfRoot] <;> ring

private theorem conjugate_record (input result : Scalar)
    (ok : QleisliKernel.Exact.Scalar.conjugate input = .ok result) :
    result = Qleisli.Semantics.Finite.rawStar input := by
  obtain ⟨c,hc,h⟩ := QleisliKernel.Exact.bind_success _ _ _ ok
  obtain ⟨d,hd,h⟩ := QleisliKernel.Exact.bind_success _ _ _ h
  obtain ⟨cn,hcn,hc⟩ := QleisliKernel.Exact.bind_success _ _ _ hc
  obtain ⟨dn,hdn,hd⟩ := QleisliKernel.Exact.bind_success _ _ _ hd
  have ceq := QleisliKernel.Exact.checkedInt_value _ _ hcn
  have deq := QleisliKernel.Exact.checkedInt_value _ _ hdn
  subst cn; subst dn
  simp only [pure,Except.pure,Except.ok.injEq] at hc hd h
  subst c; subst d; subst result
  rfl

private theorem except_bind_success {α β : Type} (first : Except Error α)
    (next : α → Except Error β) (result : β) (ok : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => simp [bind,Except.bind] at ok
  | ok value => exact ⟨value,rfl,ok⟩

private theorem except_fold_reference {α β γ : Type}
    (step : β → α → Except Error β) (reference : γ → α → Option γ)
    (meaning : β → γ)
    (sound : ∀ initial item result, step initial item = .ok result →
      reference (meaning initial) item = some (meaning result))
    (items : List α) (initial result : β)
    (ok : items.foldlM step initial = .ok result) :
    items.foldlM reference (meaning initial) = some (meaning result) := by
  induction items generalizing initial with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    rfl
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok ⊢
    obtain ⟨next,hn,hrest⟩ := except_bind_success _ _ _ ok
    rw [sound initial item next hn]
    exact ih next hrest

private noncomputable def termMeaning (term : Nat × Scalar) : Nat × ℂ := (term.1,scalar term.2)

/-- Each actual local gate contribution has its independently stated complex
amplitude, including zero controls, adjoints and scalar Unit phases. -/
theorem contributions_meaning (dependencies : List Dependency) (step : Step)
    (label : Nat) (value : Scalar) (terms : List (Nat × Scalar))
    (ok : contributions dependencies step label value = .ok terms) :
    Qleisli.Semantics.Finite.contributions dependencies step label value =
      some (terms.map termMeaning) := by
  cases zero : (value == Scalar.zero) with
  | true =>
    simp [contributions,Qleisli.Semantics.Finite.contributions,zero] at ok ⊢
    simp only [pure,Except.pure,Except.ok.injEq] at ok
    exact ok.symm
  | false =>
    cases active : enabled step.controls label with
    | false =>
      simp [contributions,Qleisli.Semantics.Finite.contributions,zero,active] at ok ⊢
      simp only [pure,Except.pure,Except.ok.injEq] at ok
      subst terms
      rfl
    | true =>
      cases action : step.action with
      | hadamard target =>
        simp only [contributions,Qleisli.Semantics.Finite.contributions,zero,active,
          action,Bool.false_eq_true,Bool.not_true,if_false,pure_bind] at ok ⊢
        obtain ⟨scaled,hm,h⟩ := except_bind_success _ _ _ ok
        have multiplied := Exact.scalar_mul_preserves _ _ _ (arithmetic_success _ _ hm)
        rw [halfRoot_meaning] at multiplied
        split at h
        · rename_i negative
          obtain ⟨signed,hn,h⟩ := except_bind_success _ _ _ h
          have negated := Exact.scalar_neg_preserves _ _ (arithmetic_success _ _ hn)
          simp only [pure,Except.pure,Except.ok.injEq] at h
          subst terms
          simp [negative,termMeaning,multiplied,negated]
        · rename_i positive
          simp only [pure,Except.pure,Except.ok.injEq] at h
          subst terms
          simp [positive,termMeaning,multiplied]
      | monomial axes permutation phases =>
        simp only [contributions,Qleisli.Semantics.Finite.contributions,zero,active,
          action,Bool.false_eq_true,Bool.not_true,if_false,pure_bind] at ok ⊢
        obtain ⟨output,ho,h⟩ := except_bind_success _ _ _ ok
        obtain ⟨exponent,he,h⟩ := except_bind_success _ _ _ h
        obtain ⟨scaled,hm,h⟩ := except_bind_success _ _ _ h
        have multiplied := Exact.scalar_mul_preserves _ _ _ (arithmetic_success _ _ hm)
        rw [phase_meaning] at multiplied
        simp only [pure,Except.pure,Except.ok.injEq] at h
        subst terms
        simp [readOption_success _ _ ho,readOption_success _ _ he,termMeaning,multiplied]
      | contract axes index adjoint =>
        simp only [contributions,Qleisli.Semantics.Finite.contributions,zero,active,
          action,Bool.false_eq_true,Bool.not_true,if_false,pure_bind] at ok ⊢
        obtain ⟨dependency,hd,h⟩ := except_bind_success _ _ _ ok
        rw [readOption_success _ _ hd]
        simp only [bind,Option.bind]
        -- The fold proof checks every dependency coefficient, never a supplied flag.
        let reference := fun (acc : List (Nat × ℂ)) output =>
          let raw := if adjoint then Qleisli.Semantics.Finite.rawStar
              (dependency.meaning.entry (gather label axes) output)
            else dependency.meaning.entry output (gather label axes)
          let coefficient := if adjoint then star (entry dependency.meaning (gather label axes) output)
            else entry dependency.meaning output (gather label axes)
          some (if raw == Scalar.zero then acc else acc ++
            [(scatter label axes output,scalar value * coefficient)])
        have folded := except_fold_reference _ reference (List.map termMeaning) ?_
          (List.range dependency.meaning.rows) [] terms h
        · simpa only [reference] using folded
        · intro initial output result success
          unfold contractContribution at success
          obtain ⟨coefficient,hc,h⟩ := except_bind_success _ _ _ success
          have raw_eq : coefficient = if adjoint then Qleisli.Semantics.Finite.rawStar
              (dependency.meaning.entry (gather label axes) output)
            else dependency.meaning.entry output (gather label axes) := by
            unfold dependencyCoefficient at hc
            cases adjoint
            · change Except.ok (dependency.meaning.entry output (gather label axes)) = .ok coefficient at hc
              exact (Except.ok.inj hc).symm
            · exact conjugate_record _ _ (arithmetic_success _ _ hc)
          have coefficient_meaning : scalar coefficient = if adjoint then
              star (entry dependency.meaning (gather label axes) output)
            else entry dependency.meaning output (gather label axes) := by
            unfold dependencyCoefficient at hc
            cases adjoint
            · simp only [Bool.false_eq_true,if_false] at raw_eq ⊢
              rw [raw_eq]
              rfl
            · exact Exact.scalar_conjugate_preserves _ _ (arithmetic_success _ _ hc)
          split at h
          · rename_i zero
            simp only [pure,Except.pure,Except.ok.injEq] at h
            subst result
            have eq := beq_iff_eq.mp zero
            simp only [reference,← raw_eq,eq,beq_self_eq_true,if_true]
          · rename_i nonzero
            simp only [pure_bind] at h
            obtain ⟨scaled,hm,h⟩ := except_bind_success _ _ _ h
            have multiplied := Exact.scalar_mul_preserves _ _ _ (arithmetic_success _ _ hm)
            simp only [pure,Except.pure,Except.ok.injEq] at h
            subst result
            have ne : coefficient ≠ Scalar.zero := by simpa only [beq_iff_eq] using nonzero
            simp [reference,← raw_eq,ne,List.map_append,termMeaning,multiplied,coefficient_meaning]

/-- Successful vector accumulation preserves the literal complex sum. -/
theorem addAt_meaning (values result : List Scalar) (term : Nat × Scalar)
    (ok : addAt values term = .ok result) :
    result.map scalar = Qleisli.Semantics.Finite.addAt (values.map scalar) (termMeaning term) := by
  obtain ⟨previous,hp,h⟩ := except_bind_success _ _ _ ok
  obtain ⟨value,ha,h⟩ := except_bind_success _ _ _ h
  have present := readOption_success _ _ hp
  have added := Exact.scalar_add_preserves _ _ _ (arithmetic_success _ _ ha)
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  simp [List.map_set,Qleisli.Semantics.Finite.addAt,termMeaning,
    List.getElem?_map,present,added]

private theorem option_fold_pure {α β : Type} (items : List α) (initial : β)
    (step : β → α → β) :
    items.foldlM (fun acc item => some (step acc item)) initial = some (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih => simp only [List.foldlM_cons,List.foldl_cons]; exact ih _

private theorem terms_meaning (terms : List (Nat × Scalar)) (values result : List Scalar)
    (ok : terms.foldlM addAt values = .ok result) :
    result.map scalar = (terms.map termMeaning).foldl Qleisli.Semantics.Finite.addAt (values.map scalar) := by
  have folded := except_fold_reference addAt
    (fun values term => some (Qleisli.Semantics.Finite.addAt values (termMeaning term)))
    (List.map scalar) (fun _ _ _ h => congrArg some (addAt_meaning _ _ _ h).symm) terms values result ok
  rw [option_fold_pure] at folded
  simpa [List.foldl_map] using (Option.some.inj folded).symm

/-- The actual bounded step agrees with the independently stated literal complex
step, without using measurement probabilities or equality modulo phase. -/
theorem applyStep_meaning (dependencies : List Dependency) (step : Step)
    (values result : List Scalar) (ok : applyStep dependencies step values = .ok result) :
    Qleisli.Semantics.Finite.applyStep dependencies step values = some (result.map scalar) := by
  unfold applyStep Qleisli.Semantics.Finite.applyStep at *
  have initial : (List.replicate values.length Scalar.zero).map scalar = List.replicate values.length (0 : ℂ) := by
    simp [Exact.scalar_zero_meaning]
  rw [← initial]
  apply except_fold_reference _ _ (List.map scalar) _ _ _ _ ok
  intro initial item result success
  rcases item with ⟨value,label⟩
  obtain ⟨terms,ht,h⟩ := except_bind_success _ _ _ success
  dsimp only
  rw [contributions_meaning _ _ _ _ _ ht]
  simp only [bind,Option.bind,pure]
  exact congrArg some (terms_meaning _ _ _ h).symm

/-- Actual execution supplies a complete literal trace of every original step. -/
theorem execution_trace (dependencies : List Dependency) (steps : List Step)
    (values result : List Scalar)
    (ok : steps.foldlM (fun values step => applyStep dependencies step values) values = .ok result) :
    Qleisli.Semantics.Finite.Trace dependencies steps values result := by
  induction steps generalizing values with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    exact .nil values
  | cons step steps ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,h⟩ := except_bind_success _ _ _ ok
    exact .cons step steps values next result (applyStep_meaning _ _ _ _ hn) (ih next h)

private theorem except_map_relation {α β : Type} (step : α → Except Error β)
    (relation : α → β → Prop) (sound : ∀ item value, step item = .ok value → relation item value)
    (items : List α) (values : List β) (ok : items.mapM step = .ok values) :
    List.Forall₂ relation items values := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst values
    exact .nil
  | cons item items ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value,hv,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨rest,hr,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst values
    exact .cons (sound item value hv) (ih rest hr)

/-- Every actual reconstructed column has a complete mathematical execution
trace of the original circuit, including all ordered dependency actions. -/
theorem circuitMatrix_trace (dependencies : List Dependency) (circuit : Circuit)
    (actual : Matrix) (work left : Nat)
    (ok : (circuitMatrix dependencies circuit).run work = (.ok actual,left)) :
    ∃ columns, List.Forall₂ (fun column values => Qleisli.Semantics.Finite.Trace dependencies circuit.steps
        ((List.range (2^width circuit.basis)).map
          (fun row => if row == column then Scalar.one else Scalar.zero)) values)
      (List.range (2^width circuit.basis)) columns ∧
    actual = ⟨2^width circuit.basis,2^width circuit.basis,
      (List.range ((2^width circuit.basis) * (2^width circuit.basis))).map fun index =>
        ((columns[index % (2^width circuit.basis)]?).getD [])[index / (2^width circuit.basis)]?.getD Scalar.zero⟩ := by
  rcases circuitMatrix_columns _ _ _ _ _ ok with ⟨_,columns,hc,actual_eq⟩
  refine ⟨columns,?_,actual_eq⟩
  apply except_map_relation _ _ _ _ _ hc
  intro column values success
  exact execution_trace _ _ _ _ success

/-- Successful reconstruction/checking establishes the complete encoded equation,
with the independently required contract and the actual reconstructed matrix. -/
theorem check_encoded (dependencies : List Dependency) (circuit : Circuit)
    (claim required : Contract) (actual : Matrix) (work left : Nat)
    (ok : (check dependencies circuit claim required).run work = (.ok actual,left)) :
    claim = required ∧ Qleisli.Semantics.Finite.Encoded actual required := by
  rcases check_conditions _ _ _ _ _ _ _ ok with
    ⟨same,_,_,_,_,_,cw,aw,lhs,lw,rhs,rw,_,hl,hr,equal⟩
  subst required
  obtain ⟨shape₁,rows₁,cols₁,entries₁⟩ := Exact.compose_meaning _ _ _ _ _ hl
  obtain ⟨shape₂,rows₂,cols₂,entries₂⟩ := Exact.compose_meaning _ _ _ _ _ hr
  have physical : actual.rows = claim.output.map.rows := by
    rw [← rows₁,equal,rows₂]
  have logical : claim.input.map.cols = claim.logical.cols := by
    rw [← cols₁,equal,cols₂]
  refine ⟨rfl,shape₁,shape₂,physical,logical,?_⟩
  intro row col hrow hcol
  rw [← entries₁ row col hrow (by rw [logical]; exact hcol),equal,
    entries₂ row col (by rw [← physical]; exact hrow) hcol]

/-- No product-state assumption: each arbitrary reference column obeys the same
accepted encoded equation, including the complete scalar phase. -/
theorem check_reference {R : Type} (dependencies : List Dependency) (circuit : Circuit)
    (claim required : Contract) (actual : Matrix) (work left : Nat)
    (ok : (check dependencies circuit claim required).run work = (.ok actual,left))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) (bound : row < actual.rows) :
    action actual (fun index r => action required.input.map joint index r) row reference =
      action required.output.map (fun index r => action required.logical joint index r) row reference := by
  rcases check_conditions _ _ _ _ _ _ _ ok with
    ⟨same,_,_,_,_,_,cw,aw,lhs,lw,rhs,rw,_,hl,hr,equal⟩
  subst required
  have physical := (check_encoded _ _ _ _ _ _ _ ok).2.2.2.1
  rw [← Exact.compose_action actual claim.input.map lhs aw lw hl joint row reference bound,
    equal,Exact.compose_action claim.output.map claim.logical rhs lw rw hr joint row reference
      (by rw [← physical]; exact bound)]

/-- Encodings and the logical map preserve norms over arbitrary reference domains. -/
theorem check_logical_norm {R : Type} (dependencies : List Dependency) (circuit : Circuit)
    (claim required : Contract) (actual : Matrix) (work left : Nat)
    (ok : (check dependencies circuit claim required).run work = (.ok actual,left))
    (joint : Nat → R → ℂ) (references : List R) :
    (references.map (fun r => ((List.range required.logical.rows).map
      (fun row => Complex.normSq (action required.logical joint row r))).sum)).sum =
    (references.map (fun r => ((List.range required.logical.cols).map
      (fun col => Complex.normSq (joint col r))).sum)).sum := by
  rcases check_conditions _ _ _ _ _ _ _ ok with ⟨same,_,_,_,_,⟨before,after,iso⟩,_⟩
  subst required
  exact Exact.isometry_joint_norm _ _ _ iso joint references

/-- Clean return follows from the actual accepted output encoding, for arbitrary
entanglement with a reference system. A scratch name or lifetime is insufficient:
the independently required encoding must have zero amplitudes in every dirty row. -/
theorem check_clean_return {R : Type} (dependencies : List Dependency) (circuit : Circuit)
    (claim required : Contract) (actual : Matrix) (work left : Nat)
    (ok : (check dependencies circuit claim required).run work = (.ok actual,left))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) (bound : row < actual.rows)
    (clean : ∀ col, col < required.output.map.cols → entry required.output.map row col = 0) :
    action actual (fun index r => action required.input.map joint index r) row reference = 0 := by
  rw [check_reference _ _ _ _ _ _ _ ok joint row reference bound]
  unfold action
  apply List.sum_eq_zero
  intro amplitude member
  obtain ⟨col,inRange,rfl⟩ := List.mem_map.mp member
  rw [clean col (List.mem_range.mp inRange),zero_mul]

/-- A successful fresh matrix reader keeps every independently reduced dyadic,
not just a common exponent or a numerical approximation. -/
theorem matrixRead_entries (input actual : Matrix) (work left : Nat)
    (ok : (matrixRead input).run work = (.ok actual,left)) :
    ∀ row col, entry actual row col = entry input row col := by
  rw [(matrixRead_value _ _ _ _ ok).1]
  exact fun _ _ => rfl

open scoped BigOperators Matrix

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,ih,Finset.sum_range_succ]

noncomputable def square (matrix : Matrix) : _root_.Matrix (Fin matrix.cols) (Fin matrix.cols) ℂ :=
  fun row col => entry matrix row col

/-- Actual whole-space acceptance gives both inverse equations, with exact phase.
The square finite domain, rather than a supplied inverse, yields the second law. -/
theorem wholeSpace_unitary (matrix : Matrix) (work left : Nat)
    (ok : (wholeSpace matrix).run work = (.ok (),left)) :
    (square matrix)ᴴ * square matrix = 1 ∧ square matrix * (square matrix)ᴴ = 1 := by
  rcases wholeSpace_conditions _ _ _ ok with ⟨dimensions,before,after,iso⟩
  have gram := (Exact.isometry_gram _ _ _ iso).2
  have first : (square matrix)ᴴ * square matrix = 1 := by
    ext row col
    have h := gram row col row.isLt col.isLt
    rw [dimensions,range_sum] at h
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,square]
    rw [Fin.sum_univ_eq_sum_range (fun k => star (entry matrix k row) * entry matrix k col)]
    simpa [Matrix.one_apply,Fin.ext_iff] using h
  exact ⟨first,mul_eq_one_comm.mp first⟩

/-- A fresh complete-artifact pass checks the independently requested root
equation and both whole-space inverse laws; raw-IR extraction is a later gate. -/
theorem checkAll_root (artifact : Artifact) (order : List Nat) (required : Contract)
    (result : Dependency) (work left : Nat)
    (ok : (checkAll artifact order required).run work = (.ok result,left)) :
    Qleisli.Semantics.Finite.Encoded result.meaning required ∧
    (square result.meaning)ᴴ * square result.meaning = 1 ∧
      square result.meaning * (square result.meaning)ᴴ = 1 := by
  rcases checkAll_conditions _ _ _ _ _ _ ok with
    ⟨root,cache,_,_,rw,ra,uw,ua,_,_,_,_,checked,unitary,_⟩
  exact ⟨(check_encoded _ _ _ _ _ rw ra checked).2,wholeSpace_unitary _ uw ua unitary⟩

end Qleisli.Finite
