import Qleisli.Finite
import QleisliKernel.Qirf.Contract
import Mathlib.Data.List.Forall2

/-! Exact correspondence for the existing full-axis, single-call wrapper.
Only proofs are added: arithmetic, circuit execution, reference meanings and
acceptance conditions are unchanged. In particular, zero suppression, axis
order and scalar Unit phases are accounted for in the executable result.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeContract.Wrapper
open QleisliKernel.Semantics.Finite

private theorem gather_range (label n : Nat) : gather label (List.range n) = label % 2^n := by
  induction n with
  | zero => simp only [gather, List.range_zero, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.pow_zero]; omega
  | succ n ih =>
    simp only [gather, List.range_succ, List.zipIdx_append, List.length_range,
      Nat.zero_add, List.zipIdx_cons, List.zipIdx_nil, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    change gather label (List.range n) + bit label n * 2^n = label % 2^(n+1)
    rw [ih, Nat.pow_succ, Nat.mod_mul]
    simp [bit, Nat.mul_comm]

private theorem scatter_range (label value n : Nat) :
    scatter label (List.range n) value = 2^n * (label / 2^n) + value % 2^n := by
  induction n with
  | zero => simp only [scatter, List.range_zero, List.zipIdx_nil, List.foldl_nil, Nat.pow_zero]; omega
  | succ n ih =>
    simp only [scatter, List.range_succ, List.zipIdx_append, List.length_range,
      Nat.zero_add, List.zipIdx_cons, List.zipIdx_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change scatter label (List.range n) value -
      bit (scatter label (List.range n) value) n * 2^n + bit value n * 2^n = _
    rw [ih]
    have pos : 0 < 2^n := Nat.two_pow_pos n
    have bitSame : bit (2^n * (label / 2^n) + value % 2^n) n = label / 2^n % 2 := by
      simp [bit, Nat.add_div, pos, Nat.div_eq_of_lt (Nat.mod_lt value pos), Nat.not_le_of_gt (Nat.mod_lt value pos)]
    rw [bitSame, Nat.pow_succ, Nat.mod_mul]
    simp only [bit, ← Nat.div_div_eq_div_mul]
    have scaled : 2^n * (label / 2^n) =
        (label / 2^n % 2) * 2^n + (2^n * 2) * (label / 2^n / 2) := by
      have h := congrArg (fun k => 2^n * k) (Nat.mod_add_div (label / 2^n) 2)
      nlinarith only [h]
    rw [scaled]
    rw [Nat.mul_comm (value / 2^n % 2) (2^n)]
    omega
open QleisliKernel.Semantics.Exact QleisliKernel.Finite

private theorem dimensions (signature : Basis) (meaning actual : Matrix) (work left : Nat)
    (ok : (circuitMatrix [⟨signature,meaning⟩]
      (QleisliKernel.Qirf.contractCircuit signature)).run work = (.ok actual,left)) :
    meaning.rows = 2^width signature ∧ meaning.cols = 2^width signature ∧
      actual.rows = 2^width signature ∧ actual.cols = 2^width signature := by
  obtain ⟨valid,columns,_,rfl⟩ := circuitMatrix_columns _ _ _ _ _ ok
  simp [QleisliKernel.Qirf.contractCircuit, circuitValid, stepValid, targets] at valid
  exact ⟨valid.2.2.1.2,valid.2.2.2,rfl,rfl⟩

open Qleisli.Semantics.Exact

private theorem gather_range_of_lt {label n : Nat} (h : label < 2^n) :
    gather label (List.range n) = label := by rw [gather_range, Nat.mod_eq_of_lt h]

private theorem scatter_range_of_lt {label value n : Nat} (hl : label < 2^n) (hv : value < 2^n) :
    scatter label (List.range n) value = value := by
  rw [scatter_range, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hv]
  simp

private theorem addAt_length (values : List ℂ) (term : Nat × ℂ) :
    (Qleisli.Semantics.Finite.addAt values term).length = values.length := by
  simp [Qleisli.Semantics.Finite.addAt]

private theorem addAt_entry (values : List ℂ) (term : Nat × ℂ) (row : Nat)
    (bound : row < values.length) :
    (Qleisli.Semantics.Finite.addAt values term)[row]?.getD 0 =
      values[row]?.getD 0 + if row = term.1 then term.2 else 0 := by
  by_cases same : row = term.1
  · subst row
    simp [Qleisli.Semantics.Finite.addAt, bound]
  · simp [Qleisli.Semantics.Finite.addAt, Ne.symm same, same]

private theorem terms_length (terms : List (Nat × ℂ)) (values : List ℂ) :
    (terms.foldl Qleisli.Semantics.Finite.addAt values).length = values.length := by
  induction terms generalizing values with
  | nil => rfl
  | cons term terms ih => simpa [List.foldl_cons,addAt_length] using ih (Qleisli.Semantics.Finite.addAt values term)

private theorem terms_entry (terms : List (Nat × ℂ)) (values : List ℂ) (row : Nat)
    (bound : row < values.length) :
    (terms.foldl Qleisli.Semantics.Finite.addAt values)[row]?.getD 0 =
      values[row]?.getD 0 + (terms.map (fun term => if row = term.1 then term.2 else 0)).sum := by
  induction terms generalizing values with
  | nil => simp
  | cons term terms ih =>
    rw [List.foldl_cons,ih _ (by simpa [addAt_length] using bound),addAt_entry _ _ _ bound]
    simp [add_assoc]

private theorem option_fold_pure {α β : Type} (items : List α) (initial : β) (step : β → α → β) :
    items.foldlM (fun acc item => some (step acc item)) initial = some (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih => simp only [List.foldlM_cons,List.foldl_cons]; exact ih _

private theorem append_fold {α β : Type} (items : List α) (initial : List β) (f : α → List β) :
    items.foldl (fun acc item => acc ++ f item) initial = initial ++ items.flatMap f := by
  induction items generalizing initial with
  | nil => simp
  | cons item items ih => simp [ih, List.append_assoc]

private theorem sum_single_range (n row : Nat) (f : Nat → ℂ) (h : row < n) :
    ((List.range n).map (fun output => if row = output then f output else 0)).sum = f row := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append]
    by_cases same : row = n
    · subst row
      have zero : ((List.range n).map (fun output => if n = output then f output else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        have hn := List.mem_range.mp hi
        simp [Nat.ne_of_gt hn]
      simp [zero]
    · rw [ih (by omega)]
      simp [same]


private theorem sum_flatMap {α : Type} (items : List α) (f : α → List ℂ) :
    (items.flatMap f).sum = (items.map (fun item => (f item).sum)).sum := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

private theorem contributions_entry (signature : Basis) (meaning : Matrix) (label row : Nat)
    (value : Scalar) (hl : label < 2^width signature) (hr : row < meaning.rows)
    (shape : meaning.rows = 2^width signature) :
    ∃ terms, Qleisli.Semantics.Finite.contributions [⟨signature,meaning⟩]
        ⟨[],.contract (List.range (width signature)) 0 false⟩ label value = some terms ∧
      (terms.map (fun term => if row = term.1 then term.2 else 0)).sum =
        scalar value * entry meaning row label := by
  by_cases zero : value = Scalar.zero
  · subst value
    refine ⟨[],?_,?_⟩
    · simp [Qleisli.Semantics.Finite.contributions]
    · simp [Qleisli.Exact.scalar_zero_meaning]
  · let terms := (List.range meaning.rows).flatMap (fun output =>
      if meaning.entry output label = Scalar.zero then []
      else [(output, scalar value * entry meaning output label)])
    refine ⟨terms,?_,?_⟩
    · simp only [Qleisli.Semantics.Finite.contributions, beq_iff_eq, zero, if_false,
        enabled, List.all_nil, Bool.not_true, Bool.false_eq_true,
        List.getElem?_cons_zero, bind, Option.bind, pure, gather_range_of_lt hl]
      rw [option_fold_pure]
      have local_step : (fun (acc : List (Nat × ℂ)) (output : Nat) =>
          if meaning.entry output label = Scalar.zero then acc
          else acc ++ [(scatter label (List.range (width signature)) output,
            scalar value * entry meaning output label)]) =
          (fun acc output => acc ++ (if meaning.entry output label = Scalar.zero then []
          else [(scatter label (List.range (width signature)) output,
            scalar value * entry meaning output label)])) := by
        funext acc output
        split <;> simp
      rw [local_step,append_fold]
      simp only [List.nil_append,Option.some.injEq]
      apply List.flatMap_congr
      intro output ho
      rw [scatter_range_of_lt hl (by simpa [← shape] using List.mem_range.mp ho)]
    · dsimp [terms]
      rw [List.map_flatMap,sum_flatMap]
      have same : (fun output => ((if meaning.entry output label = Scalar.zero then []
          else [(output,scalar value * entry meaning output label)]).map
          (fun term => if row = term.1 then term.2 else 0)).sum) =
          (fun output => if row = output then scalar value * entry meaning output label else 0) := by
        funext output
        by_cases hz : meaning.entry output label = Scalar.zero
        · have ez : entry meaning output label = 0 := by
            unfold entry
            rw [hz, Qleisli.Exact.scalar_zero_meaning]
          simp [hz,ez]
        · simp [hz]
      rw [same,sum_single_range _ _ _ hr]


private theorem zipIdx_map_range {α : Type} (f : Nat → α) (n : Nat) :
    ((List.range n).map f).zipIdx = (List.range n).map (fun i => (f i,i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.range_succ,List.zipIdx_append,ih]

private theorem call_fold_entry (signature : Basis) (meaning : Matrix)
    (items : List (Scalar × Nat)) (values : List ℂ) (row : Nat)
    (hr : row < meaning.rows) (hv : values.length = meaning.rows)
    (shape : meaning.rows = 2^width signature)
    (labels : ∀ item ∈ items, item.2 < 2^width signature) :
    ∃ result, items.foldlM (fun next (value,label) => do
        let terms ← Qleisli.Semantics.Finite.contributions [⟨signature,meaning⟩]
          ⟨[],.contract (List.range (width signature)) 0 false⟩ label value
        pure (terms.foldl Qleisli.Semantics.Finite.addAt next)) values = some result ∧
      result.length = values.length ∧
      result[row]?.getD 0 = values[row]?.getD 0 +
        (items.map (fun item => scalar item.1 * entry meaning row item.2)).sum := by
  induction items generalizing values with
  | nil => exact ⟨values,rfl,rfl,by simp⟩
  | cons item items ih =>
    obtain ⟨terms,accepted,coefficient⟩ := contributions_entry signature meaning item.2 row item.1
      (labels item (by simp)) hr shape
    have hlen := terms_length terms values
    obtain ⟨result,rest,size,entries⟩ := ih (terms.foldl Qleisli.Semantics.Finite.addAt values)
      (hlen.trans hv) (fun x hx => labels x (by simp [hx]))
    refine ⟨result,?_,size.trans hlen,?_⟩
    · simpa only [List.foldlM_cons,accepted,bind,Option.bind,pure] using rest
    · rw [entries,terms_entry _ _ _ (by omega),coefficient]
      simp [add_assoc]

private theorem call_basis_column (signature : Basis) (meaning : Matrix) (column : Nat)
    (result : List ℂ) (hc : column < 2^width signature)
    (shape : meaning.rows = 2^width signature)
    (ok : Qleisli.Semantics.Finite.applyStep [⟨signature,meaning⟩]
      ⟨[],.contract (List.range (width signature)) 0 false⟩
      ((List.range (2^width signature)).map
        (fun row => if row == column then Scalar.one else Scalar.zero)) = some result) :
    result.length = 2^width signature ∧
      ∀ row, row < meaning.rows → result[row]?.getD 0 = entry meaning row column := by
  have run := fun row (hr : row < meaning.rows) => call_fold_entry signature meaning
    ((List.range (2^width signature)).map
      (fun label => (if label == column then Scalar.one else Scalar.zero,label)))
    (List.replicate (2^width signature) 0) row hr (by simpa using shape.symm) shape
    (by intro item hi; obtain ⟨i,memIndex,itemEq⟩ := List.mem_map.mp hi; rw [← itemEq]; exact List.mem_range.mp memIndex)
  have zeroBound : 0 < meaning.rows := by rw [shape]; exact Nat.two_pow_pos _
  simp only [Qleisli.Semantics.Finite.applyStep,zipIdx_map_range,List.length_map,List.length_range] at ok
  obtain ⟨first,hfirst,len,_⟩ := run 0 zeroBound
  have firstEq : first = result := Option.some.inj (hfirst.symm.trans ok)
  subst first
  refine ⟨by simpa using len,?_⟩
  intro row hr
  obtain ⟨actual,hactual,_,coeff⟩ := run row hr
  have actualEq : actual = result := Option.some.inj (hactual.symm.trans ok)
  subst actual
  rw [coeff]
  have bound : row < 2^width signature := by simpa [shape] using hr
  simp only [List.getElem?_replicate, bound, if_true, Option.getD_some, zero_add,
    List.map_map,Function.comp_def]
  have point : (fun label => scalar (if label == column then Scalar.one else Scalar.zero) *
      entry meaning row label) =
      (fun label => if column = label then entry meaning row label else 0) := by
    funext label
    by_cases h : column = label
    · subst label
      simp [Qleisli.Exact.scalar_one_meaning]
    · simp [Ne.symm h,h,Qleisli.Exact.scalar_zero_meaning]
  rw [point,sum_single_range _ _ _ hc]


private theorem trace_singleton (dependencies : List Dependency) (step : Step)
    (values result : List Scalar)
    (trace : Qleisli.Semantics.Finite.Trace dependencies [step] values result) :
    Qleisli.Semantics.Finite.applyStep dependencies step values = some (result.map scalar) := by
  cases trace with
  | cons _ _ _ _ _ localAction rest => cases rest; exact localAction

/-- The actual full-axis single-call wrapper reconstructs exactly the supplied
operator's bounded complex coefficients and dimensions. The success premise is
from `circuitMatrix`; operator equality is a conclusion, never a premise.
Width zero is included, so scalar Unit phases remain observable. -/
theorem circuitMatrix_entries (signature : Basis) (meaning actual : Matrix) (work left : Nat)
    (ok : (circuitMatrix [⟨signature,meaning⟩]
      (QleisliKernel.Qirf.contractCircuit signature)).run work = (.ok actual,left)) :
    actual.rows = meaning.rows ∧ actual.cols = meaning.cols ∧
      ∀ row col, row < meaning.rows → col < meaning.cols →
        entry actual row col = entry meaning row col := by
  obtain ⟨mr,mc,ar,ac⟩ := dimensions signature meaning actual work left ok
  refine ⟨ar.trans mr.symm,ac.trans mc.symm,?_⟩
  intro row col hr hc
  obtain ⟨columns,traces,actualEq⟩ := Qleisli.Finite.circuitMatrix_trace _ _ _ _ _ ok
  have bound : col < 2^width signature := by omega
  have len : columns.length = 2^width signature := by simpa using traces.length_eq.symm
  have colBound : col < columns.length := by omega
  have traced := traces.get (by simpa using bound) colBound
  simp only [List.get_eq_getElem,List.getElem_range,QleisliKernel.Qirf.contractCircuit] at traced
  have single := trace_singleton _ _ _ _ traced
  obtain ⟨size,entries⟩ := call_basis_column signature meaning col
    (columns[col].map scalar) bound mr single
  have valuesLength : columns[col].length = 2^width signature := by simpa using size
  have rowBound : row < columns[col].length := by omega
  have coeff := entries row hr
  simp only [List.getElem?_map,List.getElem?_eq_getElem rowBound,Option.map_some,
    Option.getD_some] at coeff
  have dimensionPositive : 0 < 2^width signature := Nat.two_pow_pos _
  have indexBound : row * (2^width signature) + col <
      (2^width signature) * (2^width signature) := by nlinarith
  have indexMod : (row * (2^width signature) + col) % (2^width signature) = col := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
  have indexDiv : (row * (2^width signature) + col) / (2^width signature) = row := by
    simp [Nat.add_div, Nat.div_eq_of_lt bound]
    exact Nat.mod_lt _ dimensionPositive
  rw [actualEq]
  simpa only [QleisliKernel.Qirf.contractCircuit,entry,Matrix.entry,List.getElem?_map,List.getElem?_range,indexBound,
    if_true,Option.map_some,Option.getD_some,indexMod,indexDiv,
    List.getElem?_eq_getElem colBound,List.getElem?_eq_getElem rowBound] using coeff


/-- The executable finite check of the full-axis wrapper proves the encoded
operator equation for its original dependency matrix. No equality modulo phase
or producer-provided operator correspondence is used. -/
theorem check_encoded_original (signature : Basis) (meaning actual : Matrix)
    (required : Contract) (work left : Nat)
    (ok : (QleisliKernel.Finite.check [⟨signature,meaning⟩]
      (QleisliKernel.Qirf.contractCircuit signature) required required).run work = (.ok actual,left)) :
    Qleisli.Semantics.Finite.Encoded meaning required := by
  obtain ⟨_,_,_,_,_,_,cw,aw,lhs,lw,rhs,rw,constructed,_,_,_⟩ :=
    QleisliKernel.Finite.check_conditions _ _ _ _ _ _ _ ok
  obtain ⟨rows,cols,entries⟩ := circuitMatrix_entries signature meaning actual cw aw constructed
  obtain ⟨_,inputShape,outputShape,physicalShape,logicalShape,equation⟩ :=
    Qleisli.Finite.check_encoded _ _ _ _ _ _ _ ok
  refine ⟨by rw [← cols]; exact inputShape,outputShape,
    by rw [← rows]; exact physicalShape,logicalShape,?_⟩
  intro row col hr hc
  have accepted := equation row col (by simpa [rows] using hr) hc
  rw [cols] at accepted
  rw [← accepted]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [entries row k hr (List.mem_range.mp hk)]


/-- The original operator satisfies the checked encoded equation on every
joint input/reference amplitude function. References need not be finite,
separable or normalized; only the physical matrix sums are finite. -/
theorem check_reference_original {R : Type} (signature : Basis) (meaning actual : Matrix)
    (required : Contract) (work left : Nat)
    (ok : (QleisliKernel.Finite.check [⟨signature,meaning⟩]
      (QleisliKernel.Qirf.contractCircuit signature) required required).run work = (.ok actual,left))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) (bound : row < meaning.rows) :
    action meaning (fun index r => action required.input.map joint index r) row reference =
      action required.output.map (fun index r => action required.logical joint index r) row reference := by
  obtain ⟨_,_,_,_,_,_,cw,aw,lhs,lw,rhs,rw,constructed,_,_,_⟩ :=
    QleisliKernel.Finite.check_conditions _ _ _ _ _ _ _ ok
  obtain ⟨rows,cols,entries⟩ := circuitMatrix_entries signature meaning actual cw aw constructed
  have accepted := Qleisli.Finite.check_reference _ _ _ _ _ _ _ ok joint row reference
    (by simpa [rows] using bound)
  rw [← accepted]
  unfold action
  rw [cols]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [entries row k bound (List.mem_range.mp hk)]

end Qleisli.NativeContract.Wrapper
