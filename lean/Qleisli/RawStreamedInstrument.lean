import QleisliKernel.Raw.StreamedInstrument
import Qleisli.RawCoefficient
import Qleisli.RawBranchFunction
import Mathlib.Data.List.Forall2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Qleisli.Semantics.InstrumentComplete

/-! Matrix-free actual instrument refinement and complete positivity on every
finite reference system. Complete trace equations come from the executable
streamed Gram check, without a producer matrix or an isometry premise.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.StreamedInstrument
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Observation
open QleisliKernel.Raw.StreamedInstrument QleisliKernel.Finite Qleisli.Semantics.Exact
open scoped BigOperators Matrix
open scoped ComplexOrder
set_option maxHeartbeats 2000000

abbrev Literal := Qleisli.Semantics.ObservingAction.History

def Related (checked : History) (literal : Literal) : Prop :=
  checked.values = literal.values ∧ checked.hidden = literal.hidden ∧
    ∀ col, ProtectedEvaluation.StateMeaning (fun row => checked.operator row col) (fun row => literal.operator row col)

private theorem map_related {A B C D : Type} (checked : A → WorkM B) (literal : C → Option D)
    (R : A → C → Prop) (S : B → D → Prop)
    (sound : ∀ a c, R a c → ∀ b work left, (checked a).run work = (.ok b,left) →
      ∃ d, literal c = some d ∧ S b d)
    (xs : List A) (ys : List C) (related : List.Forall₂ R xs ys) (actual : List B) (work left : Nat)
    (ok : (xs.mapM checked).run work = (.ok actual,left)) :
    ∃ result, ys.mapM literal = some result ∧ List.Forall₂ S actual result := by
  induction related generalizing actual work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    exact ⟨[],rfl,.nil⟩
  | cons head tail ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value,middle,hv,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,after,hr,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst actual
    obtain ⟨next,hn,relation⟩ := sound _ _ head _ _ _ hv
    obtain ⟨remaining,hm,relations⟩ := ih rest middle after hr
    exact ⟨next::remaining,by simp [List.mapM_cons,hn,hm],.cons relation relations⟩

private theorem map_option {A B : Type} (checked : A → WorkM B) (literal : A → Option B)
    (sound : ∀ a b work left, (checked a).run work = (.ok b,left) → literal a = some b)
    (xs : List A) (actual : List B) (work left : Nat)
    (ok : (xs.mapM checked).run work = (.ok actual,left)) : xs.mapM literal = some actual := by
  induction xs generalizing actual work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    rfl
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok ⊢
    obtain ⟨b,middle,hb,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,after,hr,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst actual
    simp [sound _ _ _ _ hb,ih _ _ _ hr]

private theorem values_map (choice : Bool) (phis : List ClassicalPhi) (values : QleisliKernel.Raw.Instrument.Values)
    (actual : List (Nat × Bool)) (work left : Nat)
    (ok : (phis.mapM (fun (phi : ClassicalPhi) => do
      pure (phi.output,← QleisliKernel.Raw.Instrument.lookup values (if choice then phi.thenId else phi.elseId)))).run work =
      (.ok actual,left)) :
    phis.mapM (fun (phi : ClassicalPhi) => do
      pure (phi.output,← Qleisli.Semantics.RawInstrument.value values (if choice then phi.thenId else phi.elseId))) = some actual := by
  apply map_option _ _ _ _ _ _ _ ok
  intro phi value work left accepted
  obtain ⟨v,middle,hv,h⟩ := bind_success _ _ _ _ _ accepted
  have same := (pure_success _ _ _ _ h).1
  subst value
  simp [Instrument.Denotation.lookup_reference _ _ _ _ _ hv]

theorem merge_related (choice : Bool) (phis : List ClassicalPhi) (checked : History) (literal : Literal)
    (related : Related checked literal) (actual : History) (work left : Nat)
    (ok : (merge choice phis checked).run work = (.ok actual,left)) :
    ∃ result, Qleisli.Semantics.ObservingAction.merge choice phis literal = some result ∧ Related actual result := by
  obtain ⟨values,middle,hv,h⟩ := bind_success _ _ _ _ _ ok
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have read := values_map _ _ _ _ _ _ hv
  refine ⟨{literal with values := literal.values ++ values},?_,?_,related.2.1,related.2.2⟩
  · simp only [Qleisli.Semantics.ObservingAction.merge,← related.1,read]
    rfl
  · simp only [related.1]

theorem step_related (dependencies : List Dependency)
    (checkedRecurse : List Event → History → WorkM (List History))
    (literalRecurse : List Event → Literal → Option (List Literal))
    (sound : ∀ events checked literal, Related checked literal → ∀ actual work left,
      (checkedRecurse events checked).run work = (.ok actual,left) →
      ∃ result, literalRecurse events literal = some result ∧ List.Forall₂ Related actual result)
    (event : Event) (checked : History) (literal : Literal) (related : Related checked literal)
    (actual : List History) (work left : Nat)
    (ok : (step dependencies checkedRecurse event checked).run work = (.ok actual,left)) :
    ∃ result, Qleisli.Semantics.ObservingAction.step dependencies literalRecurse event literal = some result ∧
      List.Forall₂ Related actual result := by
  obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  cases event with
  | pure operation =>
    have same := (pure_success _ _ _ _ h).1
    subst actual
    refine ⟨_,rfl,.cons ⟨related.1,related.2.1,?_⟩ .nil⟩
    intro col
    exact Coefficient.event_meaning _ _ _ _ (related.2.2 col)
  | erase bits axes output =>
    obtain ⟨_,after,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,last,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst actual
    refine ⟨_,rfl,?_⟩
    apply List.rel_map ?_ (List.forall₂_refl (Rₐ := Eq) (List.range (2^axes.length)))
    intro a b same
    subst b
    refine ⟨?_,by simp [related.2.1],?_⟩
    · cases output <;> simp [QleisliKernel.Raw.Instrument.recordValue,related.1]
    · intro col
      exact Coefficient.erased_meaning _ _ _ _ _ (related.2.2 col)
  | classical expr output =>
    obtain ⟨value,after,hv,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst actual
    have read := Instrument.Denotation.expression_reference _ _ _ _ _ hv
    rw [related.1] at read
    refine ⟨[{literal with values := literal.values ++ [(output,value)]}],
      by simp [Qleisli.Semantics.ObservingAction.step,read],.cons ?_ .nil⟩
    exact ⟨by simp [related.1],related.2.1,related.2.2⟩
  | branch condition thenEvents elseEvents phis =>
    obtain ⟨choice,after,hc,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨next,last,hn,h⟩ := bind_success _ _ _ _ _ h
    have read := Instrument.Denotation.lookup_reference _ _ _ _ _ hc
    rw [related.1] at read
    obtain ⟨literalNext,recurred,relations⟩ := sound _ _ _ related _ _ _ hn
    obtain ⟨result,merged,relations⟩ := map_related (merge choice phis)
      (Qleisli.Semantics.ObservingAction.merge choice phis) Related Related
      (fun a b rel c work left accepted => merge_related _ _ _ _ rel _ _ _ accepted)
      next literalNext relations actual last left h
    exact ⟨result,by simp [Qleisli.Semantics.ObservingAction.step,read,recurred,merged],relations⟩

private theorem fold_related (dependencies : List Dependency)
    (checkedRecurse : List Event → History → WorkM (List History))
    (literalRecurse : List Event → Literal → Option (List Literal))
    (sound : ∀ events checked literal, Related checked literal → ∀ actual work left,
      (checkedRecurse events checked).run work = (.ok actual,left) →
      ∃ result, literalRecurse events literal = some result ∧ List.Forall₂ Related actual result)
    (events : List Event) (checked : List History) (literal : List Literal)
    (related : List.Forall₂ Related checked literal) (actual : List History) (work left : Nat)
    (ok : (events.foldlM (fun (histories : List History) event => do
      let next ← histories.mapM (step dependencies checkedRecurse event)
      return next.flatten) checked).run work = (.ok actual,left)) :
    ∃ result, events.foldlM (fun (histories : List Literal) event => do
      let next ← histories.mapM (Qleisli.Semantics.ObservingAction.step dependencies literalRecurse event)
      return next.flatten) literal = some result ∧ List.Forall₂ Related actual result := by
  induction events generalizing checked literal work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    exact ⟨literal,rfl,related⟩
  | cons event events ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨groups,after,hg,h⟩ := bind_success _ _ _ _ _ hn
    have same := (pure_success _ _ _ _ h).1
    subst next
    obtain ⟨literalGroups,hl,relations⟩ := map_related (step dependencies checkedRecurse event)
      (Qleisli.Semantics.ObservingAction.step dependencies literalRecurse event)
      Related (List.Forall₂ Related)
      (fun a b rel c work left accepted => step_related _ _ _ sound _ _ _ rel _ _ _ accepted)
      _ _ related _ _ _ hg
    obtain ⟨result,rest,relations⟩ := ih groups.flatten literalGroups.flatten (List.rel_flatten relations) middle hr
    refine ⟨result,?_,relations⟩
    simp only [List.foldlM_cons,hl]
    exact rest

theorem run_related (dependencies : List Dependency) (fuel : Nat) (events : List Event)
    (checked : History) (literal : Literal) (related : Related checked literal)
    (actual : List History) (work left : Nat)
    (ok : (run dependencies fuel events checked).run work = (.ok actual,left)) :
    ∃ result, Qleisli.Semantics.ObservingAction.run dependencies fuel events literal = some result ∧
      List.Forall₂ Related actual result := by
  induction fuel generalizing events checked literal actual work left with
  | zero => cases ok
  | succ fuel ih =>
    change (events.foldlM (fun (histories : List History) event => do
      let next ← histories.mapM (step dependencies (run dependencies fuel) event)
      return next.flatten) [checked]).run work = (.ok actual,left) at ok
    change ∃ result, events.foldlM (fun (histories : List Literal) event => do
      let next ← histories.mapM (Qleisli.Semantics.ObservingAction.step dependencies
        (Qleisli.Semantics.ObservingAction.run dependencies fuel) event)
      return next.flatten) [literal] = some result ∧ List.Forall₂ Related actual result
    exact fold_related dependencies (run dependencies fuel) (Qleisli.Semantics.ObservingAction.run dependencies fuel)
      (fun events checked literal rel actual work left success => ih events checked literal rel actual work left success)
      events [checked] [literal] (.cons related .nil) actual work left ok

theorem initial_related (values : QleisliKernel.Raw.Instrument.Values) :
    Related (initial values) (Qleisli.Semantics.ObservingAction.initial values) := by
  refine ⟨rfl,rfl,?_⟩
  intro col row actual work left ok
  have same := (pure_success _ _ _ _ ok).1
  subst actual
  by_cases same : row = col <;>
    simp [Qleisli.Semantics.ObservingAction.initial,same,
      Exact.scalar_one_meaning,Exact.scalar_zero_meaning]

noncomputable def literalInner (dimension : Nat) (history : Literal) (row col : Nat) : ℂ :=
  ((List.range dimension).map fun output => star (history.operator output row) * history.operator output col).sum

theorem inner_meaning (dimension : Nat) (checked : History) (literal : Literal)
    (related : Related checked literal) (row col : Nat) (actual : Scalar) (work left : Nat)
    (ok : (inner dimension checked row col).run work = (.ok actual,left)) :
    scalar actual = literalInner dimension literal row col := by
  apply Coefficient.sum_meaning _ _ _ _ _ _ _ ok
  intro output value work left success
  obtain ⟨a,w₁,ha,h⟩ := bind_success _ _ _ _ _ success
  obtain ⟨b,w₂,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨adjoint,w₃,hc,hm⟩ := bind_success _ _ _ _ _ h
  have result := ProtectedEvaluation.multiply_meaning _ _ _ _ _ hm
  rw [Exact.scalar_conjugate_preserves _ _ (arithmetic_success _ _ (lift_success _ _ _ _ hc).1),
    related.2.2 row _ _ _ _ ha,related.2.2 col _ _ _ _ hb] at result
  exact result

private theorem gram_fold (dimension : Nat) (checked : List History) (literal : List Literal)
    (related : List.Forall₂ Related checked literal) (row col : Nat) (initial actual : Scalar) (work left : Nat)
    (ok : (checked.foldlM (fun previous history => do
      let value ← inner dimension history row col
      lift (arithmetic (QleisliKernel.Exact.Scalar.add previous value))) initial).run work = (.ok actual,left)) :
    scalar actual = scalar initial + (literal.map (fun history => literalInner dimension history row col)).sum := by
  induction related generalizing initial work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    simp
  | cons head tail ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨value,after,hv,ha⟩ := bind_success _ _ _ _ _ hn
    have added := Exact.scalar_add_preserves _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ ha).1)
    have rest := ih next middle hr
    rw [added,inner_meaning _ _ _ head _ _ _ _ _ hv] at rest
    simpa only [List.map_cons,List.sum_cons,add_assoc] using rest

theorem gramEntry_meaning (dimension : Nat) (checked : List History) (literal : List Literal)
    (related : List.Forall₂ Related checked literal) (row col : Nat) (actual : Scalar) (work left : Nat)
    (ok : (gramEntry dimension checked row col).run work = (.ok actual,left)) :
    scalar actual = (literal.map (fun history => literalInner dimension history row col)).sum := by
  simpa only [Exact.scalar_zero_meaning,zero_add] using gram_fold _ _ _ related _ _ _ _ _ _ ok

private theorem fold_checked {A : Type} (step : A → WorkM Unit) (items : List A) (work left : Nat)
    (ok : (items.foldlM (fun _ item => step item) ()).run work = (.ok (),left)) :
    ∀ item ∈ items, ∃ a b, (step item).run a = (.ok (),b) := by
  induction items generalizing work with
  | nil => simp
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    cases next
    intro chosen member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨work,middle,hn⟩
    · exact ih middle hr chosen member

theorem complete_meaning (inputDimension outputDimension : Nat) (checked : List History) (literal : List Literal)
    (related : List.Forall₂ Related checked literal) (work left : Nat)
    (ok : (complete inputDimension outputDimension checked).run work = (.ok (),left)) :
    ∀ row col, row < inputDimension → col < inputDimension →
      (literal.map (fun h => literalInner outputDimension h row col)).sum = if row = col then 1 else 0 := by
  obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  intro row col hr hc
  obtain ⟨a,b,rows⟩ := fold_checked _ _ _ _ h row (List.mem_range.mpr hr)
  obtain ⟨c,d,cols⟩ := fold_checked _ _ _ _ rows col (List.mem_range.mpr hc)
  obtain ⟨actual,after,hg,h⟩ := bind_success _ _ _ _ _ cols
  have same := beq_iff_eq.mp (guard_success _ _ _ _ h).1
  have meaning := gramEntry_meaning _ _ _ related _ _ _ _ _ hg
  rw [same] at meaning
  by_cases equal : row = col <;>
    simpa [equal,Exact.scalar_one_meaning,Exact.scalar_zero_meaning] using meaning.symm

theorem inspect_denotes (inputs : List QleisliKernel.Semantics.ObservingFunction.Input)
    (bindings : List QleisliKernel.Semantics.ObservingFunction.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    ∃ literal,
      Qleisli.Semantics.ObservingFunction.GraphMeaning checked.receipts ∧
      checked.receipts.map (·.input) = inputs ∧ inputs = bindings ∧
      Qleisli.Semantics.ObservingAction.program
        (checked.receipts.map QleisliKernel.Semantics.ObservingFunction.Receipt.dependency) program classical = some literal ∧
      List.Forall₂ Related checked.histories literal ∧
      ∀ row col, row < 2^checked.structureCheck.prepared.inputBits → col < 2^checked.structureCheck.prepared.inputBits →
        (literal.map (fun h => literalInner (2^checked.structureCheck.state.quantum.frame.length) h row col)).sum =
          if row = col then 1 else 0 := by
  rcases inspect_execution _ _ _ _ _ _ _ ok with ⟨a,b,c,d,e,f,g,h,hf,hv,_,he,hg⟩
  have graph := BranchFunction.checkAll_semantics _ _ _ _ _ hf
  have original := (QleisliKernel.Raw.Observation.verify_conditions _ _ _ _ _ hv).2.2
  obtain ⟨literal,read,related⟩ := run_related _ _ _ _ _ (initial_related _) _ _ _ he
  refine ⟨literal,graph.1,graph.2.1,graph.2.2,?_,related,complete_meaning _ _ _ _ related _ _ hg⟩
  simp [Qleisli.Semantics.ObservingAction.program,original,read]

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last] using congrArg (fun z => z + f n) ih

noncomputable def family (inputDimension outputDimension : Nat) (literal : List Literal) (index : Fin literal.length) :
    _root_.Matrix (Fin outputDimension) (Fin inputDimension) ℂ :=
  fun row col => literal[index].operator row col

/-- No dimension bound occurs in this equation. All coefficients are checked
by the actual streamed evaluator; the original denotation is independently read. -/
theorem accepted_kraus_complete (inputs : List QleisliKernel.Semantics.ObservingFunction.Input)
    (bindings : List QleisliKernel.Semantics.ObservingFunction.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left))
    (literal : List Literal)
    (meaning : Qleisli.Semantics.ObservingAction.program
      (checked.receipts.map QleisliKernel.Semantics.ObservingFunction.Receipt.dependency) program classical = some literal) :
    let K := family (2^checked.structureCheck.prepared.inputBits) (2^checked.structureCheck.state.quantum.frame.length) literal
    ∑ i, (K i)ᴴ * K i = 1 := by
  obtain ⟨original,_,_,_,read,_,complete⟩ := inspect_denotes _ _ _ _ _ _ _ ok
  have same := Option.some.inj (meaning.symm.trans read)
  subst original
  ext row col
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply]
  have lists : (literal.map (fun h => literalInner (2^checked.structureCheck.state.quantum.frame.length) h row col)).sum =
      ∑ i, ∑ k, star (family (2^checked.structureCheck.prepared.inputBits)
        (2^checked.structureCheck.state.quantum.frame.length) literal i k row) *
        family (2^checked.structureCheck.prepared.inputBits) (2^checked.structureCheck.state.quantum.frame.length) literal i k col := by
    rw [← List.ofFn_getElem_eq_map literal (fun h => literalInner (2^checked.structureCheck.state.quantum.frame.length) h row col),List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    exact range_sum _ _
  rw [← lists]
  simpa only [Fin.ext_iff] using complete row col row.isLt col.isLt

/-- Complete positivity for a coarse public outcome retains all its hidden
histories and any finite reference; no product-state or normalization premise. -/
theorem outcome_positive {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (inputDimension outputDimension : Nat) (literal : List Literal) (selected : Fin literal.length → Bool)
    (rho : _root_.Matrix (Fin inputDimension × Reference) (Fin inputDimension × Reference) ℂ)
    (positive : rho.PosSemidef) :
    (∑ i, if selected i then Qleisli.Semantics.Instrument.density
      (family inputDimension outputDimension literal i) rho else 0).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  split
  · exact positive.mul_mul_conjTranspose_same _
  · exact Matrix.PosSemidef.zero

theorem accepted_trace_preserving {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (inputs : List QleisliKernel.Semantics.ObservingFunction.Input)
    (bindings : List QleisliKernel.Semantics.ObservingFunction.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left))
    (literal : List Literal)
    (meaning : Qleisli.Semantics.ObservingAction.program
      (checked.receipts.map QleisliKernel.Semantics.ObservingFunction.Receipt.dependency) program classical = some literal)
    (rho : _root_.Matrix (Fin (2^checked.structureCheck.prepared.inputBits) × Reference)
      (Fin (2^checked.structureCheck.prepared.inputBits) × Reference) ℂ) :
    ∑ i, Matrix.trace (Qleisli.Semantics.Instrument.density (family (2^checked.structureCheck.prepared.inputBits)
      (2^checked.structureCheck.state.quantum.frame.length) literal i) rho) = Matrix.trace rho := by
  exact Qleisli.Semantics.Instrument.complete_trace _ (accepted_kraus_complete _ _ _ _ _ _ _ ok _ meaning) rho

theorem accepted_outcome_trace_nonincreasing {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (inputs : List QleisliKernel.Semantics.ObservingFunction.Input)
    (bindings : List QleisliKernel.Semantics.ObservingFunction.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left))
    (literal : List Literal)
    (meaning : Qleisli.Semantics.ObservingAction.program
      (checked.receipts.map QleisliKernel.Semantics.ObservingFunction.Receipt.dependency) program classical = some literal)
    (selected : Fin literal.length → Bool)
    (rho : _root_.Matrix (Fin (2^checked.structureCheck.prepared.inputBits) × Reference)
      (Fin (2^checked.structureCheck.prepared.inputBits) × Reference) ℂ) (positive : rho.PosSemidef) :
    (∑ i, if selected i then Matrix.trace (Qleisli.Semantics.Instrument.density
      (family (2^checked.structureCheck.prepared.inputBits) (2^checked.structureCheck.state.quantum.frame.length) literal i) rho) else 0).re ≤
      (Matrix.trace rho).re := by
  have total := accepted_trace_preserving _ _ _ _ _ _ _ ok _ meaning rho
  rw [← total,Complex.re_sum,Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  split
  · rfl
  · simpa using Complex.re_le_re (positive.mul_mul_conjTranspose_same
      (Qleisli.Semantics.Instrument.withReference (family (2^checked.structureCheck.prepared.inputBits)
        (2^checked.structureCheck.state.quantum.frame.length) literal i))).trace_nonneg

end Qleisli.Raw.StreamedInstrument
