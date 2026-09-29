import Qleisli.HierarchicalFourierBody
import Qleisli.HierarchicalWiring
import Qleisli.HierarchicalFiniteUnitary
import QleisliKernel.Hierarchical.FourierRoot

/-! Actual outer Fourier coefficients under the bound finite H equations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
P0 actual-entry/request binding; P1 reusable routing/composition lemmas.
Complete resource typing and native/finite-reader correspondence are separate
obligations. No producer whole-circuit matrix or routing summary is assumed. -/

namespace Qleisli.HierarchicalFourierRoot
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalSemantics HierarchicalFourier
open HierarchicalUnitary HierarchicalFiniteEvaluation
open scoped BigOperators Matrix

theorem identity_matrix (n : Nat) (op : Operator)
    (ready : HierarchicalWiring.At n (List.range n) op) : matrixAt n n op = 1 := by
  ext output input
  have selected : HierarchicalWiring.select (List.range n) (List.ofFn input) = List.ofFn input := by
    simpa [HierarchicalWiring.select] using range_select (List.ofFn input)
  rw [matrixAt,ready.2.2.2.2 (List.ofFn output) (List.ofFn input) (by simp) (by simp)]
  simp only [selected,List.ofFn_inj]
  simp [Matrix.one_apply]

theorem reverse_select (n : Nat) (input : Fin n → Bool) :
    HierarchicalWiring.select (List.range n).reverse (List.ofFn input) = List.ofFn (reverseBits input) := by
  have selected := range_select (List.ofFn input)
  simp only [List.length_ofFn] at selected
  rw [HierarchicalWiring.select,List.map_reverse,selected]
  apply List.ext_getElem
  · simp
  · intro i left right
    simp only [List.getElem_reverse,List.length_ofFn,List.getElem_ofFn,reverseBits]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

theorem reversal_matrix (n : Nat) (op : Operator)
    (ready : HierarchicalWiring.At n (List.range n).reverse op) :
    matrixAt n n op = permutation (reversal n) := by
  ext output input
  rw [matrixAt,ready.2.2.2.2 (List.ofFn output) (List.ofFn input) (by simp) (by simp)]
  simp only [reverse_select,List.ofFn_inj]
  rfl

theorem fold_sizes (codes : List Wiring.Code) (start result : Wiring.Code)
    (computed : codes.foldlM Wiring.compose start = some result) :
    ∀ code ∈ codes, code.length = start.length := by
  induction codes generalizing start with
  | nil => simp
  | cons code codes ih =>
    cases hc : Wiring.compose start code with
    | none => simp [List.foldlM,hc] at computed
    | some next =>
      have rest : codes.foldlM Wiring.compose next = some result := by simpa [List.foldlM,hc] using computed
      unfold Wiring.compose at hc
      split at hc
      next sizes =>
        cases Option.some.inj hc
        intro c member
        rcases List.mem_cons.mp member with same | inside
        · subst c; exact sizes.symm
        · simpa [sizes] using ih _ rest c inside
      next impossible => contradiction

theorem dimensions (n : Nat) (codes : List Wiring.Code) (ops : List Operator)
    (ready : List.Forall₂ (fun code op => HierarchicalWiring.At code.length code op) codes ops)
    (sizes : ∀ code ∈ codes, code.length = n) :
    ∀ op ∈ ops, op.inputWidth = n ∧ op.outputWidth = n := by
  induction ready with
  | nil => simp
  | @cons code op codes ops head tail ih =>
    intro child member
    rcases List.mem_cons.mp member with same | inside
    · subst child
      simpa [sizes code (by simp)] using And.intro head.2.2.1 head.2.2.2.1
    · exact ih (fun c h => sizes c (by simp [h])) child inside

theorem matrix_fold_mul (n : Nat) (ops : List Operator) (start : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    ops.foldl (fun current child => matrixAt n n child * current) start =
      ops.foldl (fun current child => matrixAt n n child * current) 1 * start := by
  induction ops generalizing start with
  | nil => simp
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih,ih (matrixAt n n op * 1)]
    simp [mul_assoc]

theorem outer_matrix (interface : Interface) (n : Nat) (enter body : Operator)
    (codes : List Wiring.Code) (ops : List Operator)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (enterAt : HierarchicalWiring.At n (List.range n) enter)
    (bodyAt : HierarchicalFourierBody.IsBody n body)
    (ready : List.Forall₂ (fun code op => HierarchicalWiring.At code.length code op) codes ops)
    (computed : codes.foldlM Wiring.compose (List.range n) = some (List.range n).reverse) :
    matrixAt n n (apply interface .sequence (enter::body::ops)) = fourier n := by
  have sizes : ∀ code ∈ codes, code.length = n := by simpa using fold_sizes codes _ _ computed
  have dims := dimensions n codes ops ready sizes
  have suffix := HierarchicalWiring.fold_at n codes ops ready _ _ (identity n)
    (HierarchicalWiring.identity_at n) computed
  have suffixMatrix := reversal_matrix n (HierarchicalOperators.sequence n ops) suffix
  rw [sequence_matrix n ops dims] at suffixMatrix
  have all : ∀ child ∈ enter::body::ops, child.inputWidth = n ∧ child.outputWidth = n := by
    intro child member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | inside
    · exact ⟨enterAt.2.2.1,enterAt.2.2.2.1⟩
    · exact ⟨bodyAt.1,bodyAt.2.1⟩
    · exact dims child inside
  rw [apply_sequence_matrix interface n _ hi ho all]
  simp only [List.foldl_cons,identity_matrix n enter enterAt,bodyAt.2.2,mul_one]
  rw [matrix_fold_mul,suffixMatrix,explicit_reversal]

/-- The actual entry, including owner renames and explicit final data reversal,
has the requested Fourier coefficients. Only returned finite H equations remain
as premises; recursive stages and all wiring are derived from actual bodies. -/
theorem inspect_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (request : FourierRoot.Request) (order : Array Nat) (remaining : Nat) (pending : FourierRoot.Pending)
    (accepted : FourierRoot.inspect artifact request order remaining = .ok pending)
    (equations : ∀ r ∈ pending.body.requests, HierarchicalHadamard.Equation leaves r) :
    ∃ fuel actual, physical algebra leaves artifact fuel artifact.entry.implementation = some actual ∧
      actual.inputWidth = request.width ∧ actual.outputWidth = request.width ∧
      matrixAt request.width request.width actual = fourier request.width := by
  obtain ⟨_,_,_,_,d,shell,found,projected,aligned,bodyChecked,wiringChecked,routed⟩ :=
    FourierRoot.inspect_conditions artifact request order remaining pending accepted
  obtain ⟨_,_,_,hi,ho⟩ := FourierRoot.aligned_fields request d aligned
  obtain ⟨enterRoute,suffixRoutes,composed⟩ := FourierRoot.routes_fields request.width shell pending.wiring.cache pending.codes routed
  have sound := (Wiring.inspect_sound artifact order _ pending.wiring wiringChecked).1
  have ready := fun i code h => HierarchicalWiring.derives_evaluates leaves artifact i code (sound i code h)
  obtain ⟨enterFuel,enter,enterEvaluated,enterAt⟩ := ready shell.enter _ enterRoute
  have enterAt : HierarchicalWiring.At request.width (List.range request.width) enter := by simpa using enterAt
  obtain ⟨suffixFuel,ops,suffixEvaluated,suffixAt⟩ :=
    HierarchicalWiring.children_evaluate leaves artifact pending.wiring.cache ready shell.suffix pending.codes suffixRoutes
  obtain ⟨bodyFuel,body,bodyEvaluated,bodyAt⟩ := HierarchicalFourierBody.inspect_evaluates leaves artifact
    request.width request.width shell.body _ pending.body bodyChecked equations
  let fuel := enterFuel+bodyFuel+suffixFuel
  have enterMore := evaluate_more algebra (definition leaves artifact) enterFuel shell.enter enter enterEvaluated fuel (by dsimp [fuel]; omega)
  have bodyMore := evaluate_more algebra (definition leaves artifact) bodyFuel shell.body body bodyEvaluated fuel (by dsimp [fuel]; omega)
  change physical algebra leaves artifact fuel shell.enter = some enter at enterMore
  change physical algebra leaves artifact fuel shell.body = some body at bodyMore
  have suffixMore := HierarchicalEvaluation.mapM_congr_success shell.suffix
    (physical algebra leaves artifact suffixFuel) (physical algebra leaves artifact fuel) ops suffixEvaluated
    (fun child _ value evaluated => evaluate_more algebra (definition leaves artifact) suffixFuel child value evaluated fuel (by dsimp [fuel]; omega))
  have code : physicalCode d = some (.sequence,shell.enter::shell.body::shell.suffix) := by
    simp [physicalCode,FourierRoot.project_body d shell projected]
  refine ⟨fuel+1,apply d.interface .sequence (enter::body::ops),?_,hi,ho,?_⟩
  · rw [physical_step algebra leaves artifact fuel artifact.entry.implementation d .sequence _ found code]
    change (((shell.enter::shell.body::shell.suffix).mapM (physical algebra leaves artifact fuel)).bind
      (fun values => some (apply d.interface .sequence values))) = _
    simp only [List.mapM_cons,enterMore,bodyMore,suffixMore,bind,Option.bind,pure]
  · exact outer_matrix d.interface request.width enter body pending.codes ops hi ho enterAt bodyAt suffixAt composed

/-- Full complex reference amplitudes, with no separability or probability-only
premise and no dependence on the evaluation fuel used by a client. -/
theorem inspect_joint_amplitude (leaves : Leaves Operator) (artifact : Artifact)
    (request : FourierRoot.Request) (order : Array Nat) (remaining fuel : Nat) (pending : FourierRoot.Pending)
    (accepted : FourierRoot.inspect artifact request order remaining = .ok pending)
    (equations : ∀ r ∈ pending.body.requests, HierarchicalHadamard.Equation leaves r)
    (actual : Operator) (evaluated : physical algebra leaves artifact fuel artifact.entry.implementation = some actual)
    {R : Type} (joint : (Fin request.width → Bool) → R → ℂ) (output : Fin request.width → Bool) (reference : R) :
    (∑ input, matrixAt request.width request.width actual output input * joint input reference) =
      ∑ input, fourier request.width output input * joint input reference := by
  obtain ⟨more,value,computed,_,_,matrix⟩ := inspect_evaluates leaves artifact request order remaining pending accepted equations
  have same := evaluate_unique algebra (definition leaves artifact) more fuel artifact.entry.implementation value actual computed evaluated
  subst value
  rw [matrix]

/-- The actual composite checker constructs a Fourier entry with the complete
requested unitary interface. Both sets of finite obligations are explicit. -/
theorem checkAll_unitary (leaves : Leaves Operator) (artifact : Artifact)
    (order : Array Nat) (request : FourierRoot.Request) (wiringOrder : Array Nat)
    (checked : FourierRoot.Checked)
    (accepted : FourierRoot.checkAll artifact order request wiringOrder = .ok checked)
    (implementations : ∀ r ∈ checked.artifact.state.requests.toList,
      HierarchicalFiniteUnitary.Leaf leaves r)
    (hadamards : ∀ r ∈ checked.binding.body.requests, HierarchicalHadamard.Equation leaves r) :
    ∃ fuel actual, physical algebra leaves artifact fuel artifact.entry.implementation = some actual ∧
      HierarchicalTyping.UnitaryInterface request.interface actual ∧
      matrixAt request.width request.width actual = fourier request.width := by
  obtain ⟨ha,hb,_⟩ := FourierRoot.checkAll_conditions artifact order request wiringOrder checked accepted
  obtain ⟨fuel,actual,evaluated,_,_,matrix⟩ := inspect_evaluates leaves artifact request wiringOrder _ checked.binding hb hadamards
  obtain ⟨_,_,_,_,d,shell,found,projected,aligned,_⟩ :=
    FourierRoot.inspect_conditions artifact request wiringOrder _ checked.binding hb
  have unitary := HierarchicalFiniteUnitary.checked_denotation_unitary leaves artifact order
    checked.artifact ha implementations d found fuel actual evaluated
  have header := (FourierRoot.aligned_fields request d aligned).2.1
  exact ⟨fuel,actual,evaluated,header ▸ unitary,matrix⟩

/-- Both inverse laws, including any finite reference extension, for that same
actual checked Fourier value. No extra semantic environment is assumed. -/
theorem checkAll_reference_laws {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves Operator) (artifact : Artifact) (order : Array Nat)
    (request : FourierRoot.Request) (wiringOrder : Array Nat) (checked : FourierRoot.Checked)
    (accepted : FourierRoot.checkAll artifact order request wiringOrder = .ok checked)
    (implementations : ∀ r ∈ checked.artifact.state.requests.toList,
      HierarchicalFiniteUnitary.Leaf leaves r)
    (hadamards : ∀ r ∈ checked.binding.body.requests, HierarchicalHadamard.Equation leaves r) :
    ∃ fuel actual, physical algebra leaves artifact fuel artifact.entry.implementation = some actual ∧
      matrixAt request.width request.width actual = fourier request.width ∧
      let n := width request.interface.inputs
      let joint := Matrix.kronecker (matrixAt n n actual) (1 : Matrix R R ℂ)
      jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 := by
  obtain ⟨fuel,actual,evaluated,unitary,matrix⟩ :=
    checkAll_unitary leaves artifact order request wiringOrder checked accepted implementations hadamards
  exact ⟨fuel,actual,evaluated,matrix,HierarchicalUnitary.reference_unitary unitary.1⟩

end Qleisli.HierarchicalFourierRoot
