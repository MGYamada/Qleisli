import Qleisli.RuntimeGraphTransformNodes

/-! Evaluate source coefficients in the exact order of the original operation
occurrences. A single stack induction carries each child's independent source
action to the parent, including repeated uses of one description index.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeGraphSourceEvaluation
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeSelectionSteps (Edge)
open RuntimeOperationTree (Value Record StackTrace)
open RuntimeGraphCoefficients (Coefficient Agrees dimension sequential tensor)
open RuntimeGraphLocalNodes (adjoint primitiveMeaning formalSourcePosition)
open RuntimeGraphTransformNodes (control repeatedAction)

abbrev Corresponds := List.Forall₂ (fun source value => Agrees value source)

noncomputable def sourceNode {artifact catalogue context description graph order root}
    (scope : List Edge)
    (record : @Record artifact catalogue context description graph order root) (children : List Coefficient) :
    Option Coefficient :=
  match record.checked.node with
  | .provider .. =>
    match record.checked.provider with
    | .absent _ => none
    | .present occurrence _ provider _ =>
      let basis := occurrence.header.original.supplied.provider.signature.outputs.headD []
      some (RuntimeProviderSourceEntry.evaluate provider.originalBody.body basis scope)
  | .thenOp .. =>
    match record.checked.children,children with
    | [_,second],[firstAction,secondAction] =>
      some (sequential (dimension second.input) firstAction secondAction)
    | _,_ => none
  | .tensor .. =>
    match record.checked.children,children with
    | [first,_],[low,high] => some (tensor (dimension first.output) (dimension first.input) low high)
    | _,_ => none
  | .inverse .. =>
    match children with
    | [child] => some (adjoint child)
    | _ => none
  | .requested .. =>
    match children with
    | [child] => some child
    | _ => none
  | .primitive kind target => (primitiveMeaning kind target).map Qleisli.Semantics.Exact.entry
  | .formal _ _ _ _ operations ordinal => do
    let position ← formalSourcePosition record.occurrence.result operations ordinal
    children[position]?
  | .controlled .. =>
    match children with
    | [child] => some (control child)
    | _ => none
  | .power _ count =>
    match record.checked.children,children with
    | [child],[meaning] => some (repeatedAction (dimension child.input) meaning count)
    | _,_ => none
  | .conjugate .. =>
    match record.checked.children,children with
    | [outer,middle],[outerSource,middleSource] =>
      some (sequential (dimension outer.input)
        (sequential (dimension middle.input) (adjoint outerSource) middleSource) outerSource)
    | _,_ => none

private theorem lookup_related {sources : List Coefficient} {values : List Value}
    (paired : Corresponds sources values) (index : Nat) {value : Value}
    (found : values[index]? = some value) :
    ∃ source, sources[index]? = some source ∧ Agrees value source := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons source head sources values agrees _ ih =>
    cases index with
    | zero =>
      have same : head = value := Option.some.inj found
      exact ⟨source,rfl,same ▸ agrees⟩
    | succ index =>
      obtain ⟨result,lookup,related⟩ := ih index found
      exact ⟨result,lookup,related⟩

theorem source_node {artifact catalogue context description graph order root}
    (scope : List Edge) (record : @Record artifact catalogue context description graph order root)
    (children : List Coefficient) (related : Corresponds children record.checked.children) :
    ∃ source, sourceNode scope record children = some source ∧ Agrees record.checked.output source := by
  cases original : record.checked.node with
  | provider moduleName declarationName bases naturals operations =>
    obtain ⟨provider,_,checked,_,receipt,value⟩ :=
      RuntimeProviderOccurrenceAction.provider_node record.checked _ _ _ _ _ original
    let basis := provider.header.original.supplied.provider.signature.outputs.headD []
    have declared : provider.header.original.supplied.provider.signature.outputs = [basis] := by
      unfold basis
      rw [checked.paths.ir.original.prepared.ports.sourceOutputs]
      rfl
    let evaluate := RuntimeProviderSourceEntry.evaluate checked.originalBody.body basis scope
    refine ⟨evaluate,?_,⟨(RuntimeGraphCoefficients.shape _).1,(RuntimeGraphCoefficients.shape _).2,?_⟩⟩
    · simp only [sourceNode,original,receipt,evaluate,basis]
    · intro row col rowBound colBound
      change row < record.checked.value.rows at rowBound
      change col < record.checked.value.cols at colBound
      rw [value] at rowBound colBound
      change evaluate row col = Qleisli.Semantics.Exact.entry record.checked.value row col
      rw [value]
      exact RuntimeProviderSourceEntry.exact_entry checked declared
        scope row col rowBound colBound
  | thenOp leftIndex rightIndex =>
    obtain ⟨first,second,same,_,_⟩ := RuntimeGraphCoefficients.binary_children record.checked
      (show record.checked.node.children = [leftIndex,rightIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons leftAgrees tail =>
      cases tail with
      | cons rightAgrees empty =>
        cases empty
        refine ⟨_,?_,RuntimeGraphCoefficients.then_step record.checked original same leftAgrees rightAgrees⟩
        simp only [sourceNode,original,same]
  | tensor leftIndex rightIndex =>
    obtain ⟨first,second,same,_,_⟩ := RuntimeGraphCoefficients.binary_children record.checked
      (show record.checked.node.children = [leftIndex,rightIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons leftAgrees tail =>
      cases tail with
      | cons rightAgrees empty =>
        cases empty
        refine ⟨_,?_,RuntimeGraphCoefficients.tensor_step record.checked original same leftAgrees rightAgrees⟩
        simp only [sourceNode,original,same]
  | inverse childIndex =>
    obtain ⟨child,same,_⟩ := RuntimeGraphLocalNodes.unary_child record.checked
      (show record.checked.node.children = [childIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons childAgrees empty =>
      cases empty
      exact ⟨_,by simp only [sourceNode,original],
        RuntimeGraphLocalNodes.inverse_step record.checked original same childAgrees⟩
  | requested childIndex moduleName declarationName =>
    obtain ⟨child,same,_⟩ := RuntimeGraphLocalNodes.unary_child record.checked
      (show record.checked.node.children = [childIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons childAgrees empty =>
      cases empty
      exact ⟨_,by simp only [sourceNode,original],
        RuntimeGraphLocalNodes.requested_step record.checked original same childAgrees⟩
  | primitive kind target =>
    have size := record.checked.arity
    rw [original] at size
    have empty : record.checked.children = [] := List.eq_nil_of_length_eq_zero size
    obtain ⟨matrix,denoted,agrees⟩ := RuntimeGraphLocalNodes.primitive_step record.checked original empty
    exact ⟨_,by simp only [sourceNode,original,denoted,Option.map_some],agrees⟩
  | formal moduleName declarationName bases naturals operations ordinal =>
    obtain ⟨position,child,formal,found,value⟩ := RuntimeGraphLocalNodes.formal_step record.checked original
    obtain ⟨source,lookup,agrees⟩ := lookup_related related position found
    refine ⟨source,?_,⟨(RuntimeGraphCoefficients.shape _).1,(RuntimeGraphCoefficients.shape _).2,?_⟩⟩
    · simp only [sourceNode,original,formal,bind,Option.bind,lookup]
    · intro row col rowBound colBound
      change row < record.checked.value.rows at rowBound
      change col < record.checked.value.cols at colBound
      rw [value] at rowBound colBound
      change source row col = Qleisli.Semantics.Exact.entry record.checked.value row col
      rw [value]
      exact agrees.coefficient row col rowBound colBound
  | controlled childIndex =>
    obtain ⟨child,same,_⟩ := RuntimeGraphLocalNodes.unary_child record.checked
      (show record.checked.node.children = [childIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons childAgrees empty =>
      cases empty
      exact ⟨_,by simp only [sourceNode,original],
        RuntimeGraphTransformNodes.controlled_step record.checked original same childAgrees⟩
  | power childIndex count =>
    obtain ⟨child,same,_⟩ := RuntimeGraphLocalNodes.unary_child record.checked
      (show record.checked.node.children = [childIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons childAgrees empty =>
      cases empty
      refine ⟨_,?_,RuntimeGraphTransformNodes.power_step record.checked original same childAgrees⟩
      simp only [sourceNode,original,same]
  | conjugate outerIndex middleIndex =>
    obtain ⟨outer,middle,same,_,_⟩ := RuntimeGraphCoefficients.binary_children record.checked
      (show record.checked.node.children = [outerIndex,middleIndex] by rw [original]; rfl)
    rw [same] at related
    cases related with
    | cons outerAgrees tail =>
      cases tail with
      | cons middleAgrees empty =>
        cases empty
        refine ⟨_,?_,RuntimeGraphTransformNodes.conjugate_step record.checked original same outerAgrees middleAgrees⟩
        simp only [sourceNode,original,same]

noncomputable def advance {artifact catalogue context description graph order root}
    (scope : List Edge)
    (stack : List Coefficient) (record : @Record artifact catalogue context description graph order root) :
    Option (List Coefficient) := do
  let split := record.checked.remaining.length
  let node ← sourceNode scope record (stack.drop split)
  return stack.take split ++ [node]

theorem advance_sound {artifact catalogue context description graph order root}
    (scope : List Edge) (record : @Record artifact catalogue context description graph order root)
    (stack : List Coefficient) (related : Corresponds stack record.before) :
    ∃ output, advance scope stack record = some output ∧ Corresponds output record.checked.after := by
  rw [record.checked.partition] at related
  have retained := List.forall₂_take_append _ _ _ related
  have children := List.forall₂_drop_append _ _ _ related
  obtain ⟨source,executed,agrees⟩ := source_node scope record _ children
  refine ⟨_,?_,List.rel_append retained (.cons agrees .nil)⟩
  simp only [advance,executed,bind,Option.bind,pure]

/-- The successful native walk supplies every step boundary. The source
evaluation replays that same list and keeps all intermediate source values
in the original stack order. -/
theorem trace_sound {artifact catalogue context description graph order root}
    (scope : List Edge) {before records final}
    (trace : @StackTrace artifact catalogue context description graph order root before records final)
    (stack : List Coefficient) (related : Corresponds stack before) :
    ∃ output, records.foldlM (advance scope) stack = some output ∧ Corresponds output final := by
  induction trace generalizing stack with
  | nil => exact ⟨stack,rfl,related⟩
  | cons record _ ih =>
    obtain ⟨next,executed,agrees⟩ := advance_sound scope record stack related
    obtain ⟨output,rest,final⟩ := ih next agrees
    exact ⟨output,by simpa only [List.foldlM_cons,executed,bind,Option.bind] using rest,final⟩

theorem checked_graph {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations
      references prepared root requested)
    (scope : List Edge) :
    ∃ source, checked.outcome.records.foldlM (advance scope) [] = some [source] ∧
      Agrees checked.value source := by
  obtain ⟨output,executed,agrees⟩ := trace_sound scope checked.stack_trace [] .nil
  cases agrees with
  | cons agrees tail =>
    cases tail
    exact ⟨_,executed,agrees⟩

/-- The source graph's coefficient evaluator acts on arbitrary joint
references with the same exact action as its checked root. -/
theorem checked_graph_action {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations
      references prepared root requested)
    (scope : List Edge) :
    ∃ source, checked.outcome.records.foldlM (advance scope) [] = some [source] ∧
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row reference,
        row < checked.action.rows →
        ((List.range (dimension checked.value.input)).map fun col => source row col * joint col reference).sum =
          Qleisli.Semantics.Exact.action checked.action joint row reference := by
  obtain ⟨source,executed,agrees⟩ := checked_graph checked scope
  refine ⟨source,executed,?_⟩
  intro Reference joint row reference rowBound
  change row < checked.value.action.rows at rowBound
  change _ = Qleisli.Semantics.Exact.action checked.value.action joint row reference
  rw [← agrees.cols]
  unfold Qleisli.Semantics.Exact.action
  apply Qleisli.Exact.sum_map_congr
  intro col present
  rw [agrees.coefficient row col rowBound (List.mem_range.mp present)]

#print axioms checked_graph_action
#print axioms source_node
#print axioms checked_graph
end Qleisli.RuntimeGraphSourceEvaluation
