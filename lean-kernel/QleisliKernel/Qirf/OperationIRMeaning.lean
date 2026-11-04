import QleisliKernel.SourceTypes.StaticOperation
import QleisliKernel.Qirf.PureInterval
import QleisliKernel.Semantics.PrimitiveOperator

/-! Exact operation-tree evaluation over independently realized provider maps.
This calculation alone accepts neither a source body nor an IR program and
grants no access. Its enclosing caller must bind every provider occurrence to
the original source and actual final-root program, and check the complete
implementation/control/code equations. No dense joined qmatch matrix is built.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.OperationIRMeaning
open QleisliKernel QleisliKernel.SourceTypes Finite Semantics.Exact
open OperationDescription

def controlled (value : Matrix) : WorkM Matrix := do
  guard (value.rows == value.cols) .request
  let dimension := 2*value.rows
  guard (Exact.matrixValid dimension dimension) .limit
  exactWork (Exact.charge (dimension*dimension))
  let entries := (List.range (dimension*dimension)).map fun index =>
    let row := index / dimension
    let column := index % dimension
    if row % 2 != column % 2 then Scalar.zero
    else if row % 2 == 0 then if row / 2 == column / 2 then Scalar.one else Scalar.zero
    else value.entry (row / 2) (column / 2)
  lift (arithmetic (Exact.Matrix.make dimension dimension entries))

/-- All counts, including zero, receive their already checked child map. The
linear precharge precedes recursion; a huge untrusted count cannot make a free
zero-width loop. Source count/profile rules remain separately mandatory. -/
def power (value : Matrix) (count : Nat) : WorkM Matrix := do
  guard (value.rows == value.cols) .request
  exactWork (Exact.charge (8*(count+1)))
  let identity ← lift (arithmetic (Exact.Matrix.identity value.rows))
  let iterate : Nat → Matrix → WorkM Matrix :=
    Nat.rec pure (fun _ next accumulated => do
      let accumulated ← exactWork (Exact.Matrix.composeWork value accumulated)
      next accumulated)
  iterate count identity

def primitive (kind : Primitive) (target : Semantics.FiniteCarrier.Basis) : WorkM Matrix := do
  let layout ← FiniteCarrier.read target
  exactWork (Exact.charge ((layout.labels.length+1)^2))
  let reference := match kind with
    | .h => Semantics.PrimitiveOperator.Kind.h
    | .globalPhaseEighth => Semantics.PrimitiveOperator.Kind.globalPhaseEighth
  lift (readOption (Semantics.PrimitiveOperator.meaning reference target))

private def formalPosition {sources} (metadata : StaticOperation.Result sources)
    (operations : List (String × Nat)) (ordinal : Nat) : WorkM Nat := do
  let provider ← lift (readOption metadata.formal)
  match provider.signature.instantiation with
  | .closed _ => throw .request
  | .static _ environment _ =>
    let formal ← lift (readOption environment.numeric.original.header.formals[ordinal]?)
    guard (formal.ordinal == ordinal) .request
    let position := (operations.map (·.1)).idxOf formal.name
    guard (position < operations.length) .request
    return position

/-- Child values are occurrence values in the node's exact child order.
Repeated node indices never select a globally memoized provider value. Each
branch yields to the same carrier/shape checks; a branch-local `return` here
would exit the enclosing computation before those checks (#462). -/
def readNode {sources} (metadata : StaticOperation.Result sources) (node : Node)
    (children providers : List Matrix) (nextProvider : Nat) : WorkM (Matrix × Nat) := do
  let calculate : WorkM (Matrix × Nat) := match node,children with
    | .provider ..,_ => do
      pure (← lift (readOption providers[nextProvider]?),nextProvider+1)
    | .formal _ _ _ _ operations ordinal,_ => do
      let position ← formalPosition metadata operations ordinal
      pure (← lift (readOption children[position]?),nextProvider)
    | .primitive kind target,[] => do pure (← primitive kind target,nextProvider)
    | .requested _ _ _,[value] => pure (value,nextProvider)
    | .inverse _,[value] => do pure (← exactWork (Exact.Matrix.adjointWork value),nextProvider)
    | .controlled _,[value] => do pure (← controlled value,nextProvider)
    | .power _ count,[value] => do pure (← power value count,nextProvider)
    | .thenOp _ _,[first,second] => do
      pure (← exactWork (Exact.Matrix.composeWork second first),nextProvider)
    | .tensor _ _,[first,second] => do
      pure (← exactWork (Exact.Matrix.tensorWork first second),nextProvider)
    | .conjugate _ _,[outer,middle] => do
      let adjoint ← exactWork (Exact.Matrix.adjointWork outer)
      let inner ← exactWork (Exact.Matrix.composeWork middle adjoint)
      pure (← exactWork (Exact.Matrix.composeWork outer inner),nextProvider)
    | _,_ => throw .request
  let (value,nextProvider) ← calculate
  let input ← FiniteCarrier.read metadata.input
  let output ← FiniteCarrier.read metadata.output
  guard (value.cols == input.labels.length && value.rows == output.labels.length) .request
  return (value,nextProvider)

/-- Success of the executable evaluator, for every node and starting budget,
retains both actual carrier reads and exact declared logical dimensions. No
caller-supplied shape premise or reference-only acceptance predicate is used. -/
theorem readNode_shape {sources} (metadata : StaticOperation.Result sources) (node : Node)
    (children providers : List Matrix) (nextProvider : Nat) (value : Matrix)
    (consumed work left : Nat)
    (ran : (readNode metadata node children providers nextProvider).run work =
      (.ok (value,consumed),left)) :
    ∃ (input output : Semantics.FiniteCarrier.Layout) (before afterInput afterOutput : Nat),
      (FiniteCarrier.read metadata.input).run before = (.ok input,afterInput) ∧
      (FiniteCarrier.read metadata.output).run afterInput = (.ok output,afterOutput) ∧
      Semantics.FiniteCarrier.layout metadata.input = some input ∧
      Semantics.FiniteCarrier.layout metadata.output = some output ∧
      value.cols = input.labels.length ∧ value.rows = output.labels.length := by
  unfold readNode at ran
  obtain ⟨⟨actual,used⟩,before,_,tail⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨input,afterInput,inputRead,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨output,afterOutput,outputRead,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨done,afterGuard,checked,returned⟩ := bind_success _ _ _ _ _ tail
  cases done
  have sameValue : (value,consumed) = (actual,used) := (pure_success _ _ _ _ returned).1
  have dimensions := Bool.and_eq_true_iff.mp (guard_success _ _ _ _ checked).1
  refine ⟨input,output,before,afterInput,afterOutput,inputRead,outputRead,
    FiniteCarrier.read_reference _ _ _ _ inputRead,
    FiniteCarrier.read_reference _ _ _ _ outputRead,?_,?_⟩
  · rw [show value = actual from congrArg Prod.fst sameValue]
    exact beq_iff_eq.mp dimensions.1
  · rw [show value = actual from congrArg Prod.fst sameValue]
    exact beq_iff_eq.mp dimensions.2

#print axioms readNode_shape

private def visit {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (providers : List Matrix) :
    Nat → Nat → Nat → WorkM (Matrix × Nat) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next index nextProvider => do
    let node ← lift (readOption description.nodes[index]?)
    let metadata ← lift (readOption graph.results[index]?)
    let (children,nextProvider) ← node.children.foldlM (fun (children,nextProvider) child => do
      let (value,nextProvider) ← next child nextProvider
      return (children ++ [value],nextProvider)) ([],nextProvider)
    readNode metadata node children providers nextProvider)

/-- Every child edge is visited, including shared DAG children, providers in a
zero power and every unused formal actual. The existing 4096-node TREE profile
is checked before expansion, so a compact DAG cannot evade that profile. -/
def compute {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (providers : List Matrix) : WorkM Matrix := do
  -- Metadata alone does not discharge any Meaning equation.
  guard (!graph.hasMeaningRequirements) .request
  let occurrences ← StaticOperation.readOccurrences description
  exactWork (Exact.charge (16*(description.nodes.length+graph.results.length+occurrences.length+providers.length+1)^2))
  let requiredProviders := occurrences.foldl (fun count index => match description.nodes[index]? with
    | some (.provider ..) => count+1
    | _ => count) 0
  guard (requiredProviders == providers.length) .request
  let (value,consumed) ← visit graph providers (occurrences.length+1) description.root 0
  guard (consumed == providers.length) .request
  return value

private theorem option_of_lift {α : Type} (entry : Option α) (value : α) (work left : Nat)
    (ran : (lift (readOption entry)).run work = (.ok value,left)) : entry = some value := by
  have selected := (lift_success _ _ _ _ ran).1
  cases entry with
  | none => cases selected
  | some actual => exact congrArg some (Except.ok.inj selected)

private theorem name_at_idxOf (names : List String) (name : String)
    (bound : names.idxOf name < names.length) : names[names.idxOf name]? = some name := by
  induction names with
  | nil => simp at bound
  | cons first rest ih =>
    by_cases same : first = name
    · subst first
      simp only [List.idxOf_cons_self,List.getElem?_cons_zero]
    · have different : (first == name) = false := beq_eq_false_iff_ne.mpr same
      have next : (first :: rest).idxOf name = rest.idxOf name+1 := by
        rw [List.idxOf_cons,different]
        rfl
      rw [next] at bound ⊢
      have smaller : rest.idxOf name < rest.length := by
        simp only [List.length_cons] at bound
        omega
      exact ih smaller

private theorem formalPosition_selection {sources} (metadata : StaticOperation.Result sources)
    (operations : List (String × Nat)) (ordinal position work left : Nat)
    (ran : (formalPosition metadata operations ordinal).run work = (.ok position,left)) :
    ∃ (provider : StaticOperation.Provider sources) (arguments : StaticTypes.Arguments)
      (environment : StaticTypes.Environment sources provider.moduleName provider.declarationName arguments)
      (sameOriginal : environment.numeric.original.envelope = provider.signature.original)
      (formal : StaticHeaders.Formal),
      metadata.formal = some provider ∧
      provider.signature.instantiation = .static arguments environment sameOriginal ∧
      environment.numeric.original.header.formals[ordinal]? = some formal ∧
      formal.ordinal = ordinal ∧ position = (operations.map (·.1)).idxOf formal.name ∧
      position < operations.length ∧ (operations.map (·.1))[position]? = some formal.name := by
  unfold formalPosition at ran
  obtain ⟨provider,middle,providerRead,tail⟩ := bind_success _ _ _ _ _ ran
  have present := option_of_lift metadata.formal provider work middle providerRead
  cases instantiation : provider.signature.instantiation with
  | closed noStatics =>
    have refused : (throw Error.request : WorkM Nat).run middle = (.ok position,left) := by
      simpa only [instantiation] using tail
    cases refused
  | static arguments environment sameOriginal =>
    simp only [instantiation] at tail
    obtain ⟨formal,afterFormal,formalRead,tail⟩ := bind_success _ _ _ _ _ tail
    have original := option_of_lift environment.numeric.original.header.formals[ordinal]?
      formal middle afterFormal formalRead
    obtain ⟨done,afterOrdinal,ordinalRead,tail⟩ := bind_success _ _ _ _ _ tail
    cases done
    have ordinalSame : formal.ordinal = ordinal :=
      beq_iff_eq.mp (guard_success _ _ _ _ ordinalRead).1
    obtain ⟨done,afterBound,boundRead,returned⟩ := bind_success _ _ _ _ _ tail
    cases done
    have bounded : (operations.map (·.1)).idxOf formal.name < operations.length :=
      of_decide_eq_true (guard_success _ _ _ _ boundRead).1
    have selected : position = (operations.map (·.1)).idxOf formal.name :=
      (pure_success _ _ _ _ returned).1
    subst position
    refine ⟨provider,arguments,environment,sameOriginal,formal,present,instantiation,original,ordinalSame,rfl,bounded,?_⟩
    exact name_at_idxOf _ _ (by simpa only [List.length_map] using bounded)

/-- The real formal branch selects exactly the child at its original mixed
header formal's operations-name position. This consumes an actual successful
read; no position or child-action equality is supplied. The selected value
also passes the shared carrier/shape checks. Provider consumption is unchanged. Source-call and
original-duty occurrence association remain separate obligations. -/
theorem readNode_formal_selection {sources} (metadata : StaticOperation.Result sources)
    (owner name : String) (bases : List (String × Semantics.FiniteCarrier.Basis))
    (naturals : List (String × Nat)) (operations : List (String × Nat)) (ordinal : Nat)
    (children providers : List Matrix) (nextProvider : Nat) (value : Matrix) (consumed work left : Nat)
    (ran : (readNode metadata (.formal owner name bases naturals operations ordinal)
      children providers nextProvider).run work = (.ok (value,consumed),left)) :
    consumed = nextProvider ∧
      ∃ (provider : StaticOperation.Provider sources) (arguments : StaticTypes.Arguments)
        (environment : StaticTypes.Environment sources provider.moduleName provider.declarationName arguments)
        (sameOriginal : environment.numeric.original.envelope = provider.signature.original)
        (formal : StaticHeaders.Formal) (position : Nat),
        metadata.formal = some provider ∧
        provider.signature.instantiation = .static arguments environment sameOriginal ∧
        environment.numeric.original.header.formals[ordinal]? = some formal ∧ formal.ordinal = ordinal ∧
        position = (operations.map (·.1)).idxOf formal.name ∧ position < operations.length ∧
        (operations.map (·.1))[position]? = some formal.name ∧ children[position]? = some value := by
  unfold readNode at ran
  obtain ⟨selected,afterSelection,selectionRead,tail⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨input,afterInput,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨output,afterOutput,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨done,afterGuard,_,returned⟩ := bind_success _ _ _ _ _ tail
  cases done
  have finalValue : (value,consumed) = selected := (pure_success _ _ _ _ returned).1
  change (do
    let position ← formalPosition metadata operations ordinal
    let child ← lift (readOption children[position]?)
    pure (child,nextProvider)).run work = (.ok selected,afterSelection) at selectionRead
  obtain ⟨position,afterPosition,positionRead,childReturn⟩ :=
    bind_success (formalPosition metadata operations ordinal) _ work afterSelection selected selectionRead
  obtain ⟨child,afterChild,childRead,childReturned⟩ := bind_success _ _ _ _ _ childReturn
  have finalValue : (value,consumed) = (child,nextProvider) :=
    finalValue.trans (pure_success _ _ _ _ childReturned).1
  refine ⟨congrArg Prod.snd finalValue,?_⟩
  obtain ⟨provider,arguments,environment,sameOriginal,formal,present,instantiation,original,
    ordinalSame,selectedPosition,bounded,selectedName⟩ :=
      formalPosition_selection metadata operations ordinal position work afterPosition positionRead
  refine ⟨provider,arguments,environment,sameOriginal,formal,position,present,instantiation,original,
    ordinalSame,selectedPosition,bounded,selectedName,?_⟩
  have sameValue : value = child := congrArg Prod.fst finalValue
  rw [sameValue]
  exact option_of_lift children[position]? child afterPosition afterChild childRead

#print axioms readNode_formal_selection

end QleisliKernel.Qirf.OperationIRMeaning
