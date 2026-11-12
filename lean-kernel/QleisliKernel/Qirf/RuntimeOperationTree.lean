import QleisliKernel.Qirf.RuntimePreparedOperation
import QleisliKernel.Qirf.OperationIRMeaning

/-! Same-root evaluation of the original operation child-edge occurrences.
Every provider consumes its own original header/body and derived access demand.
A written requested node compares the actual child action, including a formal
whose supplied actual is constructed, with its complete original Meaning.
Zero powers still visit every child and assertion. Declaration requirements
compare the child at the original operation-argument position. The enclosing
caller supplies the root and checks its own interval.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOperationTree
open QleisliKernel Finite SourceTypes
open QleisliKernel.Semantics.Exact (Matrix)
open QleisliKernel.SourceTypes.OperationDescription (Node)

/-- Each completed subtree retains its original input and output basis trees. -/
structure Value where
  index : Nat
  input : Semantics.FiniteCarrier.Basis
  output : Semantics.FiniteCarrier.Basis
  action : Matrix

inductive Provider {artifact catalogue context description graph order}
    (occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)
    (root : Validity.Root) (demand : StaticOperation.Paths) : Type where
  | absent (original : occurrence.provider = none)
  | present (provider : RuntimePreparedOperation.Provider artifact graph occurrence.index)
      (original : occurrence.provider = some provider)
      (checked : RuntimeProviderAction.Checked provider.header root demand)
      (consumed : RuntimeInterval.Computed (RuntimeProviderAction.read provider.header root demand) checked)

def Provider.actions {artifact catalogue context description graph order occurrence root demand} :
    @Provider artifact catalogue context description graph order occurrence root demand → List Matrix
  | .absent _ => []
  | .present _ _ checked _ => [checked.action]

private def readProvider {artifact catalogue context description graph order}
    (occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)
    (root : Validity.Root) (demand : StaticOperation.Paths) : WorkM (Provider occurrence root demand) := do
  match original : occurrence.provider with
  | none => return .absent original
  | some provider =>
    let checked ← NaturalAffine.witness (RuntimeProviderAction.read provider.header root demand)
    return .present provider original checked.val (by with_reducible exact checked.property)

/-- Compare the complete child action with the Meaning at its original request. -/
structure Equation {artifact catalogue result}
    (child : Value) (requirement : RuntimePreparedOperation.Requirement artifact catalogue result)
    {root} (specification : SourceMeaningAction.Checked requirement.meaning root) : Prop where
  input : child.input = requirement.request.meaning.graph.input
  output : child.output = requirement.request.meaning.graph.output
  action : child.action = specification.action

private def compare {artifact catalogue result}
    (child : Value) (requirement : RuntimePreparedOperation.Requirement artifact catalogue result)
    {root} (specification : SourceMeaningAction.Checked requirement.meaning root) :
    WorkM (PLift (Equation child requirement specification)) := do
  exactWork (Exact.charge (8*(Raw.OwnerFlow.fields [⟨0,child.input⟩,⟨0,child.output⟩,
    ⟨0,requirement.request.meaning.graph.input⟩,⟨0,requirement.request.meaning.graph.output⟩]+1)))
  if ports : child.input = requirement.request.meaning.graph.input ∧
      child.output = requirement.request.meaning.graph.output then
    exactWork (Exact.charge (child.action.entries.length+specification.action.entries.length+1))
    if action : child.action = specification.action then
      return ⟨⟨ports.1,ports.2,action⟩⟩
    else throw .equation
  else throw .request

structure Meaning {artifact catalogue result}
    (child : Value) (requirement : RuntimePreparedOperation.Requirement artifact catalogue result)
    (root : Validity.Root) where
  specification : SourceMeaningAction.Checked requirement.meaning root
  original : RuntimeInterval.Computed (SourceMeaningAction.read requirement.meaning root) specification
  equation : Equation child requirement specification
  compared : RuntimeInterval.Computed (compare child requirement specification) (⟨equation⟩ : PLift _)

private def readMeaning {artifact catalogue result}
    (child : Value) (requirement : RuntimePreparedOperation.Requirement artifact catalogue result)
    (root : Validity.Root) : WorkM (Meaning child requirement root) := do
  let specification ← NaturalAffine.witness (SourceMeaningAction.read requirement.meaning root)
  let equation ← NaturalAffine.witness (compare child requirement specification.val)
  return ⟨specification.val,by with_reducible exact specification.property,equation.val.down,
    by with_reducible exact equation.property⟩

private def isRequested : Node → Bool
  | .requested .. => true
  | _ => false

private def hasArgumentRequirements : Node → Bool
  | .provider .. | .formal .. => true
  | _ => false

structure ArgumentMeaning {artifact catalogue result}
    (requirements : List (RuntimePreparedOperation.Requirement artifact catalogue result))
    (children : List Value) (root : Validity.Root) where
  index : Fin requirements.length
  slot : Nat
  child : Value
  originalSlot : requirements[index].argument = some slot
  atSlot : children[slot]? = some child
  subject : requirements[index].subject = child.index
  checked : Meaning child requirements[index] root

private def readArgumentMeaning {artifact catalogue result}
    (requirements : List (RuntimePreparedOperation.Requirement artifact catalogue result))
    (children : List Value) (root : Validity.Root) (index : Fin requirements.length) :
    WorkM (ArgumentMeaning requirements children root) := do
  let requirement := requirements[index]
  exactWork (Exact.charge (8*(children.length+requirements.length+1)))
  match original : requirement.argument with
  | none => throw .request
  | some slot =>
    match atSlot : children[slot]? with
    | none => throw .request
    | some child =>
      if subject : requirement.subject = child.index then
        return ⟨index,slot,child,original,atSlot,subject,← readMeaning child requirement root⟩
      else throw .request

/-- Written assertions and declaration contracts consume every original
request. Argument positions distinguish repeated edges to one DAG index. -/
inductive Requirements {artifact catalogue context description graph order}
    (occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)
    (node : Node) (children : List Value) (root : Validity.Root) : Type where
  | none (plain : isRequested node = false) (empty : occurrence.requirements = [])
  | requested (child : Value) (owner name : String)
      (written : node = .requested child.index owner name)
      (childrenRead : children = [child])
      (requirement : RuntimePreparedOperation.Requirement artifact catalogue occurrence.result)
      (original : occurrence.requirements = [requirement])
      (subject : requirement.subject = child.index)
      (checked : Meaning child requirement root)
  | arguments (fromArguments : hasArgumentRequirements node = true)
      (meanings : List (ArgumentMeaning occurrence.requirements children root))
      (every : meanings.map (·.index) = List.finRange occurrence.requirements.length)

private def readRequirements {artifact catalogue context description graph order}
    (occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)
    (node : Node) (children : List Value) (root : Validity.Root) :
    WorkM (Requirements occurrence node children root) := do
  match node with
  | .requested childIndex owner name =>
    match children with
    | [child] =>
      match original : occurrence.requirements with
      | [requirement] =>
        if childIndexRead : child.index = childIndex then
          if subject : requirement.subject = child.index then
            guard requirement.argument.isNone .request
            let checked ← readMeaning child requirement root
            return .requested child owner name (by rw [childIndexRead])
              rfl requirement original subject checked
          else throw .request
        else throw .request
      | _ => throw .request
    | _ => throw .request
  | other =>
    if plain : isRequested other = false then
      match empty : occurrence.requirements with
      | [] => return .none plain empty
      | _ =>
        if fromArguments : hasArgumentRequirements other = true then
          let meanings ← (List.finRange occurrence.requirements.length).mapM
            (readArgumentMeaning occurrence.requirements children root)
          if every : meanings.map (·.index) = List.finRange occurrence.requirements.length then
            return .arguments fromArguments meanings every
          else throw .request
        else throw .request
    else throw .request

structure Step {artifact catalogue context description graph order}
    (occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)
    (root : Validity.Root) (demand : StaticOperation.Paths) (before : List Value) where
  node : Node
  selected : description.nodes[occurrence.index]? = some node
  remaining : List Value
  children : List Value
  partition : before = remaining ++ children
  arity : children.length = node.children.length
  childIndices : children.map (·.index) = node.children
  provider : Provider occurrence root demand
  requirements : Requirements occurrence node children root
  value : Matrix
  consumedProviders : Nat
  calculated : RuntimeInterval.Computed
    (OperationIRMeaning.readNode occurrence.result node (children.map (·.action)) provider.actions 0)
    (value,consumedProviders)
  consumed : consumedProviders = provider.actions.length

def Step.output {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before) : Value :=
  ⟨occurrence.index,occurrence.result.input,occurrence.result.output,step.value⟩

def Step.after {artifact catalogue context description graph order occurrence root demand before}
    (step : @Step artifact catalogue context description graph order occurrence root demand before) : List Value :=
  step.remaining ++ [step.output]

private def readStep {artifact catalogue context description graph order}
    (occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)
    (root : Validity.Root) (demand : StaticOperation.Paths) (before : List Value) :
    WorkM (Step occurrence root demand before) := do
  exactWork (Exact.charge (16*(description.nodes.length+before.length+1)))
  match selected : description.nodes[occurrence.index]? with
  | none => throw .request
  | some node =>
    -- readNode's formal selector scans the original mixed header and compares
    -- actual argument names. Charge those real byte-bearing fields here;
    -- arithmetic and source/body readers retain their separate charges.
    let formalFields := match occurrence.result.formal with
      | none => 0
      | some formal => SourceTrace.Meter.tokenFields formal.signature.original.occurrence.header
    exactWork (Exact.charge (8*(node.children.length+1)*(formalFields+1)))
    let splitAt := before.length-node.children.length
    let remaining := before.take splitAt
    let children := before.drop splitAt
    if arity : children.length = node.children.length then
      if childIndices : children.map (·.index) = node.children then
        let provider ← readProvider occurrence root demand
        let requirements ← readRequirements occurrence node children root
        let calculated ← NaturalAffine.witness
          (OperationIRMeaning.readNode occurrence.result node (children.map (·.action)) provider.actions 0)
        if consumed : calculated.val.2 = provider.actions.length then
          return ⟨node,selected,remaining,children,(List.take_append_drop splitAt before).symm,
            arity,childIndices,provider,requirements,calculated.val.1,calculated.val.2,
            by with_reducible exact calculated.property,consumed⟩
        else throw .request
      else throw .request
    else throw .request

structure Record {artifact catalogue context description graph order}
    (root : Validity.Root) where
  occurrence : @RuntimePreparedOperation.Occurrence artifact catalogue context description graph order
  demandIndex : Nat
  demand : StaticOperation.Paths
  sameIndex : demandIndex = occurrence.index
  before : List Value
  checked : Step occurrence root demand before
  original : RuntimeInterval.Computed (readStep occurrence root demand before) checked

structure Outcome {artifact catalogue context description graph order} (root : Validity.Root) where
  stack : List Value
  records : List (@Record artifact catalogue context description graph order root)

private def walk {artifact catalogue context description graph order} (root : Validity.Root)
    (occurrences : List (@RuntimePreparedOperation.Occurrence artifact catalogue context description graph order)) :
    List (Nat × StaticOperation.Paths) → List Value → WorkM (@Outcome artifact catalogue context description graph order root) :=
  WellFounded.fix (measure (List.length (α := @RuntimePreparedOperation.Occurrence
    artifact catalogue context description graph order))).wf
    (C := fun _ => List (Nat × StaticOperation.Paths) → List Value →
      WorkM (@Outcome artifact catalogue context description graph order root))
    (fun current => match current with
      | [] => fun _ demands stack => match demands with
        | [] => pure ⟨stack,[]⟩
        | _ :: _ => throw .request
      | occurrence :: rest => fun visit demands before => do
        let (index,demand) :: demands := demands | throw .request
        if same : index = occurrence.index then
          let checked ← NaturalAffine.witness (readStep occurrence root demand before)
          let tail ← visit rest (by decreasing_tactic) demands checked.val.after
          let record : @Record artifact catalogue context description graph order root :=
            ⟨occurrence,index,demand,same,before,checked.val,by with_reducible exact checked.property⟩
          return ⟨tail.stack,record :: tail.records⟩
        else throw .request) occurrences

structure Checked {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references)
    (root : Validity.Root) (requested : StaticOperation.Paths) where
  access : OperationAccess.CheckedOccurrences graph requested
  accessRead : RuntimeInterval.Computed (OperationAccess.checkOccurrences graph requested) access
  sameOrder : access.order = prepared.order
  outcome : @Outcome artifact catalogue context description graph prepared.order root
  traversed : RuntimeInterval.Computed (walk root prepared.occurrences access.demands []) outcome
  every : outcome.records.map (·.occurrence.ordinal) = List.finRange prepared.order.length
  demands : outcome.records.map (fun record => (record.demandIndex,record.demand)) = access.demands
  value : Value
  complete : outcome.stack = [value]
  atRoot : value.index = description.root
  input : value.input = graph.root.input
  output : value.output = graph.root.output

def Checked.action {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @Checked artifact catalogue context description graph implementations references prepared root requested) : Matrix :=
  checked.value.action

/-- The original provider receipts retain their body islands under this same
native root. This projection does not discharge the enclosing source duties. -/
def Checked.providerIslands {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @Checked artifact catalogue context description graph implementations references prepared root requested) :
    List (RuntimePureBody.Island root.dependencies) :=
  checked.outcome.records.flatMap fun record =>
    match record.checked.provider with
    | .absent _ => []
    | .present _ _ provider _ => provider.originalBody.body.result.islands

/-- Read access and operation occurrences in lockstep under one root. Each
child consumes its original stack position and retains its own path and Meaning duties. -/
def read {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references)
    (root : Validity.Root) (requested : StaticOperation.Paths) : WorkM (Checked prepared root requested) := do
  exactWork (Exact.charge (16*(prepared.occurrences.length+prepared.order.length+1)^2))
  let access ← NaturalAffine.witness (OperationAccess.checkOccurrences graph requested)
  if sameOrder : access.val.order = prepared.order then
    let outcome ← NaturalAffine.witness (walk root prepared.occurrences access.val.demands [])
    if every : outcome.val.records.map (·.occurrence.ordinal) = List.finRange prepared.order.length then
      if demands : outcome.val.records.map (fun record => (record.demandIndex,record.demand)) = access.val.demands then
        match complete : outcome.val.stack with
        | [value] =>
          if atRoot : value.index = description.root then
            if ports : value.input = graph.root.input ∧ value.output = graph.root.output then
              return ⟨access.val,by with_reducible exact access.property,sameOrder,outcome.val,
                by with_reducible exact outcome.property,every,demands,value,complete,atRoot,ports.1,ports.2⟩
            else throw .request
          else throw .request
        | _ => throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Stack boundaries are tied to the successful original traversal, so
repeated description indices cannot select a different child occurrence. -/
inductive StackTrace {artifact catalogue context description graph order} {root : Validity.Root} :
    List Value → List (@Record artifact catalogue context description graph order root) → List Value → Prop
  | nil (before : List Value) : StackTrace before [] before
  | cons (record : @Record artifact catalogue context description graph order root) {rest final}
      (tail : StackTrace record.checked.after rest final) :
      StackTrace record.before (record :: rest) final

private theorem walk_occurrences {artifact catalogue context description graph order}
    (root : Validity.Root)
    (occurrences : List (@RuntimePreparedOperation.Occurrence artifact catalogue context description graph order))
    (demands : List (Nat × StaticOperation.Paths)) (before : List Value)
    (outcome : @Outcome artifact catalogue context description graph order root)
    (computed : RuntimeInterval.Computed (walk root occurrences demands before) outcome) :
    outcome.records.map (·.occurrence) = occurrences ∧
      StackTrace before outcome.records outcome.stack := by
  induction occurrences generalizing demands before outcome with
  | nil =>
    obtain ⟨work,left,ran⟩ := computed
    rw [walk,WellFounded.fix_eq] at ran
    cases demands with
    | nil =>
      have same : outcome = ⟨before,[]⟩ := (pure_success _ _ _ _ ran).1
      rw [same]
      exact ⟨rfl,.nil _⟩
    | cons first rest => cases ran
  | cons occurrence rest ih =>
    obtain ⟨work,left,ran⟩ := computed
    rw [walk,WellFounded.fix_eq] at ran
    cases demands with
    | nil => cases ran
    | cons pair demands =>
      obtain ⟨index,demand⟩ := pair
      dsimp only at ran
      by_cases same : index = occurrence.index
      · rw [dif_pos same] at ran
        obtain ⟨checked,middle,_stepRead,tail⟩ := bind_success _ _ _ _ _ ran
        obtain ⟨tailOutcome,last,tailRead,returned⟩ := bind_success _ _ _ _ _ tail
        change (walk root rest demands checked.val.after).run middle = (.ok tailOutcome,last) at tailRead
        have original := ih demands checked.val.after tailOutcome ⟨middle,last,tailRead⟩
        have sameOutcome := (pure_success _ _ _ _ returned).1
        rw [sameOutcome]
        refine ⟨congrArg (List.cons occurrence) original.1,?_⟩
        let record : @Record artifact catalogue context description graph order root :=
          ⟨occurrence,index,demand,same,before,checked.val,by with_reducible exact checked.property⟩
        exact .cons record original.2
      · rw [dif_neg same] at ran
        cases ran

/-- The actual traversal retains the exact prepared occurrence at every record
position, including all dependent graph, provider and Meaning metadata. This
follows from the successful walk itself, rather than ordinal coverage or an
assumed membership/order relation. The native reader is unchanged. -/
theorem Checked.occurrences {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @Checked artifact catalogue context description graph implementations references prepared root requested) :
    checked.outcome.records.map (·.occurrence) = prepared.occurrences :=
  (walk_occurrences root prepared.occurrences checked.access.demands [] checked.outcome checked.traversed).1

/-- The actual checked graph consumes consecutive original stack states. -/
theorem Checked.stack_trace {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @Checked artifact catalogue context description graph implementations references prepared root requested) :
    StackTrace [] checked.outcome.records [checked.value] := by
  rw [← checked.complete]
  exact (walk_occurrences root prepared.occurrences checked.access.demands [] checked.outcome checked.traversed).2

#print axioms Checked.stack_trace

#print axioms Checked.occurrences

end QleisliKernel.Qirf.RuntimeOperationTree
