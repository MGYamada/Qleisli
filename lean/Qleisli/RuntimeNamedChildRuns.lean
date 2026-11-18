import Qleisli.RuntimeNamedSourceFlow
import Qleisli.RuntimeLiteralBody
import Qleisli.RuntimeBranchInputDomain
import Qleisli.RuntimeSelectionLogicalRead
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Retain actual recursive runs of original named callees and their inputs.
The complete source-state chain and each named child's actual binding/callback
reads follow one proof of the real common loop, retaining actual primitive
histories, selection input/return maps and the original arm graph actions.
This is not a whole logical-action theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedChildRuns
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody
open RuntimeNamedSourceFlow (NodeAligned)
open RuntimeLiteralBody (At Partition)
open RuntimeSelectionLogicalRead (FromArms GraphLogical NamedArmLogical)
open RuntimeSelectionArmTrace (EventTable MixedNamed MixedInline MixedSlot)

abbrev RootInputs := List (Semantics.FiniteCarrier.Basis × RuntimeOrdinarySSA.Expression)

/-- The original callee, its complete real argument binding, visible ordinary
SSA and actual recursive result determine this named step's stored child.
The two successful reads share the same remaining-work counter. -/
inductive ChildRunAt (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution)
    (origin : Option RootInputs) :
    {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block root.dependencies program} →
    Step root.dependencies program block → Prop where
  | named {program : Semantics.Observation.Program}
      {block : RuntimeInterval.Block root.dependencies program} {start count inputs caller before ordinary}
      {event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources caller}
      {scope : RuntimeCallScope.Checked block start count inputs ordinary event.effect}
      {body : SourceTypes.SourceRuntimeTrace.Body event.target.signature}
      {bodyRead : SourceTypes.SourceRuntimeTrace.NamedRead event body}
      {rootOwner rootName : String}
      {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName
        event.target.resolution.moduleName event.target.resolution.declaration.name}
      {controlled : Bool} {request : Context}
      {plan : execution.queries.BodyData (.whole body controlled) request}
      {initialBindings : RuntimeOwnerMap.Map}
      {result : BlockResult root.dependencies scope.program scope.prepared.block}
      {receipts : List execution.Receipt}
      {boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before
        result.history result.retired body.checked.summary.value}
      {beforeInput afterInput afterChild : Nat}
      (inputRead : (RuntimeSourceBoundary.bindings
          (body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners)
          ((scope.selected.zip event.inputOwners).map fun (port,role) =>
            (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))).run beforeInput =
        (.ok initialBindings,afterInput))
      (read : (next .runtimeBody .localScope (.whole body controlled) path scope.program request plan
          ⟨initialBindings,body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners,
            body.checked.summary.nextOwner⟩
          scope.visible.ssa scope.prepared.block).run afterInput = (.ok (result,receipts),afterChild))
      (rootRead : ∀ inputs, origin = some inputs → RuntimeBranchCondition.rootEntries path = inputs := by simp) :
      ChildRunAt artifact root execution next origin
        (.named event scope body bodyRead boundary result.ordinary (Steps.ofList result.steps))

/-- A pure named node stores child actions instead of runtime steps. The
original binding, callback and shared work counter still identify the same
literal child block, original body and argument context. -/
inductive PureChildRunAt (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution)
    (origin : Option RootInputs) (ordinary : RuntimeOrdinaryBody.State) :
    {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block root.dependencies program} →
    Node root.dependencies program block → Prop where
  | named {program : Semantics.Observation.Program}
      {block : RuntimeInterval.Block root.dependencies program} {start count inputs caller before}
      {event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources caller}
      {scope : RuntimeCallInterval.Checked block start count inputs}
      {body : SourceTypes.SourceRuntimeTrace.Body event.target.signature}
      {bodyRead : SourceTypes.SourceRuntimeTrace.NamedRead event body}
      {rootOwner rootName : String}
      {parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller event.target.callerName}
      {controlled : Bool} {request : Context}
      {plan : execution.queries.BodyData (.whole body controlled) request}
      {initialBindings : RuntimeOwnerMap.Map}
      {result : BlockResult root.dependencies scope.program scope.prepared.block}
      {receipts : List execution.Receipt}
      {boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before
        result.history result.retired body.checked.summary.value}
      {beforeInput afterInput afterChild : Nat}
      (unitary : event.effect = .unitary)
      (inputRead : (RuntimeSourceBoundary.bindings
          (body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners)
          ((scope.selected.zip event.inputOwners).map fun (port,role) =>
            (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))).run beforeInput =
        (.ok initialBindings,afterInput))
      (read : (next .pureBody .localScope (.whole body controlled) (.named event body bodyRead parent) scope.program request plan
          ⟨initialBindings,body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners,
            body.checked.summary.nextOwner⟩
          ordinary scope.prepared.block).run afterInput = (.ok (result,receipts),afterChild))
      (rootRead : ∀ inputs, origin = some inputs →
        RuntimeBranchCondition.rootEntries (.named event body bodyRead parent) = inputs := by simp) :
      PureChildRunAt artifact root execution next origin ordinary
        (.named event scope body bodyRead boundary (Nodes.ofList result.actions))

abbrev ChildRun (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution)
    {program} {block : RuntimeInterval.Block root.dependencies program}
    (step : Step root.dependencies program block) : Prop :=
  ChildRunAt artifact root execution next none step

theorem ChildRunAt.forget {artifact root execution next origin program block step}
    (checked : @ChildRunAt artifact root execution next origin program block step) :
    ChildRun artifact root execution next step := by
  cases checked with
  | named inputRead read => exact .named inputRead read

/-- Both original recursive arm reads and their checked join share the
remaining-work counters of the original conditional step. -/
inductive ConditionalRun (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) :
    {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block root.dependencies program} →
    Step root.dependencies program block → Prop where
  | checked {program : Semantics.Observation.Program}
      {block : RuntimeInterval.Block root.dependencies program} {offset rootOwner rootName caller name}
      {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller name}
      {event : SourceTypes.SourceRuntimeContext.BranchEvent artifact.sources caller}
      {source : RuntimeBranchAction.Source event} {sameName : event.callerName = name}
      {actual : @RuntimeInterval.Branch root.dependencies program block offset}
      {actualRead : RuntimeInterval.Computed (RuntimeInterval.readBranch block offset) actual}
      {leftRequest rightRequest : Context}
      {controlled : Bool}
      {leftPlan : execution.queries.BodyData (.arm event sameName source.bodies source.original true controlled) leftRequest}
      {rightPlan : execution.queries.BodyData (.arm event sameName source.bodies source.original false controlled) rightRequest}
      {before ordinary}
      {left : BlockResult root.dependencies program actual.thenBlock}
      {right : BlockResult root.dependencies program actual.elseBlock}
      {leftReceipts rightReceipts : List execution.Receipt}
      {action : RuntimeBranchAction.Checked path event source actual before left.history right.history
        ordinary left.ordinary right.ordinary}
      {beforeThen afterThen afterElse afterJoin : Nat}
      (thenRead : (next .runtimeBody .frame (.arm event sameName source.bodies source.original true controlled)
          path program leftRequest leftPlan before ordinary actual.thenBlock).run beforeThen =
        (.ok (left,leftReceipts),afterThen))
      (elseRead : (next .runtimeBody .frame (.arm event sameName source.bodies source.original false controlled)
          path program rightRequest rightPlan before ordinary actual.elseBlock).run afterThen =
        (.ok (right,rightReceipts),afterElse))
      (joinRead : (RuntimeBranchAction.read path event source actual before left.history right.history
          ordinary left.ordinary right.ordinary).run afterElse = (.ok action,afterJoin)) :
      ConditionalRun artifact root execution next (.conditional path event source actual actualRead action
        (Steps.ofList left.steps) (Steps.ofList right.steps))

def CheckedStep {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (step : Step root.dependencies program block) : Prop :=
  match step with
  | .named .. => ChildRun artifact root execution next step
  | .conditional .. => ConditionalRun artifact root execution next step
  | .pure .. | .gap .. | .observation .. => True

private def plannedOperationRequest {artifact} {preparation : RuntimeGraphOperation.Preparation artifact}
    {owner controlled} {event : SourceTypes.SourceOperationApplication.Event artifact.sources owner}
    (original : RuntimeBodyQueries.Operation (.planned preparation) event controlled) : RuntimeGraphOperation.Request artifact :=
  ⟨_,_,event.operation.graph,SourceTypes.SourceRuntimeScope.applicationDemand controlled,
    original.child.bodies,original.graph.1,.application event⟩

/-- Planned source execution uses the exact receipt from consuming this
occurrence's checked graph, including its original preparation and location. -/
def OperationResult {artifact root} (execution : ExecutionMode artifact root)
    {owner controlled} {event : SourceTypes.SourceOperationApplication.Event artifact.sources owner}
    (original : RuntimeBodyQueries.Operation execution.queries event controlled)
    (expected : Semantics.Exact.Matrix) (receipts : List execution.Receipt) : Prop :=
  match execution, original with
  | .fresh _, _ => True
  | .planned _ continuation, original =>
    let request := plannedOperationRequest original
    let graph := original.graph.2.2
    ∃ (location : RuntimeGraphOperation.Location request)
      (evidence : continuation.Evidence request graph.evidence)
      (consumed : RuntimeInterval.Computed (continuation.read request graph.evidence) evidence),
      receipts = [⟨request,location,graph.evidence,graph.consumed,evidence,consumed⟩] ∧
      expected = continuation.action evidence

private theorem planned_operation_result {artifact root}
    {preparation : RuntimeGraphOperation.Preparation artifact}
    (continuation : RuntimeGraphOperation.StagedConsumption preparation root (Island root.dependencies))
    {owner controlled} {event : SourceTypes.SourceOperationApplication.Event artifact.sources owner}
    (original : RuntimeBodyQueries.Operation (.planned preparation) event controlled)
    (location : RuntimeGraphOperation.Location (plannedOperationRequest original))
    {expected children receipts work left} :
    let request := plannedOperationRequest original
    let graph := original.graph.2.2
    ((do
      let (logical,obligations,_,performed) ← (do
        let checked ← SourceTypes.NaturalAffine.witness (continuation.read request graph.evidence)
        exactWork (Exact.charge 8)
        let receipt : RuntimeGraphOperation.StagedReceipt continuation :=
          ⟨request,location,graph.evidence,graph.consumed,checked.val,by with_reducible exact checked.property⟩
        pure (continuation.action checked.val,continuation.obligations checked.val,(),[receipt]))
      pure (logical,obligations,performed)) :
      WorkM (Semantics.Exact.Matrix × List (Island root.dependencies) × List (RuntimeGraphOperation.StagedReceipt continuation))).run work =
        (.ok (expected,children,receipts),left) →
    OperationResult (.planned preparation continuation) original expected receipts := by
  intro request graph ran
  obtain ⟨result,middle,consume,returnRead⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨checked,budget,_,charged⟩ := bind_success _ _ _ _ _ consume
  obtain ⟨_,paid,_,returned⟩ := bind_success _ _ _ _ _ charged
  have actual := (pure_success _ _ _ _ returned).1
  subst result
  have result := (pure_success _ _ _ _ returnRead).1
  obtain ⟨action,_,receiptsEq⟩ := Prod.mk.inj result |>.imp id Prod.mk.inj
  exact ⟨location,checked.val,checked.property,receiptsEq,action⟩

/-- The coherent selection retains the original source table read and the
exact arm graph actions used by the literal node in selector order. -/
def SelectionOrigin {artifact root} (execution : ExecutionMode artifact root)
    {program block} (node : Node root.dependencies program block) : Prop :=
  ∃ (owner name : String) (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (offset : Nat) (selector target : Semantics.FiniteCarrier.Basis)
    (naturals : SourceTypes.PhaseApplication.Naturals artifact.sources) (scope : List String)
    (table : SourceTypes.QuantumArms.Table artifact.sources owner name offset selector target),
    RuntimeInterval.Computed (SourceTypes.QuantumArms.readArmsWithInstantiation
      source.signature.original source.signature.instantiation source.signature.supply
      offset selector target (some naturals) scope) table ∧
    FromArms table (fun index matrix => ∃ graph, GraphLogical execution table index graph matrix) node

/-- Each mixed row uses the action of its checked graph or of the actual
isolated Raw run of its written inline body. -/
def MixedLogical {artifact root} (execution : ExecutionMode artifact root)
    (next : BlockRunner artifact root execution) {rootOwner rootName owner}
    {event : SourceTypes.SourceRuntimeContext.SelectionEvent artifact.sources owner}
    {table : EventTable event} (site : RuntimeContextRequest.Site)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner event.callerName)
    (parent : RuntimeStructuralAction.SourceState) (index : Fin table.arms.length)
    (slot : MixedSlot execution.queries table index) (matrix : Semantics.Exact.Matrix) : Prop :=
  match slot with
  | .named arm _ graph => NamedArmLogical execution arm graph matrix
  | .inline arm replayed _ _ _ _ child plan =>
    ∃ subject, site.arms[index.val]? = some subject ∧
      ∃ checked : InlineChecked rfl arm replayed subject.implementation child plan path parent next,
        RuntimeInterval.Computed (readInlineArm rfl arm replayed subject.implementation child plan path parent next) checked ∧
          matrix = checked.action.code.logical

/-- The literal selection uses the original mixed table and the action of
the actual run at each of its written indices. -/
def MixedSelectionOrigin {artifact root} (execution : ExecutionMode artifact root)
    (next : BlockRunner artifact root execution) {program block}
    (node : Node root.dependencies program block) : Prop :=
  ∃ (rootOwner rootName owner name : String)
    (event : SourceTypes.SourceRuntimeContext.SelectionEvent artifact.sources owner)
    (position : Position)
    (selection : RuntimeBodyQueries.MixedSelection (name := name) execution.queries event position)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner event.callerName)
    (parent : RuntimeStructuralAction.SourceState),
    FromArms selection.table (fun index matrix => ∃ slot, MixedLogical execution next selection.site path parent index slot matrix) node

/-- The operation's original source query and the literal node share the
same ordered roles, body position and expected action. -/
def OperationOrigin {artifact root} (execution : ExecutionMode artifact root)
    {program block} : Node root.dependencies program block → Prop
  | node@(.operation (roles := roles) _ _ _ _ expected ..) =>
    ∃ (owner name : String) (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
      (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
      (position : Position) (cursor : execution.queries.Cursor)
      (data : execution.queries.EventData source (.operation event) position)
      (original : RuntimeBodyQueries.Operation execution.queries event source.requiresControl)
      (before after : RuntimeOwnerMap.Map)
      (receipts : List execution.Receipt),
      event.inputOwners = roles ∧
      RuntimeInterval.Computed (RuntimeBodyQueries.readOperation execution.queries source event position cursor data) original ∧
      RuntimeInterval.Computed (operationNode block position event.inputOwners before after expected) node ∧
      OperationResult execution original expected receipts
  | .rectangularOperation (event := retained) (expected := expected) (start := start) (count := count) _ =>
    ∃ (owner name : String) (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
      (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
      (position : Position) (cursor : execution.queries.Cursor)
      (data : execution.queries.EventData source (.operation event) position)
      (original : RuntimeBodyQueries.Operation execution.queries event source.requiresControl)
      (receipts : List execution.Receipt),
      HEq event retained ∧ position.start = start ∧ position.count = count ∧
      RuntimeInterval.Computed (RuntimeBodyQueries.readOperation execution.queries source event position cursor data) original ∧
      OperationResult execution original expected receipts
  | .named .. | .transform .. => False
  | node@(.selection ..) => SelectionOrigin execution node
  | _ => True

private theorem selection_origin {artifact root} {execution : ExecutionMode artifact root}
    {program block} {node : Node root.dependencies program block}
    (original : SelectionOrigin execution node) : OperationOrigin execution node := by
  cases node
  case selection => exact original
  all_goals
    obtain ⟨_,_,_,_,_,_,_,_,_,_,invalid⟩ := original
    exact False.elim invalid

/-- In planned execution, the source roles and exact logical matrix of a
graph node come from the source occurrence and its staged consumption. -/
theorem OperationOrigin.staged_action {artifact root}
    {preparation : RuntimeGraphOperation.Preparation artifact}
    {continuation : RuntimeGraphOperation.StagedConsumption preparation root (Island root.dependencies)}
    {program block} {node : Node root.dependencies program block}
    (checked : OperationOrigin (.planned preparation continuation) node) :
    match node with
    | .operation (roles := roles) _ _ _ _ expected .. =>
      ∃ (owner : String) (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
        (receipt : RuntimeGraphOperation.StagedReceipt continuation),
        event.inputOwners = roles ∧ HEq receipt.request.graph event.operation.graph ∧
          expected = continuation.action receipt.evidence
    | .rectangularOperation (event := retained) (expected := expected) _ =>
      ∃ (owner : String) (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
        (receipt : RuntimeGraphOperation.StagedReceipt continuation),
        HEq event retained ∧ HEq receipt.request.graph event.operation.graph ∧
          expected = continuation.action receipt.evidence
    | _ => True := by
  cases node
  case operation =>
    obtain ⟨owner,_,_,event,_,_,_,original,_,_,_,roles,_,_,performed⟩ := checked
    obtain ⟨location,evidence,consumed,_,expected⟩ := performed
    let graph := original.graph.2.2
    exact ⟨owner,event,⟨plannedOperationRequest original,location,graph.evidence,graph.consumed,evidence,consumed⟩,
      roles,HEq.rfl,expected⟩
  case rectangularOperation =>
    obtain ⟨owner,_,_,event,_,_,_,original,_,same,_,_,_,performed⟩ := checked
    obtain ⟨location,evidence,consumed,_,expected⟩ := performed
    let graph := original.graph.2.2
    exact ⟨owner,event,⟨plannedOperationRequest original,location,graph.evidence,graph.consumed,evidence,consumed⟩,
      same,HEq.rfl,expected⟩
  all_goals exact True.intro

private def IntrinsicNode {dependencies program block} : Node dependencies program block → Prop
  | .primitive .. | .structural .. | .register .. | .basis .. | .computed .. | .certifiedComputed ..
  | .structuralComputed .. | .workspace .. => True
  | _ => False

private theorem intrinsic_origin {artifact root} {execution : ExecutionMode artifact root}
    {program block} {node : Node root.dependencies program block} (intrinsic : IntrinsicNode node) :
    OperationOrigin execution node := by
  cases node <;> first | exact intrinsic | exact False.elim intrinsic

/-- A written transform's stored children and returned owners come from the
same original forward-body run, with the real query plan and shared meter. -/
inductive TransformRun (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) :
    {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block root.dependencies program} →
    Node root.dependencies program block → Prop where
  | checked {program : Semantics.Observation.Program}
      {block : RuntimeInterval.Block root.dependencies program}
      {caller name : String} {subject : SourceTypes.SourceRuntimeScope.Subject artifact.sources caller name}
      {event : SourceTypes.SourceRuntimeContext.TransformEvent artifact.sources caller}
      {position : Position} {cursor : execution.queries.Cursor}
      {data : execution.queries.EventData subject (.transform event) position}
      {transformed : RuntimeBodyQueries.Transform execution.queries event position subject.requiresControl}
      {forward : RuntimeTransformAction.Forward artifact root.dependencies transformed.request}
      {child : BlockResult root.dependencies forward.program forward.prepared.block}
      {receipts : List execution.Receipt}
      {logical : RuntimeTransformAction.ForwardMap forward child.history.bindings}
      {interval : RuntimeInterval.Checked block position.start position.count} {before}
      {owners : RuntimeTransformOwners.Checked interval event before}
      {action : RuntimeTransformAction.Checked owners logical.code.logical}
      {initial beforeForward beforeChild afterChild : Nat}
      (query : (RuntimeBodyQueries.readTransform execution.queries subject event position cursor data).run initial =
        (.ok transformed,beforeForward))
      (prepare : (RuntimeTransformAction.readForward artifact root.dependencies transformed.request).run beforeForward =
        (.ok forward,beforeChild))
      (run : (next .pureBody .rootOrder (.whole transformed.request.source subject.requiresControl)
          (.root transformed.request.source)
          forward.program transformed.request.context transformed.nested
          ⟨forward.initial,forward.roles,transformed.request.source.checked.summary.nextOwner⟩
          {} forward.prepared.block).run beforeChild = (.ok (child,receipts),afterChild)) :
      TransformRun artifact root execution next (.transform transformed.request transformed.original forward
        child.history.bindings logical owners action (Nodes.ofList child.actions))

/-- A named step retains the original caller's root ordinary input domain. -/
def CheckedStepAt {artifact root execution} (next : BlockRunner artifact root execution)
    (inputs : RootInputs) {program block} (step : Step root.dependencies program block) : Prop :=
  match step with
  | .named .. => ChildRunAt artifact root execution next (some inputs) step
  | .pure node@(.transform ..) => TransformRun artifact root execution next node
  | .pure node@(.named ..) => ∃ ordinary, PureChildRunAt artifact root execution next (some inputs) ordinary node
  | .pure node@(.selection ..) => SelectionOrigin execution node ∨ MixedSelectionOrigin execution next node
  | .pure node => OperationOrigin execution node
  | _ => CheckedStep next step

private theorem CheckedStepAt.of_operationOrigin {artifact root execution}
    {next : BlockRunner artifact root execution} {inputs program block}
    {node : Node root.dependencies program block} (origin : OperationOrigin execution node) :
    CheckedStepAt next inputs (.pure node) := by
  cases node <;> first | exact Or.inl origin | exact origin | exact False.elim origin

theorem CheckedStepAt.forget {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs program block step} (checked : @CheckedStepAt artifact root execution next inputs program block step) :
    CheckedStep next step := by
  cases step
  case named => exact ChildRunAt.forget checked
  case pure => exact True.intro
  all_goals exact checked

/-- The ordinary states belong to the same stored steps as the owner
states. A pure step leaves the complete table and measurement keys intact. -/
def OrdinaryAligned {dependencies program block} (before after : RuntimeOrdinaryBody.State)
    (step : @Step dependencies program block) : Prop :=
  match step with
  | .pure _ => after = before
  | .gap (ordinary := original) gap => before = original ∧ after = gap.ssa
  | .observation (ordinary := original) observation =>
    before = original ∧ after = observation.ordinary
  | .named (ordinary := original) _ _ _ _ _ final _ => before = original ∧ after = final
  | .conditional _ _ _ _ _ (ordinary := original) action _ _ =>
    before = original ∧ after = action.ordinaryAfter

inductive OrdinaryRun {dependencies program block} : RuntimeOrdinaryBody.State →
    List (@Step dependencies program block) → RuntimeOrdinaryBody.State → Prop where
  | nil (state : RuntimeOrdinaryBody.State) : OrdinaryRun state [] state
  | cons {initial middle final first rest}
      (head : OrdinaryAligned initial middle first) (tail : OrdinaryRun middle rest final) :
      OrdinaryRun initial (first :: rest) final

theorem OrdinaryRun.snoc {dependencies program block initial middle final steps step}
    (run : @OrdinaryRun dependencies program block initial steps middle)
    (last : OrdinaryAligned middle final step) :
    OrdinaryRun initial (steps ++ [step]) final := by
  induction run with
  | nil => exact .cons last (.nil _)
  | cons head _ ih => exact .cons head (ih last)

def ConditionFrom {dependencies program block} (inputs : RootInputs) :
    Step dependencies program block → Prop
  | .conditional path .. => RuntimeBranchCondition.rootEntries path = inputs
  | _ => True

structure Flow {artifact root execution} (next : BlockRunner artifact root execution) (inputs : RootInputs)
    {program block} (initial : RuntimeStructuralAction.SourceState)
    (steps : List (Step root.dependencies program block)) (final : RuntimeStructuralAction.SourceState)
    (initialOrdinary finalOrdinary : RuntimeOrdinaryBody.State) (cursor : Nat) : Prop where
  source : RuntimeNamedSourceFlow.Run initial steps final
  callsAt : ∀ step ∈ steps, CheckedStepAt next inputs step
  conditions : ∀ step ∈ steps, ConditionFrom inputs step
  ordinary : OrdinaryRun initialOrdinary steps finalOrdinary
  literal : Partition 0 steps cursor

theorem Flow.calls {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs program block initial steps final ordinary finalOrdinary cursor}
    (flow : @Flow artifact root execution next inputs program block initial steps final ordinary finalOrdinary cursor) :
    ∀ step ∈ steps, CheckedStep next step :=
  fun step present => (flow.callsAt step present).forget

theorem Flow.nil {artifact root execution} (next : BlockRunner artifact root execution) (inputs : RootInputs)
    {program block} (state : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State) :
    @Flow artifact root execution next inputs program block state [] state ordinary ordinary 0 :=
  ⟨.nil _,(by intro step member; cases member),(by intro step member; cases member),.nil _,.nil _⟩

theorem Flow.snoc {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs program block initial middle final steps step initialOrdinary middleOrdinary finalOrdinary middleCursor finalCursor}
    (flow : @Flow artifact root execution next inputs program block initial steps middle initialOrdinary middleOrdinary
      middleCursor)
    (source : RuntimeNamedSourceFlow.Aligned middle final step) (call : CheckedStepAt next inputs step)
    (ordinary : OrdinaryAligned middleOrdinary finalOrdinary step) (literal : At middleCursor finalCursor step)
    (origin : ConditionFrom inputs step) :
    Flow next inputs initial (steps ++ [step]) final initialOrdinary finalOrdinary finalCursor := by
  refine ⟨flow.source.snoc source,?_,?_,flow.ordinary.snoc ordinary,flow.literal.snoc literal⟩
  · intro current member
    rcases List.mem_append.mp member with old | last
    · exact flow.callsAt current old
    · exact (List.mem_singleton.mp last).symm ▸ call
  · intro current member
    rcases List.mem_append.mp member with old | last
    · exact flow.conditions current old
    · exact (List.mem_singleton.mp last).symm ▸ origin

def Invariant {artifact root execution} (next : BlockRunner artifact root execution) (inputs : RootInputs)
    {program block} (initial : RuntimeStructuralAction.SourceState) (initialOrdinary : RuntimeOrdinaryBody.State)
    (state : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt) : Prop :=
  match state with
  | (history,_,ordinary,_,steps,_,cursor,_,_) => Flow next inputs initial steps history initialOrdinary ordinary cursor

private def cursorOf {dependencies program block Cursor Receipt} :
    @QueryState dependencies program block Cursor Receipt → Nat
  | (_,_,_,_,_,_,cursor,_,_) => cursor

open RuntimeNamedSourceFlow (Returned reordered_self)

private theorem primitive_aligned {sources caller dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (history : RuntimeStructuralAction.SourceState)
    (frame : {frame : RuntimeOwnerMap.Checked (history.bindings.map (·.owner)) interval.before //
      frame.bindings = history.bindings})
    (event : SourceTypes.SourceRuntimeContext.Event sources caller)
    (location : Option (RuntimeSourceEvent.Location event start count))
    (result : RuntimeStructuralAction.SourceState × Node dependencies program block)
    (checked : RuntimeInterval.Computed (primitiveAt interval history frame event location) result) :
    NodeAligned history result.1 result.2 ∧ At start (start+count) (.pure result.2) ∧ IntrinsicNode result.2 := by
  obtain ⟨work,left,ran⟩ := checked
  unfold primitiveAt at ran
  obtain ⟨owners,a,_owners,h⟩ := bind_success _ _ _ _ _ ran
  cases event
  case phase event =>
    obtain ⟨input,b,_input,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨output,c,_output,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨action,d,_action,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,e,_charge,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩,True.intro⟩
  case primitive event =>
    obtain ⟨preserving,b,_preserving,h⟩ := bind_success _ _ _ _ _ h
    split at h
    next operand argument =>
      obtain ⟨kind,c,_kind,h⟩ := bind_success _ _ _ _ _ h
      rcases kind with ⟨kind,selection⟩
      obtain ⟨input,d,_input,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨output,e,_output,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨action,f,_action,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,g,_charge,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst result
      exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩,True.intro⟩
    all_goals cases h
  all_goals cases h

private theorem operation_aligned {artifact root} (execution : ExecutionMode artifact root)
    {owner name} (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceTypes.SourceOperationApplication.Event artifact.sources owner)
    {program} (block : RuntimeInterval.Block root.dependencies program) (position : Position)
    (cursor : execution.queries.Cursor)
    (data : execution.queries.EventData source (.operation event) position)
    (original : RuntimeBodyQueries.Operation execution.queries event source.requiresControl)
    (read : RuntimeInterval.Computed (RuntimeBodyQueries.readOperation execution.queries source event position cursor data) original)
    (expected : Semantics.Exact.Matrix) (node : Node root.dependencies program block)
    (initial : RuntimeStructuralAction.SourceState) {interval : RuntimeInterval.Checked block position.start position.count}
    (incoming : RuntimeOwnerMap.Checked (initial.bindings.map (·.owner)) interval.before)
    (initialOrder : incoming.bindings = initial.bindings)
    (owners : RuntimeOwnerTransition.Checked interval incoming.bindings)
    (ownerRead : RuntimeInterval.Computed (RuntimeOwnerTransition.read interval incoming.bindings) owners)
    (receipts : List execution.Receipt)
    (performed : OperationResult execution original expected receipts)
    (checked : RuntimeInterval.Computed
      (operationNode block position event.inputOwners initial.bindings owners.after.bindings expected) node) :
    NodeAligned initial {initial with bindings := owners.after.bindings} node ∧
      At position.start (position.start+position.count) (.pure node) ∧ OperationOrigin execution node := by
  have nodeRead := checked
  obtain ⟨work,left,ran⟩ := checked
  unfold operationNode at ran
  obtain ⟨inputs,a,_inputs,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨outputs,b,_outputs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨frame,c,_frame,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputCode,d,_input,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨outputCode,e,_output,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨physical,f,_physical,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨action,g,_action,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,i,_charge,h⟩ := bind_success _ _ _ _ _ h
  split at h
  · have same := (pure_success _ _ _ _ h).1
    subst node
    exact ⟨⟨rfl,⟨inputs,outputs,⟨work,a,_inputs⟩,⟨a,b,_outputs⟩,rfl,rfl⟩,
      ⟨interval,incoming,owners,initialOrder,rfl,ownerRead⟩⟩,⟨rfl,rfl⟩,
      ⟨owner,name,source,event,position,cursor,data,original,initial.bindings,owners.after.bindings,
        receipts,rfl,read,nodeRead,performed⟩⟩
  · cases h

private theorem selection_before_transport
    {dependencies program block start count inputs outputs selector target inputCode outputCode}
    {left right : @RuntimeInterval.Checked dependencies program block start count}
    (same : left = right)
    (codes : SelectionCodes left inputs outputs selector target inputCode outputCode) :
    (same ▸ codes).owners.before.bindings = codes.owners.before.bindings := by
  cases same
  rfl

private theorem selection_after_transport
    {dependencies program block start count inputs outputs selector target inputCode outputCode}
    {left right : @RuntimeInterval.Checked dependencies program block start count}
    (same : left = right)
    (codes : SelectionCodes left inputs outputs selector target inputCode outputCode) :
    (same ▸ codes).owners.transport.after.bindings = codes.owners.transport.after.bindings := by
  cases same
  rfl

private theorem selection_aligned {α Arm : Type} (artifact : Artifact)
    {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (frame : RuntimeOwnerMap.Checked roles interval.before)
    (owners : RuntimeOwnerTransition.Checked interval frame.bindings)
    (selector target : RuntimeOwnerMap.Owner) {moduleName name offset written ordinal}
    (table : SourceTypes.QuantumArms.TableWith artifact.sources moduleName name offset selector.basis target.basis Arm written ordinal)
    (site : RuntimeContextRequest.Site) (initial : α)
    (realize : Fin table.arms.length → Arm → α → WorkM (Semantics.Exact.Matrix × α))
    (structural : Arm → Bool)
    (result : Node dependencies program block × α)
    (before : RuntimeStructuralAction.SourceState)
    (sameBindings : frame.bindings = before.bindings)
    (checked : RuntimeInterval.Computed
      (selectionNode artifact interval frame owners selector target table site initial realize structural) result) :
    NodeAligned before {before with bindings := owners.after.bindings} result.1 ∧
      At start (start+count) (.pure result.1) := by
  obtain ⟨work,left,ran⟩ := checked
  unfold selectionNode at ran
  obtain ⟨_,a,_count,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨entry,b,_entry,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨exit,c,_exit,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,_interface,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputCode,e,_input,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨outputCode,f,_output,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨selectorRead,g,_selector,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨targetRead,i,_target,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨walk,j,_walk,h⟩ := bind_success _ _ _ _ _ h
  rcases walk with ⟨meanings,remaining⟩
  obtain ⟨expected,k,_expected,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨attached,l,_attached,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restriction,m,_restriction,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,n,_logical,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  refine ⟨?_,⟨rfl,rfl⟩⟩
  simp only [NodeAligned,selection_before_transport,selection_after_transport]
  exact ⟨sameBindings.symm,True.intro⟩


private theorem pure_gap_empty {dependencies program block start count history ordinary}
    {operations : List Semantics.Raw.Op}
    (pureBlock : (block : RuntimeInterval.Block dependencies program).operations =
      operations.map Semantics.Observation.Op.pure)
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count history ordinary) :
    count = 0 := by
  have classical := gap.checked.classical
  have empty : (block.operations.drop start).take count = [] := by
    cases literal : (block.operations.drop start).take count with
    | nil => rfl
    | cons first rest =>
      have member : first ∈ (block.operations.drop start).take count := by simp [literal]
      have pureMember := List.mem_of_mem_drop (List.mem_of_mem_take member)
      rw [pureBlock] at pureMember
      obtain ⟨op,_,rfl⟩ := List.mem_map.mp pureMember
      have impossible := List.all_eq_true.mp classical (.pure op) member
      cases impossible
  have length := congrArg List.length empty
  have within := gap.checked.interval.range
  simp only [List.length_take,List.length_drop,List.length_nil] at length
  omega

/-- A successful pure callback preserves its complete incoming SSA state. -/
def PurePreservesOrdinary {artifact root execution} (next : BlockRunner artifact root execution) : Prop :=
  ∀ {boundary rootOwner rootName owner name}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (plan : execution.queries.BodyData source request)
    (initial : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt) (work left : Nat),
    (next .pureBody boundary source path program request plan initial ordinary block).run work = (.ok result,left) →
    result.1.ordinary = ordinary

/-- A pure named receipt receives exactly the SSA state of its enclosing
pure body. Other step constructors carry their existing receipts. -/
def PureCallAt {artifact root execution} (next : BlockRunner artifact root execution)
    (inputs : RootInputs) (ordinary : RuntimeOrdinaryBody.State) {program block} :
    Step root.dependencies program block → Prop
  | .pure node@(.named ..) => PureChildRunAt artifact root execution next (some inputs) ordinary node
  | _ => True

structure PureFlowFacts {artifact root execution} (next : BlockRunner artifact root execution)
    (inputs : RootInputs) (incoming outgoing : RuntimeOrdinaryBody.State) {program block}
    (actions : List (Node root.dependencies program block)) (steps : List (Step root.dependencies program block)) : Prop where
  ordinary : outgoing = incoming
  literal : steps = actions.map Step.pure
  calls : ∀ step ∈ steps, PureCallAt next inputs incoming step

def IsPureLiteral {dependencies program block} : Step dependencies program block → Prop
  | .pure _ => True
  | _ => False

theorem PureFlowFacts.allPure {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs incoming outgoing program block actions steps}
    (facts : @PureFlowFacts artifact root execution next inputs incoming outgoing program block actions steps) :
    ∀ step ∈ steps, IsPureLiteral step := by
  intro step present
  rw [facts.literal] at present
  obtain ⟨node,_,rfl⟩ := List.mem_map.mp present
  exact True.intro

private theorem PureFlowFacts.snoc {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs incoming outgoing final program block actions steps}
    (facts : @PureFlowFacts artifact root execution next inputs incoming outgoing program block actions steps)
    (node : Node root.dependencies program block)
    (ordinary : final = outgoing) (call : PureCallAt next inputs incoming (.pure node)) :
    PureFlowFacts next inputs incoming final (actions ++ [node]) (steps ++ [.pure node]) := by
  refine ⟨ordinary.trans facts.ordinary,by simp only [facts.literal,List.map_append,List.map_singleton],?_⟩
  intro step member
  rcases List.mem_append.mp member with old | last
  · exact facts.calls step old
  · exact (List.mem_singleton.mp last).symm ▸ call

private theorem PureCallAt.of_operationOrigin {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs ordinary program block} {node : Node root.dependencies program block}
    (source : OperationOrigin execution node) : PureCallAt next inputs ordinary (.pure node) := by
  cases node <;> first | exact True.intro | exact False.elim source

/-- A runtime-body iteration records a named call as a mixed step. -/
def IsRuntimeStep {dependencies program block} : Step dependencies program block → Prop
  | .pure (.named ..) => False
  | _ => True

private theorem mixed_selection_step {artifact root execution} {next : BlockRunner artifact root execution}
    {inputs program block} {node : Node root.dependencies program block}
    (original : MixedSelectionOrigin execution next node) :
    CheckedStepAt next inputs (.pure node) ∧
      (∀ ordinary, PureCallAt next inputs ordinary (.pure node)) ∧ IsRuntimeStep (.pure node) := by
  cases node
  case selection => exact ⟨Or.inr original,fun _ => True.intro,True.intro⟩
  all_goals
    obtain ⟨_,_,_,_,_,_,_,_,_,invalid⟩ := original
    exact False.elim invalid

def RuntimeOnly {dependencies program block} (steps : List (Step dependencies program block)) : Prop :=
  ∀ step ∈ steps, IsRuntimeStep step

theorem RuntimeOnly.snoc {dependencies program block} {steps : List (Step dependencies program block)} {step}
    (old : RuntimeOnly steps) (last : IsRuntimeStep step) : RuntimeOnly (steps ++ [step]) := by
  intro current present
  rcases List.mem_append.mp present with previous | tail
  · exact old current previous
  · exact (List.mem_singleton.mp tail).symm ▸ last

private theorem IsRuntimeStep.of_operationOrigin {artifact root execution program block}
    {node : Node root.dependencies program block} (origin : @OperationOrigin artifact root execution program block node) :
    IsRuntimeStep (.pure node) := by
  cases node <;> first | exact True.intro | exact origin

structure ModeFacts {artifact root execution} (next : BlockRunner artifact root execution) (mode : Mode)
    (inputs : RootInputs) (incoming outgoing : RuntimeOrdinaryBody.State) {program block}
    (actions : List (Node root.dependencies program block)) (steps : List (Step root.dependencies program block)) : Prop where
  pure : mode = .pureBody → PureFlowFacts next inputs incoming outgoing actions steps
  runtime : mode = .runtimeBody → RuntimeOnly steps

private theorem ModeFacts.snocPure {artifact root execution} {next : BlockRunner artifact root execution}
    {mode inputs incoming middle outgoing program block actions steps}
    (facts : @ModeFacts artifact root execution next mode inputs incoming middle program block actions steps)
    (node : Node root.dependencies program block) (ordinary : outgoing = middle)
    (call : mode = .pureBody → PureCallAt next inputs incoming (.pure node))
    (runtime : mode = .runtimeBody → IsRuntimeStep (.pure node)) :
    ModeFacts next mode inputs incoming outgoing (actions ++ [node]) (steps ++ [.pure node]) :=
  ⟨fun pure => (facts.pure pure).snoc node ordinary (call pure),fun mixed => (facts.runtime mixed).snoc (runtime mixed)⟩

private def ModeInvariant {artifact root execution} (next : BlockRunner artifact root execution)
    (mode : Mode) (inputs : RootInputs) {program block}
    (initial : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (state : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt) : Prop :=
  Invariant next inputs initial ordinary state ∧
    ModeFacts next mode inputs ordinary state.2.2.1 state.2.2.2.1 state.2.2.2.2.1


private abbrev SectionState {artifact : Artifact} (queries : RuntimeBodyQueries.Mode artifact)
    (Receipt : Type) {dependencies program} (block : RuntimeInterval.Block dependencies program) :=
  QueryState dependencies program block queries.Cursor Receipt

private abbrev SectionStep {artifact : Artifact} (queries : RuntimeBodyQueries.Mode artifact)
    {owner name} (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (State : Type) :=
  (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner) → (position : Position) →
    RuntimeSourceEvent.Origin event position → queries.EventData source event position → State → WorkM State

private def withSourceCursor {dependencies program block Cursor Receipt}
    (state : @QueryState dependencies program block Cursor Receipt) (next : Cursor) :
    @QueryState dependencies program block Cursor Receipt :=
  let (history,retired,ordinary,actions,steps,obligations,cursor,_,receipts) := state
  (history,retired,ordinary,actions,steps,obligations,cursor,next,receipts)

private theorem preserves_static_conditional {artifact : Artifact}
    (queries : RuntimeBodyQueries.Mode artifact) {owner name}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    {dependencies program} (block : RuntimeInterval.Block dependencies program) {Receipt : Type}
    (positions : List Position) (pureOnly : Bool)
    (event : SourceTypes.SourceRuntimeContext.StaticEvent artifact.sources owner)
    (children : List (SourceTypes.SourceRuntimeContext.Event artifact.sources owner))
    (position : Position)
    (entry : RuntimeSourceEvent.At (source.events.zip positions) (.staticConditional event children) position)
    (data : queries.EventData source (.staticConditional event children) position)
    (advance : SectionState queries Receipt block → Nat → WorkM (SectionState queries Receipt block))
    (step : SectionStep queries source (SectionState queries Receipt block))
    (property : SectionState queries Receipt block → Prop)
    (advances : ∀ before after start work left, property before →
      (advance before start).run work = (.ok after,left) → property after)
    (steps : ∀ event position origin data before after work left, property before →
      (step event position origin data before).run work = (.ok after,left) → property after)
    (rescope : ∀ state cursor, property state → property (withSourceCursor state cursor))
    (before after : SectionState queries Receipt block) (work left : Nat) (opening : property before)
    (read : ((do
      let (_,_,_,_,_,_,_,incomingSourceCursor,_) := before
      let actual ← SourceTypes.NaturalAffine.witness
        (RuntimeBodyQueries.readStatic queries source event children position pureOnly incomingSourceCursor data)
      let selected := actual.val
      let state ← advance before position.start
      let (history,retired,ordinary,actions,steps,obligations,cursor,_,receipts) := state
      let sequence := selected.sequence
      let interval ← RuntimeInterval.check block position.start position.count
      let bindings := (← reordered (history.bindings.map (·.owner)) interval.before history.bindings).bindings
      let before : RuntimeStructuralAction.SourceState := {history with bindings}
      let _ ← RuntimeStaticPrimitive.readContinuationBefore sequence interval before source.suspended
      let count := sequence.selected.result.events.length
      exactWork (Exact.charge (32*(count+1)*(actions.length+steps.length+obligations.length+count+1)+
        32*(Raw.OwnerFlow.fields retired+1)))
      let initial : SectionState queries Receipt block :=
        (before,retired,ordinary,actions,steps,obligations,cursor,selected.cursor,receipts)
      let result ← RuntimeBodyQueries.foldEvents queries source
        (sequence.selected.result.events.zip selected.positions)
        (fun child childPosition inner childData state =>
          step child childPosition (RuntimeBodyQueries.selectedOrigin queries source positions
            event children position entry pureOnly incomingSourceCursor data
            ⟨selected,by with_reducible exact actual.property⟩ inner) childData state)
        selected.events initial
      let (after,afterRetired,_,_,_,_,afterCursor,_,_) := result
      guard (afterCursor == position.start+position.count) .request
      let _ ← RuntimeStaticPrimitive.readContinuationAfter sequence interval before after retired afterRetired source.suspended
      return result) : WorkM (SectionState queries Receipt block)).run work = (.ok after,left)) :
    property after := by
  rcases before with ⟨history,retired,ordinary,actions,stepsBefore,obligations,cursor,sourceCursor,receipts⟩
  dsimp (config := {zeta := false}) only at read
  obtain ⟨actual,a,_,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨advanced,b,advancedRead,rest⟩ := bind_success _ _ _ _ _ rest
  have entered := advances _ advanced position.start a b opening advancedRead
  rcases advanced with ⟨history,retired,ordinary,actions,stepsBefore,obligations,cursor,sourceCursor,receipts⟩
  obtain ⟨interval,c,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨ordered,d,orderedRead,rest⟩ := bind_success _ _ _ _ _ rest
  have sameMap : ordered.bindings = history.bindings := reordered_self ⟨c,d,orderedRead⟩
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,f,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨result,g,walked,rest⟩ := bind_success _ _ _ _ _ rest
  rcases result with ⟨historyAfter,retiredAfter,ordinaryAfter,actionsAfter,stepsAfter,obligationsAfter,cursorAfter,sourceCursorAfter,receiptsAfter⟩
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,returned⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ returned).1
  subst after
  have trace := RuntimeBodyQueries.foldEvents_trace queries source
    (actual.val.sequence.selected.result.events.zip actual.val.positions) _ actual.val.events _ _ f g walked
  apply trace.invariant property
  · simpa only [sameMap,withSourceCursor] using rescope _ actual.val.cursor entered
  · intro child position inner data before after work left incoming read
    exact steps child position _ data before after work left incoming read

private theorem preserves_static_fold {artifact : Artifact}
    (queries : RuntimeBodyQueries.Mode artifact) {owner name}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    {dependencies program} (block : RuntimeInterval.Block dependencies program) {Receipt : Type}
    (positions : List Position)
    (event : SourceTypes.SourceRuntimeContext.FoldEvent artifact.sources owner)
    (iterations : List (List (SourceTypes.SourceRuntimeContext.Event artifact.sources owner)))
    (position : Position)
    (entry : RuntimeSourceEvent.At (source.events.zip positions) (.staticFold event iterations) position)
    (data : queries.EventData source (.staticFold event iterations) position)
    (advance : SectionState queries Receipt block → Nat → WorkM (SectionState queries Receipt block))
    (step : SectionStep queries source (SectionState queries Receipt block))
    (property : SectionState queries Receipt block → Prop)
    (advances : ∀ before after start work left, property before →
      (advance before start).run work = (.ok after,left) → property after)
    (steps : ∀ event position origin data before after work left, property before →
      (step event position origin data before).run work = (.ok after,left) → property after)
    (rescope : ∀ state cursor, property state → property (withSourceCursor state cursor))
    (before after : SectionState queries Receipt block) (work left : Nat) (opening : property before)
    (read : ((do
      let (_,_,_,_,_,_,_,incomingSourceCursor,_) := before
      let selected ← RuntimeBodyQueries.readFold queries source event iterations position incomingSourceCursor data
      let (history,retired,ordinary,actions,steps,obligations,cursor,_,receipts) ← advance before position.start
      let interval ← RuntimeInterval.check block position.start position.count
      let _ ← RuntimeStaticFold.readBefore event interval history source.suspended
      let count := selected.partition.positions.length
      exactWork (Exact.charge (32*(count+1)*(actions.length+steps.length+obligations.length+count+1)+
        32*(Raw.OwnerFlow.fields retired+1)))
      let initial : SectionState queries Receipt block :=
        (history,retired,ordinary,actions,steps,obligations,cursor,selected.cursor,receipts)
      let result ← RuntimeBodyQueries.foldEvents queries source
        (iterations.flatten.zip selected.partition.positions)
        (fun child position inner data state =>
          step child position (.folded source positions entry selected.partition inner) data state)
        selected.events initial
      let (after,afterRetired,_,_,_,_,afterCursor,_,_) := result
      guard (afterCursor == position.start+position.count) .request
      let _ ← RuntimeStaticFold.readAfter event interval history after retired afterRetired source.suspended
      return result) : WorkM (SectionState queries Receipt block)).run work = (.ok after,left)) :
    property after := by
  rcases before with ⟨history,retired,ordinary,actions,stepsBefore,obligations,cursor,sourceCursor,receipts⟩
  dsimp (config := {zeta := false}) only at read
  obtain ⟨selected,a,_,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨advanced,b,advancedRead,rest⟩ := bind_success _ _ _ _ _ rest
  have entered := advances _ advanced position.start a b opening advancedRead
  rcases advanced with ⟨history,retired,ordinary,actions,stepsBefore,obligations,cursor,sourceCursor,receipts⟩
  obtain ⟨interval,c,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,e,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨result,f,walked,rest⟩ := bind_success _ _ _ _ _ rest
  rcases result with ⟨historyAfter,retiredAfter,ordinaryAfter,actionsAfter,stepsAfter,obligationsAfter,cursorAfter,sourceCursorAfter,receiptsAfter⟩
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,returned⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ returned).1
  subst after
  have trace := RuntimeBodyQueries.foldEvents_trace queries source
    (iterations.flatten.zip selected.partition.positions) _ selected.events _ _ e f walked
  apply trace.invariant property
  · exact rescope _ selected.cursor entered
  · intro child position inner data before after work left incoming read
    exact steps child position _ data before after work left incoming read

set_option maxHeartbeats 500000 in
/-- One proof of the actual iteration retains both the complete state chain
and its named-child computations. The recursive caller is explicit here;
core_flow fixes it to the real previous fuel level. -/
theorem step_flow_mode (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution)
    (mode : Mode) (outputBoundary : OutputBoundary) (pureNext : PurePreservesOrdinary next)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (initialOrdinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockStep artifact root execution next mode outputBoundary source path program request
        sourcePlan initialHistory initialOrdinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow next (RuntimeBranchCondition.rootEntries path) {initialHistory with bindings := initial.bindings} result.1.steps last
        initialOrdinary result.1.ordinary block.operations.length ∧
        Returned block source.outputRoles last result.1.history ∧
        ModeFacts next mode (RuntimeBranchCondition.rootEntries path)
          initialOrdinary result.1.ordinary result.1.actions result.1.steps := by
  obtain ⟨work,left,ran⟩ := checked
  simp (config := {zeta := false}) only [runBlockStep] at ran
  obtain ⟨_,w₁,_signature,rest⟩ := bind_success _ _ _ _ _ ran
  extract_lets -underBinder +onlyGivenNames afterMode at rest
  let singleton (value : SourceTypes.SourceRuntimeValues.Value) :=
    (SourceTypes.SourceRuntimeValues.ordinary value).all fun (basis,_) =>
      Semantics.FiniteCarrier.dimension basis == some 1
  let pureCheck : WorkM Unit := do
    guard (program.effect != .observe && SourceTypes.SourceEffect.permits (some program.effect) source.effect &&
      singleton source.value &&
      source.parameterValues.all singleton &&
      program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
    let _ ← lift (readOption (Sector.pureOps block.operations))
    pure ()
  have modeRead : (((match mode with
    | .pureBody => pureCheck
    | .runtimeBody => guard (SourceTypes.SourceEffect.permits (some program.effect) source.effect) .request)
      : WorkM Unit) >>= afterMode).run w₁ = (.ok result,left) := by
    cases mode <;> simpa only [pureCheck,bind_assoc] using rest
  obtain ⟨allowed,w₂,_effect,rest⟩ := bind_success _ _ _ _ _ modeRead
  have pureBlock (isPure : mode = .pureBody) :
      ∃ operations : List Semantics.Raw.Op, block.operations = operations.map Semantics.Observation.Op.pure := by
    have readMode : pureCheck.run w₁ = (.ok allowed,w₂) := by
      cases mode
      · exact _effect
      · cases isPure
    obtain ⟨_,_,_,parsed⟩ := bind_success _ _ _ _ _ readMode
    obtain ⟨operations,_,read,_⟩ := bind_success _ _ _ _ _ parsed
    have found := (lift_success _ _ _ _ read).1
    have actual : Sector.pureOps block.operations = some operations := by
      cases literal : Sector.pureOps block.operations with
      | none => simp only [literal,readOption] at found; cases found
      | some values =>
        simp only [literal,readOption,Except.ok.injEq] at found
        exact congrArg some found
    exact ⟨operations,Sector.pureOps_bound _ _ actual⟩
  dsimp (config := {zeta := false}) only [afterMode] at rest
  obtain ⟨_,w₃,_ordinal,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨initial,w₄,_initial,rest⟩ := bind_success _ _ _ _ _ rest
  extract_lets historyStart checkFresh consumeGraph advance step pureOnly outerStep at rest
  refine ⟨initial,⟨w₃,w₄,_initial⟩,?_⟩
  obtain ⟨opening,w₅,_opening,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨prefixState,w₆,_prefix,rest⟩ := bind_success _ _ _ _ _ rest
  rcases prefixState with ⟨obligations,sourceCursor,receipts⟩
  obtain ⟨_,w₇,_charge,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,w₈,_positions,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨walk,w₉,walked,rest⟩ := bind_success _ _ _ _ _ rest
  rcases walk with ⟨history,retired,ordinaryAfter,actions,steps,obligationsAfter,cursor,sourceCursorAfter,receiptsAfter⟩
  obtain ⟨_,w₁₀,_cursor,rest⟩ := bind_success _ _ _ _ _ rest
  have inBlock : cursor ≤ block.operations.length := by
    have valid := (guard_success _ _ _ _ _cursor).1
    simp only [Bool.and_eq_true] at valid
    exact of_decide_eq_true valid.1
  extract_lets finish at rest
  have finish_steps (pair : RuntimeOrdinaryBody.State × List (Step root.dependencies program block))
      (value : BlockResult root.dependencies program block × List execution.Receipt)
      (budget remaining : Nat)
      (read : (finish pair).run budget = (.ok value,remaining)) :
      value.1.steps = pair.2 ∧ value.1.ordinary = pair.1 ∧ value.1.actions = actions ∧
        Returned block source.outputRoles history value.1.history := by
    rcases pair with ⟨ordinaryResult,actualSteps⟩
    dsimp only [finish] at read
    obtain ⟨_,a,_,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨native,b,nativeRead,h⟩ := bind_success _ _ _ _ _ h
    cases mode
    all_goals
      obtain ⟨_,c,_,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨owners,d,ownersRead,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,e,_,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,f,_,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst value
      exact ⟨rfl,rfl,rfl,native,⟨a,b,nativeRead⟩,owners,⟨c,d,ownersRead⟩,rfl⟩
  suffices connected : ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary
      (history,retired,ordinaryAfter,actions,steps,obligationsAfter,cursor,sourceCursorAfter,receiptsAfter) by
    have chain := connected.1
    split at rest
    · rename_i atEnd
      have full : cursor = block.operations.length := beq_iff_eq.mp atEnd
      obtain ⟨pair,budget,opened,finished⟩ := bind_success _ _ _ _ _ rest
      have same := (pure_success _ _ _ _ opened).1
      subst pair
      have finishedData := finish_steps (ordinaryAfter,steps) result budget left finished
      refine ⟨history,finishedData.1.symm ▸ finishedData.2.1.symm ▸ full ▸ chain,finishedData.2.2.2,?_⟩
      rw [finishedData.1,finishedData.2.1,finishedData.2.2.1]
      exact connected.2
    · rename_i notAtEnd
      obtain ⟨gap,budget,_gap,rest⟩ := bind_success _ _ _ _ _ rest
      obtain ⟨pair,afterGap,opened,finished⟩ := bind_success _ _ _ _ _ rest
      have same := (pure_success _ _ _ _ opened).1
      subst pair
      let gapStep : Step root.dependencies program block :=
        @Step.gap root.dependencies program block cursor (block.operations.length-cursor) history ordinaryAfter gap
      have finishedData := finish_steps (gap.ssa,steps ++ [gapStep]) result afterGap left finished
      refine ⟨history,finishedData.1.symm ▸ finishedData.2.1.symm ▸
        chain.snoc ⟨rfl,rfl⟩ True.intro ⟨rfl,rfl⟩ ⟨rfl,by
          change cursor+(block.operations.length-cursor) = block.operations.length
          omega⟩ True.intro,finishedData.2.2.2,?_⟩
      constructor
      · intro isPure
        obtain ⟨_,pureOps⟩ := pureBlock isPure
        have count := pure_gap_empty pureOps gap
        have atEnd : cursor = block.operations.length := by omega
        simp [atEnd] at notAtEnd
      · intro isRuntime
        rw [finishedData.1]
        exact (connected.2.runtime isRuntime).snoc True.intro
  have advances (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (start budget remaining : Nat) (incoming : ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary before)
      (read : (advance before start).run budget = (.ok after,remaining)) :
      ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary after ∧ cursorOf after = start := by
    rcases before with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
    dsimp only [advance] at read
    obtain ⟨_,middle,guarded,h⟩ := bind_success _ _ _ _ _ read
    have within : cursor ≤ start := of_decide_eq_true (guard_success _ _ _ _ guarded).1
    split at h
    · rename_i noGap
      have same := (pure_success _ _ _ _ h).1
      subst after
      exact ⟨incoming,beq_iff_eq.mp noGap⟩
    · rename_i notAtStart
      obtain ⟨gap,afterGap,_gap,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst after
      have chain := incoming.1
      refine ⟨⟨chain.snoc ⟨rfl,rfl⟩ True.intro ⟨rfl,rfl⟩ ⟨rfl,by
        change cursor+(start-cursor) = start
        omega⟩ True.intro,?_⟩,rfl⟩
      constructor
      · intro isPure
        obtain ⟨_,pureOps⟩ := pureBlock isPure
        have count := pure_gap_empty pureOps gap
        have atStart : cursor = start := by omega
        simp [atStart] at notAtStart
      · exact fun isRuntime => (incoming.2.runtime isRuntime).snoc True.intro
  have named_preserves
      (event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin (.named event) position)
      (data : execution.queries.EventData source (.named event) position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary before)
      (read : (step (.named event) position origin data before).run budget = (.ok after,remaining)) :
      ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary after := by
    dsimp only [step] at read
    obtain ⟨advanced,a,advanceRead,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨entered,atStart⟩ := advances before advanced position.start budget a incoming advanceRead
    rcases advanced with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
    obtain ⟨_,b,_charge,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨interval,c,_interval,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨certificate,d,_frame,h⟩ := bind_success _ _ _ _ _ h
    rcases certificate with ⟨frame,sameBindings⟩
    obtain ⟨named,e,_named,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨ordered,f,_ordered,h⟩ := bind_success _ _ _ _ _ h
    split at h
    next callerName =>
      cases mode
      case pureBody =>
        obtain ⟨_,g,effectRead,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨opened,i,_opened,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨bound,j,_bound,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨childInitial,k,_initial,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨children,l,_children,h⟩ := bind_success _ _ _ _ _ h
        rcases children with ⟨nested,childReceipts⟩
        obtain ⟨boundary,m,_boundary,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have ordinarySame := pureNext _ _ _ _ _ _ _ _ _ _ _ _children
        have authentic : PureChildRunAt artifact root execution next
            (some (RuntimeBranchCondition.rootEntries path)) ordinary
            (.named event opened.val named.body named.original boundary (Nodes.ofList nested.actions)) := by
          refine .named (beq_iff_eq.mp (guard_success _ _ _ _ effectRead).1) _initial _children ?_
          intro inputs sameRoot
          have same := Option.some.inj sameRoot
          subst inputs
          rw [Qleisli.RuntimeBranchInputDomain.named_entries]
          cases callerName
          rfl
        refine ⟨entered.1.snoc ⟨?_,rfl⟩ ⟨ordinary,authentic⟩ ordinarySame ⟨atStart.symm,rfl⟩ True.intro,
          entered.2.snocPure _ ordinarySame ?_ ?_⟩
        · change history = {history with bindings := frame.bindings}
          rw [sameBindings]
        · intro isPure
          have facts := entered.2.pure isPure
          exact facts.ordinary ▸ authentic
        · intro impossible
          cases impossible
      case runtimeBody =>
        obtain ⟨opened,g,_opened,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨bound,i,_bound,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨childInitial,j,_initial,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨children,k,_children,h⟩ := bind_success _ _ _ _ _ h
        rcases children with ⟨nested,childReceipts⟩
        obtain ⟨boundary,l,_boundary,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered.1
        refine ⟨chain.snoc ?_ ?_ ⟨rfl,rfl⟩ ⟨atStart.symm,rfl⟩ True.intro,
          ⟨(by intro impossible; cases impossible),fun mixed => (entered.2.runtime mixed).snoc True.intro⟩⟩
        · constructor
          · change history = {history with bindings := frame.bindings}
            rw [sameBindings]
          · rfl
        · refine .named _initial _children ?_
          intro inputs sameRoot
          have same := Option.some.inj sameRoot
          subst inputs
          rw [Qleisli.RuntimeBranchInputDomain.named_entries]
          cases callerName
          rfl
    next => cases h
  have steps_preserve
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary before)
      (read : (step event position origin data before).run budget = (.ok after,remaining)) :
      ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary after := by
    cases event
    case named event =>
      exact named_preserves event position origin data before after budget remaining incoming read
    all_goals
      dsimp only [step] at read
      obtain ⟨advanced,a,advanceRead,h⟩ := bind_success _ _ _ _ _ read
      obtain ⟨entered,atStart⟩ := advances before advanced position.start budget a incoming advanceRead
      rcases advanced with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
      obtain ⟨_,b,_charge,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨interval,c,_interval,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨certificate,d,_frame,h⟩ := bind_success _ _ _ _ _ h
      rcases certificate with ⟨frame,sameBindings⟩
    case phase =>
      obtain ⟨performed,e,_performed,returned⟩ := bind_success _ _ _ _ _ h
      rcases performed with ⟨nextHistory,node⟩
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have chain := entered.1
      obtain ⟨aligned,⟨first,last⟩,intrinsic⟩ := primitive_aligned interval history ⟨frame,sameBindings⟩ _ _ _ ⟨d,e,_performed⟩
      refine ⟨chain.snoc aligned (.of_operationOrigin (intrinsic_origin intrinsic)) rfl
        ⟨first.trans atStart.symm,last⟩ True.intro,?_⟩
      exact entered.2.snocPure _ rfl (fun _ => .of_operationOrigin (execution := execution) (intrinsic_origin intrinsic))
        (fun _ => .of_operationOrigin (execution := execution) (intrinsic_origin intrinsic))
    case operation =>
      obtain ⟨operation,e,_operation,h⟩ := bind_success _ _ _ _ _ h
      split at h
      swap
      · cases h
      rename_i caller
      obtain ⟨performed,f,_performed,h⟩ := bind_success _ _ _ _ _ h
      rcases performed with ⟨expected,children,performedReceipts⟩
      have resultRead : OperationResult execution operation expected performedReceipts := by
        cases execution with
        | fresh _ => trivial
        | planned preparation continuation =>
          rcases operation with ⟨child,⟨references,afterPlan,graph⟩,queryCursor⟩
          exact planned_operation_result continuation _ ⟨rootOwner,rootName,owner,name,path,.application _ caller⟩ _performed
      split at h
      · obtain ⟨_,i,_shape,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨owners,j,_owners,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨node,k,_node,h⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ h).1
        subst after
        have original := (show RuntimeInterval.Computed _ node from ⟨j,k,_node⟩)
        obtain ⟨aligned,⟨first,last⟩,authentic⟩ := operation_aligned execution source _ block position
          sourceCursor data operation ⟨d,e,_operation⟩ expected node history frame sameBindings owners
          ⟨i,j,_owners⟩ performedReceipts resultRead
          (by simpa only [sameBindings] using original)
        exact ⟨entered.1.snoc aligned (.of_operationOrigin authentic) rfl ⟨first.trans atStart.symm,last⟩ True.intro,
          entered.2.snocPure _ rfl (fun _ => .of_operationOrigin (execution := execution) authentic)
            (fun _ => .of_operationOrigin (execution := execution) authentic)⟩
      · obtain ⟨checked,_,_checked,h⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ h).1
        subst after
        have authentic : OperationOrigin execution (.rectangularOperation checked) :=
          ⟨owner,name,source,_,position,sourceCursor,data,operation,performedReceipts,
            HEq.rfl,rfl,rfl,⟨d,e,_operation⟩,resultRead⟩
        have startsWithSource : history = {history with bindings := frame.bindings} := by
          rw [sameBindings]
        exact ⟨entered.1.snoc ⟨startsWithSource,rfl⟩ (.of_operationOrigin authentic) rfl ⟨atStart.symm,rfl⟩ True.intro,
          entered.2.snocPure _ rfl (fun _ => .of_operationOrigin (execution := execution) authentic)
            (fun _ => .of_operationOrigin (execution := execution) authentic)⟩
    case transform =>
      obtain ⟨transformed,e,_transformed,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨forward,f,_forward,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨performed,g,_performed,h⟩ := bind_success _ _ _ _ _ h
      rcases performed with ⟨child,performedReceipts⟩
      obtain ⟨logical,i,_logical,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨owners,j,_owners,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨action,k,_action,returned⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have chain := entered.1
      have startsWithSource : history = {history with bindings := frame.bindings} := by
        rw [sameBindings]
      refine ⟨chain.snoc ⟨startsWithSource,rfl⟩ (TransformRun.checked _transformed _forward _performed)
        rfl ⟨?_,?_⟩ True.intro,entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
      · exact atStart.symm
      · rfl
    case selection =>
      let event : SourceTypes.SourceRuntimeContext.SelectionEvent artifact.sources owner := by assumption
      obtain ⟨owners,e,_owners,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨selected,f,_selected,h⟩ := bind_success _ _ _ _ _ h
      cases selected
      case inl selected =>
        obtain ⟨performed,g,_performed,h⟩ := bind_success _ _ _ _ _ h
        rcases performed with ⟨logicals,children,cursor,receipts⟩
        obtain ⟨actual,i,_node,returned⟩ := bind_success _ _ _ _ _ h
        rcases actual with ⟨node,extra⟩
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered.1
        obtain ⟨aligned,⟨first,last⟩⟩ := selection_aligned artifact interval frame owners _ _ _ _ _ _ (fun _ => false)
          (node,extra) history sameBindings ⟨g,i,_node⟩
        have exactActions := RuntimeSelectionLogicalRead.selectionNode_from_fold interval frame owners _ _
          selected.table selected.site execution.queries _
          (fun state : List Semantics.Exact.Matrix × List (Island root.dependencies) ×
            execution.queries.Cursor × List execution.Receipt => state.1)
          (GraphLogical execution selected.table) (by
            intro index data start finish work left ran
            obtain ⟨_,charged,_,ran⟩ := bind_success _ _ _ _ _ ran
            obtain ⟨value,returned,graphRead,ran⟩ := bind_success _ _ _ _ _ ran
            rcases value with ⟨matrix,children,cursor,receipts⟩
            obtain ⟨rfl,_⟩ := pure_success _ _ _ _ ran
            refine ⟨matrix,rfl,?_⟩
            cases execution with
            | fresh _ => exact True.intro
            | planned preparation continuation =>
              rcases data with ⟨implementations,references,plan⟩
              obtain ⟨checked,budget,_,paid⟩ := bind_success _ _ _ _ _ graphRead
              obtain ⟨_,finished,_,returned⟩ := bind_success _ _ _ _ _ paid
              have action := congrArg Prod.fst (pure_success _ _ _ _ returned).1
              exact ⟨checked.val,checked.property,action⟩)
          selected.arms _ _ rfl ⟨f,g,_performed⟩ (node,extra) ⟨g,i,_node⟩
        have original : SelectionOrigin execution node :=
          ⟨_,_,source,_,_,_,_,_,selected.table,selected.original,
            exactActions.weaken (fun _ _ ⟨graph,_,_,_,_,_,produced⟩ => ⟨graph,produced⟩)⟩
        exact ⟨chain.snoc (by simpa only [sameBindings] using aligned) (.of_operationOrigin (selection_origin original)) rfl
          ⟨first.trans atStart.symm,last⟩ True.intro,
          entered.2.snocPure _ rfl (fun _ => .of_operationOrigin (execution := execution) (selection_origin original))
            (fun _ => .of_operationOrigin (execution := execution) (selection_origin original))⟩
      case inr selected =>
        obtain ⟨performed,g,_performed,h⟩ := bind_success _ _ _ _ _ h
        rcases performed with ⟨logicals,children,finalCursor,finalReceipts⟩
        obtain ⟨actual,i,_node,returned⟩ := bind_success _ _ _ _ _ h
        rcases actual with ⟨node,extra⟩
        have same := (pure_success _ _ _ _ returned).1
        subst after
        let childPath : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner event.callerName :=
          selected.sameName.symm ▸ path
        let parent := {history with bindings := frame.bindings}
        let State := List Semantics.Exact.Matrix × List (Island root.dependencies) ×
          execution.queries.Cursor × List execution.Receipt
        let named : MixedNamed execution.queries selected.table State :=
          fun index arm atIndex data (logicals,checked,cursor,receipts) => do
            exactWork (Exact.charge (16*(logicals.length+receipts.length+1)))
            let (logical,children,cursor,performed) ← consumeGraph arm.operation.graph
              SourceTypes.OperationAccess.controllable (.arm arm.operation) path
              (.arm arm (.mixed event selected.sameName selected.table index atIndex))
              cursor data (!request.references.isEmpty)
            return (logicals ++ [logical],checked ++ children,cursor,receipts ++ performed)
        let inline : MixedInline execution.queries event State :=
          fun {index} arm replay child plan (logicals,checked,cursor,receipts) => do
            exactWork (Exact.charge (16*(logicals.length+receipts.length+index+1)))
            let subject ← lift (readOption selected.site.arms[index]?)
            let inlineCheck ← readInlineArm rfl arm replay subject.implementation child plan childPath parent next
            return (logicals ++ [inlineCheck.action.code.logical],checked ++ inlineCheck.result.islands,
              cursor,receipts ++ inlineCheck.receipts)
        let initial : State := ([],[],selected.cursor,receipts)
        let final : State := (logicals,children,finalCursor,finalReceipts)
        let structural (arm : SourceTypes.QuantumArms.RuntimeArm event event.selector.basis event.target.basis) : Bool :=
          match arm with
          | .inline .. => true
          | .operation _ => false
        have folded : RuntimeInterval.Computed
            (RuntimeBodyQueries.foldMixedArms execution.queries position selected.table named inline selected.arms initial) final :=
          ⟨f,g,_performed⟩
        obtain ⟨aligned,⟨first,last⟩⟩ := selection_aligned artifact interval frame owners _ _ _ _ _ _ structural
          (node,extra) history sameBindings ⟨g,i,_node⟩
        have exactActions := RuntimeSelectionLogicalRead.selectionNode_from_mixed_fold interval frame owners
          selected.table selected.site structural execution.queries position named inline
          (Prod.fst : State → List Semantics.Exact.Matrix)
          (MixedLogical execution next selected.site childPath parent) (by
            intro index slot start finish work left ran
            cases slot with
            | named arm selected data =>
              dsimp only [MixedSlot.run,named] at ran
              obtain ⟨_,charged,_,ran⟩ := bind_success _ _ _ _ _ ran
              obtain ⟨value,returned,graphRead,ran⟩ := bind_success _ _ _ _ _ ran
              rcases value with ⟨matrix,children,cursor,receipts⟩
              obtain ⟨rfl,_⟩ := pure_success _ _ _ _ ran
              refine ⟨matrix,rfl,?_⟩
              cases execution with
              | fresh _ => exact True.intro
              | planned preparation continuation =>
                rcases data with ⟨implementations,references,plan⟩
                obtain ⟨checked,budget,_,paid⟩ := bind_success _ _ _ _ _ graphRead
                obtain ⟨_,finished,_,returned⟩ := bind_success _ _ _ _ _ paid
                have action := congrArg Prod.fst (pure_success _ _ _ _ returned).1
                exact ⟨checked.val,checked.property,action⟩
            | inline arm replayed ports label originalLabel original child plan =>
              dsimp only [MixedSlot.run,inline] at ran
              obtain ⟨_,charged,_,ran⟩ := bind_success _ _ _ _ _ ran
              obtain ⟨subject,entry,lookup,ran⟩ := bind_success _ _ _ _ _ ran
              obtain ⟨checked,exit,traversal,ran⟩ := bind_success _ _ _ _ _ ran
              obtain ⟨rfl,_⟩ := pure_success _ _ _ _ ran
              have subjectAt : selected.site.arms[index.val]? = some subject := by
                have read := (lift_success _ _ _ _ lookup).1
                cases found : selected.site.arms[index.val]? with
                | none => simp [found,readOption] at read
                | some entry =>
                  have same : (Except.ok entry : Except Error _) = .ok subject := by
                    simpa only [found,readOption] using read
                  exact congrArg some (Except.ok.inj same)
              exact ⟨_,rfl,subject,subjectAt,checked,⟨entry,exit,traversal⟩,rfl⟩)
          selected.arms initial final rfl folded (node,extra) ⟨g,i,_node⟩
        have original : MixedSelectionOrigin execution next node :=
          ⟨_,_,_,_,event,position,selected,childPath,parent,
            exactActions.weaken (fun _ _ ⟨slot,_,_,_,_,_,produced⟩ => ⟨slot,produced⟩)⟩
        obtain ⟨checked,pure,runtime⟩ := mixed_selection_step (inputs := RuntimeBranchCondition.rootEntries path) original
        exact ⟨entered.1.snoc (by simpa only [sameBindings] using aligned) checked rfl
          ⟨first.trans atStart.symm,last⟩ True.intro,
          entered.2.snocPure _ rfl (fun _ => pure _) (fun _ => runtime)⟩
    case basis =>
      obtain ⟨_,e,_source,ran⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,_,_action,returned⟩ := bind_success _ _ _ _ _ ran
      have same := (pure_success _ _ _ _ returned).1
      subst after
      refine ⟨entered.1.snoc ⟨?_,rfl⟩ True.intro rfl ⟨atStart.symm,rfl⟩ True.intro,
        entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
      change history = {history with bindings := frame.bindings}
      rw [sameBindings]
    case computed =>
      obtain ⟨structural,e,_dispatched,ran⟩ := bind_success _ _ _ _ _ h
      cases structural
      case true =>
        obtain ⟨_,_,_prepared,ran⟩ := bind_success _ _ _ _ _ ran
        obtain ⟨_,_,_action,returned⟩ := bind_success _ _ _ _ _ ran
        have same := (pure_success _ _ _ _ returned).1
        subst after
        refine ⟨entered.1.snoc ⟨?_,rfl⟩ True.intro rfl ⟨atStart.symm,rfl⟩ True.intro,
          entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
        change history = {history with bindings := frame.bindings}
        rw [sameBindings]
      case false =>
        obtain ⟨prepared,_,_source,ran⟩ := bind_success _ _ _ _ _ ran
        cases prepared
        all_goals
          obtain ⟨_,_,_action,returned⟩ := bind_success _ _ _ _ _ ran
          have same := (pure_success _ _ _ _ returned).1
          subst after
          refine ⟨entered.1.snoc ⟨?_,rfl⟩ True.intro rfl ⟨atStart.symm,rfl⟩ True.intro,
            entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
          change history = {history with bindings := frame.bindings}
          rw [sameBindings]
    case registerPrimitive =>
      obtain ⟨_,_,_action,returned⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ returned).1
      subst after
      refine ⟨entered.1.snoc ⟨?_,rfl⟩ True.intro rfl ⟨atStart.symm,rfl⟩ True.intro,
        entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
      change history = {history with bindings := frame.bindings}
      rw [sameBindings]
    case workspace =>
      obtain ⟨_,_,_source,ran⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,_,_literal,ran⟩ := bind_success _ _ _ _ _ ran
      obtain ⟨_,_,_map,returned⟩ := bind_success _ _ _ _ _ ran
      have same := (pure_success _ _ _ _ returned).1
      subst after
      refine ⟨entered.1.snoc ⟨?_,rfl⟩ True.intro rfl ⟨atStart.symm,rfl⟩ True.intro,
        entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
      change history = {history with bindings := frame.bindings}
      rw [sameBindings]
    case primitive =>
      split at h
      · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered.1
        refine ⟨chain.snoc ⟨?_,rfl⟩ True.intro rfl ⟨atStart.symm,rfl⟩ True.intro,
          entered.2.snocPure _ rfl (fun _ => True.intro) (fun _ => True.intro)⟩
        change history = {history with bindings := frame.bindings}
        rw [sameBindings]
      · split at h
        · cases mode
          case pureBody => cases h
          case runtimeBody =>
            obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
            have same := (pure_success _ _ _ _ returned).1
            subst after
            have chain := entered.1
            refine ⟨chain.snoc ⟨?_,rfl⟩ True.intro ⟨rfl,rfl⟩ ⟨atStart.symm,rfl⟩ True.intro, ?_⟩
            · change history = {history with bindings := frame.bindings}
              rw [sameBindings]
            · exact ⟨(by intro impossible; cases impossible),fun mixed => (entered.2.runtime mixed).snoc True.intro⟩
        · obtain ⟨performed,e,_performed,returned⟩ := bind_success _ _ _ _ _ h
          rcases performed with ⟨nextHistory,node⟩
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered.1
          obtain ⟨aligned,⟨first,last⟩,intrinsic⟩ := primitive_aligned interval history ⟨frame,sameBindings⟩ _ _ _ ⟨d,e,_performed⟩
          exact ⟨chain.snoc aligned (.of_operationOrigin (intrinsic_origin intrinsic)) rfl
            ⟨first.trans atStart.symm,last⟩ True.intro,
            entered.2.snocPure _ rfl (fun _ => .of_operationOrigin (execution := execution) (intrinsic_origin intrinsic))
              (fun _ => .of_operationOrigin (execution := execution) (intrinsic_origin intrinsic))⟩
    case conditional =>
      cases mode
      case pureBody => cases h
      case runtimeBody =>
        obtain ⟨_,e,_count,h⟩ := bind_success _ _ _ _ _ h
        have one : position.count = 1 := beq_iff_eq.mp (guard_success _ _ _ _ _count).1
        obtain ⟨selected,f,_selected,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨actual,g,_actual,h⟩ := bind_success _ _ _ _ _ h
        split at h
        · obtain ⟨left,i,_left,h⟩ := bind_success _ _ _ _ _ h
          obtain ⟨right,j,_right,h⟩ := bind_success _ _ _ _ _ h
          rcases left with ⟨thenResult,thenReceipts⟩
          rcases right with ⟨elseResult,elseReceipts⟩
          obtain ⟨action,k,_action,h⟩ := bind_success _ _ _ _ _ h
          obtain ⟨_,l,_charge,returned⟩ := bind_success _ _ _ _ _ h
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered.1
          refine ⟨chain.snoc ⟨?_,rfl⟩ (ConditionalRun.checked _left _right _action) ⟨rfl,rfl⟩
            ⟨atStart.symm,by change position.start+1 = position.start+position.count; rw [one]⟩ rfl,
            ⟨(by intro impossible; cases impossible),fun mixed => (entered.2.runtime mixed).snoc True.intro⟩⟩
          change history = {history with bindings := frame.bindings}
          rw [sameBindings]
        · cases h
    all_goals
      obtain ⟨_,e,_owners,failed⟩ := bind_success _ _ _ _ _ h
      cases failed
  have outer_preserves
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (entry : RuntimeSourceEvent.At (source.events.zip request.positions) event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary before)
      (read : (outerStep event position entry data before).run budget = (.ok after,remaining)) :
      ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary after := by
    cases event
    case staticConditional event children =>
      exact preserves_static_conditional execution.queries source block request.positions pureOnly
        event children position entry data advance step
        (ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary)
        (fun before after start work left h run => (advances before after start work left h run).1)
        steps_preserve (by intro state cursor h; rcases state with ⟨_,_,_,_,_,_,_,_,_⟩; exact h)
        before after budget remaining incoming read
    case staticFold event iterations =>
      exact preserves_static_fold execution.queries source block request.positions
        event iterations position entry data advance step
        (ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary)
        (fun before after start work left h run => (advances before after start work left h run).1)
        steps_preserve (by intro state cursor h; rcases state with ⟨_,_,_,_,_,_,_,_,_⟩; exact h)
        before after budget remaining incoming read
    all_goals
      exact steps_preserve _ position (.direct source request.positions entry)
        data before after budget remaining incoming read
  have trace := RuntimeBodyQueries.foldEvents_trace execution.queries source
    (source.events.zip request.positions) outerStep opening.events _ _ w₈ w₉ walked
  exact trace.invariant (ModeInvariant next mode (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary) ⟨Flow.nil next (RuntimeBranchCondition.rootEntries path) historyStart initialOrdinary,
    ⟨(fun _ => ⟨rfl,rfl,by intro step member; cases member⟩),by intro _ step member; cases member⟩⟩
    (fun event position entry data before after budget remaining incoming read =>
      outer_preserves event position entry data before after budget remaining incoming read)

theorem core_pure_preserves_ordinary (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (fuel : Nat) :
    PurePreservesOrdinary (runBlockCore artifact root execution fuel) := by
  induction fuel with
  | zero =>
    intro boundary rootOwner rootName owner name source path program request plan initial ordinary block result work left read
    cases read
  | succ fuel ih =>
    intro boundary rootOwner rootName owner name source path program request plan initial ordinary block result work left read
    obtain ⟨_,_,_,_,_,same⟩ := step_flow_mode artifact root execution (runBlockCore artifact root execution fuel)
      .pureBody boundary ih source path program request plan initial ordinary block result ⟨work,left,read⟩
    exact (same.pure rfl).ordinary

theorem step_flow (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) (outputBoundary : OutputBoundary) (pureNext : PurePreservesOrdinary next)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (initialOrdinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockStep artifact root execution next .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory initialOrdinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow next (RuntimeBranchCondition.rootEntries path) {initialHistory with bindings := initial.bindings} result.1.steps last
        initialOrdinary result.1.ordinary block.operations.length ∧
        Returned block source.outputRoles last result.1.history := by
  obtain ⟨initial,ordered,last,flow,returned,_⟩ := step_flow_mode artifact root execution next
    .runtimeBody outputBoundary pureNext source path program request sourcePlan initialHistory initialOrdinary
    block result checked
  exact ⟨initial,ordered,last,flow,returned⟩

/-- Instantiate the callback with the actual previous fuel level, retaining
computed child runs of the real original recursion. -/
theorem core_flow (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (fuel : Nat) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockCore artifact root execution (fuel+1) .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory ordinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow (runBlockCore artifact root execution fuel) (RuntimeBranchCondition.rootEntries path)
        {initialHistory with bindings := initial.bindings} result.1.steps last ordinary result.1.ordinary
        block.operations.length ∧
        Returned block source.outputRoles last result.1.history :=
  step_flow artifact root execution (runBlockCore artifact root execution fuel) outputBoundary
    (core_pure_preserves_ordinary artifact root execution fuel) source path program request sourcePlan initialHistory ordinary block result checked

/-- The actual runtime callback can return mixed named steps, including
inside a selected branch, and its literal list retains that mode. -/
theorem core_runtime_only (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (fuel : Nat) (boundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (plan : execution.queries.BodyData source request)
    (history : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockCore artifact root execution (fuel+1) .runtimeBody boundary source path program request
        plan history ordinary block) result) :
    RuntimeOnly result.1.steps := by
  obtain ⟨_,_,_,_,_,facts⟩ := step_flow_mode artifact root execution (runBlockCore artifact root execution fuel)
    .runtimeBody boundary (core_pure_preserves_ordinary artifact root execution fuel)
    source path program request plan history ordinary block result checked
  exact facts.runtime rfl

/-- The actual root keeps computed runs of all its named children on their
original callees and real native blocks, in addition to full source-state flow.
This does not supply source provenance for other step constructors. -/
theorem original_body {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    let source := SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let execution := ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let initialHistory := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles body.checked.native.block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow (runBlockCore artifact body.root execution 127)
        (RuntimeBranchCondition.rootEntries (.root prepared.source.body))
        {initialHistory with bindings := initial.bindings} body.checked.result.steps last
        body.checked.initial.ssa body.checked.result.ordinary body.checked.native.block.operations.length ∧
        Returned body.checked.native.block source.outputRoles last body.checked.result.history := by
  exact core_flow artifact body.root
    (.planned (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root))
    127 .rootOrder (.whole prepared.source.body) (.root prepared.source.body) body.root.program request
    prepared.planned.plan _ body.checked.initial.ssa body.checked.native.block
    (body.checked.result,body.checked.receipts) body.checked.traversed

/-- The original observing-capable root uses the runtime-body mode on
its actual checked source, block and staged request. -/
theorem original_body_runtime_only {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    RuntimeOnly body.checked.result.steps :=
  core_runtime_only artifact body.root
    (.planned (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root))
    127 .rootOrder (.whole prepared.source.body) (.root prepared.source.body) body.root.program request
    prepared.planned.plan _ body.checked.initial.ssa body.checked.native.block
    (body.checked.result,body.checked.receipts) body.checked.traversed

/-- The actual provider receipt opens the same pure root walk. Its recursively
checked named nodes retain the original child callbacks. -/
theorem original_pure_body {artifact root owner name signature program request bindings}
    {body : @SourceTypes.SourceRuntimeTrace.Body artifact.sources owner name signature}
    (checked : @RuntimePureBody.Checked artifact root owner name signature body program request bindings) :
    let source := SourceTypes.SourceRuntimeScope.Subject.whole body
    let initialHistory : RuntimeStructuralAction.SourceState :=
      ⟨bindings,body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners,
        body.checked.summary.nextOwner⟩
    let execution : ExecutionMode artifact root := .fresh .strict
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles checked.result.prepared.block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles checked.result.prepared.block.entry initialHistory.bindings)
        initial ∧
      ∃ last, Flow (runBlockCore artifact root execution 127) (RuntimeBranchCondition.rootEntries (.root body))
        {initialHistory with bindings := initial.bindings} checked.result.steps last {} checked.result.ordinary
        checked.result.prepared.block.operations.length ∧
        Returned checked.result.prepared.block source.outputRoles last checked.result.history ∧
        PureFlowFacts (runBlockCore artifact root execution 127)
          (RuntimeBranchCondition.rootEntries (.root body)) {} checked.result.ordinary
          checked.result.actions checked.result.steps := by
  obtain ⟨native,result,work,left,read⟩ := checked
  unfold RuntimePureBody.run at read
  obtain ⟨walk,afterBlock,blockRead,returned⟩ := bind_success _ _ _ _ _ read
  have resultData := (pure_success _ _ _ _ returned).1
  subst result
  unfold RuntimePureBody.runBlock RuntimePureBody.runBlockUsing at blockRead
  obtain ⟨actual,afterCore,coreRead,blockReturned⟩ := bind_success _ _ _ _ _ blockRead
  have walkData := (pure_success _ _ _ _ blockReturned).1
  subst walk
  obtain ⟨initial,ordered,last,flow,final,same⟩ := step_flow_mode artifact root (.fresh .strict)
    (runBlockCore artifact root (.fresh .strict) 127) .pureBody .rootOrder
    (core_pure_preserves_ordinary artifact root (.fresh .strict) 127)
    (.whole body) (.root body) program request () _ {} native.block actual ⟨work,afterCore,coreRead⟩
  exact ⟨initial,ordered,last,flow,final,same.pure rfl⟩

#print axioms PureFlowFacts.allPure
#print axioms original_pure_body
#print axioms core_pure_preserves_ordinary
#print axioms step_flow
#print axioms core_flow
#print axioms original_body
#print axioms original_body_runtime_only
end Qleisli.RuntimeNamedChildRuns
