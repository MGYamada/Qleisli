import QleisliKernel.Qirf.RuntimePureBody

/-! Structural composition of the actual retained pure source intervals.
No joined code matrix is built. Literal partitions retain the original Raw
trace, caller frame and final owner order; sector lifting reuses the existing
universal restriction theorem. The code-lifting algebra below preserves errors
and arbitrary reference-indexed amplitude families without a separability
premise. Instantiating that algebra with every Raw localization and complete
typed-forest code is still required before full root semantic admission.
This preparation issues no handle and proves no general AST/runtime theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePureComposition
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimePureBody RuntimeOwnerMap

structure Local {dependencies program} (block : RuntimeInterval.Block dependencies program) where
  arity : Nat
  start : Nat
  count : Nat
  inputs : List Nat
  outputs : List Nat
  roles : List Owner
  frame : RuntimePureInterval.Checked block arity start count inputs outputs roles

def region {dependencies program block} : Node dependencies program block → Local block
  | .primitive (start := start) (count := count) (input := input) (output := output)
      (role := role) action => ⟨1,start,count,[input],[output],[role],action.interval⟩
  | .named (arity := arity) (start := start) (count := count) (inputs := inputs)
      (outputs := outputs) (roles := roles) frame .. => ⟨arity,start,count,inputs,outputs,roles,frame⟩
  | .operation (arity := arity) (start := start) (count := count) (inputs := inputs)
      (outputs := outputs) (roles := roles) frame .. => ⟨arity,start,count,inputs,outputs,roles,frame⟩
  | .selection (start := start) (count := count) (inputs := inputs)
      (outputs := outputs) (roles := roles) frame .. => ⟨2,start,count,inputs,outputs,roles,frame⟩

def operations {dependencies program block} (node : Node dependencies program block) : List Semantics.Raw.Op :=
  (region node).frame.operations

/-- Every caller spectator, including distinct zero-width owners, is retained
by this same interval. No tensor-product state assumption occurs here. -/
theorem spectators {dependencies program block} (node : Node dependencies program block) :
    PureInterval.spectators (region node).frame.interval.before (region node).inputs =
      PureInterval.spectators (region node).frame.interval.after (region node).outputs :=
  (region node).frame.spectators

inductive Covers {dependencies program} {block : RuntimeInterval.Block dependencies program} :
    Nat → List (Node dependencies program block) → Nat → Prop where
  | nil (cursor : Nat) : Covers cursor [] cursor
  | cons {cursor finish node nodes} (atCursor : (region node).start = cursor)
      (rest : Covers (cursor+(region node).count) nodes finish) : Covers cursor (node::nodes) finish

theorem Covers.literalRemaining {dependencies program block cursor nodes finish}
    (cover : @Covers dependencies program block cursor nodes finish) :
    (nodes.flatMap operations).map Semantics.Observation.Op.pure ++ block.operations.drop finish =
      block.operations.drop cursor := by
  induction cover with
  | nil cursor => rfl
  | @cons cursor finish node nodes atCursor rest ih =>
    simp only [List.flatMap_cons,List.map_append,List.append_assoc,ih]
    change (region node).frame.operations.map Semantics.Observation.Op.pure ++
      block.operations.drop (cursor+(region node).count) = block.operations.drop cursor
    rw [← (region node).frame.literal,atCursor]
    simpa only [List.drop_drop] using List.take_append_drop (region node).count (block.operations.drop cursor)

theorem Covers.literal {dependencies program block nodes}
    (cover : @Covers dependencies program block 0 nodes block.operations.length) :
    (nodes.flatMap operations).map Semantics.Observation.Op.pure = block.operations := by
  simpa only [List.drop_length,List.append_nil,List.drop_zero] using cover.literalRemaining

private def readCover {dependencies program block} :
    (nodes : List (Node dependencies program block)) → (cursor : Nat) →
    WorkM (PLift (Covers cursor nodes block.operations.length))
  | [],cursor =>
    if finished : cursor = block.operations.length then
      pure ⟨by simpa only [finished] using (Covers.nil (block := block) cursor)⟩
    else throw .request
  | node::nodes,cursor => do
    if atCursor : (region node).start = cursor then
      let rest ← readCover nodes (cursor+(region node).count)
      return ⟨.cons atCursor rest.down⟩
    else throw .request

structure Partition {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (nodes : List (Node dependencies program block)) : Type where
  cover : Covers 0 nodes block.operations.length
  literal : (nodes.flatMap operations).map Semantics.Observation.Op.pure = block.operations

/-- Only actual literal operations are compared. This check does not enumerate
the caller's quantum states or construct its combined owner code. -/
def readPartition {dependencies program block} (nodes : List (Node dependencies program block)) :
    WorkM (Partition block nodes) := do
  exactWork (Exact.charge (32*(nodes.length+block.operations.length+1)+
    (nodes.map fun node => Raw.rawFields
      (RuntimePureInterval.fragment (region node).frame.selected (operations node) (region node).outputs)).sum))
  let cover ← readCover nodes 0
  return ⟨cover.down,cover.down.literal⟩

/-- Grouping the same operations into source intervals preserves the complete
independent trace, its ordered frame and the first missing-operand failure. -/
theorem executeChunks (chunks : List (List Semantics.Raw.Op)) (initial : Semantics.RawTrace.Prepared) :
    chunks.flatten.foldlM Semantics.RawTrace.advance initial =
      chunks.foldlM (fun state chunk => chunk.foldlM Semantics.RawTrace.advance state) initial := by
  induction chunks generalizing initial with
  | nil => rfl
  | cons chunk chunks ih =>
    rw [List.flatten_cons,List.foldlM_append,List.foldlM_cons]
    cases executed : chunk.foldlM Semantics.RawTrace.advance initial with
    | none => rfl
    | some next => simpa only [bind,Option.bind] using ih next

structure Prepared (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (request : RuntimeContextRequest.Context) (initial : Map)
    (checked : RuntimePureBody.Checked artifact root body root.program request initial) where
  partition : Partition checked.result.prepared.block checked.result.actions
  raw : Semantics.Raw.Program
  original : Sector.project root.program = some raw
  operations : raw.operations = checked.result.actions.flatMap RuntimePureComposition.operations
  sourceOrder : (body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners).Perm
    (SourceRuntimeValues.valueOwners body.checked.summary.value)
  finalOwners : RuntimeOwnerMap.Checked (SourceRuntimeValues.valueOwners body.checked.summary.value) root.checked.state
  returned : List Semantics.Raw.Port
  returnRead : RuntimeInterval.Computed
    (RuntimePureBody.rolePorts (SourceRuntimeValues.valueOwners body.checked.summary.value)
      checked.result.bindings) returned
  outputOrder : returned.map (·.token) = root.program.outputs

/-- The final order comes from the original body and its computed role map,
including zero-width identities. The same final root supplies every live port.
Observing/general contexts retain their separate instrument continuation. -/
def prepare (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (request : RuntimeContextRequest.Context) (initial : Map)
    (checked : RuntimePureBody.Checked artifact root body root.program request initial) :
    WorkM (Prepared artifact root body request initial checked) := do
  let partition ← readPartition checked.result.actions
  let inputRoles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let outputRoles := SourceRuntimeValues.valueOwners body.checked.summary.value
  exactWork (Exact.charge (32*(root.program.operations.length+root.program.inputs.length+
    root.program.outputs.length+checked.result.bindings.length+1)+
    16*(Raw.OwnerFlow.fields inputRoles+Raw.OwnerFlow.fields outputRoles+1)*
      (inputRoles.length+outputRoles.length+1)))
  match original : Sector.project root.program with
  | none => throw .request
  | some raw =>
    if operations : raw.operations = checked.result.actions.flatMap RuntimePureComposition.operations then
      if sourceOrder : (body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners).Perm
          (SourceRuntimeValues.valueOwners body.checked.summary.value) then
        let finalOwners ← RuntimeOwnerMap.check (SourceRuntimeValues.valueOwners body.checked.summary.value)
          root.checked.state checked.result.bindings
        let returned ← NaturalAffine.witness (RuntimePureBody.rolePorts
          (SourceRuntimeValues.valueOwners body.checked.summary.value) checked.result.bindings)
        if outputOrder : returned.val.map (·.token) = root.program.outputs then
          return ⟨partition,raw,original,operations,sourceOrder,finalOwners,returned.val,
            by with_reducible exact returned.property,outputOrder⟩
        else throw .request
      else throw .request
    else throw .request

theorem Prepared.originalRoot {artifact root owner name signature body request initial checked}
    (prepared : @Prepared artifact root owner name signature body request initial checked) :
    root.program = Semantics.Ownership.pureProgram prepared.raw :=
  (Sector.project_bound _ _ prepared.original).1

theorem Prepared.orderedExecution {artifact root owner name signature body request initial checked}
    (prepared : @Prepared artifact root owner name signature body request initial checked)
    (state : Semantics.RawTrace.Prepared) :
    prepared.raw.operations.foldlM Semantics.RawTrace.advance state =
      (checked.result.actions.map RuntimePureComposition.operations).foldlM
        (fun state chunk => chunk.foldlM Semantics.RawTrace.advance state) state := by
  rw [prepared.operations]
  exact executeChunks (checked.result.actions.map RuntimePureComposition.operations) state

theorem Prepared.orderedRootTrace {artifact root owner name signature body request initial checked}
    (prepared : @Prepared artifact root owner name signature body request initial checked) :
    Semantics.RawTrace.run prepared.raw = (do
      let state := Semantics.RawTrace.initial prepared.raw.inputs
      let final ← (checked.result.actions.map RuntimePureComposition.operations).foldlM
        (fun state chunk => chunk.foldlM Semantics.RawTrace.advance state)
        ⟨state,[],state.frame.length⟩
      pure (Semantics.RawTrace.finish prepared.raw final)) := by
  simp only [Semantics.RawTrace.run]
  rw [prepared.orderedExecution]

/-- Existing sector evidence supplies all-vector lifting of the actual full
step list, independently of the target code and source arm checks. -/
theorem sectorLifting {dependencies selector target program retained}
    (read : RuntimeInterval.Computed (Raw.Sector.read dependencies selector target program) retained) :
    QleisliKernel.Exact.ListRel
      (FiniteRestriction.SectorEvaluationBinding dependencies (Semantics.Finite.width selector) target retained.steps)
      (List.range (2^Semantics.Finite.width selector)) retained.sectors := by
  obtain ⟨before,after,ran⟩ := read
  exact (Raw.Sector.read_bound _ _ _ _ _ _ _ ran).2.2.2.2.2.2.2

/-- This equation permits unrelated vectors at every reference coordinate.
It assumes no factorization of a joint source/reference state. -/
theorem sectorReferences {Reference : Type} (dependencies : List Semantics.Finite.Dependency)
    (steps restricted : List Semantics.Finite.Step) (selector label : Nat)
    (bound : label < 2^selector)
    (restrictedRead : FiniteRestriction.restrictSteps selector label steps = some restricted)
    (values : Reference → List Semantics.Exact.Scalar) :
    (fun reference => steps.foldlM (fun state step => applyStep dependencies step state)
      (FiniteRestriction.liftVector selector label (values reference))) =
    (fun reference => (restricted.foldlM (fun state step => applyStep dependencies step state)
      (values reference)).map (FiniteRestriction.liftVector selector label)) := by
  funext reference
  exact FiniteRestriction.foldSteps_lift dependencies steps selector label (values reference) restricted bound restrictedRead

/-- Error-preserving code/action commutation. These are independently supplied
mathematical functions, not a producer success receipt or a native acceptance
condition. Concrete Raw localization and forest-code proofs must establish it. -/
def Commutes {Logical Physical : Type} (input output : Logical → Physical)
    (actual : Physical → Except Finite.Error Physical) (required : Logical → Except Finite.Error Logical) : Prop :=
  ∀ value, actual (input value) = (required value).map output

theorem commutes_compose {Logical Physical : Type} {input middle output : Logical → Physical}
    {first second : Physical → Except Finite.Error Physical}
    {requiredFirst requiredSecond : Logical → Except Finite.Error Logical}
    (left : Commutes input middle first requiredFirst)
    (right : Commutes middle output second requiredSecond) :
    Commutes input output (fun value => (first value).bind second)
      (fun value => (requiredFirst value).bind requiredSecond) := by
  intro value
  change (first (input value)).bind second = ((requiredFirst value).bind requiredSecond).map output
  rw [left value]
  cases ran : requiredFirst value with
  | error error => rfl
  | ok result => simpa only [Except.map,bind,Except.bind] using right result

theorem commutes_references {Reference Logical Physical : Type} {input output : Logical → Physical}
    {actual : Physical → Except Finite.Error Physical} {required : Logical → Except Finite.Error Logical}
    (law : Commutes input output actual required) (values : Reference → Logical) :
    (fun reference => actual (input (values reference))) =
      (fun reference => (required (values reference)).map output) := by
  funext reference
  exact law (values reference)

/-- Different boundary encodings remain explicit at every source interval.
The final encoding may include the original source's owner permutation. -/
inductive Chain (Logical Physical : Type) :
    (Logical → Physical) → List (Physical → Except Finite.Error Physical) →
      List (Logical → Except Finite.Error Logical) → (Logical → Physical) → Prop where
  | nil (code : Logical → Physical) : Chain Logical Physical code [] [] code
  | cons {input middle output first required actuals requirements}
      (action : Commutes input middle first required)
      (rest : Chain Logical Physical middle actuals requirements output) :
      Chain Logical Physical input (first::actuals) (required::requirements) output

def runActions {State : Type} (actions : List (State → Except Finite.Error State)) (initial : State) :
    Except Finite.Error State := actions.foldlM (fun value action => action value) initial

theorem Chain.commutes {Logical Physical input output actuals requirements}
    (chain : Chain Logical Physical input actuals requirements output) :
    Commutes input output (runActions actuals) (runActions requirements) := by
  induction chain with
  | nil code => intro value; rfl
  | cons action rest ih =>
    simpa only [runActions,List.foldlM_cons] using commutes_compose action ih

theorem Chain.references {Reference Logical Physical input output actuals requirements}
    (chain : Chain Logical Physical input actuals requirements output) (values : Reference → Logical) :
    (fun reference => runActions actuals (input (values reference))) =
      (fun reference => (runActions requirements (values reference)).map output) := by
  funext reference
  exact chain.commutes (values reference)

end QleisliKernel.Qirf.RuntimePureComposition
