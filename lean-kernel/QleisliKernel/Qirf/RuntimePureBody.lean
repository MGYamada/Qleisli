import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimePrimitiveSource
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.RuntimeStaticPrimitive
import QleisliKernel.Qirf.RuntimeNamedBoundary
import QleisliKernel.Qirf.RuntimeCallScope
import QleisliKernel.Qirf.RuntimeOrdinaryInputs
import QleisliKernel.Qirf.RuntimeBranchAction
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.RuntimeContextRequest
import QleisliKernel.Qirf.RuntimeOperationPaths
import QleisliKernel.Qirf.RuntimeGraphOperation
import QleisliKernel.Qirf.RuntimeBodyQueries
import QleisliKernel.Qirf.RuntimeRegisterAction
import QleisliKernel.Qirf.StructuralComputedRaw
import QleisliKernel.Qirf.RuntimeTransformAction
import QleisliKernel.Qirf.RuntimeRectangularOperation
import QleisliKernel.Qirf.OperationIRMeaning
import QleisliKernel.Qirf.SectorArm
import QleisliKernel.SourceTypes.QuantumArms

/-! One original runtime-body loop with literal caller frames.
Source parameter/result trees and owner permutations stay intact. A child uses
only its actual literal parent interval; its canonical role namespace is local,
while the parent interval separately retains every caller spectator. Pure
islands and actual ordinary/observing steps remain distinct checked data. This
stage refuses forms whose continuations have not yet been connected; complete
instrument/code and ordinary history/storage obligations remain open. It issues
no handle and is not the complete v5 runtime acceptance gate.
Fresh and staged runtime calls share this native handler. Arm graph reads now
precede all sector comparisons, and branch source acquisition precedes the
native branch read; work and first-failure observations can change. Planned
pure static continuations refuse; existing pure callers retain fresh queries.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePureBody
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues RuntimeOwnerMap
abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position

inductive OutputBoundary where
  | rootOrder
  | localScope
  | frame

inductive Mode where
  | pureBody
  | runtimeBody

def rolePorts (roles : List Owner) (bindings : Map) : WorkM (List Semantics.Raw.Port) :=
  RuntimePrimitiveSource.rolePorts roles bindings

/-- The native reads that supplied both widths and the exact selector label
order. A caller cannot infer all-arm coverage from the list length alone. -/
structure SelectionLayouts (selector target : Semantics.FiniteCarrier.Basis)
    (selectorBits targetBits : Nat) (labels : List Nat) : Prop where
  selectorRead : RuntimeInterval.Computed (FiniteCarrier.read selector) ⟨selectorBits,labels⟩
  targetRead : ∃ targetLabels, RuntimeInterval.Computed (FiniteCarrier.read target) ⟨targetBits,targetLabels⟩

/-- On two original Bit ports the same source layout and successful matrix
checks bind the logical results at 0 and 1, in canonical selector order. -/
theorem SelectionLayouts.bit_bindings {selector target selectorBits targetBits labels}
    (layouts : SelectionLayouts selector target selectorBits targetBits labels)
    (selectorBasis : selector = [.bit]) (targetBasis : target = [.bit])
    {inputCode outputCode sectors expected logical}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode sectors labels expected) logical) :
    selectorBits = 1 ∧ targetBits = 1 ∧ labels = [0,1] ∧ ∃ zero one,
      expected = [zero,one] ∧ logical = [zero,one] ∧
      NominalSector.LogicalBinding inputCode outputCode sectors (0,zero) zero ∧
      NominalSector.LogicalBinding inputCode outputCode sectors (1,one) one := by
  obtain ⟨a,b,sel⟩ := layouts.selectorRead
  obtain ⟨targetLabels,c,d,tgt⟩ := layouts.targetRead
  have selectorLayout := FiniteCarrier.read_reference _ _ _ _ sel
  have targetLayout := FiniteCarrier.read_reference _ _ _ _ tgt
  rw [selectorBasis] at selectorLayout
  rw [targetBasis] at targetLayout
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some ⟨selectorBits,labels⟩ at selectorLayout
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some ⟨targetBits,targetLabels⟩ at targetLayout
  have labelsEq := congrArg Semantics.FiniteCarrier.Layout.labels (Option.some.inj selectorLayout).symm
  have sBits := congrArg Semantics.FiniteCarrier.Layout.bits (Option.some.inj selectorLayout).symm
  have tBits := congrArg Semantics.FiniteCarrier.Layout.bits (Option.some.inj targetLayout).symm
  change labels = [0,1] at labelsEq
  refine ⟨sBits,tBits,labelsEq,?_⟩
  obtain ⟨work,left,ran⟩ := equations
  obtain ⟨count,each⟩ := NominalSector.checkLogicals_bound _ _ _ _ _ _ work left ran
  rw [labelsEq] at count each
  have two (xs : List Semantics.Exact.Matrix) (length : xs.length = 2) : ∃ a b,xs = [a,b] :=
    ⟨_,_,List.eq_getElem_of_length_eq_two xs length⟩
  obtain ⟨zero,one,rfl⟩ := two expected count
  have actualCount := QleisliKernel.Exact.listRel_length _ _ _ each
  obtain ⟨first,second,rfl⟩ := two logical actualCount
  have boundZero : NominalSector.LogicalBinding inputCode outputCode sectors (0,zero) first := each.1
  have boundOne : NominalSector.LogicalBinding inputCode outputCode sectors (1,one) second := each.2.1
  have zeroEq : first = zero := boundZero.1
  have oneEq : second = one := boundOne.1
  subst first second
  exact ⟨zero,one,rfl,rfl,boundZero,boundOne⟩

/-- The sector equations use the encodings read from the actual target owner
at entry and return. Matching dimensions alone would also admit zero codes. -/
structure SelectionCodes {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (inputs outputs : List Nat) (selector target : Owner) (inputCode outputCode : Semantics.Exact.Matrix) where
  owners : RuntimeOwnerTransition.Selection interval inputs outputs [selector,target]
  inputRead : RuntimeInterval.Computed
    (Carrier.ownerCode [⟨owners.selected.second.port,target.basis⟩]) inputCode
  outputRead : RuntimeInterval.Computed
    (Carrier.ownerCode [⟨owners.returned.second.port,target.basis⟩]) outputCode

mutual
inductive Node (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | primitive {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count input output role kind}
      (action : RuntimePrimitiveAction.Checked block start count input output role kind)
      (source : RuntimePrimitiveSource.Checked action) : Node dependencies program block
  | structural {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller event before}
      (action : RuntimeStructuralAction.Checked (sources := sources) (caller := caller) block start count event before) :
      Node dependencies program block
  | register {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller} {event : SourceRuntimeContext.RegisterEvent sources caller} {before}
      (location : RuntimeSourceEvent.Location (.registerPrimitive event) start count)
      (action : RuntimeRegisterAction.Checked block start count event before) : Node dependencies program block
  | basis {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller} {event : SourceRuntimeContext.BasisEvent sources caller} {before}
      (interval : RuntimeInterval.Checked block start count)
      (location : RuntimeSourceEvent.Location (.basis event) start count)
      (source : RuntimeBasisAction.Source event)
      (action : RuntimeBasisAction.Checked event interval before) : Node dependencies program block
  | computed {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
      {children : List (SourceRuntimeContext.Event sources caller)} {before}
      (interval : RuntimeInterval.Checked block start count)
      (location : RuntimeSourceEvent.Location (.computed event children) start count)
      (prepared : RuntimeComputedUse.Prepared event)
      (action : RuntimeComputedUse.Checked prepared interval before) : Node dependencies program block
  | certifiedComputed {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
      {children : List (SourceRuntimeContext.Event sources caller)} {before}
      (interval : RuntimeInterval.Checked block start count)
      (location : RuntimeSourceEvent.Location (.computed event children) start count)
      (prepared : RuntimeCertifiedComputed.Prepared event)
      (action : RuntimeCertifiedComputed.Checked prepared interval before) : Node dependencies program block
  | structuralComputed {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
      {children : List (SourceRuntimeContext.Event sources caller)} {before}
      (interval : RuntimeInterval.Checked block start count)
      (location : RuntimeSourceEvent.Location (.computed event children) start count)
      (action : StructuralComputedRaw.IntervalChecked event interval before) : Node dependencies program block
  | workspace {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller} {event : SourceRuntimeContext.WorkspaceEvent sources caller}
      {children : List (SourceRuntimeContext.Event sources caller)} {before}
      (interval : RuntimeInterval.Checked block start count)
      (location : RuntimeSourceEvent.Location (.workspace event children) start count)
      (prepared : RuntimeWorkspace.Original event children)
      (action : RuntimeWorkspace.Literal prepared interval before)
      (map : RuntimeWorkspace.CallerMap action) : Node dependencies program block
  | named {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count inputs} {sources : Sources} {caller : String} {before childHistory childRetired}
      (event : SourceRuntimeContext.NamedEvent sources caller)
      (frame : RuntimeCallInterval.Checked block start count inputs)
      (source : SourceRuntimeTrace.Body event.target.signature)
      (sourceRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) source)
      (boundary : RuntimeNamedBoundary.Checked frame.interval inputs event before childHistory childRetired source.checked.summary.value)
      (children : Nodes dependencies frame.program frame.prepared.block) : Node dependencies program block
  | operation {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {arity start count inputs outputs roles}
      (frame : RuntimePureInterval.Checked block arity start count inputs outputs roles)
      (inputCode outputCode physical expected : Semantics.Exact.Matrix)
      (inputRead : RuntimeInterval.Computed
        (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) inputCode)
      (outputRead : RuntimeInterval.Computed
        (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) outputCode)
      (physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
      (action : CodeSpace.Map inputCode outputCode physical) (equation : action.logical = expected) : Node dependencies program block
  | rectangularOperation {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {sources caller start count before expected} {event : SourceOperationApplication.Event sources caller}
      {interval : RuntimeInterval.Checked block start count}
      (checked : RuntimeRectangularOperation.Checked event interval before expected) : Node dependencies program block
  | transform {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {artifact : Artifact} {caller : String} {event : SourceRuntimeContext.TransformEvent artifact.sources caller}
      {position : Position} {request : Context} {before : RuntimeStructuralAction.SourceState}
      {interval : RuntimeInterval.Checked block position.start position.count}
      (source : RuntimeTransformRequest.Checked event position request)
      (original : RuntimeInterval.Computed (RuntimeTransformRequest.read event position request) source)
      (forward : RuntimeTransformAction.Forward artifact dependencies source)
      (forwardReturned : Map) (logical : RuntimeTransformAction.ForwardMap forward forwardReturned)
      (owners : RuntimeTransformOwners.Checked interval event before)
      (action : RuntimeTransformAction.Checked owners logical.code.logical)
      (children : Nodes dependencies forward.program forward.prepared.block) : Node dependencies program block
  | selection {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count inputs outputs} {selector target : Owner}
      (frame : RuntimePureInterval.Checked block 2 start count inputs outputs [selector,target])
      (selectorBits targetBits : Nat) (restriction : Raw.Sector.Retained)
      (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) restriction)
      (inputCode outputCode : Semantics.Exact.Matrix) (labels : List Nat)
      (expected logical : List Semantics.Exact.Matrix)
      (equations : RuntimeInterval.Computed
        (NominalSector.checkLogicals inputCode outputCode restriction.sectors labels expected) logical)
      (codes : SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
      (layouts : SelectionLayouts selector.basis target.basis selectorBits targetBits labels) : Node dependencies program block

inductive Nodes (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | nil {program block} : Nodes dependencies program block
  | cons {program block} (first : Node dependencies program block)
      (rest : Nodes dependencies program block) : Nodes dependencies program block
end

/-- Check the literal caller interval on the original owners in their source
order. The operation graph supplies its independently checked expected action. -/
def operationNode {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (position : Position) (roles : List Owner) (before after : Map)
    (expected : Semantics.Exact.Matrix) : WorkM (Node dependencies program block) := do
  let inputs ← rolePorts roles before
  let outputs ← rolePorts roles after
  let frame ← RuntimePureInterval.check block inputs.length position.start position.count
    (inputs.map (·.token)) (outputs.map (·.token)) roles
  let inputCode ← NaturalAffine.witness
    (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩))
  let outputCode ← NaturalAffine.witness
    (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩))
  let physical ← NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragment frame.selected frame.operations (outputs.map (·.token))))
  let action ← CodeSpace.readMap inputCode.val outputCode.val physical.val
  exactWork (Exact.charge (action.logical.entries.length+expected.entries.length+1))
  if equation : action.logical = expected then
    return .operation frame inputCode.val outputCode.val physical.val expected
      (by with_reducible exact inputCode.property) (by with_reducible exact outputCode.property)
      (by with_reducible exact physical.property) action equation
  else throw .equation

/-- One original owner-preserving primitive in its actual interval. The
enclosing traversal supplies the current complete history and checked native
frame. Only the existing h/global-phase/closed-phase cases are handled here;
this helper does not select source events or provide a whole-body equation. -/
def primitiveAt {sources caller dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (history : RuntimeStructuralAction.SourceState)
    (boundFrame : {frame : RuntimeOwnerMap.Checked (history.bindings.map (·.owner)) interval.before //
      frame.bindings = history.bindings})
    (event : SourceRuntimeContext.Event sources caller)
    (location : Option (RuntimeSourceEvent.Location event start count) := none) :
    WorkM (RuntimeStructuralAction.SourceState × Node dependencies program block) := do
  let callerFrame := boundFrame.val
  let owners ← NaturalAffine.witness (RuntimeOwnerTransition.read interval callerFrame.bindings)
  match event,location with
  | .primitive event,location =>
    let preserving ← NaturalAffine.witness (guard
      (event.allocated.isEmpty && event.consumed.isEmpty && event.nextOrdinal == history.nextOrdinal) .request)
    have preserved : (event.allocated.isEmpty && event.consumed.isEmpty &&
        event.nextOrdinal == history.nextOrdinal) = true := by
      obtain ⟨work,left,read⟩ := preserving.property
      have unit : preserving.val = () := by cases preserving.val; rfl
      rw [unit] at read
      exact (guard_success _ _ _ _ read).1
    match argument : event.arguments with
    | [[.owner operand]] =>
      let ⟨kind,selected⟩ ← RuntimePrimitiveSource.readKind event.kind
      let input ← RuntimePrimitiveSource.readPort operand callerFrame.bindings
      let output ← RuntimePrimitiveSource.readPort operand owners.val.after.bindings
      let action ← NaturalAffine.witness
        (RuntimePrimitiveAction.check block start count input.port.token output.port.token operand kind)
      -- Reserve the constant new source/lookup receipt cells, not another read.
      exactWork (Exact.charge 32)
      let source : RuntimePrimitiveSource.Checked action.val :=
        ⟨sources,caller,.primitive event,location,history,interval,callerFrame,boundFrame.property,
          .primitive event history.nextOrdinal operand kind preserved argument selected,owners.val,
          by with_reducible exact owners.property,input,rfl,output,rfl,by with_reducible exact action.property⟩
      return (source.after,.primitive action.val source)
    | _ => throw .request
  | .phase event,location =>
    let input ← RuntimePrimitiveSource.readPort event.operand callerFrame.bindings
    let output ← RuntimePrimitiveSource.readPort event.operand owners.val.after.bindings
    let action ← NaturalAffine.witness
      (RuntimePrimitiveAction.check block start count input.port.token output.port.token event.operand
        (.phase event.application.coefficient.exponent))
    -- Reserve the constant new source/lookup receipt cells, not another read.
    exactWork (Exact.charge 32)
    let source : RuntimePrimitiveSource.Checked action.val :=
      ⟨sources,caller,.phase event,location,history,interval,callerFrame,boundFrame.property,.phase event history.nextOrdinal,owners.val,
        by with_reducible exact owners.property,input,rfl,output,rfl,by with_reducible exact action.property⟩
    return (source.after,.primitive action.val source)
  | _,_ => throw .request

private def prepareSelectionCodes {α : Type} (input output : Semantics.Exact.Matrix)
    (arms : List α) : WorkM (SectorArm.Codes input output) :=
  match arms with
  | _::_::_ => SectorArm.prepareCodes input output
  | _ => pure {}

/-- Verify every literal arm and the complete selector partition with the
actual ordered source owners and their encodings. The enclosing traversal
supplies a source realization at each index of this exact arm table. -/
def selectionNode {α : Type} (artifact : Artifact) {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (callerFrame : RuntimeOwnerMap.Checked roles interval.before)
    (owners : RuntimeOwnerTransition.Checked interval callerFrame.bindings)
    (selector target : Owner) {moduleName name offset}
    (table : QuantumArms.Table artifact.sources moduleName name offset selector.basis target.basis)
    (site : RuntimeContextRequest.Site) (initial : α)
    (realize : Fin table.arms.length → QuantumArms.BoundArm artifact.sources moduleName selector.basis target.basis →
      α → WorkM (Semantics.Exact.Matrix × α)) : WorkM (Node dependencies program block × α) := do
  guard (table.arms.length == site.arms.length) .request
  let entry ← RuntimeOwnerTransition.readPair [selector,target] callerFrame.bindings
  let exit ← RuntimeOwnerTransition.readPair [selector,target] owners.after.bindings
  let si := entry.first.port
  let ti := entry.second.port
  let so := exit.first.port
  let to := exit.second.port
  let expectedInterface : Semantics.CarrierInterface.Interface :=
    ⟨[⟨si,selector.basis⟩,⟨ti,target.basis⟩],[⟨so,selector.basis⟩,⟨to,target.basis⟩],.unitary⟩
  guard (site.attached == expectedInterface && site.required == expectedInterface) .request
  let inputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨ti,target.basis⟩])
  let outputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨to,target.basis⟩])
  let selectorRead ← NaturalAffine.witness (FiniteCarrier.read selector.basis)
  let targetRead ← NaturalAffine.witness (FiniteCarrier.read target.basis)
  let selectorLayout := selectorRead.val
  let targetLayout := targetRead.val
  let preparedCodes ← prepareSelectionCodes inputCode.val outputCode.val table.arms
  let arms := table.arms.mapFinIdx fun index arm valid => ((⟨index,valid⟩ : Fin table.arms.length),arm)
  let (meanings,remaining) ← (arms.zip site.arms).foldlM
    (fun (meanings,current) ((index,arm),subject) => do
      let (logical,next) ← realize index arm current
      let reference : SectorArm.Reference := ⟨arm.label.ordinal,target.basis,.unitary,
        subject.implementation,subject.controlled⟩
      let actual ← SectorArm.readUsing artifact dependencies target.basis targetLayout.bits
        inputCode.val outputCode.val preparedCodes reference
      exactWork (Exact.charge (logical.entries.length+actual.logical.entries.length+1))
      guard (actual.logical == logical) .equation
      pure (meanings ++ [(arm.label.ordinal,logical)],next)) ([],initial)
  let expected ← (List.range selectorLayout.labels.length).mapM fun ordinal => do
    let some (_,logical) := meanings.find? (·.1 == ordinal) | throw .request
    pure logical
  let attached ← RuntimePureInterval.checkAt interval 2 [si.token,ti.token] [so.token,to.token] [selector,target]
  let frame := attached.val
  let sourcePorts : RuntimeOwnerTransition.Selection interval [si.token,ti.token] [so.token,to.token] [selector,target] :=
    ⟨_,callerFrame,owners,entry,exit,rfl,rfl⟩
  let codes : SelectionCodes interval [si.token,ti.token] [so.token,to.token] selector target inputCode.val outputCode.val :=
    ⟨sourcePorts,by with_reducible exact inputCode.property,by with_reducible exact outputCode.property⟩
  let restriction ← NaturalAffine.witness (Raw.Sector.read dependencies [.bits selectorLayout.bits]
    [.bits targetLayout.bits] (RuntimePureInterval.fragment frame.selected frame.operations [so.token,to.token]))
  let logical ← NaturalAffine.witness (NominalSector.checkLogicals inputCode.val outputCode.val restriction.val.sectors
    selectorLayout.labels expected)
  let node : Node dependencies program block := .selection frame selectorLayout.bits targetLayout.bits restriction.val
    (by with_reducible exact restriction.property) inputCode.val outputCode.val selectorLayout.labels expected logical.val
    (by with_reducible exact logical.property) (attached.property.symm ▸ codes)
    ⟨by with_reducible exact selectorRead.property,
      ⟨targetLayout.labels,by with_reducible exact targetRead.property⟩⟩
  return (node,remaining)

def Nodes.ofList {dependencies program block} (nodes : List (Node dependencies program block)) :
    Nodes dependencies program block := nodes.foldr Nodes.cons Nodes.nil

def staticNodes {dependencies program block start count} :
    (action : RuntimeStaticPrimitive.Action) →
      (bound : @RuntimeStaticPrimitive.Bound dependencies program block start count action) →
      (match bound with
        | .identity _ => Unit
        | .primitive checked => RuntimePrimitiveSource.Checked checked) →
      List (Node dependencies program block)
  | _,.identity _,_ => []
  | _,.primitive checked,source => [.primitive checked source]

mutual
/-- The common loop records every actual mixed interval. Pure composition
continues to consume only its pure islands and requires complete pure coverage;
an observation or classical gap cannot acquire a fabricated pure equation. -/
inductive Step (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | pure {program block} (node : Node dependencies program block) : Step dependencies program block
  | gap {program block start count before ordinary}
      (checked : RuntimeOrdinaryBody.Gap block start count before ordinary) : Step dependencies program block
  | observation {program block sources rootOwner rootName caller functionName path event position before ordinary}
      (checked : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies program
        path event block position before ordinary) : Step dependencies program block
  | named {program block start count inputs sources caller before childHistory childRetired ordinary}
      (event : SourceRuntimeContext.NamedEvent sources caller)
      (frame : RuntimeCallScope.Checked block start count inputs ordinary event.effect)
      (source : SourceRuntimeTrace.Body event.target.signature)
      (sourceRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) source)
      (boundary : RuntimeNamedBoundary.Checked frame.interval inputs event before childHistory childRetired source.checked.summary.value)
      (finalOrdinary : RuntimeOrdinaryBody.State)
      (children : Steps dependencies frame.program frame.prepared.block) : Step dependencies program block
  | conditional {program block offset sources rootOwner rootName caller name}
      (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller name)
      (event : SourceRuntimeContext.BranchEvent sources caller)
      (source : RuntimeBranchAction.Source event)
      (actual : @RuntimeInterval.Branch dependencies program block offset)
      (actualRead : RuntimeInterval.Computed (RuntimeInterval.readBranch block offset) actual)
      {before left right ordinary leftOrdinary rightOrdinary}
      (action : RuntimeBranchAction.Checked path event source actual before left right ordinary leftOrdinary rightOrdinary)
      (thenSteps : Steps dependencies program actual.thenBlock)
      (elseSteps : Steps dependencies program actual.elseBlock) : Step dependencies program block

inductive Steps (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | nil {program block} : Steps dependencies program block
  | cons {program block} (first : Step dependencies program block)
      (rest : Steps dependencies program block) : Steps dependencies program block
end

def Steps.ofList {dependencies program block} (steps : List (Step dependencies program block)) :
    Steps dependencies program block := steps.foldr Steps.cons Steps.nil

abbrev Island (dependencies : List Semantics.Finite.Dependency) :=
  (program : Semantics.Observation.Program) ×
    (block : RuntimeInterval.Block dependencies program) × Node dependencies program block

/-- The enclosing Lean definition fixes the graph consumer. Failure never
selects another mode, and no untrusted context field chooses a continuation. -/
inductive OperationMode (artifact : Artifact) (root : Validity.Root) where
  | strict
  | extended (continuation : RuntimeGraphOperation.Consumption artifact root (Island root.dependencies))

def OperationMode.Receipt {artifact root} : OperationMode artifact root → Type
  | .strict => Empty
  | .extended continuation => RuntimeGraphOperation.CheckedReceipt continuation

def OperationMode.takeReferences {artifact root} (mode : OperationMode artifact root) (explicit : Bool)
    (references : List (List (List RuntimeProviderHeader.Request))) :
    WorkM (List (List RuntimeProviderHeader.Request) × List (List (List RuntimeProviderHeader.Request))) := do
  match mode with
  | .strict =>
    if explicit then
      let group :: remaining := references | throw .request
      guard group.isEmpty .request
      return ([],remaining)
    else
      guard references.isEmpty .request
      return ([],[])
  | .extended _ =>
    let group :: remaining := references | throw .request
    return (group,remaining)

def OperationMode.checkSignature {artifact root} (mode : OperationMode artifact root) {owner name}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name) : WorkM Unit :=
  match mode with
  | .strict => guard (!signature.operations.hasMeaningRequirements) .request
  | .extended _ => guard signature.operations.rootRequirements.isEmpty .request

/-- The enclosing reader fixes source acquisition and graph consumption together.
The planned continuation is indexed by the same source preparation value. -/
inductive ExecutionMode (artifact : Artifact) (root : Validity.Root) where
  | fresh (operations : OperationMode artifact root)
  | planned (preparation : RuntimeGraphOperation.Preparation artifact)
      (continuation : RuntimeGraphOperation.StagedConsumption preparation root (Island root.dependencies))

def ExecutionMode.queries {artifact root} : ExecutionMode artifact root → RuntimeBodyQueries.Mode artifact
  | .fresh _ => .fresh
  | .planned preparation _ => .planned preparation

def ExecutionMode.Receipt {artifact root} : ExecutionMode artifact root → Type
  | .fresh operations => operations.Receipt
  | .planned _ continuation => RuntimeGraphOperation.StagedReceipt continuation

def ExecutionMode.checkSignature {artifact root} (mode : ExecutionMode artifact root) {owner name}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name) (hasOriginalCaller : Bool) : WorkM Unit :=
  match mode with
  | .fresh operations => operations.checkSignature signature
  | .planned _ _ => guard (hasOriginalCaller || signature.operations.rootRequirements.isEmpty) .request

def ExecutionMode.referenceCount {artifact root} (mode : ExecutionMode artifact root)
    (cursor : mode.queries.Cursor) : Nat :=
  match mode with
  | .fresh _ => cursor.references.length
  | .planned _ _ => 0

def ExecutionMode.exhausted {artifact root} (mode : ExecutionMode artifact root)
    (cursor : mode.queries.Cursor) : Bool :=
  match mode with
  | .fresh _ => cursor.isEmpty
  | .planned _ _ => true

/-- Child consumption carries the fixed mode, its actual graph consumer and
its indexed source query through one dependent match. No graph comparison or
transport chooses staged evidence. -/
private def consumeOperationChild {artifact : Artifact} {root : Validity.Root} {owner : String}
    (execution : ExecutionMode artifact root) (event : SourceOperationApplication.Event artifact.sources owner)
    (consume : (cursor : execution.queries.Cursor) →
      execution.queries.GraphData event.operation.graph OperationAccess.applicable (.application event) → Bool →
      WorkM (Semantics.Exact.Matrix × List (Island root.dependencies) × execution.queries.Cursor × List execution.Receipt))
    (operation : RuntimeBodyQueries.Operation execution.queries event) :
    WorkM (Semantics.Exact.Matrix × List (Island root.dependencies) × List execution.Receipt) := do
  match execution,consume,operation with
  | .fresh _,consume,operation =>
    let (expected,children,remaining,performed) ← consume
      (RuntimeBodyPlan.Queues.ofContext operation.child) () (!operation.child.references.isEmpty)
    guard (remaining.bodies.isEmpty && remaining.references.isEmpty) .request
    pure (expected,children,performed)
  | .planned _ _,consume,operation =>
    let ⟨references,_,graph⟩ := operation.graph
    let (expected,children,_,performed) ← consume () ⟨operation.child.bodies,references,graph⟩ true
    pure (expected,children,performed)

/-- Every recursive arm remains indexed by its genuine literal block. A whole
function is wrapped with its existing Prepared object only at the public edge. -/
structure BlockResult (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (block : RuntimeInterval.Block dependencies program) where
  history : RuntimeStructuralAction.SourceState
  retired : List Owner
  actions : List (Node dependencies program block)
  steps : List (Step dependencies program block)
  ordinary : RuntimeOrdinaryBody.State
  obligations : List (Island dependencies) := []

def BlockResult.islands {dependencies program block} (result : BlockResult dependencies program block) :
    List (Island dependencies) :=
  result.actions.map (fun node => ⟨program,block,node⟩) ++ result.obligations

structure Result (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) where
  prepared : RuntimeInterval.Prepared dependencies program
  history : RuntimeStructuralAction.SourceState
  retired : List Owner
  actions : List (Node dependencies program prepared.block)
  steps : List (Step dependencies program prepared.block)
  ordinary : RuntimeOrdinaryBody.State
  obligations : List (Island dependencies) := []

def Result.bindings {dependencies program} (result : Result dependencies program) : Map := result.history.bindings

def Result.islands {dependencies program} (result : Result dependencies program) : List (Island dependencies) :=
  result.actions.map (fun node => ⟨program,result.prepared.block,node⟩) ++ result.obligations


/-- One state and one event handler are shared by enclosing and selected
static sequences. Context cursors and source history are never reconstructed. -/
abbrev LoopState (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (block : RuntimeInterval.Block dependencies program)
    (Receipt : Type := Empty) :=
  RuntimeStructuralAction.SourceState × List Owner × RuntimeOrdinaryBody.State ×
    List (Node dependencies program block) × List (Step dependencies program block) × List (Island dependencies) ×
    Nat × List (Position × Context) × List RuntimeContextRequest.Site ×
    List (Position × Context × Context) × List RuntimeProviderHeader.Request ×
    List (List (List RuntimeProviderHeader.Request)) × List Receipt

/-- Native history and source acquisition have separate fixed state fields.
Planned mode has no second context cursor that could diverge from its plan. -/
abbrev QueryState (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (block : RuntimeInterval.Block dependencies program)
    (Cursor Receipt : Type) :=
  RuntimeStructuralAction.SourceState × List Owner × RuntimeOrdinaryBody.State ×
    List (Node dependencies program block) × List (Step dependencies program block) × List (Island dependencies) ×
    Nat × Cursor × List Receipt

def reordered (roles : List Owner) (state : Raw.Observation.State) (bindings : Map) :
    WorkM (RuntimeOwnerMap.Checked roles state) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  RuntimeOwnerMap.check roles state ordered

private def singletonOrdinary (value : Value) : Bool := (ordinary value).all fun (basis,_) =>
  Semantics.FiniteCarrier.dimension basis == some 1

/-- The complete callback interface shared by the actual recursive body reader. -/
abbrev BlockRunner (artifact : Artifact) (root : Validity.Root) (execution : ExecutionMode artifact root) :=
    Mode → OutputBoundary →
    {rootOwner rootName owner name : String} →
    (source : SourceRuntimeScope.Subject artifact.sources owner name) →
    RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name →
    (program : Semantics.Observation.Program) → (request : Context) →
    execution.queries.BodyData source request → RuntimeStructuralAction.SourceState →
    RuntimeOrdinaryBody.State → (block : RuntimeInterval.Block root.dependencies program) →
    WorkM (BlockResult root.dependencies program block × List execution.Receipt)

/-- One unchanged native body iteration, with the recursive caller explicit.
This is the sole handler used by runBlockCore; factoring it introduces no
additional acceptance mode or work reset. -/
def runBlockStep (artifact : Artifact) (root : Validity.Root) (execution : ExecutionMode artifact root)
    (next : BlockRunner artifact root execution) : BlockRunner artifact root execution :=
  fun mode outputBoundary {rootOwner rootName owner name} source path program request sourcePlan initialHistory initialOrdinary block => do
    let dependencies := root.dependencies
    execution.checkSignature source.signature (match path with | .root _ => false | .named .. => true)
    match mode with
    | .pureBody =>
      guard (program.effect != .observe && SourceEffect.permits (some program.effect) source.effect &&
        singletonOrdinary source.value &&
        source.parameterValues.all singletonOrdinary &&
        program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
      let _ ← lift (readOption (Sector.pureOps block.operations))
      pure ()
    | .runtimeBody =>
      guard (SourceEffect.permits (some program.effect) source.effect) .request
    guard (initialHistory.nextOrdinal == source.initialOrdinal) .request
    let initial ← reordered source.initialRoles block.entry initialHistory.bindings
    let initialHistory := {initialHistory with bindings := initial.bindings}
    let checkFreshOperation (operations : OperationMode artifact root)
        (childRun : ∀ {owner name : String} {signature : SourceRuntimeContext.Signature artifact.sources owner name}
          (body : SourceRuntimeTrace.Body signature),
          (program : Semantics.Observation.Program) → Context → RuntimeStructuralAction.SourceState →
          (prepared : RuntimeInterval.Prepared dependencies program) →
            WorkM (BlockResult dependencies program prepared.block × List operations.Receipt))
        {context description siteOwner siteName} (graph : StaticOperation.CheckedGraph artifact.sources context description)
        (requested : StaticOperation.Paths) (origin : RuntimeGraphOperation.Origin graph)
        (sitePath : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName siteOwner siteName)
        (site : RuntimeGraphOperation.Site siteOwner siteName origin)
        (requests : List RuntimeProviderHeader.Request)
        (references : List (List RuntimeProviderHeader.Request)) :
        WorkM (Semantics.Exact.Matrix × List (Island dependencies) × List operations.Receipt) := do
      match operations with
      | .extended continuation =>
        let call : RuntimeGraphOperation.Request artifact := ⟨context,description,graph,requested,requests,references,origin⟩
        let checked ← NaturalAffine.witness (continuation.read call)
        exactWork (Exact.charge 8)
        let receipt : RuntimeGraphOperation.CheckedReceipt continuation :=
          ⟨call,⟨rootOwner,rootName,siteOwner,siteName,sitePath,site⟩,checked.val,by with_reducible exact checked.property⟩
        return (continuation.action checked.val,continuation.obligations checked.val,[receipt])
      | .strict =>
        guard references.isEmpty .request
        let paths ← RuntimeOperationPaths.read graph root requested requests
        let children ← paths.bodies.mapM fun {_} {headerRequest} header _ native => do
          let body := header.original.body
          let canonical := body.checked.summary.parameterValues.flatMap valueOwners
          let owner := (⟨native.ir.original.prepared.ports.input,native.ir.original.prepared.ports.domain⟩ :
            Semantics.CarrierInterface.Owner)
          let bindings ← RuntimeSourceBoundary.bindings canonical [owner]
          let prepared ← RuntimeInterval.prepare dependencies native.ir.original.program
          let initial : RuntimeStructuralAction.SourceState :=
            ⟨bindings,canonical,body.checked.summary.nextOwner⟩
          let (checked,_) ← childRun body native.ir.original.program headerRequest.2 initial prepared
          pure checked.islands
        let logical ← OperationIRMeaning.compute graph paths.bodies.logicals
        pure (logical,children.flatten,[])
    let consumeGraph {context description siteOwner siteName}
        (graph : StaticOperation.CheckedGraph artifact.sources context description)
        (requested : StaticOperation.Paths) (origin : RuntimeGraphOperation.Origin graph)
        (sitePath : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName siteOwner siteName)
        (site : RuntimeGraphOperation.Site siteOwner siteName origin)
        (cursor : execution.queries.Cursor)
        (data : execution.queries.GraphData graph requested origin) (explicit : Bool) :
        WorkM (Semantics.Exact.Matrix × List (Island dependencies) × execution.queries.Cursor × List execution.Receipt) := do
      match execution with
      | .fresh operations =>
        let occurrences ← StaticOperation.readOccurrences description
        let count := (RuntimeProviderHeaders.providerIndices description occurrences).length
        guard (count ≤ cursor.bodies.length) .request
        let (group,references) ← operations.takeReferences explicit cursor.references
        let childRun := fun {owner name : String} {signature : SourceRuntimeContext.Signature artifact.sources owner name}
            (body : SourceRuntimeTrace.Body signature) (program : Semantics.Observation.Program) (child : Context)
            (initial : RuntimeStructuralAction.SourceState) (prepared : RuntimeInterval.Prepared dependencies program) =>
          next .pureBody .rootOrder (.whole body) (.root body) program child () initial {} prepared.block
        let (logical,checked,receipts) ← checkFreshOperation operations childRun graph requested origin sitePath site
          (cursor.bodies.take count) group
        pure (logical,checked,{cursor with bodies := cursor.bodies.drop count, references},receipts)
      | .planned preparation continuation =>
        let ⟨implementations,references,plan⟩ := data
        let call : RuntimeGraphOperation.Request artifact :=
          ⟨context,description,graph,requested,implementations,references,origin⟩
        let checked ← NaturalAffine.witness (continuation.read call plan.evidence)
        exactWork (Exact.charge 8)
        let receipt : RuntimeGraphOperation.StagedReceipt continuation :=
          ⟨call,⟨rootOwner,rootName,siteOwner,siteName,sitePath,site⟩,plan.evidence,plan.consumed,checked.val,
            by with_reducible exact checked.property⟩
        return (continuation.action checked.val,continuation.obligations checked.val,(),[receipt])
    let opening ← RuntimeBodyQueries.openBody execution.queries source request sourcePlan
    let (obligations,sourceCursor,receipts) ← RuntimeBodyQueries.foldPrefixes execution.queries source.signature
      (fun actual origin data (obligations,cursor,receipts) => do
        exactWork (Exact.charge (receipts.length+1))
        let ⟨_,_,sitePath,site⟩ ← RuntimeGraphOperation.prefixSite origin path
        let (_,checked,cursor,performed) ← consumeGraph actual.2.graph
          (RuntimeGraphOperation.required source.signature actual.1.1) origin sitePath site cursor data (!request.references.isEmpty)
        pure (obligations ++ checked,cursor,receipts ++ performed))
      opening.actuals opening.prefixes
      (([] : List (Island dependencies)),opening.cursor,([] : List execution.Receipt))
    exactWork (Exact.charge (32*(source.events.length+request.positions.length+request.calls.length+1)^2))
    guard (request.positions.length == source.events.length &&
      request.positions.map (·.offset) == source.events.map SourceRuntimeContext.Event.offset) .request
    let advance : QueryState dependencies program block execution.queries.Cursor execution.Receipt → Nat →
        WorkM (QueryState dependencies program block execution.queries.Cursor execution.Receipt) :=
      fun (history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts) start => do
        guard (cursor ≤ start) .request
        if cursor == start then
          return (history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts)
        else
          let gap ← RuntimeOrdinaryBody.readGap block cursor (start-cursor) history ordinary
          return (history,retired,gap.ssa,actions,steps ++ [.gap gap],obligations,start,sourceCursor,receipts)
    let step : (event : SourceRuntimeContext.Event artifact.sources owner) → (position : Position) →
        RuntimeSourceEvent.Origin event position → execution.queries.EventData source event position →
        QueryState dependencies program block execution.queries.Cursor execution.Receipt →
          WorkM (QueryState dependencies program block execution.queries.Cursor execution.Receipt) := fun event position origin data state => do
        let (history,retired,ordinary,actions,steps,obligations,_cursor,sourceCursor,receipts) ← advance state position.start
        exactWork (Exact.charge (receipts.length+execution.referenceCount sourceCursor+1))
        let interval ← RuntimeInterval.check block position.start position.count
        let boundFrame ← RuntimeOwnerMap.checkBindings (history.bindings.map (·.owner)) interval.before history.bindings
        let callerFrame := boundFrame.val
        let bindings := callerFrame.bindings
        let before : RuntimeStructuralAction.SourceState := {history with bindings}
        let structural := match event with
          | .primitive event => ([.join,.split,.unit,.finish] : List CallName.Primitive).contains event.kind
          | _ => false
        let observing := match event with
          | .primitive event => ([.measureZ,.discard] : List CallName.Primitive).contains event.kind
          | _ => false
        let readOwners := RuntimeOwnerTransition.read interval callerFrame.bindings
        let continuation (owners : RuntimeOwnerTransition.Checked interval callerFrame.bindings) :
            RuntimeStructuralAction.SourceState := {before with bindings := owners.after.bindings}
        match event,data,origin with
        | .primitive event,data,origin =>
          if structural then
            let action ← RuntimeStructuralAction.read block position.start position.count event before
            let node : Node dependencies program block := .structural action
            return (action.after,retired ++ action.inputRoles,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations,position.start+position.count,sourceCursor,receipts)
          else if observing then
            match mode with
            | .pureBody => throw .request
            | .runtimeBody =>
              let action ← RuntimeOrdinaryBody.readObservation path event block position before ordinary
              return (action.after,retired ++ action.retired,action.ordinary,actions,steps ++ [.observation action],
                obligations,position.start+position.count,sourceCursor,receipts)
          else do
            let (after,node) ← primitiveAt interval history boundFrame (.primitive event) (some ⟨position,rfl,rfl,origin⟩)
            return (after,retired,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations,position.start+position.count,sourceCursor,receipts)
        | .phase event,data,origin =>
          let (after,node) ← primitiveAt interval history boundFrame (.phase event) (some ⟨position,rfl,rfl,origin⟩)
          return (after,retired,ordinary,actions ++ [node],steps ++ [.pure node],
            obligations,position.start+position.count,sourceCursor,receipts)
        | .registerPrimitive event,data,origin =>
          let action ← RuntimeRegisterAction.read interval event before
          let node : Node dependencies program block := .register ⟨position,rfl,rfl,origin⟩ action
          return (action.after,retired ++ event.consumed,ordinary,actions ++ [node],steps ++ [.pure node],
            obligations,position.start+position.count,sourceCursor,receipts)
        | .basis event,data,origin =>
          let sourceBody ← RuntimeBodyQueries.readBasis execution.queries source event position data
          let action ← RuntimeBasisAction.read event interval before
          let node : Node dependencies program block :=
            .basis interval ⟨position,rfl,rfl,origin⟩ sourceBody action
          let after := RuntimeBasisAction.continued event before action.output
          let consumed := if event.input == event.output then [] else [event.input]
          return (after,retired ++ consumed,ordinary,actions ++ [node],steps ++ [.pure node],
            obligations,position.start+position.count,sourceCursor,receipts)
        | .computed event children,data,origin =>
          let finish output node :=
            let after := RuntimeComputedPredicate.continued event before output
            pure (after,retired ++ event.body.consumed ++ [event.returned.auxiliary],ordinary,actions ++ [node],steps ++ [.pure node],
              obligations,position.start+position.count,sourceCursor,receipts)
          if ← (do
              exactWork (Exact.charge (8*(position.start+position.count+1)))
              pure (StructuralComputedRaw.isStructuralInterval interval)) then
            let action ← StructuralComputedRaw.readInterval event interval before
            finish action.checked.output (.structuralComputed interval ⟨position,rfl,rfl,origin⟩ action)
          else
            let prepared ← RuntimeBodyQueries.readComputed execution.queries source event children position data
            match prepared with
            | .inl prepared =>
              let action ← RuntimeComputedUse.read prepared interval before
              finish action.literal.output (.computed interval ⟨position,rfl,rfl,origin⟩ prepared action)
            | .inr prepared =>
              let action ← RuntimeCertifiedComputed.read prepared interval before
              finish action.literal.output (.certifiedComputed interval ⟨position,rfl,rfl,origin⟩ prepared action)
        | .workspace event children,data,origin =>
          let prepared ← RuntimeBodyQueries.readWorkspace execution.queries source event children position data
          let action ← RuntimeWorkspace.readLiteral prepared interval before
          let map ← RuntimeWorkspace.readCallerMap action root.receipts
          let node : Node dependencies program block := .workspace interval ⟨position,rfl,rfl,origin⟩ prepared action map
          let retired := retired ++ event.body.consumed ++ (if event.fresh then [event.scratchOut] else [])
          return (action.continuation,retired,ordinary,actions ++ [node],steps ++ [.pure node],
            obligations,position.start+position.count,sourceCursor,receipts)
        | .named event,data,_ =>
          let named ← RuntimeBodyQueries.readNamed execution.queries source event position sourceCursor data
          let child := named.context
          let original := named.body
          let sourceCursor := named.cursor
          let ordered ← NaturalAffine.witness (RuntimeOwnerMap.order event.inputOwners before.bindings)
          let inputs := ordered.val.map (·.port)
          let tokens := inputs.map (·.token)
          let bindAt (actual : RuntimeInterval.Checked block position.start position.count) (same : actual = interval)
              (selected : List Semantics.Raw.Port) (found : PureInterval.ports actual.before tokens = some selected) :
              WorkM (RuntimeNamedBoundary.Inputs actual tokens event before) := do
            let checked ← RuntimeNamedBoundary.bindInputs interval tokens event before ordered.val
              (by with_reducible exact ordered.property) rfl selected (same ▸ found)
            pure (same.symm ▸ checked)
          let childRoles := original.checked.summary.parameterValues.flatMap valueOwners
          if callerName : event.target.callerName = name then
            let parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner event.target.callerName := by
              simpa only [callerName] using path
            let childPath := RuntimeOrdinaryBody.CallPath.named event original
              named.original parent
            match mode with
            | .pureBody =>
              guard (event.effect == .unitary) .request
              let opened ← RuntimeCallInterval.readWithInterval interval tokens
              let frame := opened.val
              let bound ← bindAt frame.interval opened.property frame.selected frame.atEntry
              let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
                (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
              let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
              let childHistory : RuntimeStructuralAction.SourceState :=
                ⟨childInitial,childRoles,original.checked.summary.nextOwner⟩
              let (nested,childReceipts) ← next .pureBody .localScope (.whole original) childPath frame.program child named.nested childHistory
                ordinary frame.prepared.block
              let boundary ← RuntimeNamedBoundary.readWithInputs frame.interval tokens
                event before nested.history nested.retired original.checked.summary.value bound
              let node : Node dependencies program block := .named event frame original
                named.original boundary (Nodes.ofList nested.actions)
              return (boundary.after,retired ++ event.consumed,nested.ordinary,actions ++ [node],steps ++ [.pure node],
                obligations ++ nested.obligations,position.start+position.count,sourceCursor,receipts ++ childReceipts)
            | .runtimeBody =>
              let opened ← RuntimeCallScope.readWithInterval interval tokens ordinary event.effect
              let frame := opened.val
              let bound ← bindAt frame.interval opened.property frame.selected frame.atEntry
              let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
                (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
              let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
              let childHistory : RuntimeStructuralAction.SourceState :=
                ⟨childInitial,childRoles,original.checked.summary.nextOwner⟩
              let (nested,childReceipts) ← next .runtimeBody .localScope (.whole original) childPath frame.program child named.nested childHistory
                frame.visible.ssa frame.prepared.block
              let boundary ← RuntimeNamedBoundary.readWithInputs frame.interval tokens
                event before nested.history nested.retired original.checked.summary.value bound
              let step : Step dependencies program block := .named event frame original
                named.original boundary nested.ordinary (Steps.ofList nested.steps)
              return (boundary.after,retired ++ event.consumed,nested.ordinary,actions,steps ++ [step],
                obligations ++ nested.obligations,position.start+position.count,sourceCursor,receipts ++ childReceipts)
          else throw .request
        | .conditional event thenEvents elseEvents,data,_ =>
          match mode with
          | .pureBody => throw .request
          | .runtimeBody =>
            guard (position.count == 1) .request
            let selected ← RuntimeBodyQueries.readBranch execution.queries source event thenEvents elseEvents position sourceCursor data
            let actualRead ← NaturalAffine.witness (RuntimeInterval.readBranch block position.start)
            let actual := actualRead.val
            if sameName : event.callerName = name then
              let thenSource : SourceRuntimeScope.Subject artifact.sources owner name :=
                .arm event sameName selected.source.bodies selected.source.original true
              let elseSource : SourceRuntimeScope.Subject artifact.sources owner name :=
                .arm event sameName selected.source.bodies selected.source.original false
              let (left,leftReceipts) ← next .runtimeBody .frame thenSource path program selected.left selected.thenPlan
                before ordinary actual.thenBlock
              let (right,rightReceipts) ← next .runtimeBody .frame elseSource path program selected.right selected.elsePlan
                before ordinary actual.elseBlock
              let action ← RuntimeBranchAction.read path event selected.source actual before left.history right.history
                ordinary left.ordinary right.ordinary
              exactWork (Exact.charge (leftReceipts.length+1))
              let branchStep : Step dependencies program block := .conditional path event selected.source actual
                (by with_reducible exact actualRead.property) action (Steps.ofList left.steps) (Steps.ofList right.steps)
              return (action.next,retired ++ action.retired,action.ordinaryAfter,actions,steps ++ [branchStep],
                obligations ++ left.islands ++ right.islands,position.start+position.count,selected.cursor,
                receipts ++ leftReceipts ++ rightReceipts)
            else throw .request
        | .operation event,data,_ =>
          let operation ← RuntimeBodyQueries.readOperation execution.queries source event position sourceCursor data
          if caller : event.callerName = name then
            let (expected,children,performed) ← consumeOperationChild execution event
              (consumeGraph event.operation.graph OperationAccess.applicable
                (.application event) path (.application event caller)) operation
            let finish after retired node :=
              pure (after,retired,ordinary,actions ++ [node],steps ++ [.pure node],
                obligations ++ children,position.start+position.count,operation.cursor,receipts ++ performed)
            if event.operation.graph.root.input == event.operation.graph.root.output then do
              guard (event.allocated.isEmpty && event.consumed.isEmpty) .request
              let owners ← readOwners
              let node ← operationNode block position event.inputOwners bindings owners.after.bindings expected
              finish (continuation owners) retired node
            else do
              let checked ← RuntimeRectangularOperation.read event interval before expected
              let after := RuntimeRectangularOperation.continued before checked.source.input checked.source.output checked.returned
              finish after (retired ++ event.consumed) (.rectangularOperation checked)
          else throw .request
        | .transform event,data,_ =>
          let transformed ← RuntimeBodyQueries.readTransform execution.queries source event position sourceCursor data
          let forward ← RuntimeTransformAction.readForward artifact dependencies transformed.request
          let body := transformed.request.source
          let initial : RuntimeStructuralAction.SourceState :=
            ⟨forward.initial,forward.roles,body.checked.summary.nextOwner⟩
          let (child,performed) ← next .pureBody .rootOrder (.whole body) (.root body) forward.program
            transformed.request.context transformed.nested initial {} forward.prepared.block
          let logical ← RuntimeTransformAction.readForwardMap forward child.history.bindings
          let owners ← RuntimeTransformOwners.read interval event before
          let action ← RuntimeTransformAction.read owners logical.code.logical
          let node : Node dependencies program block := .transform transformed.request transformed.original
            forward child.history.bindings logical owners action (Nodes.ofList child.actions)
          return (owners.after,retired ++ event.consumed,ordinary,actions ++ [node],steps ++ [.pure node],
            obligations ++ child.islands,position.start+position.count,transformed.cursor,receipts ++ performed)
        | .selection tokens parsed original selector target scope naturals held remaining,data,_ =>
          let owners ← RuntimeOwnerTransition.read interval callerFrame.bindings
          let selected ← RuntimeBodyQueries.readSelection execution.queries source position sourceCursor data
          let table := selected.table
          let (logicals,checked,sourceCursor,receipts) ← RuntimeBodyQueries.foldArms execution.queries table
            (fun index data (logicals,checked,cursor,receipts) => do
              exactWork (Exact.charge (16*(logicals.length+receipts.length+1)))
              let (logical,children,cursor,performed) ← consumeGraph (table.arms[index]).operation.graph
                OperationAccess.controllable (.arm (table.arms[index]).operation) path (.arm table index)
                cursor data (!request.references.isEmpty)
              return (logicals ++ [logical],checked ++ children,cursor,receipts ++ performed)) selected.arms
            (([] : List Semantics.Exact.Matrix),([] : List (Island dependencies)),selected.cursor,receipts)
          let (node,_) ← selectionNode artifact interval callerFrame owners selector target table selected.site ()
            fun index _ _ => do
              exactWork (Exact.charge (index.val+1))
              let logical ← lift (readOption logicals[index.val]?)
              pure (logical,())
          pure ({before with bindings := owners.after.bindings},retired,ordinary,actions ++ [node],steps ++ [.pure node],
            obligations ++ checked,position.start+position.count,sourceCursor,receipts)
        | _,_,_ =>
          let _ ← readOwners
          throw .request
    let outerStep : (event : SourceRuntimeContext.Event artifact.sources owner) → (position : Position) →
        RuntimeSourceEvent.At (source.events.zip request.positions) event position →
        execution.queries.EventData source event position →
        QueryState dependencies program block execution.queries.Cursor execution.Receipt →
          WorkM (QueryState dependencies program block execution.queries.Cursor execution.Receipt) := fun event position entry data state => do
        match event,data,entry with
        | .staticConditional event children,data,entry =>
          let (_,_,_,_,_,_,_,incomingSourceCursor,_) := state
          let pureOnly := match mode with | .pureBody => true | .runtimeBody => false
          let actual ← NaturalAffine.witness (RuntimeBodyQueries.readStatic execution.queries source event children position
            pureOnly incomingSourceCursor data)
          let selected := actual.val
          let state ← advance state position.start
          let (history,retired,ordinary,actions,steps,obligations,cursor,_,receipts) := state
          let sequence := selected.sequence
          let interval ← RuntimeInterval.check block position.start position.count
          let bindings := (← reordered (history.bindings.map (·.owner)) interval.before history.bindings).bindings
          let before : RuntimeStructuralAction.SourceState := {history with bindings}
          let _ ← RuntimeStaticPrimitive.readContinuationBefore sequence interval before
          let count := sequence.selected.result.events.length
          exactWork (Exact.charge (32*(count+1)*(actions.length+steps.length+obligations.length+count+1)+
            32*(Raw.OwnerFlow.fields retired+1)))
          let initial : QueryState dependencies program block execution.queries.Cursor execution.Receipt :=
            (before,retired,ordinary,actions,steps,obligations,cursor,selected.cursor,receipts)
          let result ← RuntimeBodyQueries.foldEvents execution.queries source
            (sequence.selected.result.events.zip selected.positions)
            (fun event_ position_ inner data_ state_ =>
              step event_ position_ (RuntimeBodyQueries.selectedOrigin execution.queries source request.positions
                event children position entry pureOnly incomingSourceCursor data
                ⟨selected,by with_reducible exact actual.property⟩ inner) data_ state_)
            selected.events initial
          let (after,afterRetired,_ordinary,_actions,_steps,_obligations,afterCursor,_sourceCursor,_receipts) := result
          guard (afterCursor == position.start+position.count) .request
          let _ ← RuntimeStaticPrimitive.readContinuationAfter sequence interval before after retired afterRetired
          return result
        | event,data,entry => step event position (.direct source request.positions entry) data state
    let (history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts) ←
      RuntimeBodyQueries.foldEvents execution.queries source (source.events.zip request.positions) outerStep opening.events
        (initialHistory,([] : List Owner),initialOrdinary,
          ([] : List (Node dependencies program block)),([] : List (Step dependencies program block)),
          obligations,0,sourceCursor,receipts)
    guard (cursor ≤ block.operations.length && execution.exhausted sourceCursor) .request
    let (ordinary,steps) ← if cursor == block.operations.length then pure (ordinary,steps) else do
      let gap ← RuntimeOrdinaryBody.readGap block cursor (block.operations.length-cursor) history ordinary
      pure (gap.ssa,steps ++ [.gap gap])
    guard (history.issued == initialHistory.issued ++ source.allocated && retired == source.consumed &&
      history.nextOrdinal == source.nextOrdinal) .request
    let final ← RuntimeInterval.check block block.operations.length 0
    match mode with
    | .pureBody => guard (!final.after.observe) .request
    | .runtimeBody => pure ()
    let bindings := (← reordered source.outputRoles final.after history.bindings).bindings
    let outputs ← rolePorts source.outputRoles bindings
    guard (match outputBoundary with
      | .rootOrder => outputs.map (·.token) == program.outputs
      | .localScope => decide ((outputs.map (·.token)).Perm program.outputs)
      | .frame => true) .request
    return (⟨{history with bindings},retired,actions,steps,ordinary,obligations⟩,receipts)

/-- One structural recursion checks whole functions and both authentic arm
blocks. Source scopes supply original outcomes; only the genuine Block supplies
native operations, scope and issuance history. No alternative body evaluator,
shortened program or invented signature is used for a branch. -/
def runBlockCore (artifact : Artifact) (root : Validity.Root) (execution : ExecutionMode artifact root) :
    Nat → BlockRunner artifact root execution :=
  Nat.rec (fun _ _ {_ _ _ _} _ _ _ _ _ _ _ _ => throw .limit)
    (fun _ next => runBlockStep artifact root execution next)

theorem runBlockCore_succ (artifact : Artifact) (root : Validity.Root) (execution : ExecutionMode artifact root) (fuel : Nat) :
    runBlockCore artifact root execution (fuel+1) =
      runBlockStep artifact root execution (runBlockCore artifact root execution fuel) := rfl

/-- Existing callers use the same native loop with fresh original source queries. -/
def runBlockUsing (artifact : Artifact) (root : Validity.Root) (operations : OperationMode artifact root)
    (fuel : Nat) (mode : Mode) (outputBoundary : OutputBoundary) {rootOwner rootName owner name : String}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context) (initialHistory : RuntimeStructuralAction.SourceState)
    (initialOrdinary : RuntimeOrdinaryBody.State) (block : RuntimeInterval.Block root.dependencies program) :
    WorkM (BlockResult root.dependencies program block × List operations.Receipt) :=
  runBlockCore artifact root (.fresh operations) fuel mode outputBoundary source path program request ()
    initialHistory initialOrdinary block

/-- A staged caller must supply the actual complete source-indexed Body plan.
Every graph read consumes its exact preparation under this same final root. -/
def runBlockPlanned (artifact : Artifact) (root : Validity.Root)
    (preparation : RuntimeGraphOperation.Preparation artifact)
    (continuation : RuntimeGraphOperation.StagedConsumption preparation root (Island root.dependencies))
    (fuel : Nat) (mode : Mode) (outputBoundary : OutputBoundary) {rootOwner rootName owner name : String}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context) (plan : RuntimeBodyPlan.Body preparation source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (initialOrdinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program) :
    WorkM (BlockResult root.dependencies program block × List (RuntimeGraphOperation.StagedReceipt continuation)) :=
  runBlockCore artifact root (.planned preparation continuation) fuel mode outputBoundary source path program request plan
    initialHistory initialOrdinary block

/-- Strict callers use the same loop with no Meaning continuation. -/
def runBlock (artifact : Artifact) (root : Validity.Root) (fuel : Nat) (mode : Mode) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context) (initialHistory : RuntimeStructuralAction.SourceState)
    (initialOrdinary : RuntimeOrdinaryBody.State) (block : RuntimeInterval.Block root.dependencies program) :
    WorkM (BlockResult root.dependencies program block) := do
  let (result,_) ← runBlockUsing artifact root .strict fuel mode outputBoundary source path program request
    initialHistory initialOrdinary block
  return result

/-- Whole-body callers retain the same exact Body, Prepared object and public
run interface. The shared block walk also owns all recursive branch/call steps. -/
def run (artifact : Artifact) (root : Validity.Root) (fuel : Nat) (mode : Mode) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    (body : SourceRuntimeTrace.Body signature)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map)
    (ordinary : RuntimeOrdinaryBody.State) (prepared : RuntimeInterval.Prepared root.dependencies program) :
    WorkM (Result root.dependencies program) := do
  let initialHistory : RuntimeStructuralAction.SourceState :=
    ⟨initial,body.checked.summary.parameterValues.flatMap valueOwners,body.checked.summary.nextOwner⟩
  let result ← runBlock artifact root fuel mode outputBoundary (.whole body) path program request initialHistory
    ordinary prepared.block
  return ⟨prepared,result.history,result.retired,result.actions,result.steps,result.ordinary,result.obligations⟩

structure Checked (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) where
  prepared : RuntimeInterval.Prepared root.dependencies program
  result : Result root.dependencies program
  checked : RuntimeInterval.Computed
    (run artifact root 128 .pureBody .rootOrder body (.root body) program request initial {} prepared) result

def checkPrepared (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map)
    (prepared : RuntimeInterval.Prepared root.dependencies program) :
    WorkM (Checked artifact root body program request initial) := do
  let checked ← NaturalAffine.witness
    (run artifact root 128 .pureBody .rootOrder body (.root body) program request initial {} prepared)
  return ⟨prepared,checked.val,by with_reducible exact checked.property⟩

def check (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) :
    WorkM (Checked artifact root body program request initial) := do
  let prepared ← RuntimeInterval.prepare root.dependencies program
  checkPrepared artifact root body program request initial prepared

structure RuntimeChecked (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (request : Context) (runtime : RuntimeFamily.Request)
    (prepared : RuntimeInterval.Prepared root.dependencies root.program)
    (inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage)
    (ordinary : RuntimeOrdinaryInputs.Checked body prepared runtime inputs) where
  result : Result root.dependencies root.program
  checked : RuntimeInterval.Computed
    (run artifact root 128 .runtimeBody .rootOrder body (.root body) root.program request
      inputs.owners.bindings ordinary.ssa prepared) result

/-- The general preparation receives only an independently derived initial SSA
state on the same body/root/storage/preparation. Complete actual history and
final ordinary storage correspondence, branch continuations and code/instrument
composition remain necessary before any production acceptance can use it. -/
def checkRuntime (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (request : Context) (runtime : RuntimeFamily.Request)
    (prepared : RuntimeInterval.Prepared root.dependencies root.program)
    (inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage)
    (ordinary : RuntimeOrdinaryInputs.Checked body prepared runtime inputs) :
    WorkM (RuntimeChecked artifact root body request runtime prepared inputs ordinary) := do
  let checked ← NaturalAffine.witness
    (run artifact root 128 .runtimeBody .rootOrder body (.root body) root.program request
      inputs.owners.bindings ordinary.ssa prepared)
  return ⟨checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimePureBody
