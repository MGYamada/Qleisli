import QleisliKernel.Qirf.RuntimeAccessPartition
import QleisliKernel.Qirf.RuntimeStructuralAction

/-! The original access call reserves real Raw ports for the existing callee
verifier. Only that verifier's ordered returns can reassemble its parents.
For `ctrl`, the same actual callee interval must preserve the written sectors.
Both histories and the exact enclosing interval are retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeExclusiveAction
open QleisliKernel Finite SourceTypes SourceRuntimeValues
open RuntimeOwnerMap (Owner Map Binding)
open RuntimeStructuralAction (SourceState)
abbrev RawPort := Semantics.Raw.Port

abbrev Access := SourceRuntimeContext.ExclusiveEvent

def places {sources caller} (access : Access sources caller) : List RuntimeAccessPartition.ActivePlace :=
  access.checked.entries.map fun entry => ⟨entry.2.parent,entry.2.coordinates.range⟩

def routeCount {sources caller} (access : Access sources caller) : Nat :=
  RuntimeAccessPartition.activeCount (places access)

private def visibleHeld {sources caller} (access : Access sources caller) (suspended : List Owner) : List Owner :=
  access.held.filter (fun owner => !suspended.contains owner)

private def reserveBindings {sources caller} (access : Access sources caller)
    (remainders : List (Owner × Option RawPort)) (selected : List RawPort) : Map :=
  let spectators := remainders.filterMap fun (parent,port) =>
    let role := (access.reservation.remainders.find? (fun (original,_) => original == parent)).map Prod.snd
    port.map fun port => (⟨role.getD parent,port⟩ : RuntimeOwnerMap.Binding)
  spectators ++ (access.reservation.arguments.zip selected).map (fun (owner,port) => ⟨owner,port⟩)

/-- A structural change groups exact register factors over an unchanged live
spectator map. The old and new groups preserve their respective map orders. -/
structure Repartition (before after : Map) where
  oldBlock : Map
  newBlock : Map
  spectators : Map
  inputOrder : (oldBlock ++ spectators).Perm before
  outputOrder : (newBlock ++ spectators).Perm after
  oldLayout : ∀ binding ∈ oldBlock,
    (binding.owner.basis = [.bit] ∨ ∃ size, binding.owner.basis = [.bits size]) ∧
    binding.port.bits = RuntimeStructuralAction.basisBits binding.owner.basis ∧
    binding.port.wires.length = binding.port.bits
  newLayout : ∀ binding ∈ newBlock,
    (binding.owner.basis = [.bit] ∨ ∃ size, binding.owner.basis = [.bits size]) ∧
    binding.port.bits = RuntimeStructuralAction.basisBits binding.owner.basis ∧
    binding.port.wires.length = binding.port.bits

private def flatRegister : Semantics.FiniteCarrier.Basis → Bool
  | [.bit] | [.bits _] => true
  | _ => false

private def registerLayout (binding : Binding) : Bool :=
  flatRegister binding.owner.basis &&
    (binding.port.bits == RuntimeStructuralAction.basisBits binding.owner.basis &&
      binding.port.wires.length == binding.port.bits)

private theorem registerLayout_checked {binding : Binding} (ok : registerLayout binding = true) :
    (binding.owner.basis = [.bit] ∨ ∃ size, binding.owner.basis = [.bits size]) ∧
    binding.port.bits = RuntimeStructuralAction.basisBits binding.owner.basis ∧
    binding.port.wires.length = binding.port.bits := by
  simp only [registerLayout,Bool.and_eq_true,beq_iff_eq] at ok
  refine ⟨?_,ok.2⟩
  obtain ⟨shape,_⟩ := ok
  generalize binding.owner.basis = basis at shape ⊢
  unfold flatRegister at shape
  split at shape
  · exact Or.inl rfl
  · exact Or.inr ⟨_,rfl⟩
  · cases shape

private def indexedParents {sources caller} (access : Access sources caller) : List Owner :=
  access.reservation.remainders.map Prod.fst

private def readRepartition (before after : Map) (oldOwners newOwners : List Owner) :
    WorkM (Repartition before after) := do
  guard (before.length ≤ 128 && after.length ≤ 128 && oldOwners.length ≤ 128 && newOwners.length ≤ 128) .limit
  let fields := Raw.OwnerFlow.fields (before.map (·.owner) ++ after.map (·.owner) ++ oldOwners ++ newOwners)
  let wires := ((before ++ after).map (·.port.wires.length)).sum
  exactWork (Exact.charge (16*(fields+wires+1)*(before.length+after.length+oldOwners.length+newOwners.length+1)))
  let wasSelected := fun binding : Binding => oldOwners.contains binding.owner
  let isSelected := fun binding : Binding => newOwners.contains binding.owner
  let oldBlock := before.filter wasSelected
  let newBlock := after.filter isSelected
  let spectators := before.filter (fun binding => !wasSelected binding)
  let afterSpectators := after.filter (fun binding => !isSelected binding)
  guard (decide ((oldBlock.map (·.owner)).Perm oldOwners) &&
    decide ((newBlock.map (·.owner)).Perm newOwners)) .request
  -- Permutation compares each exact owner and Raw port, including wire order.
  if same : spectators.Perm afterSpectators then
    if oldLayout : oldBlock.all registerLayout = true then
      if newLayout : newBlock.all registerLayout = true then
        return ⟨oldBlock,newBlock,spectators,List.filter_append_perm wasSelected before,
          (same.append_left newBlock).trans (List.filter_append_perm isSelected after),
          fun binding member => registerLayout_checked (List.all_eq_true.mp oldLayout binding member),
          fun binding member => registerLayout_checked (List.all_eq_true.mp newLayout binding member)⟩
      else throw .request
    else throw .request
  else throw .request

structure Opened {sources caller dependencies program block start count} (access : Access sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (suspended : List Owner) (before : SourceState) where
  route : RuntimeAccessPartition.ActiveEntry interval before.bindings (places access)
  ordinal : before.nextOrdinal = access.nextOrdinal
  suspendedIssued : suspended.all (fun owner => before.issued.contains owner && access.held.contains owner) = true
  beforeRoles : (before.bindings.map (·.owner)).Perm (visibleHeld access suspended ++ owners access.before)
  reservedRoles : (reserveBindings access route.remainders route.selected |>.map (·.owner)).Perm
    (visibleHeld access suspended ++ owners access.activation.remaining ++ access.reservation.arguments)
  selectedWidths : RuntimeStructuralAction.widths route.selected access.reservation.arguments = true
  initial : SourceState
  bindings : initial.bindings = reserveBindings access route.remainders route.selected
  issued : initial.issued = before.issued ++ access.reservation.temporary
  nextOrdinal : initial.nextOrdinal = access.reservation.issued.nextOrdinal
  frame : RuntimeOwnerMap.Checked (initial.bindings.map (·.owner)) interval.before
  nativeBindings : frame.bindings = initial.bindings
  repartition : Repartition before.bindings initial.bindings

def readOpen {sources caller dependencies program block start count} (access : Access sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (suspended : List Owner) (before : SourceState) : WorkM (Opened access interval suspended before) := do
  let route ← RuntimeAccessPartition.readActiveEntry interval before.bindings (places access)
  let held := visibleHeld access suspended
  let beforeRoles := held ++ owners access.before
  let reservedRoles := held ++ owners access.activation.remaining ++ access.reservation.arguments
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (beforeRoles ++ reservedRoles ++ before.issued ++
    access.reservation.temporary ++ suspended ++ access.held)+1)*
    (before.bindings.length+route.remainders.length+route.selected.length+
      access.checked.entries.length+suspended.length+1)))
  let initial : SourceState := ⟨reserveBindings access route.remainders route.selected,
    before.issued ++ access.reservation.temporary,access.reservation.issued.nextOrdinal⟩
  if valid : before.nextOrdinal = access.nextOrdinal ∧
      suspended.all (fun owner => before.issued.contains owner && access.held.contains owner) = true ∧
      (before.bindings.map (·.owner)).Perm beforeRoles ∧
      (initial.bindings.map (·.owner)).Perm reservedRoles ∧
      RuntimeStructuralAction.widths route.selected access.reservation.arguments = true then
    let frame ← RuntimeOwnerMap.checkBindings (initial.bindings.map (·.owner)) interval.before initial.bindings
    let repartition ← readRepartition before.bindings initial.bindings
      (indexedParents access) access.reservation.temporary
    return ⟨route,valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2,
      initial,rfl,rfl,rfl,frame.val,frame.property,repartition⟩
  else throw .request

private def wholeOutputs {sources caller} (access : Access sources caller) : List (Owner × Owner) :=
  (access.checked.entries.zip access.returned.outputs).filterMap fun (entry,output) =>
    if entry.2.coordinates.range.isNone then some (entry.2.parent,output) else none

private def restoredRole (whole : List (Owner × Owner)) (owner : Owner) : Owner :=
  ((whole.find? (fun (parent,_) => parent == owner)).map Prod.snd).getD owner

def inputRoles {sources caller} (access : Access sources caller) : List Owner :=
  ((places access).map (·.parent)).eraseDups

def outputRoles {sources caller} (access : Access sources caller) : List Owner :=
  (inputRoles access).map (restoredRole (wholeOutputs access))

private def portList (roles : List Owner) (bindings : Map) : WorkM (List RawPort) := do
  pure ((← RuntimeOwnerMap.order roles bindings).map (·.port))

def controlAxes {sources caller} (access : Access sources caller) (selected : List RawPort) : List Nat :=
  RuntimeAccessInterval.orderedControlAxes ((access.written.arguments.zip selected).map
    fun (argument,port) => (argument.2.role,port.bits))

private def controlFragment (selected returned : List RawPort) (operations : List Semantics.Raw.Op) :
    Semantics.Observation.Program :=
  Semantics.Ownership.pureProgram (RuntimePureInterval.fragment selected operations (returned.map (·.token)))

/-- Check sectors on the exact inner operations with the ports obtained by
opening and returning the original places. Routing around the call is not
part of this sector decision. -/
inductive ControlEvidence {sources caller dependencies program} (access : Access sources caller)
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (selected returned : List RawPort) : Type where
  | excl (onlyExclusive : access.written.exclusive = true)
  | ctrl (hasControl : access.written.exclusive = false)
      (arity : selected.length = access.written.arguments.length)
      (operations : List Semantics.Raw.Op)
      (literal : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure)
      (sectors : RuntimeAccessInterval.FragmentSectors dependencies
        (controlFragment selected returned operations) (controlAxes access selected))

private def readControl {sources caller dependencies program} (access : Access sources caller)
    (block : RuntimeInterval.Block dependencies program) (start count : Nat) (selected returned : List RawPort) :
    WorkM (ControlEvidence access block start count selected returned) := do
  if onlyExclusive : access.written.exclusive = true then
    return .excl onlyExclusive
  else
    let bits := (selected.map (·.bits)).sum
    guard (bits ≤ 6) .limit
    exactWork (Exact.charge (16*(selected.length+returned.length+start+count+1)))
    if arity : selected.length = access.written.arguments.length then
      match pure : Sector.pureOps ((block.operations.drop start).take count) with
      | none => throw .request
      | some operations =>
        let fragment := controlFragment selected returned operations
        guard (ControlAccess.ownersPreflight fragment) .limit
        let sectors ← RuntimeAccessInterval.checkFragmentSectors (dependencies := dependencies)
          fragment bits (controlAxes access selected)
        return .ctrl (Bool.eq_false_iff.mpr onlyExclusive) arity operations (Sector.pureOps_bound _ _ pure) sectors
    else throw .request

structure Closed {sources caller dependencies program block start count access interval suspended before}
    (opening : @Opened sources caller dependencies program block start count access interval suspended before)
    (child : SourceState) (childRetired : List Owner) where
  childIssued : child.issued = opening.initial.issued ++ access.allocated
  childOrdinal : child.nextOrdinal = access.innerOrdinal
  childConsumed : childRetired = access.consumed
  childFrame : RuntimeOwnerMap.Checked (child.bindings.map (·.owner)) interval.after
  childBindings : childFrame.bindings = child.bindings
  returned : List RawPort
  returnedRead : RuntimeInterval.Computed (portList access.returned.outputs child.bindings) returned
  route : RuntimeAccessPartition.ActiveExit opening.route returned
  after : SourceState
  bindings : after.bindings = route.restored.map (fun binding =>
    {binding with owner := restoredRole (wholeOutputs access) binding.owner})
  issued : after.issued = child.issued
  nextOrdinal : after.nextOrdinal = child.nextOrdinal
  afterRoles : (after.bindings.map (·.owner)).Perm
    (visibleHeld access suspended ++ owners access.returned.restored)
  inputs : List RawPort
  sourceInputs : RuntimeInterval.Computed (portList (inputRoles access) before.bindings) inputs
  outputs : List RawPort
  sourceOutputs : RuntimeInterval.Computed (portList (outputRoles access) after.bindings) outputs
  literal : RuntimePureInterval.Literal block (start-routeCount access) (routeCount access+count+routeCount access)
    (inputs.map (·.token)) (outputs.map (·.token)) .unitary
  inputPorts : literal.selected = inputs
  outputPorts : literal.returned = outputs
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) literal.interval.after
  afterBindings : afterFrame.bindings = after.bindings
  repartition : Repartition child.bindings after.bindings
  control : ControlEvidence access block start count opening.route.selected returned

/-- Close exactly the verified child's return. Select owners from its live
map before checking reinsertion, and retain the whole literal interval for
pure composition and coherent-arm evaluation. -/
def readClose {sources caller dependencies program block start count access interval suspended before}
    (opening : @Opened sources caller dependencies program block start count access interval suspended before)
    (child : SourceState) (childRetired : List Owner) : WorkM (Closed opening child childRetired) := do
  let expected := visibleHeld access suspended ++ owners access.returned.restored
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (child.issued ++ opening.initial.issued ++
    access.reservation.temporary ++ access.allocated ++ access.consumed ++ access.returned.outputs ++
    childRetired ++ expected)+1)*(before.bindings.length+child.bindings.length+access.checked.entries.length+1)))
  if history : child.issued = opening.initial.issued ++ access.allocated ∧
      child.nextOrdinal = access.innerOrdinal ∧ childRetired = access.consumed then
    let returned ← NaturalAffine.witness (portList access.returned.outputs child.bindings)
    let route ← RuntimeAccessPartition.readActiveExit opening.route returned.val
    let whole := wholeOutputs access
    let after : SourceState := {child with
      bindings := route.restored.map (fun binding => {binding with owner := restoredRole whole binding.owner})}
    if roles : (after.bindings.map (·.owner)).Perm expected then
      let inputs ← NaturalAffine.witness (portList (inputRoles access) before.bindings)
      let outputs ← NaturalAffine.witness (portList (outputRoles access) after.bindings)
      let size := routeCount access
      let outer ← RuntimeInterval.check block (start-size) (size+count+size)
      let literal ← RuntimePureInterval.readLiteral outer
        (inputs.val.map (·.token)) (outputs.val.map (·.token)) .unitary
      exactWork (Exact.charge (32*(inputs.val.length+outputs.val.length+1)))
      if ports : literal.val.selected = inputs.val ∧ literal.val.returned = outputs.val then
        let childFrame ← RuntimeOwnerMap.checkBindings (child.bindings.map (·.owner)) interval.after child.bindings
        let afterFrame ← RuntimeOwnerMap.checkBindings (after.bindings.map (·.owner)) literal.val.interval.after after.bindings
        let repartition ← readRepartition child.bindings after.bindings access.returned.retired (indexedParents access)
        let control ← readControl access block start count opening.route.selected returned.val
        return ⟨history.1,history.2.1,history.2.2,childFrame.val,childFrame.property,
          returned.val,by with_reducible exact returned.property,
          route,after,rfl,rfl,rfl,roles,inputs.val,by with_reducible exact inputs.property,
          outputs.val,by with_reducible exact outputs.property,literal.val,ports.1,ports.2,
          afterFrame.val,afterFrame.property,repartition,control⟩
      else throw .request
    else throw .request
  else throw .request

/-- The canonical child sees only the selected owners. Keep the full
issuance history so the ordinary named boundary maps the actual allocation
and retirement ordinals. -/
def selectedState {sources caller dependencies program block start count access interval suspended before}
    (opening : @Opened sources caller dependencies program block start count access interval suspended before) : SourceState :=
  let tokens := opening.route.selected.map (·.token)
  {opening.initial with bindings := opening.initial.bindings.filter (fun binding => tokens.contains binding.port.token)}

/-- Close an actual ordinary branch in a marked call. The independently
checked projection carries only the callee owners, while this receipt checks
the full raw return frame before the original lexical owners are restored. -/
structure BranchClosed {sources caller dependencies program block offset access suspended before ordinary}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    (opening : @Opened sources caller dependencies program block offset 1 access branch.interval suspended before)
    (projected : RuntimeBranchProjection.Checked branch opening.frame (opening.route.selected.map (·.token)) ordinary)
    (child : SourceState) (childRetired : List Owner) (childOrdinary : RuntimeOrdinaryBody.State) where
  onlyExclusive : access.written.exclusive = true
  childIssued : child.issued = opening.initial.issued ++ access.allocated
  childOrdinal : child.nextOrdinal = access.innerOrdinal
  childConsumed : childRetired = access.consumed
  childFrame : RuntimeOwnerMap.Checked
    ((child.bindings ++ projected.moves.map (·.2.original.binding)).map (·.owner)) branch.interval.after
  childBindings : childFrame.bindings = child.bindings ++ projected.moves.map (·.2.original.binding)
  returned : List RawPort
  returnedRead : RuntimeInterval.Computed (portList access.returned.outputs child.bindings) returned
  route : RuntimeAccessPartition.BranchExit opening.route projected returned
  after : SourceState
  bindings : after.bindings = route.restored.bindings.map (fun binding =>
    {binding with owner := restoredRole (wholeOutputs access) binding.owner})
  issued : after.issued = child.issued
  nextOrdinal : after.nextOrdinal = child.nextOrdinal
  afterRoles : (after.bindings.map (·.owner)).Perm
    (visibleHeld access suspended ++ owners access.returned.restored)
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) route.after
  afterBindings : afterFrame.bindings = after.bindings
  repartition : Repartition (child.bindings ++ projected.moves.map (·.2.original.binding)) after.bindings
  finalOrdinary : RuntimeOrdinaryBody.Visible route.after childOrdinary

def readBranchClose {sources caller dependencies program block offset access suspended before ordinary}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    (opening : @Opened sources caller dependencies program block offset 1 access branch.interval suspended before)
    (projected : RuntimeBranchProjection.Checked branch opening.frame (opening.route.selected.map (·.token)) ordinary)
    (child : SourceState) (childRetired : List Owner) (childOrdinary : RuntimeOrdinaryBody.State) :
    WorkM (BranchClosed opening projected child childRetired childOrdinary) := do
  let expected := visibleHeld access suspended ++ owners access.returned.restored
  let inner := child.bindings ++ projected.moves.map (·.2.original.binding)
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (child.issued ++ opening.initial.issued ++
    access.reservation.temporary ++ access.allocated ++ access.consumed ++ access.returned.outputs ++
    childRetired ++ expected ++ inner.map (·.owner))+1)*
    (before.bindings.length+child.bindings.length+access.checked.entries.length+inner.length+1)))
  if history : access.written.exclusive = true ∧ child.issued = opening.initial.issued ++ access.allocated ∧
      child.nextOrdinal = access.innerOrdinal ∧ childRetired = access.consumed then
    let childFrame ← RuntimeOwnerMap.checkBindings (inner.map (·.owner)) branch.interval.after inner
    let returned ← NaturalAffine.witness (portList access.returned.outputs child.bindings)
    let route ← RuntimeAccessPartition.readBranchExit opening.route projected returned.val
    let whole := wholeOutputs access
    let after : SourceState := {child with
      bindings := route.restored.bindings.map (fun binding => {binding with owner := restoredRole whole binding.owner})}
    if roles : (after.bindings.map (·.owner)).Perm expected then
      let afterFrame ← RuntimeOwnerMap.checkBindings (after.bindings.map (·.owner)) route.after after.bindings
      let repartition ← readRepartition inner after.bindings access.returned.retired (indexedParents access)
      let visible ← RuntimeOrdinaryBody.readVisible route.after childOrdinary
      return ⟨history.1,history.2.1,history.2.2.1,history.2.2.2,childFrame.val,childFrame.property,
        returned.val,by with_reducible exact returned.property,route,after,rfl,rfl,rfl,roles,
        afterFrame.val,afterFrame.property,repartition,visible⟩
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeExclusiveAction
