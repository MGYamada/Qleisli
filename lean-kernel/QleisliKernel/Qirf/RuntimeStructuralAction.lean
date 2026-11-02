import QleisliKernel.Qirf.RuntimeOwnerMap
import QleisliKernel.SourceTypes.SourceRuntimeContext
import QleisliKernel.Raw.Coefficient

/-! Concrete explicit owner regrouping in an original runtime interval.
Join/split retain different owner and source-type boundaries. Only their
selected code-coordinate forests agree, by the actual explicit source form;
neither equal width nor implicit reassociation supplies this transport.
Unit creation/release retain distinct zero-width identities. The literal Raw
step has no quantum events, so it changes neither coefficients nor phase on
any caller/reference state. Complete body/history composition remains required;
this component alone grants no execution, inverse or controlled capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeStructuralAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues RuntimeOwnerMap

inductive Kind where
  | join | split | unit | finish
  deriving BEq, DecidableEq

def Kind.primitive : Kind → CallName.Primitive
  | .join => .join | .split => .split | .unit => .unit | .finish => .finish

def atomBits : Semantics.FiniteCarrier.Atom → Nat
  | .bit => 1
  | .bits bits => bits
  | .enumeration _ variants => Semantics.FiniteCarrier.tagBits variants.length
  | _ => 0

/-- Width reservation visits the full existing source tree without enumerating
its labels or building its code matrix. Exact type/owner trees stay retained. -/
def basisBits (basis : Semantics.FiniteCarrier.Basis) : Nat := (basis.map atomBits).sum

private def stackBits (stack : List Semantics.FiniteCarrier.Layout) : Nat := (stack.map (·.bits)).sum

private theorem tensorBits (stack : List Semantics.FiniteCarrier.Layout) (initial : Semantics.FiniteCarrier.Layout) :
    (stack.foldl Semantics.FiniteCarrier.tensor initial).bits = initial.bits+stackBits stack := by
  induction stack generalizing initial with
  | nil => simp [stackBits]
  | cons first rest ih =>
    simp only [List.foldl_cons,ih,Semantics.FiniteCarrier.tensor,stackBits,List.map_cons,List.sum_cons]
    omega

private theorem branchBits (arity : Nat) (before after : List Semantics.FiniteCarrier.Layout)
    (read : (if arity > before.length then none else
      some ((before.take arity).foldl Semantics.FiniteCarrier.tensor Semantics.FiniteCarrier.singleton ::
        before.drop arity)) = some after) : stackBits after = stackBits before := by
  by_cases tooMany : arity > before.length
  · simp [tooMany] at read
  · simp only [tooMany,if_false,Option.some.injEq] at read
    subst after
    have split := congrArg stackBits (List.take_append_drop arity before)
    simp only [stackBits,List.map_append,List.sum_append] at split
    simpa only [stackBits,List.map_cons,List.sum_cons,tensorBits,Semantics.FiniteCarrier.singleton,
      Nat.zero_add] using split

private theorem stepBits (atom : Semantics.FiniteCarrier.Atom)
    (before after : List Semantics.FiniteCarrier.Layout)
    (read : Semantics.FiniteCarrier.layoutStep atom (some before) = some after) :
    stackBits after = atomBits atom+stackBits before := by
  cases atom with
  | unit =>
    simp only [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children,
      Semantics.FiniteCarrier.leaf,bind,Option.bind,pure,Option.pure,Option.some.injEq] at read
    subst after
    simp [stackBits,atomBits,Semantics.FiniteCarrier.singleton]
  | bit =>
    simp only [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children,
      Semantics.FiniteCarrier.leaf,bind,Option.bind,pure,Option.pure,Option.some.injEq] at read
    subst after
    rfl
  | bits width =>
    simp only [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children,
      Semantics.FiniteCarrier.leaf,bind,Option.bind,pure,Option.pure,Option.some.injEq] at read
    subst after
    rfl
  | enumeration _origin variants =>
    by_cases empty : variants.isEmpty = true
    · simp [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children,
        Semantics.FiniteCarrier.leaf,empty] at read
    · simp [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children,
        Semantics.FiniteCarrier.leaf,empty] at read
      subst after
      rfl
  | pair =>
    have result := branchBits 2 before after (by
      simpa [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children] using read)
    simpa [atomBits] using result
  | tuple arity =>
    have result := branchBits arity before after (by
      simpa [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children] using read)
    simpa [atomBits] using result
  | record _origin fields =>
    have result := branchBits fields.length before after (by
      simpa [Semantics.FiniteCarrier.layoutStep,Semantics.FiniteCarrier.children] using read)
    simpa [atomBits] using result

private theorem foldedBits (basis : Semantics.FiniteCarrier.Basis)
    (before after : List Semantics.FiniteCarrier.Layout)
    (read : basis.foldr Semantics.FiniteCarrier.layoutStep (some before) = some after) :
    stackBits after = basisBits basis+stackBits before := by
  induction basis generalizing after with
  | nil =>
    simp only [List.foldr_nil,Option.some.injEq] at read
    subst after
    simp [basisBits]
  | cons atom rest ih =>
    cases tailRead : rest.foldr Semantics.FiniteCarrier.layoutStep (some before) with
    | none => simp [List.foldr_cons,tailRead,Semantics.FiniteCarrier.layoutStep] at read
    | some middle =>
      have head : Semantics.FiniteCarrier.layoutStep atom (some middle) = some after := by
        simpa only [List.foldr_cons,tailRead] using read
      have first := stepBits atom middle after head
      have tail := ih middle tailRead
      simp only [basisBits,List.map_cons,List.sum_cons]
      rw [first,tail]
      omega

/-- The scalar width reader agrees with the existing independent full prefix
interpretation for every successful layout. The proof never expands a concrete
large label set or code matrix. -/
theorem basisBits_reference (basis : Semantics.FiniteCarrier.Basis) (layout : Semantics.FiniteCarrier.Layout)
    (read : Semantics.FiniteCarrier.layout basis = some layout) : layout.bits = basisBits basis := by
  unfold Semantics.FiniteCarrier.layout at read
  cases folded : basis.foldr Semantics.FiniteCarrier.layoutStep (some []) with
  | none => simp [folded] at read
  | some stack =>
    cases stack with
    | nil => simp [folded] at read
    | cons first rest =>
      cases rest with
      | cons second rest => simp [folded] at read
      | nil =>
        simp only [folded,bind,Option.bind,pure,Option.pure,Option.some.injEq] at read
        subst layout
        have width := foldedBits basis [] [first] folded
        simpa [stackBits] using width

structure SourceState where
  bindings : Map
  issued : List Owner
  nextOrdinal : Nat

def sourceShape {sources caller} (event : SourceRuntimeContext.PrimitiveEvent sources caller) (kind : Kind) : Bool :=
  event.kind == kind.primitive && match kind,event.arguments,event.value with
  | .join,[[.owner first],[.owner second]],[.owner result] =>
    first.ordinal != second.ordinal && result.basis == .pair :: first.basis ++ second.basis
  | .split,[[.owner input]],[.tuple 2,.owner left,.owner right] =>
    input.basis == .pair :: left.basis ++ right.basis
  | .unit,[[.ordinary basis _]],[.owner result] => basis == [.unit] && result.basis == [.unit]
  | .finish,[[.owner input]],[.ordinary basis _] => input.basis == [.unit] && basis == [.unit]
  | _,_,_ => false

private def outputTokens (kind : Kind) (operation : Semantics.Raw.Op)
    (inputs : List Semantics.Raw.Port) (outputs : List Owner) : Except Finite.Error (List Nat) := do
  match kind,operation,inputs,outputs with
  | .join,.join left right output,[first,second],[_] =>
    if left == first.token && right == second.token then pure [output] else throw .request
  | .split,.split input left right leftBits,[port],[first,_] =>
    if input == port.token && leftBits == basisBits first.basis then pure [left,right] else throw .request
  | .unit,.packUnit output,[],[_] => pure [output]
  | .finish,.unpackUnit input,[port],[] =>
    if input == port.token && port.bits == 0 && port.wires.isEmpty then pure [] else throw .request
  | _,_,_,_ => throw .request

def owners (ports : List Semantics.Raw.Port) (roles : List Owner) : List Semantics.CarrierInterface.Owner :=
  (ports.zip roles).map fun (port,role) => ⟨port,role.basis⟩

def widths (ports : List Semantics.Raw.Port) (roles : List Owner) : Bool :=
  ports.length == roles.length && (ports.zip roles).all fun (port,role) =>
    port.bits == basisBits role.basis && port.wires.length == port.bits

theorem widths_reference (ports : List Semantics.Raw.Port) (roles : List Owner)
    (checked : widths ports roles = true) (port : Semantics.Raw.Port) (role : Owner)
    (member : (port,role) ∈ ports.zip roles) (layout : Semantics.FiniteCarrier.Layout)
    (read : Semantics.FiniteCarrier.layout role.basis = some layout) :
    port.bits = layout.bits ∧ port.wires.length = layout.bits := by
  have all := (Bool.and_eq_true.mp checked).2
  have good := List.all_eq_true.mp all (port,role) member
  have fields := Bool.and_eq_true.mp good
  have bits : port.bits = basisBits role.basis := beq_iff_eq.mp fields.1
  have wires : port.wires.length = port.bits := beq_iff_eq.mp fields.2
  have same := basisBits_reference role.basis layout read
  exact ⟨bits.trans same.symm,wires.trans (bits.trans same.symm)⟩

structure Checked {dependencies program sources caller}
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller) (before : SourceState) where
  kind : Kind
  source : sourceShape event kind = true
  interval : RuntimeInterval.Checked block start count
  operation : Semantics.Raw.Op
  literal : (block.operations.drop start).take count = [.pure operation]
  inputRoles : List Owner
  originalInputs : inputRoles = event.arguments.flatMap valueOwners
  outputRoles : List Owner
  originalOutputs : outputRoles = valueOwners event.value
  allocated : event.allocated = outputRoles
  consumed : event.consumed = inputRoles
  issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal
  liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true
  fresh : outputRoles.map (·.ordinal) = (List.range outputRoles.length).map (before.nextOrdinal+·)
  nextOrdinal : event.nextOrdinal = before.nextOrdinal+outputRoles.length
  beforeFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  inputs : List Semantics.Raw.Port
  inputRead : RuntimeInterval.Computed (do
    let bound ← RuntimeOwnerMap.order inputRoles before.bindings
    pure (bound.map (·.port))) inputs
  outputs : List Semantics.Raw.Port
  outputRead : PureInterval.ports interval.after (outputs.map (·.token)) = some outputs
  inputWidths : widths inputs inputRoles = true
  outputWidths : widths outputs outputRoles = true
  coordinates : Semantics.CarrierInterface.forest (owners inputs inputRoles) =
    Semantics.CarrierInterface.forest (owners outputs outputRoles)
  spectators : PureInterval.spectators interval.before (inputs.map (·.token)) =
    PureInterval.spectators interval.after (outputs.map (·.token))
  reference : Semantics.RawTrace.step interval.before.quantum.reference operation =
    some (interval.after.quantum.reference,[])
  after : SourceState
  afterBindings : after.bindings = before.bindings.filter (fun binding => !inputRoles.contains binding.owner) ++
    (outputRoles.zip outputs).map (fun (owner,port) => ⟨owner,port⟩)
  afterIssued : after.issued = before.issued ++ outputRoles
  afterOrdinal : after.nextOrdinal = event.nextOrdinal
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) interval.after

def read {dependencies program sources caller}
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller) (before : SourceState) :
    WorkM (Checked block start count event before) := do
  let kind ← match event.kind with
    | .join => pure Kind.join | .split => pure Kind.split
    | .unit => pure Kind.unit | .finish => pure Kind.finish
    | _ => throw .request
  exactWork (Exact.charge (64*(valueFields event.value+(event.arguments.map valueFields).sum+
    Raw.OwnerFlow.fields before.issued+Raw.OwnerFlow.fields (before.bindings.map (·.owner))+
    before.nextOrdinal+before.bindings.length+block.operations.length+1)))
  if source : sourceShape event kind = true then
    let interval ← RuntimeInterval.check block start count
    match literal : (block.operations.drop start).take count with
    | [.pure operation] =>
      let inputRoles := event.arguments.flatMap valueOwners
      let outputRoles := valueOwners event.value
      if allocated : event.allocated = outputRoles then
        if consumed : event.consumed = inputRoles then
          if issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal then
            if liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true then
              if fresh : outputRoles.map (·.ordinal) = (List.range outputRoles.length).map (before.nextOrdinal+·) then
                if nextOrdinal : event.nextOrdinal = before.nextOrdinal+outputRoles.length then
                  let beforeFrame ← RuntimeOwnerMap.check (before.bindings.map (·.owner)) interval.before before.bindings
                  let inputs ← NaturalAffine.witness (do
                    let bound ← RuntimeOwnerMap.order inputRoles before.bindings
                    pure (bound.map (·.port)))
                  let tokens ← lift (outputTokens kind operation inputs.val outputRoles)
                  match _outputRead : PureInterval.ports interval.after tokens with
                  | none => throw .request
                  | some outputs =>
                    -- Ports are retrieved by the actual Raw destinations;
                    -- source identities never come from width/wire matching.
                    guard (outputs.map (·.token) == tokens) .request
                    match returned : PureInterval.ports interval.after (outputs.map (·.token)) with
                    | none => throw .request
                    | some actualOutputs =>
                      if sameOutputs : actualOutputs = outputs then
                        if inputWidths : widths inputs.val inputRoles = true then
                          if outputWidths : widths outputs outputRoles = true then
                            if coordinates : Semantics.CarrierInterface.forest (owners inputs.val inputRoles) =
                                Semantics.CarrierInterface.forest (owners outputs outputRoles) then
                              if spectators : PureInterval.spectators interval.before (inputs.val.map (·.token)) =
                                  PureInterval.spectators interval.after (outputs.map (·.token)) then
                                if reference : Semantics.RawTrace.step interval.before.quantum.reference operation =
                                    some (interval.after.quantum.reference,[]) then
                                  let assigned := before.bindings.filter (fun binding => !inputRoles.contains binding.owner) ++
                                    (outputRoles.zip outputs).map (fun (owner,port) => (⟨owner,port⟩ : Binding))
                                  let after : SourceState := ⟨assigned,before.issued ++ outputRoles,event.nextOrdinal⟩
                                  let afterFrame ← RuntimeOwnerMap.check (after.bindings.map (·.owner)) interval.after after.bindings
                                  return ⟨kind,source,interval,operation,literal,inputRoles,rfl,outputRoles,rfl,
                                    allocated,consumed,issued,liveIssued,fresh,nextOrdinal,beforeFrame,inputs.val,
                                    by with_reducible exact inputs.property,outputs,by simpa only [sameOutputs] using returned,
                                    inputWidths,outputWidths,coordinates,spectators,reference,after,rfl,rfl,rfl,afterFrame⟩
                                else throw .request
                              else throw .request
                            else throw .request
                          else throw .request
                        else throw .request
                      else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    | _ => throw .request
  else throw .request

/-- Every issued source identity is retained after consumption. The next
structural event therefore starts the same complete canonical history. -/
theorem Checked.history {dependencies program sources caller block start count event before}
    (checked : @Checked dependencies program sources caller block start count event before) :
    checked.after.issued.map (·.ordinal) = List.range checked.after.nextOrdinal := by
  rw [checked.afterIssued,List.map_append,checked.issued,checked.fresh,checked.afterOrdinal,checked.nextOrdinal]
  exact List.range_add.symm

theorem Checked.noRevival {dependencies program sources caller block start count event before}
    (checked : @Checked dependencies program sources caller block start count event before)
    (created : Owner) (newMember : created ∈ checked.outputRoles) (old : Owner) (oldMember : old ∈ before.issued) :
    created.ordinal ≠ old.ordinal := by
  intro same
  have freshMember : created.ordinal ∈ checked.outputRoles.map (·.ordinal) :=
    List.mem_map.mpr ⟨created,newMember,rfl⟩
  rw [checked.fresh] at freshMember
  obtain ⟨offset,_bound,ordinal⟩ := List.mem_map.mp freshMember
  have previous : old.ordinal ∈ before.issued.map (·.ordinal) := List.mem_map.mpr ⟨old,oldMember,rfl⟩
  rw [checked.issued] at previous
  have bound := List.mem_range.mp previous
  omega

/-- The existing independent code interpretation is the same expression on
both sides. This proof constructs no combined labels or dense matrix. Distinct
runtime/source owner lists remain in the checked action above. -/
theorem Checked.codeCoordinates {dependencies program sources caller block start count event before}
    (checked : @Checked dependencies program sources caller block start count event before) :
    (Semantics.FiniteCarrier.layout (Semantics.CarrierInterface.forest (owners checked.inputs checked.inputRoles))).map
        Semantics.FiniteCarrier.encoding =
      (Semantics.FiniteCarrier.layout (Semantics.CarrierInterface.forest (owners checked.outputs checked.outputRoles))).map
        Semantics.FiniteCarrier.encoding := by
  rw [checked.coordinates]

/-- The actual original Raw step contributes no quantum event on any lazy
coefficient function, including functions encoding entangled references. -/
theorem Checked.coefficients {dependencies program sources caller block start count event before}
    (checked : @Checked dependencies program sources caller block start count event before)
    (values : Raw.Coefficient.State) :
    (Semantics.RawTrace.step checked.interval.before.quantum.reference checked.operation).map
      (fun (_,events) => events.foldl (fun state action => Raw.Coefficient.event dependencies action state) values) =
      some values := by
  rw [checked.reference]
  rfl

end QleisliKernel.Qirf.RuntimeStructuralAction
