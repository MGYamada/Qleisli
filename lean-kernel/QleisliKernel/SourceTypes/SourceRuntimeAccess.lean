import QleisliKernel.SourceTypes.AccessSyntax
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceRuntimeOrdinary

/-! Closed quantum access places from the original lexical scope. Each place
retains its written selector, exact live parent and checked finite interval.
Actual extraction, call, control sectors and reassembly belong to the
enclosing Raw check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeAccess
open QleisliKernel Finite SourceRuntimeValues
open AccessSyntax (Argument Natural Selection)
open QleisliKernel.Semantics.SourceOwners (Owner)
open QleisliKernel.Semantics.FiniteCarrier (Basis)

structure Bound (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (expression : Natural) where
  valid : ∃ before after,
    (PhaseApplication.validateNatural sources caller naturals scope expression).run before = (.ok (),after)
  concrete : LexicalNatural.Checked sources caller naturals.helpers.val naturals.environment scope expression
  rows : List (String × String)
  retained : ∃ before after,
    (NaturalRows.bindings sources caller naturals.helpers.val concrete.bindings.val).run before = (.ok rows,after)

private def readBound (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (expression : Natural) : WorkM (Bound sources caller naturals scope expression) := do
  let valid ← NaturalAffine.witness (PhaseApplication.validateNatural sources caller naturals scope expression)
  let concrete ← LexicalNatural.read sources caller naturals.helpers.val naturals.environment scope expression
  let rows ← NaturalAffine.witness (NaturalRows.bindings sources caller naturals.helpers.val concrete.bindings.val)
  have unit : valid.val = () := by cases valid.val; rfl
  return ⟨by with_reducible simpa only [unit] using valid.property,
    concrete,rows.val,by with_reducible exact rows.property⟩

inductive Coordinates {sources : Sources} (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (parent : Owner) : Selection → Type where
  | whole : Coordinates caller naturals scope parent .whole
  | index {expression : Natural} (width : Nat) (register : parent.basis = [.bits width])
      (axis : Bound sources caller naturals scope expression) (inside : axis.concrete.result.value < width) :
      Coordinates caller naturals scope parent (.index expression)
  | slice {first last : Natural} (width : Nat) (register : parent.basis = [.bits width])
      (start : Bound sources caller naturals scope first) (stop : Bound sources caller naturals scope last)
      (ordered : start.concrete.result.value ≤ stop.concrete.result.value)
      (inside : stop.concrete.result.value ≤ width) :
      Coordinates caller naturals scope parent (.slice first last)

def Coordinates.range {sources caller naturals scope parent selection} :
    @Coordinates sources caller naturals scope parent selection → Option (Nat × Nat)
  | .whole => none
  | .index _ _ axis _ => some (axis.concrete.result.value,axis.concrete.result.value+1)
  | .slice _ _ start stop _ _ => some (start.concrete.result.value,stop.concrete.result.value)

def Coordinates.basis {sources caller naturals scope parent selection} :
    @Coordinates sources caller naturals scope parent selection → Basis
  | .whole => parent.basis
  | .index .. => [.bit]
  | .slice _ _ start stop _ _ => [.bits (stop.concrete.result.value-start.concrete.result.value)]

def Coordinates.rows {sources caller naturals scope parent selection} :
    @Coordinates sources caller naturals scope parent selection → List (String × String)
  | .whole => []
  | .index _ _ axis _ => axis.rows
  | .slice _ _ start stop _ _ => start.rows ++ stop.rows

private def readCoordinates (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (parent : Owner) : (selection : Selection) → WorkM (Coordinates caller naturals scope parent selection)
  | .whole => pure .whole
  | .index expression => do
    match register : parent.basis with
    | [.bits width] =>
      let axis ← readBound sources caller naturals scope expression
      if inside : axis.concrete.result.value < width then
        pure (.index width register axis inside)
      else throw .request
    | _ => throw .request
  | .slice first last => do
    match register : parent.basis with
    | [.bits width] =>
      let start ← readBound sources caller naturals scope first
      let stop ← readBound sources caller naturals scope last
      if inside : start.concrete.result.value ≤ stop.concrete.result.value ∧ stop.concrete.result.value ≤ width then
        pure (.slice width register start stop inside.1 inside.2)
      else throw .request
    | _ => throw .request

structure Place (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (environment : Environment) (written : Sigma Argument) where
  cell : Cell
  binding : environment.find? (fun current => current.name == written.2.owner.text) = some cell
  parent : Owner
  owned : cell.value = [.owner parent]
  coordinates : Coordinates caller naturals scope parent written.2.selection

private def readPlace (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (environment : Environment) (written : Sigma Argument) :
    WorkM (Place sources caller naturals scope environment written) := do
  match binding : environment.find? (fun cell => cell.name == written.2.owner.text) with
  | none => throw .request
  | some cell =>
    match owned : cell.value with
    | [.owner parent] =>
      let coordinates ← readCoordinates sources caller naturals scope parent written.2.selection
      return ⟨cell,binding,parent,owned,coordinates⟩
    | _ => throw .request

abbrev Entry (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (environment : Environment) :=
  Sigma (Place sources caller naturals scope environment)

def compatible {sources caller naturals scope environment}
    (first second : Entry sources caller naturals scope environment) : Bool :=
  first.2.parent.ordinal != second.2.parent.ordinal ||
    (first.2.cell.name == second.2.cell.name &&
      match first.2.coordinates.range,second.2.coordinates.range with
      | some (start,stop),some (otherStart,otherStop) =>
        stop ≤ start || otherStop ≤ otherStart || stop ≤ otherStart || otherStop ≤ start
      | _,_ => false)

private def allCompatible {sources caller naturals scope environment}
    (entries : List (Entry sources caller naturals scope environment)) : Bool :=
  let visit : Nat → List (Entry sources caller naturals scope environment) → Bool :=
    Nat.rec (·.isEmpty) (fun _ next entries =>
      match entries with
      | [] => true
      | entry :: rest => if rest.all (compatible entry) then next rest else false)
  visit entries.length entries

private def ordered (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (environment : Environment) (arguments : List (Sigma Argument)) :
    WorkM (List (Entry sources caller naturals scope environment)) :=
  arguments.mapM fun argument => do
    let place ← readPlace sources caller naturals scope environment argument
    return ⟨argument,place⟩

structure Checked (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (environment : Environment) {tokens : List LocatedToken}
    (written : AccessSyntax.CheckedAccessCall tokens) where
  entries : List (Entry sources caller naturals scope environment)
  original : ∃ before after,
    (ordered sources caller naturals scope environment written.arguments).run before = (.ok entries,after)
  disjoint : allCompatible entries = true

def read (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) (environment : Environment) {tokens : List LocatedToken}
    (written : AccessSyntax.CheckedAccessCall tokens) : WorkM (Checked sources caller naturals scope environment written) := do
  let count := written.arguments.length
  let names := (written.arguments.map (fun argument => argument.2.owner.text.utf8ByteSize)).sum
  let cells := (environment.map (fun cell => cell.name.utf8ByteSize+1)).sum
  exactWork (Exact.charge (16*((count+1)*(count+cells+1)+names*(environment.length+1))))
  let entries ← NaturalAffine.witness (ordered sources caller naturals scope environment written.arguments)
  if disjoint : allCompatible entries.val = true then
    return ⟨entries.val,by with_reducible exact entries.property,disjoint⟩
  else throw .request

structure Issued where
  arguments : List Owner := []
  temporary : List Owner := []
  nextOrdinal : Nat
  remainders : List (Owner × Owner) := []

private def issueArguments {sources caller naturals scope environment}
    (nextOrdinal : Nat) (entries : List (Entry sources caller naturals scope environment)) : Issued :=
  entries.foldl
    (fun state entry =>
      match entry.2.coordinates.range with
      | none => {state with arguments := entry.2.parent :: state.arguments}
      | some _ =>
        let argument : Owner := ⟨state.nextOrdinal,entry.2.coordinates.basis⟩
        {state with
          arguments := argument :: state.arguments
          temporary := argument :: state.temporary
          nextOrdinal := state.nextOrdinal+1})
    {nextOrdinal}

private def issue {sources caller naturals scope environment}
    (nextOrdinal : Nat) (entries : List (Entry sources caller naturals scope environment)) : Option Issued := do
  let selected := entries.filterMap fun entry =>
    entry.2.coordinates.range.map fun (start,stop) => (entry.2.parent,stop-start)
  let parents := (selected.map (·.1)).eraseDups
  parents.foldlM (fun state parent => do
    let [.bits width] := parent.basis | none
    let held := (selected.filterMap fun (owner,size) =>
      if owner.ordinal == parent.ordinal then some size else none).sum
    if held > width then none else
      let remainder : Owner := ⟨state.nextOrdinal,[.bits (width-held)]⟩
      pure {state with
        temporary := remainder :: state.temporary
        nextOrdinal := state.nextOrdinal+1
        remainders := (parent,remainder) :: state.remainders}) (issueArguments nextOrdinal entries)

private def parentNames {sources caller naturals scope environment}
    (entries : List (Entry sources caller naturals scope environment)) : List String :=
  entries.map (·.2.cell.name)

private def suspend (names : List String) (environment : Environment) : Environment :=
  environment.filter (fun cell => !names.contains cell.name)

structure Reservation {sources caller naturals scope environment tokens}
    {written : AccessSyntax.CheckedAccessCall tokens} (access : Checked sources caller naturals scope environment written)
    (nextOrdinal : Nat) where
  issued : Issued
  allocated : issue nextOrdinal access.entries = some issued
  remaining : Environment
  suspended : suspend (parentNames access.entries) environment = remaining

def reserve {sources caller naturals scope environment tokens} {written : AccessSyntax.CheckedAccessCall tokens}
    (access : Checked sources caller naturals scope environment written) (nextOrdinal : Nat) :
    WorkM (Reservation access nextOrdinal) := do
  let names := parentNames access.entries
  exactWork (Exact.charge (16*((environment.map (·.name.utf8ByteSize)).sum+environment.length+1)*(names.length+1)+
    16*((names.map String.utf8ByteSize).sum+1)*(environment.length+1)+32*(names.length+1)^2))
  match allocated : issue nextOrdinal access.entries with
  | some issued => return ⟨issued,allocated,suspend names environment,rfl⟩
  | none => throw .request

def Reservation.arguments {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) : List Owner :=
  reservation.issued.arguments.reverse

def Reservation.temporary {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) : List Owner :=
  reservation.issued.temporary.reverse

def Reservation.remainders {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) : List (Owner × Owner) :=
  reservation.issued.remainders.reverse

structure Activated {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) where
  remaining : Environment
  exactRemaining : remaining =
    reservation.remaining ++ reservation.remainders.filterMap (fun (parent,remainder) =>
      (access.entries.find? (fun entry => entry.2.parent == parent)).map fun entry =>
        {entry.2.cell with value := [.owner remainder]})
  arguments : List Value
  exactArguments : arguments = reservation.arguments.map (fun owner => [.owner owner])
  frame : Environment
  exactFrame : frame =
    remaining ++ (access.entries.zip reservation.arguments).map (fun (entry,owner) =>
      {entry.2.cell with value := [.owner owner]})

/-- The temporary call frame supplies only the selected arguments. The exact
register remainders are parked in the continuation and never resolve as extra
arguments. Their original lexical cells and owner identities are retained. -/
def activate {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) : WorkM (Activated reservation) := do
  let fields := Raw.OwnerFlow.fields (reservation.arguments ++ reservation.temporary)
  exactWork (Exact.charge (16*(fields+access.entries.length+1)*(access.entries.length+1)))
  let parked := reservation.remainders.filterMap (fun (parent,remainder) =>
    (access.entries.find? (fun entry => entry.2.parent == parent)).map fun entry =>
      {entry.2.cell with value := [.owner remainder]})
  guard (parked.length == reservation.remainders.length &&
    reservation.arguments.length == access.entries.length) .request
  let remaining := reservation.remaining ++ parked
  return ⟨remaining,rfl,reservation.arguments.map (fun owner => [.owner owner]),rfl,
    remaining ++ (access.entries.zip reservation.arguments).map (fun (entry,owner) =>
      {entry.2.cell with value := [.owner owner]}),rfl⟩

private def readOrdinaryValue (permitsBit : Bool) (environment : Environment)
    (tokens : List LocatedToken) : Except String Value :=
  (SourceRuntimeOrdinary.readAccessOrdinary permitsBit tokens environment).map (·.value)

/-- The full source argument list and its separate ordered owner projection
are both tied to the same access activation. -/
structure Arguments {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    {reservation : Reservation access nextOrdinal} (activation : Activated reservation) where
  values : List Value
  original : written.fillArguments activation.arguments (readOrdinaryValue written.exclusive environment) = .ok values
  complete : values.length = written.slots.length
  marked : values.flatMap valueOwners = reservation.arguments

def readArguments {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    {reservation : Reservation access nextOrdinal} (activation : Activated reservation) :
    WorkM (Arguments activation) := do
  exactWork (Exact.charge (16*(written.slots.length+(activation.arguments.map valueFields).sum+1)))
  if written.hasOrdinary then
    let fields := (environment.map fun cell => cell.name.utf8ByteSize+valueFields cell.value+2).sum
    let ordinaryTokens := (written.slots.map fun slot =>
      if slot.2.isAccess then 0 else (slot.1.map (fun token => token.text.utf8ByteSize+4)).sum).sum
    exactWork (Exact.charge (32*((written.slots.length+1)*(fields+1)+ordinaryTokens)))
  match original : written.fillArguments activation.arguments (readOrdinaryValue written.exclusive environment) with
  | .error _ => throw .request
  | .ok values =>
    if complete : values.length = written.slots.length then
      if marked : values.flatMap valueOwners = reservation.arguments then
        return ⟨values,original,complete,marked⟩
      else throw .request
    else throw .request

private def outputOwners (count : Nat) (value : Value) : Option (List Owner) := do
  if count == 1 then
    let [.owner owner] := value | none
    return [owner]
  else
    let .tuple arity :: fields := value | none
    if arity != count || fields.length != count then none else
      fields.mapM fun field => match field with | .owner owner => some owner | _ => none

private def restore {sources caller naturals scope environment}
    (entries : List (Entry sources caller naturals scope environment)) (outputs : List Owner) : Environment :=
  let whole := (entries.zip outputs).filterMap fun (entry,owner) =>
    if entry.2.coordinates.range.isNone then some (entry.2.cell.name,owner) else none
  environment.map fun cell => match whole.find? (fun updated => updated.1 == cell.name) with
    | some (_,owner) => {cell with value := [.owner owner]}
    | none => cell

structure Returned {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) (value : Value) where
  outputs : List Owner
  shape : outputOwners reservation.arguments.length value = some outputs
  types : outputs.map (·.basis) = reservation.arguments.map (·.basis)
  restored : Environment
  returned : restore access.entries outputs = restored

/-- Temporary remainders are never supplied as arguments. Returned selected
owners close in their written order before the caller's parents resume. -/
def Returned.retired {sources caller naturals scope environment tokens nextOrdinal value}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    {reservation : Reservation access nextOrdinal} (closed : Returned reservation value) : List Owner :=
  ((access.entries.zip closed.outputs).filterMap (fun (entry,owner) =>
    if entry.2.coordinates.range.isSome then some owner else none)) ++ reservation.remainders.map (·.2)

def close {sources caller naturals scope environment tokens nextOrdinal}
    {written : AccessSyntax.CheckedAccessCall tokens} {access : Checked sources caller naturals scope environment written}
    (reservation : Reservation access nextOrdinal) (value : Value) : WorkM (Returned reservation value) := do
  let count := access.entries.length
  let names := parentNames access.entries
  exactWork (Exact.charge (16*(valueFields value+
    Raw.OwnerFlow.fields reservation.arguments+1)+
    16*((environment.map (·.name.utf8ByteSize)).sum+environment.length+1)*(count+1)+
    16*((names.map String.utf8ByteSize).sum+1)*(environment.length+1)))
  match shape : outputOwners reservation.arguments.length value with
  | none => throw .request
  | some outputs =>
    if types : outputs.map (·.basis) = reservation.arguments.map (·.basis) then
      return ⟨outputs,shape,types,restore access.entries outputs,rfl⟩
    else throw .request

end QleisliKernel.SourceTypes.SourceRuntimeAccess
