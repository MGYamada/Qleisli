import QleisliKernel.Qirf.RuntimeOrdinaryBody
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.RuntimeFamily
import QleisliKernel.SourceTypes.SourceRuntimeNominalValue

/-! Actual retained ordinary inputs for the single original runtime body loop.
The existing exact Body, prepared Raw root and typed input boundary are reused.
All original input fields, including zero-width and nominal fields, receive
their exact logical ordinal. Symbolic SSA bits use the complete carrier code;
physical width alone never identifies a type or source value. Canonical rows
are independently enumerated under the existing ordinary-domain limits.
No source/root reread, joined quantum matrix or accepted handle is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOrdinaryInputs
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOrdinarySSA
abbrev Basis := Semantics.FiniteCarrier.Basis
abbrev Stored := Semantics.RuntimeStorage.Value

def codeBit (labels : List Nat) (coordinate : Nat) (logical : Expression) : Expression :=
  labels.zipIdx.foldr (fun (code,ordinal) rest =>
    .choose (.equalsOrdinal ordinal logical) (.bit ((code / 2^coordinate) % 2 == 1)) rest) (.bit false)

private def align (bindings : RuntimeOwnerMap.Map) (stored : Stored) :
    SourceRuntimeValues.Value → WorkM (Table × SourceRuntimeValues.Value) :=
  WellFounded.fix (measure (fun current : Stored => sizeOf current)).wf
    (C := fun _ => SourceRuntimeValues.Value → WorkM (Table × SourceRuntimeValues.Value))
    (fun current => match current with
      | [] => fun _ source => pure ([],source)
      | stored :: rest => fun visit source => do
        exactWork (Exact.charge (32*(SourceRuntimeValues.valueFields source+bindings.length+1)))
        match stored with
        | .tuple arity =>
          let .tuple sourceArity :: source := source | throw .request
          guard (sourceArity == arity) .request
          visit rest (by decreasing_tactic) source
        | .quantum owner =>
          let .owner role :: source := source | throw .request
          let some binding := RuntimeOwnerMap.byOwner bindings role | throw .request
          guard (binding.owner == role && binding.port == owner.port && role.basis == owner.basis) .request
          visit rest (by decreasing_tactic) source
        | .ordinary basis storage =>
          let (subtree,source) ← lift ((SourceRuntimeValues.splitValue source).mapError fun _ => .request)
          let (actual,logical) ← lift ((SourceRuntimeNominalValue.collapse subtree).mapError fun _ => .request)
          guard (actual == basis) .request
          let layout ← FiniteCarrier.read basis
          let ids ← OrdinaryFamily.storageIds [storage]
          guard (ids.length == layout.bits) .request
          exactWork (Exact.charge (32*(layout.labels.length+1)*(layout.bits+1)*
            (SourceRuntimeValues.expressionFields logical+SourceRuntimeValues.expressionSize logical+1)))
          let current := ids.zipIdx.map fun (id,coordinate) => (id,codeBit layout.labels coordinate logical)
          let (tail,source) ← visit rest (by decreasing_tactic) source
          return (current ++ tail,source)) stored

def alignInputs (bindings : RuntimeOwnerMap.Map) (sources : List SourceRuntimeValues.Value) :
    List Stored → WorkM Table :=
  WellFounded.fix (measure (fun current : List SourceRuntimeValues.Value => sizeOf current)).wf
    (C := fun _ => List Stored → WorkM Table) (fun current => match current with
      | [] => fun _ stores => match stores with | [] => pure [] | _ => throw .request
      | source :: sources => fun visit stores => do
        let stored :: stores := stores | throw .request
        let (current,rest) ← align bindings stored source
        guard rest.isEmpty .request
        let tail ← visit sources (by decreasing_tactic) stores
        return current ++ tail) sources

structure Field (entry : Basis × Expression) where
  ordinal : Nat
  seeded : entry.2 = .input ordinal
  layout : Semantics.FiniteCarrier.Layout
  original : RuntimeInterval.Computed (FiniteCarrier.read entry.1) layout

abbrev Fields := List ((entry : Basis × Expression) × Field entry)

def readFields (entries : List (Basis × Expression)) : WorkM Fields :=
  entries.zipIdx.mapM fun (entry,index) => do
    if seeded : entry.2 = .input index then
      let layout ← NaturalAffine.witness (FiniteCarrier.read entry.1)
      return ⟨entry,⟨index,seeded,layout.val,by with_reducible exact layout.property⟩⟩
    else throw .request

def decode (fields : Fields) : List Bool → WorkM (List Nat) :=
  WellFounded.fix (measure (fun current : Fields => sizeOf current)).wf
    (C := fun _ => List Bool → WorkM (List Nat)) (fun current => match current with
      | [] => fun _ bits => do
        guard bits.isEmpty .request
        pure []
      | field :: fields => fun visit bits => do
        exactWork (Exact.charge (32*(field.2.layout.labels.length+bits.length+1)))
        guard (field.2.layout.bits ≤ bits.length) .request
        let code := Semantics.OrdinaryValue.littleEndian (bits.take field.2.layout.bits)
        let ordinal := field.2.layout.labels.idxOf code
        guard (field.2.layout.labels[ordinal]? == some code) .equation
        let tail ← visit fields (by decreasing_tactic) (bits.drop field.2.layout.bits)
        return ordinal :: tail) fields

structure Checked {sources owner name signature dependencies program}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (prepared : RuntimeInterval.Prepared dependencies program) (runtime : RuntimeFamily.Request)
    (inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage) where
  table : Table
  aligned : RuntimeInterval.Computed (alignInputs inputs.owners.bindings
    (RuntimeSourceBoundary.summary body).parameterValues runtime.inputStorage) table
  actualIds : table.map Prod.fst = program.classicalInputs
  fields : Fields
  originalFields : fields.map Sigma.fst =
    (RuntimeSourceBoundary.summary body).parameterValues.flatMap SourceRuntimeValues.ordinary
  canonical : fields.map (fun field => field.2.ordinal) = List.range fields.length
  domain : OrdinaryDomain.Checked ((RuntimeFamily.inputValues runtime).map Prod.fst)
  sourceCode : Semantics.OrdinaryInputs.forest
    (((RuntimeSourceBoundary.summary body).parameterValues.flatMap SourceRuntimeValues.ordinary).map Prod.fst) =
      some domain.code
  supplied : runtime.inputRows = OrdinaryDomain.assignments domain

def Checked.ssa {sources owner name signature dependencies program body prepared runtime inputs}
    (checked : @Checked sources owner name signature dependencies program body prepared runtime inputs) :
    RuntimeOrdinaryBody.State := ⟨checked.table,[]⟩

/-- Derive initial SSA from the same complete source/storage forest already
bound to this root. The internal source field forest may contain more atomic
Unit fields than the stored block forest; no new field-count cap erases them. -/
def read {sources owner name signature dependencies program}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (prepared : RuntimeInterval.Prepared dependencies program) (runtime : RuntimeFamily.Request)
    (inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage) :
    WorkM (Checked body prepared runtime inputs) := do
  let source := RuntimeSourceBoundary.summary body
  exactWork (Exact.charge (32*((source.parameterValues.map SourceRuntimeValues.valueFields).sum+
    runtime.inputStorage.length+program.classicalInputs.length+1)))
  let table ← NaturalAffine.witness (alignInputs inputs.owners.bindings source.parameterValues runtime.inputStorage)
  if actualIds : table.val.map Prod.fst = program.classicalInputs then
    let entries := source.parameterValues.flatMap SourceRuntimeValues.ordinary
    let fields ← readFields entries
    if originalFields : fields.map Sigma.fst = entries then
      if canonical : fields.map (fun field => field.2.ordinal) = List.range fields.length then
        let domain ← OrdinaryDomain.read ((RuntimeFamily.inputValues runtime).map Prod.fst)
        -- Bound the independent source forest before it enumerates any product
        -- labels, preserving the existing six classical input-bit domain.
        guard ((fields.map fun field => field.2.layout.bits).sum ≤ 6 &&
          (fields.map fun field => field.2.layout.labels.length).foldl (·*·) 1 ≤ 64) .limit
        exactWork (Exact.charge (32*(fields.length+1)*(domain.code.labels.length+1)))
        if sourceCode : Semantics.OrdinaryInputs.forest (entries.map Prod.fst) = some domain.code then
          if supplied : runtime.inputRows = OrdinaryDomain.assignments domain then
            return ⟨table.val,by with_reducible exact table.property,actualIds,fields,originalFields,canonical,
              domain,sourceCode,supplied⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

structure Row {sources owner name signature dependencies program body prepared runtime inputs}
    (checked : @Checked sources owner name signature dependencies program body prepared runtime inputs)
    (assignment : List Bool) where
  originalAssignment : assignment ∈ OrdinaryDomain.assignments checked.domain
  ordinals : List Nat
  decoded : RuntimeInterval.Computed (decode checked.fields assignment) ordinals
  stores : OrdinaryFamily.InputsFor (program.classicalInputs.zip assignment)
    ((RuntimeFamily.inputValues runtime).map Prod.fst) ((RuntimeFamily.inputValues runtime).map Prod.snd)
  agreement : CheckedAgreement (RuntimeOrdinaryBody.valuation ordinals [] (program.classicalInputs.zip assignment))
    (program.classicalInputs.zip assignment) checked.table

/-- Read one member of the independently enumerated complete input domain.
The enclosing all-row gate must consume every canonical assignment, retaining
unused and zero-width original input fields in the ordinal valuation. -/
def readRow {sources owner name signature dependencies program body prepared runtime inputs}
    (checked : @Checked sources owner name signature dependencies program body prepared runtime inputs)
    (assignment : List Bool) : WorkM (Row checked assignment) := do
  exactWork (Exact.charge (32*(checked.domain.code.labels.length+assignment.length+1)))
  if member : assignment ∈ OrdinaryDomain.assignments checked.domain then
    let decoded ← NaturalAffine.witness (decode checked.fields assignment)
    let stores ← OrdinaryFamily.readStores (program.classicalInputs.zip assignment)
      ((RuntimeFamily.inputValues runtime).map Prod.fst) ((RuntimeFamily.inputValues runtime).map Prod.snd)
    let agreement ← RuntimeOrdinarySSA.readAgreement
      (RuntimeOrdinaryBody.valuation decoded.val [] (program.classicalInputs.zip assignment))
      (program.classicalInputs.zip assignment) checked.table
    return ⟨member,decoded.val,by with_reducible exact decoded.property,stores,agreement⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeOrdinaryInputs
