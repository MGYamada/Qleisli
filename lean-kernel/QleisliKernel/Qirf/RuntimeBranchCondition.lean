import QleisliKernel.Qirf.RuntimeOrdinaryInputs

/-! Source conditions against actual SSA for authentic ordinary branches.
The original CallPath supplies the complete root input forest. Every canonical
input and every possible already-issued measurement valuation is checked,
including valuations with zero quantum probability. No joined quantum state,
probability selection or producer condition table supplies the reference.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBranchCondition
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes RuntimeOrdinarySSA
abbrev Path := RuntimeOrdinaryBody.CallPath
abbrev Measurement := RuntimeOrdinaryBody.Measurement

def rootEntries {sources rootOwner rootName owner name}
    (path : Path sources rootOwner rootName owner name) : List (Semantics.FiniteCarrier.Basis × Expression) :=
  WellFounded.fix (measure (fun packed : RuntimeOrdinaryBody.CallPath.Packed sources rootOwner rootName =>
      sizeOf packed.2.2)).wf (C := fun _ => List (Semantics.FiniteCarrier.Basis × Expression))
    (fun packed => match packed with
      | ⟨_,_,.root body⟩ => fun _ => body.checked.summary.parameterValues.flatMap SourceRuntimeValues.ordinary
      | ⟨_,_,.named _ _ _ parent⟩ => fun visit => visit ⟨_,_,parent⟩ (by decreasing_tactic)) ⟨owner,name,path⟩

structure Inputs {sources rootOwner rootName owner name}
    (path : Path sources rootOwner rootName owner name) where
  fields : RuntimeOrdinaryInputs.Fields
  originalFields : fields.map Sigma.fst = rootEntries path
  domain : OrdinaryDomain.Checked ((rootEntries path).map Prod.fst)
  rows : List (List Nat)
  original : RuntimeInterval.Computed
    ((OrdinaryDomain.assignments domain).mapM (RuntimeOrdinaryInputs.decode fields)) rows

def readInputs {sources rootOwner rootName owner name}
    (path : Path sources rootOwner rootName owner name) : WorkM (Inputs path) := do
  let entries := rootEntries path
  exactWork (Exact.charge (32*((entries.map fun entry =>
    SourceRuntimeValues.expressionFields entry.2+SourceRuntimeValues.expressionSize entry.2+
      Raw.OwnerFlow.fields [⟨0,entry.1⟩]).sum+1)))
  let fields ← RuntimeOrdinaryInputs.readFields entries
  if originalFields : fields.map Sigma.fst = rootEntries path then
    let domain ← OrdinaryDomain.read (entries.map Prod.fst)
    let rows ← NaturalAffine.witness
      ((OrdinaryDomain.assignments domain).mapM (RuntimeOrdinaryInputs.decode fields))
    return ⟨fields,originalFields,domain,rows.val,by with_reducible exact rows.property⟩
  else throw .request

/-- No new measurement-count maximum is introduced. The actual row generation
reserves its copies before each doubling and stops on the existing work error. -/
def bitRows : Nat → List (List Bool) :=
  Nat.rec [[]] (fun _ previous => previous.flatMap fun row => [false :: row,true :: row])

private def readBitRows : (count : Nat) → WorkM {rows : List (List Bool) // rows = bitRows count} :=
  Nat.rec (pure ⟨[[]],rfl⟩) (fun count previous => do
    let previous ← previous
    exactWork (Exact.charge (32*(count+2)*(previous.val.length+1)))
    return ⟨previous.val.flatMap (fun row => [false :: row,true :: row]),by rw [previous.property]; rfl⟩)

theorem bitRows_complete (bits : List Bool) : bits ∈ bitRows bits.length := by
  induction bits with
  | nil => exact List.mem_cons_self
  | cons bit bits ih =>
    apply List.mem_flatMap.mpr
    refine ⟨bits,ih,?_⟩
    cases bit <;> simp

private def measurementFields (measurements : List Measurement) : Nat :=
  (measurements.map fun entry => entry.origin.moduleName.utf8ByteSize+entry.origin.functionName.utf8ByteSize+
    (entry.calls.map fun site => site.moduleName.utf8ByteSize+site.functionName.utf8ByteSize+1).sum+
    Raw.OwnerFlow.fields [entry.owner]+2).sum

def reference (inputs : List Nat) (measurements : List Measurement) (bits : List Bool) : Valuation :=
  RuntimeOrdinaryBody.valuation inputs measurements
    ((measurements.zip bits).map fun (entry,bit) => (entry.output,bit))

def sameAt (measurements : List Measurement) (required actual : Expression)
    (inputs : List Nat) (bits : List Bool) : Bool :=
  match Semantics.SourceOrdinary.evaluate (reference inputs measurements bits) required,
    Semantics.SourceOrdinary.evaluate (reference inputs measurements bits) actual with
  | some left,some right => decide (left ≤ 1 ∧ left = right)
  | _,_ => false

def every (inputs : List (List Nat)) (bits : List (List Bool)) (measurements : List Measurement)
    (required actual : Expression) : Bool :=
  inputs.all fun input => bits.all (sameAt measurements required actual input)

private def readEvery (inputs : List (List Nat)) (bits : List (List Bool)) (measurements : List Measurement)
    (required actual : Expression) : WorkM {_row : Unit // every inputs bits measurements required actual = true} := do
  let fields := measurementFields measurements
  let cost := 32*(SourceRuntimeValues.expressionSize required+SourceRuntimeValues.expressionFields required+
    SourceRuntimeValues.expressionSize actual+SourceRuntimeValues.expressionFields actual+1)*(fields+1)^2
  let checked ← inputs.foldlM (fun _ input => do
    bits.foldlM (fun _ assignment => do
      exactWork (Exact.charge (cost*(input.length+assignment.length+1)))
      guard (sameAt measurements required actual input assignment) .equation) ()) ()
  -- Retain the exact independently executable predicate after the same reads.
  -- This final pass is also real work, rather than a claimed earlier run.
  exactWork (Exact.charge (cost*(inputs.length+1)*(bits.length+1)*
    ((inputs.map List.length).sum+(bits.map List.length).sum+1)))
  if original : every inputs bits measurements required actual = true then return ⟨checked,original⟩
  else throw .equation

structure Checked {sources rootOwner rootName owner name dependencies program block offset}
    (path : Path sources rootOwner rootName owner name)
    (source : SourceRuntimeContext.BranchEvent sources owner)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (before : RuntimeOrdinaryBody.State) where
  required : Expression
  transported : path.transport source.condition = .ok required
  condition : Read before.table actual.condition
  inputs : Inputs path
  assignments : List (List Bool)
  complete : assignments = bitRows before.measurements.length
  valid : every inputs.rows assignments before.measurements required condition.expression = true

def read {sources rootOwner rootName owner name dependencies program block offset}
    (path : Path sources rootOwner rootName owner name)
    (source : SourceRuntimeContext.BranchEvent sources owner)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (before : RuntimeOrdinaryBody.State) : WorkM (Checked path source actual before) := do
  exactWork (Exact.charge (32*(path.fields+SourceRuntimeValues.expressionSize source.condition+
    SourceRuntimeValues.expressionFields source.condition+measurementFields before.measurements+1)^2))
  let keys := before.measurements.map fun entry => (entry.origin,entry.calls,entry.owner)
  guard (keys.eraseDups.length == keys.length &&
    (before.measurements.map (·.output)).eraseDups.length == before.measurements.length) .request
  match transported : path.transport source.condition with
  | .error _ => throw .request
  | .ok required =>
    let condition ← RuntimeOrdinarySSA.read before.table actual.condition
    let inputs ← readInputs path
    let assignments ← readBitRows before.measurements.length
    let valid ← readEvery inputs.rows assignments.val before.measurements required condition.expression
    return ⟨required,transported,condition,inputs,assignments.val,assignments.property,valid.property⟩

theorem Checked.every {sources rootOwner rootName owner name dependencies program block offset path source actual before}
    (checked : @Checked sources rootOwner rootName owner name dependencies program block offset path source actual before)
    (input : List Nat) (inputMember : input ∈ checked.inputs.rows) (bits : List Bool)
    (width : bits.length = before.measurements.length) :
    sameAt before.measurements checked.required checked.condition.expression input bits = true := by
  have member : bits ∈ checked.assignments := by
    rw [checked.complete,← width]
    exact bitRows_complete bits
  exact List.all_eq_true.mp (List.all_eq_true.mp checked.valid input inputMember) bits member

end QleisliKernel.Qirf.RuntimeBranchCondition
