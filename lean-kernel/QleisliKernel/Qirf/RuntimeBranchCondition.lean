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

private theorem all_of_checks {α : Type} (test : α → Bool) (read : α → WorkM Unit)
    (valid : ∀ value work left, (read value).run work = (.ok (),left) → test value = true)
    (values : List α) {work left}
    (ran : (values.foldlM (fun _ value => read value) ()).run work = (.ok (),left)) :
    values.all test = true := by
  induction values generalizing work with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.foldlM_cons] at ran
    obtain ⟨checked,middle,head,tail⟩ := bind_success _ _ _ _ _ ran
    cases checked
    simp only [List.all_cons,valid value work middle head,ih tail,Bool.and_self]

private def readEvery (inputs : List (List Nat)) (bits : List (List Bool)) (measurements : List Measurement)
    (required actual : Expression) : WorkM {_row : Unit // every inputs bits measurements required actual = true} := do
  -- Each measured expression scans the measurement keys once, then looks up
  -- its output bit. The row also pays for constructing the assignment table.
  let fields := measurementFields measurements
  let cost := 32*(SourceRuntimeValues.expressionSize required+SourceRuntimeValues.expressionFields required+
    SourceRuntimeValues.expressionSize actual+SourceRuntimeValues.expressionFields actual+1)*(fields+1)
  let compare := sameAt measurements required actual
  let readAssignment (input : List Nat) (assignment : List Bool) : WorkM Unit := do
    exactWork (Exact.charge (cost*(input.length+assignment.length+1)))
    guard (compare input assignment) .equation
  let readInput (input : List Nat) := bits.foldlM (fun _ assignment => readAssignment input assignment) ()
  let checked ← NaturalAffine.witness (inputs.foldlM (fun _ input => readInput input) ())
  -- The successful metered fold proves the Boolean conjunction directly.
  return ⟨(),by
    obtain ⟨work,left,ran⟩ := checked.property
    cases checked with
    | mk result _ =>
      cases result
      apply all_of_checks (fun input => bits.all (compare input)) readInput _ inputs ran
      intro input work left read
      apply all_of_checks (compare input) (readAssignment input) _ bits read
      intro assignment work left read
      obtain ⟨_,_,_,compared⟩ := bind_success _ _ _ _ _ read
      exact (guard_success _ _ _ _ compared).1⟩

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
