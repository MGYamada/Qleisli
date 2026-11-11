import QleisliKernel.Qirf.RuntimePrimitiveSource
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Match an original coherent basis table to the same literal Raw interval.
Each logical row is checked in physical carrier order, including every
captured ordinary valuation retained by the source function.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBasisAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
abbrev Layout := QleisliKernel.Semantics.FiniteCarrier.Layout
open RuntimeStructuralAction (SourceState)
open RuntimePrimitiveSource (PortAt readPort)

structure Source {sources caller} (event : SourceRuntimeContext.BasisEvent sources caller) where
  body : SourceRuntimeContext.Outcome sources caller event.bodyInitial
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readBasisSource event) body

def readSource {sources caller} (event : SourceRuntimeContext.BasisEvent sources caller) :
    WorkM (Source event) := do
  let original ← NaturalAffine.witness (SourceRuntimeTrace.readBasisSource event)
  return ⟨original.val,by with_reducible exact original.property⟩

private def rowEntry (labels table : Array Nat) (entry : Nat × Nat) : Bool :=
  match labels[entry.2]?,table[entry.1]? with
  | some expected,some actual => expected == actual
  | _,_ => false

def rowsMatch (input output : Layout) (rows : List (List Nat)) (table : List Nat) : Bool :=
  let labels := output.labels.toArray
  let entries := table.toArray
  !rows.isEmpty && rows.all fun row =>
    row.length == input.labels.length && (input.labels.zip row).all (rowEntry labels entries)

theorem matched_entry {input output rows table}
    (checked : rowsMatch input output rows table = true)
    {row : List Nat} (member : row ∈ rows)
    {ordinal code targetOrdinal : Nat}
    (original : input.labels[ordinal]? = some code) (selected : row[ordinal]? = some targetOrdinal) :
    ∃ target, output.labels[targetOrdinal]? = some target ∧ table[code]? = some target := by
  have every := (Bool.and_eq_true_iff.mp checked).2
  have rowChecked := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp every row member)).2
  have found : (input.labels.zip row)[ordinal]? = some (code,targetOrdinal) :=
    List.getElem?_zip_eq_some.mpr ⟨original,selected⟩
  have entry := List.all_eq_true.mp rowChecked (code,targetOrdinal) (List.mem_of_getElem? found)
  unfold rowEntry at entry
  simp only [List.getElem?_toArray] at entry
  split at entry
  · rename_i expected actual label codeEntry
    exact ⟨expected,label,by simpa only [beq_iff_eq.mp entry] using codeEntry⟩
  · contradiction

structure Table {sources caller} (event : SourceRuntimeContext.BasisEvent sources caller)
    (table : List Nat) where
  inputLayout : Layout
  inputRead : QleisliKernel.Semantics.FiniteCarrier.layout event.input.basis = some inputLayout
  sameInput : event.function.inputDomain.code = inputLayout
  outputRead : QleisliKernel.Semantics.FiniteCarrier.layout event.outputBasis = some event.function.outputLayout
  agreement : rowsMatch inputLayout event.function.outputLayout event.function.rows table = true

def readTable {sources caller} (event : SourceRuntimeContext.BasisEvent sources caller)
    (table : List Nat) : WorkM (Table event table) := do
  let input ← NaturalAffine.witness (FiniteCarrier.read event.input.basis)
  exactWork (Exact.charge (32*(table.length+input.val.labels.length+event.function.outputLayout.labels.length+
    (event.function.rows.map fun row => row.length+1).sum+1)))
  if sameInput : event.function.inputDomain.code = input.val then
    if agreement : rowsMatch input.val event.function.outputLayout event.function.rows table = true then
      have inputRead : QleisliKernel.Semantics.FiniteCarrier.layout event.input.basis = some input.val := by
        obtain ⟨work,left,read⟩ := input.property
        exact FiniteCarrier.read_reference _ _ work left read
      have outputRead : QleisliKernel.Semantics.FiniteCarrier.layout event.outputBasis = some event.function.outputLayout := by
        obtain ⟨work,left,read⟩ := event.function.outputRead
        exact FiniteCarrier.read_reference _ _ work left read
      return ⟨input.val,inputRead,sameInput,outputRead,agreement⟩
    else throw .equation
  else throw .request

def updatedBindings {sources caller} (event : SourceRuntimeContext.BasisEvent sources caller)
    (before : RuntimeOwnerMap.Map) (output : Semantics.Raw.Port) : RuntimeOwnerMap.Map :=
  if event.input == event.output then
    before.map fun binding => if binding.owner == event.input then ⟨event.output,output⟩ else binding
  else
    before.filter (fun binding => binding.owner != event.input) ++ [⟨event.output,output⟩]

def continued {sources caller} (event : SourceRuntimeContext.BasisEvent sources caller)
    (before : SourceState) (output : Semantics.Raw.Port) : SourceState :=
  let allocated := if event.input == event.output then [] else [event.output]
  ⟨updatedBindings event before.bindings output,before.issued ++ allocated,before.nextOrdinal+allocated.length⟩

structure Checked {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.BasisEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) where
  input : PortAt event.input before.bindings
  output : Semantics.Raw.Port
  table : List Nat
  literal : (block.operations.drop start).take count =
    [.pure (.liftBasis input.port.token output.token output.wires table)]
  outputRead : PureInterval.ports interval.after [output.token] = some [output]
  codes : Table event table
  widths : input.port.bits = codes.inputLayout.bits ∧ output.bits = event.function.outputLayout.bits
  sourceOwner : event.output.basis = event.outputBasis ∧ event.bodyOrdinal = before.nextOrdinal ∧
    event.output = (if event.input.basis = event.outputBasis then event.input else ⟨before.nextOrdinal,event.outputBasis⟩)
  spectators : PureInterval.spectators interval.before [input.port.token] =
    PureInterval.spectators interval.after [output.token]
  after : RuntimeOwnerMap.Checked ((continued event before output).bindings.map (·.owner)) interval.after
  afterBindings : after.bindings = (continued event before output).bindings

/-- Bind the actual literal instruction, retained spectators and original
owner issuance to the independently evaluated basis rows. -/
def read {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.BasisEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) :
    WorkM (Checked event interval before) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (event.input :: event.output :: before.issued) +
    Raw.OwnerFlow.fields (before.bindings.map (·.owner))+before.bindings.length+block.operations.length+1)))
  if sourceOwner : event.output.basis = event.outputBasis ∧ event.bodyOrdinal = before.nextOrdinal ∧
      event.output = (if event.input.basis = event.outputBasis then event.input else ⟨before.nextOrdinal,event.outputBasis⟩) then
    let input ← readPort event.input before.bindings
    match literal : (block.operations.drop start).take count with
    | [.pure (.liftBasis inputToken outputToken wires table)] =>
      match returned : PureInterval.ports interval.after [outputToken] with
      | some [output] =>
        if ports : inputToken = input.port.token ∧ outputToken = output.token ∧ wires = output.wires then
          let codes ← readTable event table
          if widths : input.port.bits = codes.inputLayout.bits ∧ output.bits = event.function.outputLayout.bits then
            if spectators : PureInterval.spectators interval.before [input.port.token] =
                PureInterval.spectators interval.after [output.token] then
              let next := continued event before output
              let after ← RuntimeOwnerMap.checkBindings (next.bindings.map (·.owner)) interval.after next.bindings
              return ⟨input,output,table,by simpa only [ports.1,ports.2.1,ports.2.2] using literal,
                by simpa only [ports.2.1] using returned,codes,widths,sourceOwner,spectators,after.val,after.property⟩
            else throw .request
          else throw .request
        else throw .request
      | _ => throw .request
    | _ => throw .request
  else throw .request

#print axioms matched_entry
end QleisliKernel.Qirf.RuntimeBasisAction
