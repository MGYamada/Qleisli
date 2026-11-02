import QleisliKernel.SourceTypes.SourceMeaning
import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.SourceTypes.SourceRuntimeOrdinary
import QleisliKernel.OrdinaryDomain
import QleisliKernel.Semantics.PrimitiveOperator

/-! Prepare ordinary candidates for original permutation/phase Meaning leaves.
The actual original body is freshly traversed; only its symbolic value is
interpreted by the independent ordinary reference. Every canonical input is
retained, with complete nominal/tuple types and original dependency queries.
No producer table, quantum subject, generic-audit outcome or runtime execution
supplies these rows. The original source-tree/callee semantics correspondence
to the freshly computed symbolic value remains unproved. Accordingly this is
preparation only: its candidate cannot discharge a Meaning assertion. Actual
source correspondence, quantum/reference equations and source/native preservation
remain required; this component issues no accepted handle or admitted map.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceMeaningOrdinary
open QleisliKernel Finite SourceTypes
open Semantics.FiniteCarrier
open SourceRuntimeValues (Value)

inductive Kind where
  | permutation | phase
  deriving BEq, DecidableEq, Repr

def outputBasis (kind : Kind) (input : Basis) : Basis :=
  match kind with
  | .permutation => input
  | .phase => [.pair,.bit,.pair,.bit,.bit]

structure Original {sources} (catalogue : GenericCatalogue.Checked sources)
    (reference : SourceMeaning.ClassicalReference sources) where
  signature : SourceRuntimeContext.Signature sources
    reference.resolution.result.moduleName reference.resolution.result.declaration.name
  signatureRead : ∃ before after,
    (SourceRuntimeContext.readSignature sources reference.resolution.result.moduleName
      reference.resolution.result.declaration.name {} (.source reference.caller) (some catalogue)).run before =
      (.ok signature,after)
  original : signature.original = reference.signature.original
  parameters : signature.parameters.map (·.tree) = reference.signature.inputs.map Semantics.RuntimeType.ordinary
  result : signature.result.tree = Semantics.RuntimeType.ordinary reference.signature.basis
  body : SourceRuntimeTrace.Body signature
  traversed : ∃ before after,
    (SourceRuntimeTrace.readBodyWithSignature signature).run before = (.ok body,after)
  pure : body.checked.summary.generic.inferredEffect = .unitary ∧
    body.checked.summary.inferredEffect = .unitary ∧
    body.checked.summary.generic.quantumUse = false ∧ body.checked.summary.quantumUse = false ∧
    body.checked.summary.allocated = [] ∧ body.checked.summary.consumed = []

def readOriginal {sources} (catalogue : GenericCatalogue.Checked sources)
    (reference : SourceMeaning.ClassicalReference sources) : WorkM (Original catalogue reference) := do
  let signature ← NaturalAffine.witness (SourceRuntimeContext.readSignature sources
    reference.resolution.result.moduleName reference.resolution.result.declaration.name {}
    (.source reference.caller) (some catalogue))
  let bytes := signature.val.original.source.utf8ByteSize+reference.signature.original.source.utf8ByteSize
  exactWork (Exact.charge (16*(bytes+signature.val.parameters.length+reference.signature.inputs.length+1)))
  if same : signature.val.original.source = reference.signature.original.source ∧
      signature.val.original.declaration = reference.signature.original.declaration ∧
      signature.val.original.occurrence = reference.signature.original.occurrence then
    if ports : signature.val.parameters.map (·.tree) = reference.signature.inputs.map Semantics.RuntimeType.ordinary ∧
        signature.val.result.tree = Semantics.RuntimeType.ordinary reference.signature.basis then
      let body ← NaturalAffine.witness (SourceRuntimeTrace.readBodyWithSignature signature.val)
      if pure : body.val.checked.summary.generic.inferredEffect = .unitary ∧
          body.val.checked.summary.inferredEffect = .unitary ∧
          body.val.checked.summary.generic.quantumUse = false ∧ body.val.checked.summary.quantumUse = false ∧
          body.val.checked.summary.allocated = [] ∧ body.val.checked.summary.consumed = [] then
        return ⟨signature.val,by with_reducible exact signature.property,
          OrdinarySignature.Original.sameEnvelope _ _ same.1 same.2.1 same.2.2,
          ports.1,ports.2,body.val,by with_reducible exact body.property,pure⟩
      else throw .request
    else throw .request
  else throw .request

/-- Original query rows only. Auditing the entire catalogue does not make its
unrelated sources relevant to this Meaning leaf. -/
def Original.sourceRows {sources catalogue reference} (original : @Original sources catalogue reference) :
    List (String × String) :=
  ResolutionProvenance.sourceRows reference.resolution.result ++ reference.signature.sourceRows ++
    reference.staticRows ++ original.signature.sourceRows ++ original.body.checked.summary.staticRows

structure Field where
  basis : Basis
  ordinal : Nat
  code : Layout
  read : ∃ before after,(FiniteCarrier.read basis).run before = (.ok code,after)

private def readField (value : Basis × Semantics.SourceOrdinary.Expression) : WorkM Field := do
  let .input ordinal := value.2 | throw .request
  let code ← NaturalAffine.witness (FiniteCarrier.read value.1)
  return ⟨value.1,ordinal,code.val,by with_reducible exact code.property⟩

/-- Scalar fields come from one already checked finite source tree. Preserve
all of its zero-width leaves without introducing a new argument-count limit.
The original six-bit/64-label ordinary domain bounds the Cartesian code. -/
def readFieldCode (fields : List Field) : WorkM Layout := do
  exactWork (Exact.charge (16*(fields.length+1)))
  let (_,dimension) ← fields.foldlM (fun (width,dimension) field => do
    let width := width+field.code.bits
    let dimension := dimension*field.code.labels.length
    guard (width ≤ 6 && dimension ≤ 64) .limit
    pure (width,dimension)) (0,1)
  exactWork (Exact.charge (16*(fields.length+1)*(dimension+1)))
  return fields.foldr (fun field rest => Semantics.FiniteCarrier.tensor field.code rest)
    Semantics.FiniteCarrier.singleton

structure Inputs {sources catalogue reference} (original : @Original sources catalogue reference)
    (basis : Basis) where
  oneParameter : reference.signature.inputs = [basis]
  parameter : Value
  value : original.body.checked.summary.parameterValues = [parameter]
  exactType : SourceRuntimeValues.typeOf parameter = Semantics.RuntimeType.ordinary basis
  fields : List Field
  fieldsRead : ∃ before after,
    ((SourceRuntimeValues.ordinary parameter).mapM readField).run before = (.ok fields,after)
  ordinals : fields.map (·.ordinal) = List.range original.body.checked.summary.nextOrdinary
  domain : OrdinaryDomain.Checked [basis]
  fieldCode : Layout
  fieldCodeRead : ∃ before after,(readFieldCode fields).run before = (.ok fieldCode,after)
  sameCode : fieldCode = domain.code

def readInputs {sources catalogue reference} (original : @Original sources catalogue reference) (basis : Basis) :
    WorkM (Inputs original basis) := do
  exactWork (Exact.charge (16*(SourceRuntimeValues.valueFields
    (original.body.checked.summary.parameterValues.flatten)+basis.length+1)))
  if oneParameter : reference.signature.inputs = [basis] then
    let parameter ← lift (readOption original.body.checked.summary.parameterValues.head?)
    if value : original.body.checked.summary.parameterValues = [parameter] then
      if exactType : SourceRuntimeValues.typeOf parameter = Semantics.RuntimeType.ordinary basis then
        let fields ← NaturalAffine.witness ((SourceRuntimeValues.ordinary parameter).mapM readField)
        if ordinals : fields.val.map (·.ordinal) = List.range original.body.checked.summary.nextOrdinary then
          let domain ← OrdinaryDomain.read [basis]
          let fieldCode ← NaturalAffine.witness (readFieldCode fields.val)
          if sameCode : fieldCode.val = domain.code then
            return ⟨oneParameter,parameter,value,exactType,fields.val,
              by with_reducible exact fields.property,ordinals,domain,fieldCode.val,
              by with_reducible exact fieldCode.property,sameCode⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Decode each original scalar input key, including zero-bit keys. The
complete independently read codes and the separate source shape are both
required by Inputs; equal widths supply neither of those facts. -/
def decode (fields : List Field) (label : Nat) : Except String (List (Nat × Nat)) := do
  let (values,rest) ← fields.foldlM (fun (values,rest) field => do
    let physical := rest % 2^field.code.bits
    let ordinal := field.code.labels.idxOf physical
    if ordinal ≥ field.code.labels.length then throw "original Meaning input outside its exact code"
    return (values ++ [(field.ordinal,ordinal)],rest / 2^field.code.bits)) ([],label)
  if rest != 0 then throw "original Meaning input has trailing coordinates"
  pure values

def valuation (inputs : List (Nat × Nat)) : Semantics.SourceOrdinary.Valuation :=
  { inputs := fun ordinal => (inputs.find? (·.1 == ordinal)).map (·.2)
    basisInputs := fun _ => none
    measured := fun _ _ _ => none }

structure Label where
  basis : Basis
  ordinal : Nat
  dimension : Nat
  deriving BEq, DecidableEq, Repr

/-- Preserve the complete result prefix while forming its logical ordinal.
Nominal records remain atomic and each tuple keeps its actual arity/order. -/
def pack (value : Semantics.SourceOrdinary.Result) : Except String Label := do
  let stack ← value.reverse.foldlM (fun (stack : List Label) atom => do
    match atom with
    | .owner _ => throw "quantum owner in an ordinary Meaning result"
    | .ordinary basis ordinal =>
      let some dimension := Semantics.FiniteCarrier.dimension basis | throw "invalid original Meaning result basis"
      if ordinal ≥ dimension then throw "original Meaning result outside its exact basis"
      return ⟨basis,ordinal,dimension⟩ :: stack
    | .tuple arity =>
      if arity > stack.length then throw "original Meaning result tuple shape"
      let fields := stack.take arity
      let (ordinal,dimension) := fields.foldl (fun (ordinal,stride) field =>
        (ordinal+stride*field.ordinal,stride*field.dimension)) (0,1)
      let basis := (if arity == 2 then Atom.pair else .tuple arity) :: fields.flatMap (·.basis)
      return ⟨basis,ordinal,dimension⟩ :: stack.drop arity) ([] : List Label)
  let [result] := stack | throw "original Meaning result multiplicity"
  pure result

structure Row {sources catalogue reference original basis}
    (inputs : @Inputs sources catalogue reference original basis) (label : Nat) where
  arguments : List (Nat × Nat)
  decoded : decode inputs.fields label = .ok arguments
  result : Semantics.SourceOrdinary.Result
  evaluated : SourceRuntimeOrdinary.extract (valuation arguments)
    original.body.checked.summary.value = .ok result
  output : Label
  packed : pack result = .ok output
  exactType : output.basis = reference.signature.basis
  bounded : Semantics.FiniteCarrier.dimension output.basis = some output.dimension ∧
    output.ordinal < output.dimension

def readRow {sources catalogue reference original basis}
    (inputs : @Inputs sources catalogue reference original basis) (label : Nat) : WorkM (Row inputs label) := do
  match decoded : decode inputs.fields label with
  | .error _ => throw .request
  | .ok arguments =>
    match evaluated : SourceRuntimeOrdinary.extract (valuation arguments) original.body.checked.summary.value with
    | .error _ => throw .request
    | .ok result =>
      match packed : pack result with
      | .error _ => throw .request
      | .ok output =>
        if exactType : output.basis = reference.signature.basis then
          if bounded : Semantics.FiniteCarrier.dimension output.basis = some output.dimension ∧
              output.ordinal < output.dimension then
            pure ⟨arguments,decoded,result,evaluated,output,packed,exactType,bounded⟩
          else throw .request
        else throw .request

inductive Rows {sources catalogue reference original basis}
    (inputs : @Inputs sources catalogue reference original basis) : List Nat → Type where
  | nil : Rows inputs []
  | cons {label labels} (head : Row inputs label) (tail : Rows inputs labels) : Rows inputs (label :: labels)

def readRows {sources catalogue reference original basis}
    (inputs : @Inputs sources catalogue reference original basis) :
    Nat → (labels : List Nat) → WorkM (Rows inputs labels) :=
  Nat.rec (fun _ => throw .limit) (fun _ next labels => do
    match labels with
    | [] => pure .nil
    | label :: labels => return .cons (← readRow inputs label) (← next labels))

def Rows.targets {sources catalogue reference original basis inputs labels}
    (rows : @Rows sources catalogue reference original basis inputs labels) : List Nat :=
  match rows with
  | .nil => []
  | .cons head tail => head.output.ordinal :: tail.targets

theorem Rows.count {sources catalogue reference original basis inputs labels}
    (rows : @Rows sources catalogue reference original basis inputs labels) : rows.targets.length = labels.length := by
  induction rows with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

theorem Rows.every {sources catalogue reference original basis inputs labels}
    (rows : @Rows sources catalogue reference original basis inputs labels)
    (label : Nat) (member : label ∈ labels) : Nonempty (Row inputs label) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst label; exact ⟨head⟩
    · exact ih later

theorem Row.expression_evaluates {sources catalogue reference original basis inputs label}
    (row : @Row sources catalogue reference original basis inputs label) :
    Semantics.SourceOrdinary.Evaluates (valuation row.arguments)
      original.body.checked.summary.value row.result :=
  SourceRuntimeOrdinary.extract_sound _ _ _ row.evaluated

def candidateMatrix (kind : Kind) (targets : List Nat) : Except Exact.Error Semantics.Exact.Matrix := do
  let dimension := targets.length
  let entries ← (List.range (dimension*dimension)).mapM fun index => do
    let row := index / dimension
    let column := index % dimension
    let some target := targets[column]? | throw .shapeMismatch
    pure (match kind with
      | .permutation => if target == row then Semantics.Exact.Scalar.one else .zero
      | .phase => if row == column then Semantics.PrimitiveOperator.phase target else .zero)
  Exact.Matrix.make dimension dimension entries

structure Prepared {sources} (catalogue : GenericCatalogue.Checked sources)
    (reference : SourceMeaning.ClassicalReference sources) (kind : Kind) (basis : Basis) where
  original : Original catalogue reference
  ports : reference.signature.basis = outputBasis kind basis
  inputs : Inputs original basis
  rows : Rows inputs inputs.domain.code.labels
  targetBounds : rows.targets.all (fun target => decide (target < match kind with
    | .permutation => inputs.domain.code.labels.length | .phase => 8)) = true
  permutation : kind = .permutation → rows.targets.Nodup
  candidate : Semantics.Exact.Matrix
  candidateComputed : candidateMatrix kind rows.targets = .ok candidate

/-- Fresh original source, canonical complete inputs and independent ordinary
EXPRESSION evaluation prepare a candidate. No theorem here connects the
original source tree/callees to that expression, so every Meaning assertion
remains unconsumed. A future native gate must retain that genuine source
correspondence before it may compare an actual implementation with a Meaning.
No Raw program, caller table or execution authority is accepted here. -/
def prepare {sources} (catalogue : GenericCatalogue.Checked sources)
    (reference : SourceMeaning.ClassicalReference sources) (kind : Kind) (basis : Basis) :
    WorkM (Prepared catalogue reference kind basis) := do
  let original ← readOriginal catalogue reference
  if ports : reference.signature.basis = outputBasis kind basis then
    let inputs ← readInputs original basis
    let value := original.body.checked.summary.value
    let expressions := (SourceRuntimeValues.ordinary value).map fun (_,term) => SourceRuntimeValues.expressionSize term
    let cells := SourceRuntimeValues.valueFields value+expressions.sum+inputs.fields.length+
      (inputs.fields.map fun field => field.code.labels.length).sum+1
    exactWork (Exact.charge (64*(inputs.domain.code.labels.length+1)*cells+
      inputs.domain.code.labels.length*inputs.domain.code.labels.length+1))
    let rows ← readRows inputs (inputs.domain.code.labels.length+1) inputs.domain.code.labels
    if targetBounds : rows.targets.all (fun target => decide (target < match kind with
        | .permutation => inputs.domain.code.labels.length | .phase => 8)) = true then
      if permutation : kind = .permutation → rows.targets.Nodup then
        match computed : candidateMatrix kind rows.targets with
        | .error error => throw (.arithmetic error)
        | .ok action => pure ⟨original,ports,inputs,rows,targetBounds,permutation,action,computed⟩
      else throw .notIsometric
    else throw .request
  else throw .request

end QleisliKernel.Qirf.SourceMeaningOrdinary
