import QleisliKernel.Semantics.Finite
import QleisliKernel.ExactMatrix

/-! Fresh bounded reconstruction and encoded equations for VM-24.
Inputs are original finite data, never Rust decisions or computed matrices.
This component is not raw-IR extraction or production authority.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Finite
open Semantics.Exact Semantics.Finite

inductive Error where
  | invalid | limit | notIsometric | equation | request
  | arithmetic (error : Exact.Error)
  deriving BEq, DecidableEq, Repr
abbrev WorkM := ExceptT Error (StateM Nat)

def lift {α : Type} (result : Except Error α) : WorkM α :=
  match result with | .ok value => pure value | .error error => throw error

def arithmetic {α : Type} (result : Except Exact.Error α) : Except Error α :=
  result.mapError Error.arithmetic

def exactWork {α : Type} (action : Exact.WorkM α) : WorkM α := fun work =>
  let (result, left) := action.run work
  (arithmetic result, left)

def guard (condition : Bool) (error : Error := .invalid) : WorkM Unit :=
  if condition then pure () else throw error

/-- Validate all prefix nodes before transformations, keeping Unit and tuple arity. -/
def treeStep (stack : Option (List Nat)) (atom : Atom) : Option (List Nat) := do
  let depth :: rest ← stack | none
  if depth > 32 then none else
  match atom with
  | .unit | .bit | .bits _ => some rest
  | .pair => some ((depth+1) :: (depth+1) :: rest)
  | .tuple arity =>
    if arity < 3 || arity > 128 then none
    else some (List.replicate arity (depth+1) ++ rest)

def basisValid (basis : Basis) : Bool :=
  basis.length ≤ 128 && width basis ≤ 6 &&
    basis.foldl treeStep (some [0]) == some []

def axesValid (bits : Nat) (axes : List Nat) : Bool :=
  axes.length ≤ bits && axes.all (· < bits) && axes.eraseDups.length == axes.length

def targets : Action → List Nat
  | .hadamard target => [target]
  | .monomial axes _ _ | .contract axes _ _ => axes

def stepValid (dependencies : List Dependency) (bits : Nat) (step : Step) : Bool :=
  step.controls.length ≤ bits &&
  axesValid bits (step.controls.map (·.index) ++ targets step.action) &&
  match step.action with
  | .hadamard _ => true
  | .monomial axes permutation phases =>
    axes.length ≤ bits && permutation.length == 2^axes.length &&
    phases.length == permutation.length && permutation.all (· < 2^axes.length) &&
    permutation.eraseDups.length == permutation.length && phases.all (· < 8)
  | .contract axes index _ => (do
      let dependency ← dependencies[index]?
      return basisValid dependency.signature && axes.length == width dependency.signature &&
        dependency.meaning.rows == 2^axes.length && dependency.meaning.cols == 2^axes.length).getD false

def circuitValid (dependencies : List Dependency) (circuit : Circuit) : Bool :=
  basisValid circuit.basis && circuit.steps.length ≤ 1024 &&
    circuit.steps.all (stepValid dependencies (width circuit.basis))

/-- Freshly read row-major canonical coefficients. Precharge precedes their traversal. -/
def matrixRead (matrix : Matrix) : WorkM Matrix := do
  guard (Exact.matrixValid matrix.rows matrix.cols) .limit
  guard (matrix.entries.length == matrix.rows * matrix.cols)
  exactWork (Exact.charge (4 * matrix.entries.length))
  guard (matrix.entries.all Exact.Scalar.valid)
  lift (arithmetic (Exact.Matrix.make matrix.rows matrix.cols matrix.entries))

def readOption {α : Type} (value : Option α) : Except Error α :=
  match value with | some value => .ok value | none => .error .invalid

/-- The serialized format requires canonical decimal strings and already reduced
independent dyadics; unlike arithmetic construction, it never normalizes them. -/
def decimalValid (text : String) : Bool :=
  let digits := if text.startsWith "-" then text.drop 1 |>.toString else text
  !digits.isEmpty && digits.toList.all Char.isDigit &&
    (if digits.startsWith "0" then text == "0" else true) && text.length ≤ 40

def dyadicRead (description : DyadicDescription) : Except Error Coefficient := do
  if !decimalValid description.numerator then throw .invalid
  let numerator ← readOption description.numerator.toInt?
  let value : Coefficient := ⟨numerator,description.denominatorBits⟩
  if !Exact.Coefficient.valid value then throw .invalid
  return value

def scalarRead (descriptions : List DyadicDescription) : Except Error Scalar := do
  match descriptions with
  | [a,b,c,d] => return ⟨← dyadicRead a,← dyadicRead b,← dyadicRead c,← dyadicRead d⟩
  | _ => throw .invalid

def descriptionRead (description : MatrixDescription) : WorkM Matrix := do
  guard (Exact.matrixValid description.rows description.cols) .limit
  guard (description.entries.length == description.rows * description.cols)
  exactWork (Exact.charge (4 * description.entries.length))
  let entries ← lift (description.entries.mapM scalarRead)
  lift (arithmetic (Exact.Matrix.make description.rows description.cols entries))

def halfRoot : Scalar := ⟨.integer 0, ⟨1,1⟩, .integer 0, .integer 0⟩

def dependencyCoefficient (meaning : Matrix) (adjoint : Bool) (input output : Nat) : Except Error Scalar :=
  if adjoint then arithmetic (Exact.Scalar.conjugate (meaning.entry input output))
  else pure (meaning.entry output input)

def contractContribution (meaning : Matrix) (axes : List Nat) (adjoint : Bool)
    (label : Nat) (value : Scalar) (terms : List (Nat × Scalar)) (output : Nat) :
    Except Error (List (Nat × Scalar)) := do
  let coefficient ← dependencyCoefficient meaning adjoint (gather label axes) output
  if coefficient == Scalar.zero then return terms
  let scaled ← arithmetic (Exact.Scalar.mul value coefficient)
  return terms ++ [(scatter label axes output,scaled)]

/-- Literal contributions retain the Rust scalar operations and phase. The list
materializes local terms before accumulation; detailed failure locations are
not transported by this component. Work is precharged for the complete step. -/
def contributions (dependencies : List Dependency) (step : Step)
    (label : Nat) (value : Scalar) : Except Error (List (Nat × Scalar)) := do
  if value == Scalar.zero then return []
  if !enabled step.controls label then return [(label, value)]
  match step.action with
  | .hadamard target =>
    let low := label - bit label target * 2^target
    let high := low + 2^target
    let scaled ← arithmetic (Exact.Scalar.mul value halfRoot)
    let signed ← if label == high then arithmetic (Exact.Scalar.neg scaled) else pure scaled
    return [(low,scaled),(high,signed)]
  | .monomial axes permutation phases =>
    let input := gather label axes
    let output ← readOption permutation[input]?
    let phase ← readOption phases[input]?
    let scaled ← arithmetic (Exact.Scalar.mul value (Exact.Scalar.phase phase))
    return [(scatter label axes output, scaled)]
  | .contract axes index adjoint =>
    let dependency ← readOption dependencies[index]?
    (List.range dependency.meaning.rows).foldlM
      (contractContribution dependency.meaning axes adjoint label value) []

def addAt (values : List Scalar) (term : Nat × Scalar) : Except Error (List Scalar) := do
  let previous ← readOption values[term.1]?
  let value ← arithmetic (Exact.Scalar.add previous term.2)
  return values.set term.1 value

def applyStep (dependencies : List Dependency) (step : Step)
    (values : List Scalar) : Except Error (List Scalar) :=
  (values.zipIdx).foldlM (fun next (value,label) => do
    let terms ← contributions dependencies step label value
    terms.foldlM addAt next) (List.replicate values.length Scalar.zero)

def stepCost (dependencies : List Dependency) (step : Step) : Nat :=
  match step.action with
  | .contract _ index _ => 3 * ((dependencies[index]?).map (·.meaning.rows)).getD 0
  | _ => 6

/-- All step charges occur before column evaluation; later failures retain them. -/
def circuitMatrix (dependencies : List Dependency) (circuit : Circuit) : WorkM Matrix := do
  guard (circuitValid dependencies circuit)
  let dimension := 2^(width circuit.basis)
  circuit.steps.foldlM (fun _ step =>
    exactWork (Exact.charge (dimension * dimension * stepCost dependencies step))) ()
  let columns ← lift ((List.range dimension).mapM fun column =>
    circuit.steps.foldlM (fun values step => applyStep dependencies step values)
      ((List.range dimension).map (fun row => if row == column then Scalar.one else Scalar.zero)))
  let entries := (List.range (dimension * dimension)).map fun index =>
    ((columns[index % dimension]?).getD [])[index / dimension]?.getD Scalar.zero
  lift (arithmetic (Exact.Matrix.make dimension dimension entries))

def encodingRead (encoding : Encoding) : WorkM Encoding := do
  guard (basisValid encoding.logical && basisValid encoding.physical)
  guard (encoding.map.cols == 2^(width encoding.logical) && encoding.map.rows == 2^(width encoding.physical))
  let map ← matrixRead encoding.map
  let isometry ← exactWork (Exact.Matrix.isometryWork map)
  guard isometry .notIsometric
  pure { encoding with map }

def contractRead (contract : Contract) : WorkM Contract := do
  let input ← encodingRead contract.input
  let output ← encodingRead contract.output
  let logical ← matrixRead contract.logical
  guard (logical.cols == input.map.cols && logical.rows == output.map.cols)
  let isometry ← exactWork (Exact.Matrix.isometryWork logical)
  guard isometry .notIsometric
  pure ⟨input,output,logical⟩

/-- The actual circuit is reconstructed afresh and the caller requirement is separate. -/
def check (dependencies : List Dependency) (circuit : Circuit)
    (claim required : Contract) : WorkM Matrix := do
  guard (claim == required) .request
  let contract ← contractRead claim
  guard (circuit.basis == contract.input.physical && circuit.basis == contract.output.physical)
  let actual ← circuitMatrix dependencies circuit
  let lhs ← exactWork (Exact.Matrix.composeWork actual contract.input.map)
  let rhs ← exactWork (Exact.Matrix.composeWork contract.output.map contract.logical)
  guard (lhs == rhs) .equation
  pure actual

/-- Prove both whole-space inverse laws by checking a reconstructed physical map.
This additional inspection is separate from the compatibility equation budget. -/
def wholeSpace (matrix : Matrix) : WorkM Unit := do
  guard (matrix.rows == matrix.cols)
  let isometry ← exactWork (Exact.Matrix.isometryWork matrix)
  guard isometry .notIsometric

structure Cache where
  dependencies : List Dependency
  heights : List Nat
  checked : List Bool
  deriving Repr

def emptyDependency : Dependency := ⟨[],⟨1,1,[Scalar.zero]⟩⟩

def references (circuit : Circuit) : List Nat := circuit.steps.filterMap fun step =>
  match step.action with | .contract _ index _ => some index | _ => none

/-- A fresh pass checks a complete permutation and derives every dependency from
actual earlier entries. Restricted encodings cannot become whole-space calls. -/
def checkEntry (artifact : Artifact) (cache : Cache) (index : Nat) : WorkM Cache := do
  let evidence ← lift (readOption artifact.evidence[index]?)
  guard (!(cache.checked[index]?.getD true))
  let refs := references evidence.circuit
  guard (refs.all fun child => cache.checked[child]?.getD false)
  let height := 1 + (refs.map fun child => cache.heights[child]?.getD 0).foldl max 0
  guard (height ≤ 32) .limit
  let actual ← check cache.dependencies evidence.circuit evidence.claim evidence.claim
  wholeSpace actual
  let identity ← lift (arithmetic (Exact.Matrix.identity actual.rows))
  let callable := evidence.claim.input.logical == evidence.circuit.basis &&
    evidence.claim.output.logical == evidence.circuit.basis &&
    evidence.claim.input.map == identity && evidence.claim.output.map == identity
  let dependency := if callable then Dependency.mk evidence.circuit.basis actual else emptyDependency
  pure ⟨cache.dependencies.set index dependency,cache.heights.set index height,cache.checked.set index true⟩

def checkAll (artifact : Artifact) (order : List Nat) (required : Contract) : WorkM Dependency := do
  guard (artifact.evidence.length ≤ 65536 && order.length == artifact.evidence.length) .limit
  guard (artifact.root < artifact.evidence.length)
  let root ← lift (readOption artifact.evidence[artifact.root]?)
  guard (root.claim == required) .request
  let cache : Cache := ⟨List.replicate artifact.evidence.length emptyDependency,
    List.replicate artifact.evidence.length 0,List.replicate artifact.evidence.length false⟩
  let cache ← order.foldlM (checkEntry artifact) cache
  guard (cache.checked.all id)
  -- The root may have a restricted encoding; the complete reconstructed map is
  -- checked again against the independent requirement rather than a cache flag.
  let actual ← check cache.dependencies root.circuit root.claim required
  wholeSpace actual
  pure ⟨root.circuit.basis,actual⟩

-- Proofs expose actual inputs and intermediate computations, not assumed flags.
theorem bind_run {α β : Type} (first : WorkM α) (next : α → WorkM β) (work : Nat) :
    (first >>= next).run work =
      match first.run work with
      | (.error error, left) => (.error error,left)
      | (.ok value,left) => (next value).run left := by
  simp only [ExceptT.run,bind,ExceptT.bind,ExceptT.mk,StateT.bind]
  cases first work with
  | mk result middle => cases result <;> rfl

theorem bind_success {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (work left : Nat) (value : β) (ok : (first >>= next).run work = (.ok value,left)) :
    ∃ intermediate middle, first.run work = (.ok intermediate,middle) ∧
      (next intermediate).run middle = (.ok value,left) := by
  rw [bind_run] at ok
  cases h : first.run work with
  | mk result middle =>
    rw [h] at ok
    cases result with
    | error error => cases ok
    | ok intermediate => exact ⟨intermediate,middle,rfl,ok⟩

theorem pure_success {α : Type} (value result : α) (work left : Nat)
    (ok : (pure value : WorkM α).run work = (.ok result,left)) : result = value ∧ left = work := by
  cases ok
  exact ⟨rfl,rfl⟩

theorem lift_success {α : Type} (result : Except Error α) (value : α) (work left : Nat)
    (ok : (lift result).run work = (.ok value,left)) : result = .ok value ∧ left = work := by
  cases result with
  | error error => cases ok
  | ok result => cases ok; exact ⟨rfl,rfl⟩

theorem arithmetic_success {α : Type} (input : Except Exact.Error α) (value : α)
    (ok : arithmetic input = .ok value) : input = .ok value := by
  cases input <;> simp_all [arithmetic,Except.mapError]

theorem except_bind_success {α β : Type} (first : Except Error α)
    (next : α → Except Error β) (result : β) (ok : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => simp [bind,Except.bind] at ok
  | ok value => exact ⟨value,rfl,ok⟩

theorem dyadicRead_valid (description : DyadicDescription) (value : Coefficient)
    (ok : dyadicRead description = .ok value) :
    decimalValid description.numerator = true ∧
    description.numerator.toInt? = some value.numerator ∧
    value.exponent = description.denominatorBits ∧ Exact.Coefficient.valid value = true := by
  unfold dyadicRead at ok
  split at ok
  · cases ok
  · rename_i canonical
    simp only [pure_bind] at ok
    obtain ⟨numerator,hn,h⟩ := except_bind_success _ _ _ ok
    split at h
    · cases h
    · rename_i reduced
      simp only [pure,Except.pure,Except.ok.injEq] at h
      subst value
      have number : description.numerator.toInt? = some numerator := by
        cases he : description.numerator.toInt? <;> simp_all [readOption]
      exact ⟨by simpa using canonical,number,rfl,by simpa using reduced⟩

theorem scalarRead_valid (descriptions : List DyadicDescription) (value : Scalar)
    (ok : scalarRead descriptions = .ok value) : Exact.Scalar.valid value = true := by
  unfold scalarRead at ok
  split at ok
  · obtain ⟨a,ha,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨b,hb,h⟩ := except_bind_success _ _ _ h
    obtain ⟨c,hc,h⟩ := except_bind_success _ _ _ h
    obtain ⟨d,hd,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst value
    simp [Exact.Scalar.valid,(dyadicRead_valid _ _ ha).2.2.2,
      (dyadicRead_valid _ _ hb).2.2.2,(dyadicRead_valid _ _ hc).2.2.2,
      (dyadicRead_valid _ _ hd).2.2.2]
  · cases ok

private theorem scalarRead_all (descriptions : List (List DyadicDescription)) (values : List Scalar)
    (ok : descriptions.mapM scalarRead = .ok values) : values.all Exact.Scalar.valid = true := by
  induction descriptions generalizing values with
  | nil =>
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst values
    rfl
  | cons description descriptions ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value,hv,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨rest,hr,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst values
    simp [scalarRead_valid _ _ hv,ih _ hr]

/-- The successful description reader retains all row-major entries with four
independently canonical dyadics; it does not normalize an invalid description. -/
theorem descriptionRead_valid (description : MatrixDescription) (value : Matrix) (work left : Nat)
    (ok : (descriptionRead description).run work = (.ok value,left)) :
    value.rows = description.rows ∧ value.cols = description.cols ∧
    value.entries.all Exact.Scalar.valid = true := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨entries,w₄,he,h⟩ := bind_success _ _ _ _ _ h
  have read := (lift_success _ _ _ _ he).1
  have made := arithmetic_success _ _ (lift_success _ _ _ _ h).1
  have value_eq := (Exact.matrix_make_value _ _ _ _ made).1
  subst value
  exact ⟨rfl,rfl,scalarRead_all _ _ read⟩

theorem exactWork_success {α : Type} (action : Exact.WorkM α) (value : α) (work left : Nat)
    (ok : (exactWork action).run work = (.ok value,left)) : action.run work = (.ok value,left) := by
  change (arithmetic (action.run work).1, (action.run work).2) = (.ok value,left) at ok
  cases h : action.run work with
  | mk result middle =>
    rw [h] at ok
    cases result <;> simp_all [arithmetic,Except.mapError]

theorem guard_success (condition : Bool) (error : Error) (work left : Nat)
    (ok : (guard condition error).run work = (.ok (),left)) : condition = true ∧ left = work := by
  unfold guard at ok
  cases condition with
  | false => cases ok
  | true => exact ⟨rfl,(pure_success () () work left ok).2⟩

theorem matrixRead_value (input result : Matrix) (work left : Nat)
    (ok : (matrixRead input).run work = (.ok result,left)) :
    result = input ∧ input.entries.all Exact.Scalar.valid = true := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hg,h⟩ := bind_success _ _ _ _ _ h
  have canonical := (guard_success _ _ _ _ hg).1
  have made := (lift_success _ _ _ _ h).1
  have made : Exact.Matrix.make input.rows input.cols input.entries = .ok result := by
    cases hm : Exact.Matrix.make input.rows input.cols input.entries <;> simp_all [arithmetic,Except.mapError]
  have result_eq := Exact.matrix_make_value _ _ _ _ made
  exact ⟨by cases input; simpa using result_eq.1, canonical⟩

theorem encodingRead_conditions (input result : Encoding) (work left : Nat)
    (ok : (encodingRead input).run work = (.ok result,left)) :
    result = input ∧ basisValid input.logical = true ∧ basisValid input.physical = true ∧
    input.map.cols = 2^(width input.logical) ∧ input.map.rows = 2^(width input.physical) ∧
    ∃ before after, Exact.Matrix.isometry input.map before = (.ok true,after) := by
  obtain ⟨_,w₁,hb,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨map,w₃,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨iso,w₄,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,hg,h⟩ := bind_success _ _ _ _ _ h
  have map_eq := (matrixRead_value _ _ _ _ hm).1
  subst map
  have iso_true := (guard_success _ _ _ _ hg).1
  subst iso
  have result_eq := (pure_success _ _ _ _ h).1
  have bases := (guard_success _ _ _ _ hb).1
  have dimensions := (guard_success _ _ _ _ hd).1
  simp only [Bool.and_eq_true,beq_iff_eq] at bases dimensions
  refine ⟨?_,bases.1,bases.2,dimensions.1,dimensions.2,w₃,w₄,exactWork_success _ _ _ _ hi⟩
  simpa using result_eq

theorem contractRead_conditions (input result : Contract) (work left : Nat)
    (ok : (contractRead input).run work = (.ok result,left)) :
    result = input ∧
    (∃ before after, Exact.Matrix.isometry input.input.map before = (.ok true,after)) ∧
    (∃ before after, Exact.Matrix.isometry input.output.map before = (.ok true,after)) ∧
    (∃ before after, Exact.Matrix.isometry input.logical before = (.ok true,after)) ∧
    input.logical.cols = input.input.map.cols ∧ input.logical.rows = input.output.map.cols := by
  obtain ⟨ein,w₁,he,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨eout,w₂,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,w₃,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨iso,w₅,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hg,h⟩ := bind_success _ _ _ _ _ h
  have ein_info := encodingRead_conditions _ _ _ _ he
  have eout_info := encodingRead_conditions _ _ _ _ ho
  have logical_eq := (matrixRead_value _ _ _ _ hl).1
  rcases ein_info with ⟨ein_eq,_,_,_,_,ein_iso⟩
  rcases eout_info with ⟨eout_eq,_,_,_,_,eout_iso⟩
  subst ein; subst eout; subst logical
  have iso_true := (guard_success _ _ _ _ hg).1
  subst iso
  have dimensions := (guard_success _ _ _ _ hd).1
  simp only [Bool.and_eq_true,beq_iff_eq] at dimensions
  exact ⟨(pure_success _ _ _ _ h).1,ein_iso,eout_iso,⟨w₄,w₅,exactWork_success _ _ _ _ hi⟩,dimensions⟩

/-- Every accepted equation names the actual fresh reconstruction and arithmetic
runs on the original matrices. No witness is supplied by the producer. -/
theorem check_conditions (dependencies : List Dependency) (circuit : Circuit)
    (claim required : Contract) (actual : Matrix) (work left : Nat)
    (ok : (check dependencies circuit claim required).run work = (.ok actual,left)) :
    claim = required ∧ circuit.basis = claim.input.physical ∧ circuit.basis = claim.output.physical ∧
    (∃ before after, Exact.Matrix.isometry claim.input.map before = (.ok true,after)) ∧
    (∃ before after, Exact.Matrix.isometry claim.output.map before = (.ok true,after)) ∧
    (∃ before after, Exact.Matrix.isometry claim.logical before = (.ok true,after)) ∧
    ∃ circuitWork afterCircuit lhs lhsWork rhs rhsWork,
      (circuitMatrix dependencies circuit).run circuitWork = (.ok actual,afterCircuit) ∧
      Exact.Matrix.compose actual claim.input.map afterCircuit = (.ok lhs,lhsWork) ∧
      Exact.Matrix.compose claim.output.map claim.logical lhsWork = (.ok rhs,rhsWork) ∧ lhs = rhs := by
  obtain ⟨_,w₁,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨contract,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨matrix,w₄,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨lhs,w₅,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rhs,w₆,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,hg,h⟩ := bind_success _ _ _ _ _ h
  have actual_eq := (pure_success _ _ _ _ h).1
  have condition := contractRead_conditions _ _ _ _ hc
  rcases condition with ⟨contract_eq,ein_iso,eout_iso,logical_iso,_,_⟩
  subst contract
  subst actual
  have required_eq := (guard_success _ _ _ _ hr).1
  have basis_eq := (guard_success _ _ _ _ hb).1
  have equation := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,beq_iff_eq] at required_eq basis_eq equation
  exact ⟨required_eq,basis_eq.1,basis_eq.2,ein_iso,eout_iso,logical_iso,
    w₃,w₄,lhs,w₅,rhs,w₆,hm,exactWork_success _ _ _ _ hl,exactWork_success _ _ _ _ ho,equation⟩

theorem wholeSpace_conditions (matrix : Matrix) (work left : Nat)
    (ok : (wholeSpace matrix).run work = (.ok (),left)) :
    matrix.rows = matrix.cols ∧ ∃ before after,
      Exact.Matrix.isometry matrix before = (.ok true,after) := by
  obtain ⟨_,w₁,hd,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨iso,w₂,hi,hg⟩ := bind_success _ _ _ _ _ h
  have iso_true := (guard_success _ _ _ _ hg).1
  subst iso
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hd).1,w₁,w₂,exactWork_success _ _ _ _ hi⟩

/-- A successful reader returns precisely the actual column evaluation, after
validating the complete original type/steps and charging the entire circuit. -/
theorem circuitMatrix_columns (dependencies : List Dependency) (circuit : Circuit)
    (actual : Matrix) (work left : Nat)
    (ok : (circuitMatrix dependencies circuit).run work = (.ok actual,left)) :
    circuitValid dependencies circuit = true ∧ ∃ columns,
      ((List.range (2^width circuit.basis)).mapM fun column =>
        circuit.steps.foldlM (fun values step => applyStep dependencies step values)
          ((List.range (2^width circuit.basis)).map
            (fun row => if row == column then Scalar.one else Scalar.zero))) = .ok columns ∧
      actual = ⟨2^width circuit.basis,2^width circuit.basis,
        (List.range ((2^width circuit.basis) * (2^width circuit.basis))).map fun index =>
          ((columns[index % (2^width circuit.basis)]?).getD [])[index / (2^width circuit.basis)]?.getD Scalar.zero⟩ := by
  obtain ⟨_,w₁,hg,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨columns,w₃,hc,h⟩ := bind_success _ _ _ _ _ h
  have read := (lift_success _ _ _ _ hc).1
  have made := arithmetic_success _ _ (lift_success _ _ _ _ h).1
  exact ⟨(guard_success _ _ _ _ hg).1,columns,read,(Exact.matrix_make_value _ _ _ _ made).1⟩

/-- The accepted root is checked from a freshly created cache and a complete
pass over original entries; the caller requirement is checked independently. -/
theorem checkAll_conditions (artifact : Artifact) (order : List Nat) (required : Contract)
    (result : Dependency) (work left : Nat)
    (ok : (checkAll artifact order required).run work = (.ok result,left)) :
    ∃ root cache beforePass afterPass beforeRoot afterRoot beforeUnitary afterUnitary,
      artifact.evidence[artifact.root]? = some root ∧ root.claim = required ∧
      (order.foldlM (checkEntry artifact)
        ⟨List.replicate artifact.evidence.length emptyDependency,
          List.replicate artifact.evidence.length 0,List.replicate artifact.evidence.length false⟩).run beforePass =
          (.ok cache,afterPass) ∧ cache.checked.all id = true ∧
      (check cache.dependencies root.circuit root.claim required).run beforeRoot = (.ok result.meaning,afterRoot) ∧
      (wholeSpace result.meaning).run beforeUnitary = (.ok (),afterUnitary) ∧
      result.signature = root.circuit.basis := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨root,w₃,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hq,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨cache,w₅,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₇,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,hu,h⟩ := bind_success _ _ _ _ _ h
  have result_eq := (pure_success _ _ _ _ h).1
  subst result
  have root_eq := (lift_success _ _ _ _ hr).1
  have root_eq : artifact.evidence[artifact.root]? = some root := by
    cases he : artifact.evidence[artifact.root]? <;> simp_all [readOption]
  exact ⟨root,cache,w₄,w₅,w₆,w₇,w₇,w₈,root_eq,
    beq_iff_eq.mp (guard_success _ _ _ _ hq).1,hc,(guard_success _ _ _ _ hg).1,ha,hu,rfl⟩

end QleisliKernel.Finite
