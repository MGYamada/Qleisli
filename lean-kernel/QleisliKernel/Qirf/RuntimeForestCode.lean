import QleisliKernel.Qirf.RuntimePureComposition
import QleisliKernel.Qirf.RuntimeStructuredRoot

/-! Sparse coordinates of the actual complete runtime owner forest.
Only scalar owner leaves have enumerated labels. Tensor construction stores a
coordinate function instead of a joined label list or matrix. Original basis
trees, port wires, caller-frame order and zero-width owners remain explicit.
Local composed-kernel equality extends to arbitrary spectator/reference
amplitudes without reassociating bounded arithmetic. Raw step locality and
sequential code/action composition are separate obligations; this component
issues no accepted handle and constructs no dense caller matrix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeForestCode
open QleisliKernel Finite Semantics.Exact
open Semantics.FiniteCarrier
open RuntimeOwnerMap (Binding Map Owner)

structure Sparse where
  bits : Nat
  dimension : Nat
  coordinate : Nat → Option Nat

def Sparse.ofLayout (layout : Layout) : Sparse :=
  ⟨layout.bits,layout.labels.length,fun index => layout.labels[index]?⟩

def Sparse.singleton : Sparse := .ofLayout Semantics.FiniteCarrier.singleton

def Sparse.tensor (first second : Sparse) : Sparse :=
  ⟨first.bits+second.bits,first.dimension*second.dimension,fun index => do
    let low ← first.coordinate (index % first.dimension)
    let high ← second.coordinate (index / first.dimension)
    pure (low+2^first.bits*high)⟩

/-- The complete label relation, rather than physical-width equality. -/
structure Agrees (sparse : Sparse) (layout : Layout) : Prop where
  bits : sparse.bits = layout.bits
  dimension : sparse.dimension = layout.labels.length
  labels : ∀ index,sparse.coordinate index = layout.labels[index]?

theorem ofLayout_agrees (layout : Layout) : Agrees (.ofLayout layout) layout := ⟨rfl,rfl,fun _ => rfl⟩

private theorem product_length (low high : List Nat) (scale : Nat) :
    (high.flatMap fun upper => low.map (fun lower => lower+scale*upper)).length =
      low.length*high.length := by
  induction high with
  | nil => simp
  | cons upper rest ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons,ih,Nat.mul_succ]
    omega

/-- Random access to the existing low-first Cartesian label list. The reader
uses division/remainder instead of materializing that list. -/
private theorem product_get (low high : List Nat) (scale index : Nat) :
    (high.flatMap fun upper => low.map (fun lower => lower+scale*upper))[index]? = (do
      let lower ← low[index % low.length]?
      let upper ← high[index / low.length]?
      pure (lower+scale*upper)) := by
  by_cases empty : low = []
  · subst low
    have noLabels : (high.flatMap fun upper => ([] : List Nat).map
        (fun lower => lower+scale*upper)) = [] := by
      induction high with
      | nil => rfl
      | cons upper rest ih =>
        simpa only [List.flatMap_cons,List.map_nil,List.nil_append] using ih
    rw [noLabels]
    rfl
  · have positive : 0 < low.length := List.length_pos_iff.mpr empty
    induction high generalizing index with
    | nil =>
      simp only [List.flatMap_nil,List.getElem?_nil]
      cases low[index % low.length]? <;> rfl
    | cons upper rest ih =>
      simp only [List.flatMap_cons]
      by_cases before : index < low.length
      · rw [List.getElem?_append_left (by simpa only [List.length_map] using before)]
        simp only [List.getElem?_map,Nat.div_eq_of_lt before,Nat.mod_eq_of_lt before,List.getElem?_cons_zero]
        cases low[index]? <;> rfl
      · have after : low.length ≤ index := Nat.le_of_not_gt before
        rw [List.getElem?_append_right (by simpa only [List.length_map] using after),List.length_map,ih]
        rw [Nat.div_eq_sub_div positive after,Nat.mod_eq_sub_mod after]
        simp only [List.getElem?_cons_succ]

theorem tensor_agrees {first second : Sparse} {left right : Layout}
    (a : Agrees first left) (b : Agrees second right) :
    Agrees (first.tensor second) (Semantics.FiniteCarrier.tensor left right) := by
  refine ⟨by simp only [Sparse.tensor,Semantics.FiniteCarrier.tensor,a.bits,b.bits],?_,?_⟩
  · change first.dimension*second.dimension = _
    rw [a.dimension,b.dimension]
    exact (product_length left.labels right.labels (2^left.bits)).symm
  · intro index
    change (do
      let low ← first.coordinate (index % first.dimension)
      let high ← second.coordinate (index / first.dimension)
      pure (low+2^first.bits*high)) = _
    rw [a.dimension,a.bits,a.labels,b.labels]
    exact (product_get left.labels right.labels (2^left.bits) index).symm

private theorem related_take {left : List Sparse} {right : List Layout}
    (related : Exact.ListRel Agrees left right) (count : Nat) :
    Exact.ListRel Agrees (left.take count) (right.take count) := by
  induction left generalizing right count with
  | nil => cases right <;> simp_all [Exact.ListRel]
  | cons first rest ih =>
    cases right with
    | nil => exact False.elim related
    | cons firstRaw restRaw =>
      cases count with
      | zero => trivial
      | succ count => exact ⟨related.1,ih related.2 count⟩

private theorem related_drop {left : List Sparse} {right : List Layout}
    (related : Exact.ListRel Agrees left right) (count : Nat) :
    Exact.ListRel Agrees (left.drop count) (right.drop count) := by
  induction left generalizing right count with
  | nil => cases right <;> simp_all [Exact.ListRel]
  | cons first rest ih =>
    cases right with
    | nil => exact False.elim related
    | cons firstRaw restRaw =>
      cases count with
      | zero => exact related
      | succ count => exact ih related.2 count

private theorem folded_agrees {left : List Sparse} {right : List Layout}
    (related : Exact.ListRel Agrees left right) (initial : Sparse) (original : Layout)
    (same : Agrees initial original) :
    Agrees (left.foldl Sparse.tensor initial) (right.foldl Semantics.FiniteCarrier.tensor original) := by
  induction left generalizing right initial original with
  | nil => cases right with
    | nil => exact same
    | cons first rest => exact False.elim related
  | cons first rest ih =>
    cases right with
    | nil => exact False.elim related
    | cons firstRaw restRaw =>
      exact ih related.2 _ _ (tensor_agrees same related.1)

def sparseStep (atom : Atom) (pending : Option (List Sparse)) : Option (List Sparse) := do
  let stack ← pending
  match Semantics.FiniteCarrier.children atom with
  | none => return Sparse.ofLayout (← Semantics.FiniteCarrier.leaf atom) :: stack
  | some arity =>
    if arity > stack.length then none
    else some ((stack.take arity).foldl Sparse.tensor Sparse.singleton :: stack.drop arity)

def sparseLayout (basis : Basis) : Option Sparse := do
  let [result] ← basis.foldr sparseStep (some []) | none
  pure result

private def StackAgrees : Option (List Sparse) → Option (List Layout) → Prop
  | none,none => True
  | some left,some right => Exact.ListRel Agrees left right
  | _,_ => False

private theorem step_agrees (atom : Atom) (left : Option (List Sparse)) (right : Option (List Layout))
    (related : StackAgrees left right) :
    StackAgrees (sparseStep atom left) (Semantics.FiniteCarrier.layoutStep atom right) := by
  cases left with
  | none => cases right <;> simp_all [StackAgrees,sparseStep,Semantics.FiniteCarrier.layoutStep]
  | some left =>
    cases right with
    | none => exact False.elim related
    | some right =>
      have lengths := Exact.listRel_length Agrees left right related
      cases arities : Semantics.FiniteCarrier.children atom with
      | none =>
        cases leaves : Semantics.FiniteCarrier.leaf atom with
        | none => simp [sparseStep,Semantics.FiniteCarrier.layoutStep,arities,leaves,StackAgrees]
        | some leaf =>
          simpa only [sparseStep,Semantics.FiniteCarrier.layoutStep,arities,leaves,bind,Option.bind,
            pure,StackAgrees,Exact.ListRel] using And.intro (ofLayout_agrees leaf) related
      | some arity =>
        by_cases bounded : arity > left.length
        · simp [sparseStep,Semantics.FiniteCarrier.layoutStep,arities,bounded,lengths,StackAgrees]
        · simp only [sparseStep,Semantics.FiniteCarrier.layoutStep,arities,bind,Option.bind,lengths,bounded,
            if_false,StackAgrees,Exact.ListRel]
          exact ⟨folded_agrees (related_take related arity) _ _ (ofLayout_agrees _),related_drop related arity⟩

private theorem fold_agrees (basis : Basis) :
    StackAgrees (basis.foldr sparseStep (some []))
      (basis.foldr Semantics.FiniteCarrier.layoutStep (some [])) := by
  induction basis with
  | nil => trivial
  | cons atom rest ih => exact step_agrees atom _ _ ih

/-- Structural agreement with the actual independent prefix interpreter.
The joined reference label list occurs only in this erased proof. -/
theorem sparseLayout_reference (basis : Basis) (sparse : Sparse)
    (read : sparseLayout basis = some sparse) :
    ∃ layout,Semantics.FiniteCarrier.layout basis = some layout ∧ Agrees sparse layout := by
  have related := fold_agrees basis
  unfold sparseLayout at read
  cases left : basis.foldr sparseStep (some []) with
  | none => simp [left] at read
  | some stack =>
    cases stack with
    | nil => simp [left] at read
    | cons first rest =>
      cases rest with
      | cons second rest => simp [left] at read
      | nil =>
        have same : first = sparse := by
          simpa only [left,bind,Option.bind,pure,Option.some.injEq] using read
        subst first
        cases right : basis.foldr Semantics.FiniteCarrier.layoutStep (some []) with
        | none => simp [left,right,StackAgrees] at related
        | some actual =>
          cases actual with
          | nil => simp [left,right,StackAgrees,Exact.ListRel] at related
          | cons original tail =>
            cases tail with
            | cons second rest => simp [left,right,StackAgrees,Exact.ListRel] at related
            | nil =>
              have pair : Agrees sparse original ∧ True := by
                simpa only [left,right,StackAgrees,Exact.ListRel] using related
              exact ⟨original,by simp [Semantics.FiniteCarrier.layout,right],pair.1⟩

def carrierOwners (bindings : Map) : List Semantics.CarrierInterface.Owner :=
  bindings.map fun binding => ⟨binding.port,binding.owner.basis⟩

def forestBasis (bindings : Map) : Basis := Semantics.CarrierInterface.forest (carrierOwners bindings)

def forestAxes (frame : List Nat) (bindings : Map) : List Nat :=
  (bindings.flatMap fun binding => binding.port.wires).map frame.idxOf

/-- One entry of an encoding, with no allocation of its matrix. -/
def sparseEntry (sparse : Sparse) (physical logical : Nat) : Scalar :=
  if sparse.coordinate logical == some physical then Scalar.one else Scalar.zero

private theorem encoding_entry (layout : Layout) (row col : Nat)
    (rowBound : row < 2^layout.bits) (colBound : col < layout.labels.length) :
    (Semantics.FiniteCarrier.encoding layout).entry row col =
      (if layout.labels[col]? == some row then Scalar.one else Scalar.zero) := by
  have positive : 0 < layout.labels.length := Nat.lt_of_le_of_lt (Nat.zero_le col) colBound
  have indexBound : row*layout.labels.length+col < 2^layout.bits*layout.labels.length := by
    calc
      row*layout.labels.length+col < row*layout.labels.length+layout.labels.length := Nat.add_lt_add_left colBound _
      _ = (row+1)*layout.labels.length := (Nat.succ_mul _ _).symm
      _ ≤ 2^layout.bits*layout.labels.length := Nat.mul_le_mul_right _ rowBound
  have remainder : (row*layout.labels.length+col) % layout.labels.length = col := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt colBound]
  have quotient : (row*layout.labels.length+col) / layout.labels.length = row := by
    rw [Nat.mul_comm row layout.labels.length,Nat.mul_add_div positive,Nat.div_eq_of_lt colBound,Nat.add_zero]
  simp only [Semantics.FiniteCarrier.encoding,Matrix.entry,List.getElem?_map,
    List.getElem?_range indexBound,Option.map_some,Option.getD_some,remainder,quotient]

/-- Agreement is with the independent encoding's actual coefficient, at all
valid coordinates. This proof never evaluates a large concrete encoding. -/
theorem Agrees.encodingEntry {code : Sparse} {layout : Layout} (same : Agrees code layout)
    (physical logical : Nat) (physicalBound : physical < 2^layout.bits)
    (logicalBound : logical < layout.labels.length) :
    sparseEntry code physical logical = (Semantics.FiniteCarrier.encoding layout).entry physical logical := by
  unfold sparseEntry
  rw [same.labels,encoding_entry layout physical logical physicalBound logicalBound]

/-- Each coordinate is in the actual Raw caller-frame order. The enclosing
binding list retains every original owner boundary, including zero-width ones. -/
def embed (frame : List Nat) (bindings : Map) (code : Sparse) (physical logical : Nat) : Scalar :=
  sparseEntry code (Semantics.Finite.gather physical (forestAxes frame bindings)) logical

structure OwnerCode (binding : Binding) where
  layout : Layout
  original : RuntimeInterval.Computed
    (Carrier.readOwner ⟨binding.port,binding.owner.basis⟩) layout

inductive OwnerCodes : Map → Type where
  | nil : OwnerCodes []
  | cons {binding bindings} (first : OwnerCode binding) (rest : OwnerCodes bindings) :
      OwnerCodes (binding::bindings)

private def readOwners (bindings : Map) : WorkM (OwnerCodes bindings) :=
  (Nat.rec (motive := fun fuel => (bindings : Map) → bindings.length ≤ fuel → WorkM (OwnerCodes bindings))
    (fun bindings bound => match bindings with
      | [] => pure .nil
      | _ :: rest => False.elim (Nat.not_succ_le_zero rest.length bound))
    (fun _ next bindings bound => match bindings with
      | [] => pure .nil
      | binding :: rest => do
        let layout ← SourceTypes.NaturalAffine.witness (Carrier.readOwner ⟨binding.port,binding.owner.basis⟩)
        let tail ← next rest (Nat.le_of_succ_le_succ bound)
        pure (.cons ⟨layout.val,by with_reducible exact layout.property⟩ tail))
    bindings.length) bindings (Nat.le_refl _)

structure Frame {roles : List Owner} {state : RuntimeOwnerMap.State}
    (checked : RuntimeOwnerMap.Checked roles state) where
  owners : OwnerCodes checked.bindings
  code : Sparse
  original : sparseLayout (forestBasis checked.bindings) = some code

/-- All scalar owner checks remain the existing per-owner finite reader.
Combining their source trees builds only sparse tensor coordinates. -/
def readFrame {roles state} (checked : RuntimeOwnerMap.Checked roles state) : WorkM (Frame checked) := do
  let nodes := (checked.bindings.map fun binding => binding.owner.basis.length+1).sum
  exactWork (Exact.charge (16*128*(nodes+1)))
  let owners ← readOwners checked.bindings
  match original : sparseLayout (forestBasis checked.bindings) with
  | none => throw .request
  | some code => pure ⟨owners,code,original⟩

def Frame.embedding {roles state checked} (frame : @Frame roles state checked) : Nat → Nat → Scalar :=
  embed state.quantum.frame checked.bindings frame.code

theorem Frame.originalCode {roles state checked} (frame : @Frame roles state checked) :
    ∃ layout,Semantics.FiniteCarrier.layout (forestBasis checked.bindings) = some layout ∧
      Agrees frame.code layout := sparseLayout_reference _ _ frame.original

/-- Neither complete-frame coverage nor nominal/zero-width identity is replaced
by the sparse coordinate product. The same ordered binding map remains present. -/
theorem Frame.complete {roles state checked} (_frame : @Frame roles state checked) :
    (checked.bindings.map (·.owner)) = roles ∧
      (checked.bindings.map (·.port)).Perm state.quantum.live := ⟨checked.ordered,checked.complete⟩

theorem Frame.encodingEntries {roles state checked} (frame : @Frame roles state checked) :
    ∃ layout,Semantics.FiniteCarrier.layout (forestBasis checked.bindings) = some layout ∧
      ∀ physical logical,
        Semantics.Finite.gather physical (forestAxes state.quantum.frame checked.bindings) < 2^layout.bits →
        logical < layout.labels.length →
        frame.embedding physical logical = (Semantics.FiniteCarrier.encoding layout).entry
          (Semantics.Finite.gather physical (forestAxes state.quantum.frame checked.bindings)) logical := by
  obtain ⟨layout,original,same⟩ := frame.originalCode
  refine ⟨layout,original,?_ ⟩
  intro physical logical physicalBound logicalBound
  exact same.encodingEntry _ _ physicalBound logicalBound

def portAxes (frame : List Nat) (ports : List Semantics.Raw.Port) : List Nat :=
  (ports.flatMap (·.wires)).map frame.idxOf

/-- Spectators are indexed by their complete ordered bindings. Distinct
zero-width owners remain distinct entries even though their coordinate is 0. -/
def spectatorCoordinates (frame : List Nat) (spectators : Map) (physical : Nat) : List Nat :=
  spectators.map fun binding => Semantics.Finite.gather physical (binding.port.wires.map frame.idxOf)

/-- Apply one already-composed local kernel to an arbitrary joint amplitude
slice. There is no factorization into a selected and a spectator vector. Every
sum/multiplication keeps its original bounded arithmetic and first error. -/
def liftKernel (frame : List Nat) (selected : List Semantics.Raw.Port) (spectators : Map)
    (kernel : Matrix) (values : List Nat → Nat → WorkM Scalar) (output : Nat) : WorkM Scalar :=
  Raw.Coefficient.sum kernel.cols fun input => do
    let value ← values (spectatorCoordinates frame spectators output) input
    Raw.ProtectedEvaluation.multiply value
      (kernel.entry (Semantics.Finite.gather output (portAxes frame selected)) input)

/-- The lifted equation retains the actual successful local compositions. It
does not assert a reassociation of partial scalar arithmetic or a replacement
of the original Raw circuit by a producer-supplied kernel. -/
def LiftedEquation (inputCode outputCode physical logical : Matrix)
    (frame : List Nat) (selected : List Semantics.Raw.Port) (spectators : Map) : Prop :=
  ∃ actual specified a b c d,
    Exact.Matrix.compose physical inputCode a = (.ok actual,b) ∧
    Exact.Matrix.compose outputCode logical c = (.ok specified,d) ∧
    ∀ (Reference : Type) (values : Reference → List Nat → Nat → WorkM Scalar),
      (fun reference output => liftKernel frame selected spectators actual (values reference) output) =
      (fun reference output => liftKernel frame selected spectators specified (values reference) output)

theorem lift_composition {inputCode outputCode physical logical : Matrix}
    (equation : CodeSpace.CompositionEquation inputCode outputCode physical logical)
    (frame : List Nat) (selected : List Semantics.Raw.Port) (spectators : Map) :
    LiftedEquation inputCode outputCode physical logical frame selected spectators := by
  obtain ⟨kernel,a,b,c,d,actual,specified⟩ := equation
  exact ⟨kernel,kernel,a,b,c,d,actual,specified,fun _ _ => rfl⟩

/-- Concrete local E for the actual primitive action, extended through every
spectator/reference amplitude in the same actual caller output frame. -/
theorem primitiveReferences {dependencies program block start count input output role kind}
    (action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    {roles : List Owner} (complete : RuntimeOwnerMap.Checked roles action.interval.interval.after) :
    LiftedEquation action.inputCode action.outputCode action.physical action.expected
      action.interval.interval.after.quantum.frame action.interval.returned
      (complete.bindings.filter fun binding => binding.port.token != output) :=
  lift_composition action.fullCodeEquation _ _ _

def selectedBasis (ports : List Semantics.Raw.Port) (roles : List Owner) : Basis :=
  Semantics.CarrierInterface.forest (RuntimeStructuralAction.owners ports roles)

/-- Explicit source join/split supplies this equality. Its output owner list
is distinct; no width, singleton cardinality or reassociation rule is inferred. -/
theorem structuralSparse {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) :
    sparseLayout (selectedBasis action.inputs action.inputRoles) =
      sparseLayout (selectedBasis action.outputs action.outputRoles) := by
  unfold selectedBasis
  rw [action.coordinates]

/-- The actual Raw structural step is identity on every reference-indexed
lazy amplitude function. No product-state or separability premise is used. -/
theorem structuralReferences {Reference : Type} {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (values : Reference → Raw.Coefficient.State) :
    (fun reference => (Semantics.RawTrace.step action.interval.before.quantum.reference action.operation).map
      (fun (_,events) => events.foldl (fun state operation => Raw.Coefficient.event dependencies operation state)
        (values reference))) = (fun reference => some (values reference)) := by
  funext reference
  exact action.coefficients (values reference)

structure Root {sources owner name signature body root prepared request}
    (boundary : @RuntimeStructuredRoot.Boundary sources owner name signature body root prepared request) where
  input : Frame boundary.inputs.owners
  output : Frame boundary.owners

/-- Reuse both complete maps from the already checked original root boundary.
No accepted root, storage order, or function interface is reconstructed here. -/
def readRoot {sources owner name signature body root prepared request}
    (boundary : @RuntimeStructuredRoot.Boundary sources owner name signature body root prepared request) :
    WorkM (Root boundary) := do
  let input ← readFrame boundary.inputs.owners
  let output ← readFrame boundary.owners
  pure ⟨input,output⟩

/-- The sparse output forest follows the original source's full result order,
including separate zero-width owners. The actual Raw final permutation is
retained rather than replaced with equal physical widths. -/
theorem Root.outputOrder {sources owner name signature body root prepared request boundary}
    (_code : @Root sources owner name signature body root prepared request boundary) :
    (boundary.owners.bindings.map fun binding => binding.port.token) = root.program.outputs := by
  have order := boundary.outputs.rawOutputs
  rw [boundary.outputs.originalOwners] at order
  simpa only [RuntimeSourceBoundary.returnedOwners,List.map_map] using order

/-- Literal whole-program composition and sparse full-frame code are about the
same original body/root. Local Raw/code commutation must still be established
for each retained node before this can become a sequential action theorem. -/
theorem Root.literalComposition {artifact root owner name signature body context initial checked request boundary}
    (composition : @RuntimePureComposition.Prepared artifact root owner name signature body context initial checked)
    (code : @Root artifact.sources owner name signature body root checked.result.prepared request boundary) :
    (checked.result.actions.flatMap RuntimePureComposition.operations).map Semantics.Observation.Op.pure =
        checked.result.prepared.block.operations ∧
      (boundary.owners.bindings.map fun binding => binding.port.token) = root.program.outputs :=
  ⟨composition.partition.literal,code.outputOrder⟩

end QleisliKernel.Qirf.RuntimeForestCode
