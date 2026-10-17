import QleisliKernel.Hierarchical.Artifact

/-! Complete typed side maps, used by hierarchical calls and rewires.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
These checks establish coordinate permutations, not a circuit's meaning or the
fresh renaming relationship between both sides of a call. -/

namespace QleisliKernel.Hierarchical.Ports
open Artifact

/-- Axis IDs are local labels. Canonical coordinates follow the declared port
and within-port order, without sorting IDs or flattening type trees. -/
def coordinateStep (state : Nat × Layout.Interface) (port : QuantumPort) :
    Nat × Layout.Interface :=
  (state.1 + port.axes.size,
    ⟨port.basis.toList, (List.range port.axes.size).map (state.1 + ·)⟩ :: state.2)

def coordinatesFrom (offset : Nat) (ports : List QuantumPort) : Layout.Interface :=
  (ports.foldl coordinateStep (offset, [])).2.reverse

theorem coordinateFold_length (ports : List QuantumPort) (offset : Nat) (acc : Layout.Interface) :
    (ports.foldl coordinateStep (offset, acc)).2.length = acc.length + ports.length := by
  induction ports generalizing offset acc with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons port rest ih =>
    simpa only [List.foldl_cons, coordinateStep, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (offset + port.axes.size)
        (⟨port.basis.toList, (List.range port.axes.size).map (offset + ·)⟩ :: acc)

def coordinates (side : Side) : Layout.Interface := coordinatesFrom 0 side.quantum.toList

theorem coordinatesFrom_length (ports : List QuantumPort) (offset : Nat) :
    (coordinatesFrom offset ports).length = ports.length := by
  simp only [coordinatesFrom, List.length_reverse, coordinateFold_length, List.length_nil, Nat.zero_add]

theorem coordinates_length (side : Side) : (coordinates side).length = side.quantum.size := by
  simp only [coordinates, coordinatesFrom_length, Array.length_toList]

/-- The exact sum of per-port widths, with zero-width ports retained. -/
private def coordinateWidth (ports : List QuantumPort) : Nat :=
  ports.foldr (fun port total => port.axes.size + total) 0

private theorem coordinateFold_acc (ports : List QuantumPort) (offset : Nat)
    (acc : Layout.Interface) :
    (ports.foldl coordinateStep (offset, acc)).2.reverse =
      acc.reverse ++ (ports.foldl coordinateStep (offset, [])).2.reverse := by
  induction ports generalizing offset acc with
  | nil => simp
  | cons port rest ih =>
    simp only [List.foldl_cons, coordinateStep]
    rw [ih (offset := offset + port.axes.size)
      (acc := ⟨port.basis.toList, (List.range port.axes.size).map (offset + ·)⟩ :: acc)]
    rw [ih (offset := offset + port.axes.size)
      (acc := [⟨port.basis.toList, (List.range port.axes.size).map (offset + ·)⟩])]
    simp [List.reverse_cons, List.append_assoc]

private theorem coordinatesFrom_cons (offset : Nat) (port : QuantumPort)
    (rest : List QuantumPort) :
    coordinatesFrom offset (port :: rest) =
      ⟨port.basis.toList, (List.range port.axes.size).map (offset + ·)⟩ ::
        coordinatesFrom (offset + port.axes.size) rest := by
  simp only [coordinatesFrom, List.foldl_cons, coordinateStep]
  rw [coordinateFold_acc]
  simp

private theorem coordinatesFrom_wires (ports : List QuantumPort) (offset : Nat) :
    Layout.wires (coordinatesFrom offset ports) = List.range' offset (coordinateWidth ports) := by
  induction ports generalizing offset with
  | nil => simp [coordinatesFrom, Layout.wires, coordinateWidth]
  | cons port rest ih =>
    rw [coordinatesFrom_cons]
    change (List.range port.axes.size).map (offset + ·) ++
      Layout.wires (coordinatesFrom (offset + port.axes.size) rest) = _
    rw [ih]
    simpa only [coordinateWidth, List.range'_eq_map_range] using
      (List.range'_append_1 (s := offset) (m := port.axes.size) (n := coordinateWidth rest))

private theorem physicalFold_width (ports : List QuantumPort) (acc : Array Nat) :
    (ports.foldl (fun axes port => axes ++ port.axes) acc).size =
      acc.size + coordinateWidth ports := by
  induction ports generalizing acc with
  | nil => simp [coordinateWidth]
  | cons port rest ih =>
    simp only [List.foldl_cons, ih, Array.size_append, coordinateWidth, List.foldr_cons]
    omega

theorem coordinates_wires_length (side : Side) :
    (Layout.wires (coordinates side)).length = (wires side).size := by
  rw [coordinates, coordinatesFrom_wires]
  simp only [List.length_range']
  rw [Artifact.wires, ← Array.foldl_toList, physicalFold_width]
  simp

private theorem quantum_widths (side : Side) (valid : sideValid side = true) :
    ∀ port ∈ side.quantum.toList, Layout.basisWidth port.basis.toList = some port.axes.size := by
  unfold sideValid at valid
  split at valid
  next rejected => contradiction
  next bounded =>
    simp only [Bool.and_eq_true] at valid
    have all := valid.1.1.1.1.1
    rw [← Array.all_toList] at all
    intro port member
    have checked := (List.all_eq_true.mp all) port member
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    exact checked.1.2

private theorem coordinatesFrom_types (ports : List QuantumPort) (offset : Nat)
    (valid : ∀ port ∈ ports, Layout.basisWidth port.basis.toList = some port.axes.size) :
    (coordinatesFrom offset ports).all
      (fun port => Layout.basisWidth port.basis == some port.axes.length) = true := by
  induction ports generalizing offset with
  | nil => simp [coordinatesFrom]
  | cons port rest ih =>
    rw [coordinatesFrom_cons]
    simp only [List.all_cons, Bool.and_eq_true, List.length_map, List.length_range, beq_iff_eq]
    refine ⟨valid port (by simp), ih (offset + port.axes.size) ?_⟩
    intro other member
    exact valid other (by simp [member])

/-- Actual side validity fixes every type tree and width. Coordinates preserve
all ports and assign a contiguous local axis range without sorting source IDs. -/
theorem coordinates_interfaceValid (side : Side) (valid : sideValid side = true) :
    Layout.interfaceValid (coordinates side) = true := by
  have types := coordinatesFrom_types side.quantum.toList 0 (quantum_widths side valid)
  have wiresRange : Layout.wires (coordinates side) =
      List.range (coordinateWidth side.quantum.toList) := by
    simpa only [coordinates, ← List.range_eq_range'] using
      coordinatesFrom_wires side.quantum.toList 0
  change (coordinates side).all
    (fun port => Layout.basisWidth port.basis == some port.axes.length) = true at types
  unfold Layout.interfaceValid
  rw [wiresRange]
  simp only [List.nodup_range, decide_true, Bool.and_true]
  simp only [Bool.and_eq_true]
  constructor
  · exact types
  · simp only [List.length_range, List.all_eq_true, decide_eq_true_eq]
    intro i member
    exact List.mem_range.mp member

def layout (source destination : Side) (map : PortMap) : Layout.Rewire :=
  ⟨coordinates source, coordinates destination, map.owners.toList, map.axes.toList⟩

/-- A candidate inverse is computed from the actual map, never supplied by an
untrusted producer. Missing or duplicated positions fail the two inverse laws. -/
def inverse (n : Nat) (map : Array Nat) : List Nat :=
  let forward := map.toList
  (List.range n).map (fun i => forward.findIdx (· == i))

private theorem findIdx_range (n i : Nat) (inside : i < n) :
    (List.range n).findIdx (· == i) = i := by
  apply (List.findIdx_eq (by simpa using inside)).2
  constructor
  · simp
  · intro j before
    simp only [List.getElem_range, beq_eq_false_iff_ne]
    omega

private theorem inverse_range (n : Nat) : inverse n (Array.range n) = List.range n := by
  unfold inverse
  simp only [Array.toList_range]
  calc
    (List.range n).map (fun i => (List.range n).findIdx (· == i)) =
        (List.range n).map (fun i => i) := by
      apply List.map_eq_map_iff.mpr
      intro i member
      exact findIdx_range n i (List.mem_range.mp member)
    _ = List.range n := by simp

def witness (source : Side) (map : PortMap) : Layout.Witness :=
  ⟨inverse source.quantum.size map.owners, inverse (wires source).size map.axes⟩

def ClassicalMatch (source destination : Side) (map : PortMap) : Prop :=
  source.classical.size = destination.classical.size ∧
  Layout.Permutation source.classical.size map.classical.toList
    (inverse source.classical.size map.classical) ∧
  ∀ i : Fin destination.classical.size,
    ∃ input, source.classical[Layout.indexAt map.classical.toList i]? = some input ∧
      input.basis = destination.classical[i].basis

instance (source destination : Side) (map : PortMap) :
    Decidable (ClassicalMatch source destination map) := by
  unfold ClassicalMatch
  infer_instance

def shapeValid (source destination : Side) (map : PortMap) : Bool :=
  sideValid source && sideValid destination &&
  Layout.structureValid (layout source destination map) (witness source map) &&
  decide (ClassicalMatch source destination map)

/-- Exact positional identity only. Canonical coordinate-port equality
compares every ordered basis tree and per-port axis range, including Unit and
Bits0 owners; it neither sorts IDs nor compares only flattened widths. -/
def positionalIdentity (source destination : Side) (map : PortMap) : Bool :=
  source.quantum.size == destination.quantum.size &&
  source.classical.size == destination.classical.size &&
  map.owners == Array.range source.quantum.size &&
  map.axes == Array.range (wires source).size &&
  map.classical == Array.range source.classical.size &&
  decide (coordinates source = coordinates destination) &&
  decide (source.classical.map ClassicalPort.basis = destination.classical.map ClassicalPort.basis)

private theorem identityClassical (source destination : Side) (map : PortMap)
    (count : source.classical.size = destination.classical.size)
    (mapping : map.classical = Array.range source.classical.size)
    (bases : source.classical.map ClassicalPort.basis =
      destination.classical.map ClassicalPort.basis) : ClassicalMatch source destination map := by
  refine ⟨count, ?_, ?_⟩
  · simpa only [mapping, Array.toList_range, inverse_range] using
      Layout.range_permutation source.classical.size
  · intro i
    have inside : i.val < source.classical.size := by omega
    refine ⟨source.classical[i.val], ?_, ?_⟩
    · simp [Layout.indexAt, mapping, inside]
    · have equal := congrArg (fun entries : Array Basis => entries[i.val]?) bases
      simpa only [Array.getElem?_map, Array.getElem?_eq_getElem inside,
        Array.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq] using equal

private theorem positionalIdentity_sound (source destination : Side) (map : PortMap)
    (before : sideValid source = true) (_after : sideValid destination = true)
    (identity : positionalIdentity source destination map = true) :
    Layout.structureValid (layout source destination map) (witness source map) = true ∧
      ClassicalMatch source destination map := by
  simp only [positionalIdentity, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at identity
  obtain ⟨⟨⟨⟨⟨⟨quantumCount, classicalCount⟩, owners⟩, axes⟩, classical⟩, ports⟩, bases⟩ := identity
  constructor
  · simpa only [layout, witness, owners, axes, inverse_range, Array.toList_range,
      ← ports, coordinates_length, coordinates_wires_length] using
      Layout.identity_structureValid (coordinates source) (coordinates_interfaceValid source before)
  · exact identityClassical source destination map classicalCount classical bases

/-- This prepared helper is used only after complete Side headers were checked
on this same immutable artifact. A failed identity selector still runs the full
existing map predicate; its work is charged by the prepared caller. -/
def shapeAfterHeaders (source destination : Side) (map : PortMap) : Bool :=
  if positionalIdentity source destination map then true else
    Layout.structureValid (layout source destination map) (witness source map) &&
      decide (ClassicalMatch source destination map)

theorem shapeAfterHeaders_eq (source destination : Side) (map : PortMap)
    (before : sideValid source = true) (after : sideValid destination = true) :
    shapeAfterHeaders source destination map = shapeValid source destination map := by
  by_cases identity : positionalIdentity source destination map = true
  · have original := positionalIdentity_sound source destination map before after identity
    simp [shapeAfterHeaders, shapeValid, identity, before, after, original.1, original.2]
  · have rejected : positionalIdentity source destination map = false := by
      cases outcome : positionalIdentity source destination map <;> simp_all
    simp [shapeAfterHeaders, shapeValid, rejected, before, after]

def atoms (side : Side) : Nat :=
  side.quantum.foldl (fun n p => n + p.basis.size) 0 +
  side.classical.foldl (fun n p => n + p.basis.size) 0

/-- Read array sizes without allocating flattened coordinates on rejected input. -/
def wireCount (side : Side) : Nat := side.quantum.foldl (fun n p => n + p.axes.size) 0

/-- Constant-time array sizes are charged before any traversal. -/
def scanCharge (source destination : Side) (map : PortMap) : Nat :=
  8 * (1 + sideScan source + sideScan destination + mapCharge map)^2

/-- Conservative quadratic charge covers canonical coordinate construction,
computed inverse searches, uniqueness, prefix trees and all structural equality. -/
def workCharge (source destination : Side) (map : PortMap) : Nat :=
  scanCharge source destination map +
    8 * (1 + sideScan source + sideScan destination + mapCharge map +
      atoms source + atoms destination + wireCount source + wireCount destination)^2

/-- Array lengths only: this is charged before reading per-port fields to
compute the full identity-attempt allowance. No range or inverse is built. -/
def identityScanCharge (source destination : Side) (map : PortMap) : Nat :=
  4 * (1 + sideScan source + sideScan destination + mapCharge map)

/-- Covers two actual selector evaluations (cost selection and predicate),
range and coordinate construction, complete type/classical comparisons, and
all field scans used to select the charge. A failed selector retains this
whole allowance in addition to the original full map charge. -/
def identityAttemptCharge (source destination : Side) (map : PortMap) : Nat :=
  identityScanCharge source destination map +
    16 * (1 + sideScan source + sideScan destination + mapCharge map +
      atoms source + atoms destination + wireCount source + wireCount destination)

/-- A raw-size upper bound used only to select the unchanged legacy route
before any optional selector or per-port attempt-cost scan. Complete checked
Side headers bound every basis to 128 atoms and each side to 16 axes. -/
def identityAttemptUpper (source destination : Side) (map : PortMap) : Nat :=
  identityScanCharge source destination map +
    16 * (1 + sideScan source + sideScan destination + mapCharge map +
      128 * (sideScan source + sideScan destination) + 32)

private theorem basisValid_size (basis : Basis) (valid : basisValid basis = true) :
    basis.size ≤ 128 := by
  unfold basisValid at valid
  split at valid
  next oversized => contradiction
  next bounded => omega

private theorem basisFold_bound {α : Type} (ports : List α) (basis : α → Basis)
    (acc : Nat) (bounded : ∀ port ∈ ports, (basis port).size ≤ 128) :
    ports.foldl (fun n port => n + (basis port).size) acc ≤ acc + 128 * ports.length := by
  induction ports generalizing acc with
  | nil => simp
  | cons port rest ih =>
    have head := bounded port (by simp)
    have tail := ih (acc + (basis port).size) (by
      intro other member
      exact bounded other (by simp [member]))
    simp only [List.foldl_cons, List.length_cons]
    omega

private theorem sideIdentityBounds (side : Side) (valid : sideValid side = true) :
    atoms side ≤ 128 * sideScan side ∧ wireCount side ≤ 16 := by
  unfold sideValid at valid
  split at valid
  next oversized => contradiction
  next bounded =>
    simp only [Bool.and_eq_true] at valid
    have quantum := valid.1.1.1.1.1
    have classical := valid.1.1.1.1.2
    rw [← Array.all_toList] at quantum classical
    have q := basisFold_bound side.quantum.toList QuantumPort.basis 0 (by
      intro port member
      have checked := (List.all_eq_true.mp quantum) port member
      simp only [Bool.and_eq_true] at checked
      exact basisValid_size port.basis checked.1.1.2)
    have c := basisFold_bound side.classical.toList ClassicalPort.basis 0 (by
      intro port member
      have checked := (List.all_eq_true.mp classical) port member
      simp only [Bool.and_eq_true] at checked
      exact basisValid_size port.basis checked.2)
    simp only [Array.length_toList, Nat.zero_add] at q c
    constructor
    · unfold atoms sideScan
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      omega
    · simpa only [wireCount] using Nat.le_of_not_gt bounded

/-- The pre-selector legacy routing bound is proved from complete checked
headers, including every zero-width port and every ordered type tree. -/
theorem identityAttemptCharge_le_upper (source destination : Side) (map : PortMap)
    (before : sideValid source = true) (after : sideValid destination = true) :
    identityAttemptCharge source destination map ≤ identityAttemptUpper source destination map := by
  have s := sideIdentityBounds source before
  have d := sideIdentityBounds destination after
  unfold identityAttemptCharge identityAttemptUpper
  omega

/-- Only a proven exact identity omits the old inverse/permutation algorithm.
Failed attempts pay for their complete scan and the complete original path. -/
def selectedWorkCharge (source destination : Side) (map : PortMap) : Nat :=
  identityAttemptCharge source destination map +
    if positionalIdentity source destination map then 0 else workCharge source destination map

theorem selectedWorkCharge_le_original_upper (source destination : Side) (map : PortMap)
    (before : sideValid source = true) (after : sideValid destination = true) :
    selectedWorkCharge source destination map ≤
      workCharge source destination map + identityAttemptUpper source destination map := by
  have attempt := identityAttemptCharge_le_upper source destination map before after
  unfold selectedWorkCharge
  split <;> omega


structure Checked where
  visits : Nat
  deriving Repr

/-- `remaining` comes from the enclosing verifier's shared budget. This result
is ordinary structural data and never authorizes a quantum semantic equation. -/
def check (source destination : Side) (map : PortMap) (remaining : Nat) :
    Except Error Checked :=
  if remaining > Limits.maxVisits || scanCharge source destination map > remaining then .error .limit
  else if workCharge source destination map > remaining then .error .limit
  else if !shapeValid source destination map then .error .invalidIr
  else .ok ⟨workCharge source destination map⟩

theorem check_conditions (source destination : Side) (map : PortMap) (remaining : Nat)
    (checked : Checked) (accepted : check source destination map remaining = .ok checked) :
    checked.visits = workCharge source destination map ∧ checked.visits ≤ remaining ∧
    remaining ≤ 2000000 ∧ shapeValid source destination map = true := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next bounded =>
    split at accepted
    next invalid => contradiction
    next enough =>
      split at accepted
      next invalid => contradiction
      next valid =>
        cases Except.ok.inj accepted
        have limits : remaining ≤ 2000000 ∧ scanCharge source destination map ≤ remaining := by
          simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] using bounded
        exact ⟨rfl, Nat.le_of_not_gt enough, limits.1, by simpa using valid⟩

theorem check_structure (source destination : Side) (map : PortMap) (remaining : Nat)
    (checked : Checked) (accepted : check source destination map remaining = .ok checked) :
    Layout.structureValid (layout source destination map) (witness source map) = true ∧
    ClassicalMatch source destination map := by
  have valid := (check_conditions source destination map remaining checked accepted).2.2.2
  simp only [shapeValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact ⟨valid.1.2, valid.2⟩

theorem check_owners (source destination : Side) (map : PortMap) (remaining : Nat)
    (checked : Checked) (accepted : check source destination map remaining = .ok checked) :
    Layout.Permutation source.quantum.size map.owners.toList
      (witness source map).inverseOwners := by
  have valid := (check_structure source destination map remaining checked accepted).1
  simp only [Layout.structureValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  simpa only [layout, coordinates_length] using valid.1.1.2

theorem check_axes (source destination : Side) (map : PortMap) (remaining : Nat)
    (checked : Checked) (accepted : check source destination map remaining = .ok checked) :
    Layout.Permutation (Layout.wires (coordinates source)).length map.axes.toList
      (witness source map).inverseAxes := by
  have valid := (check_structure source destination map remaining checked accepted).1
  simp only [Layout.structureValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.2

theorem check_types (source destination : Side) (map : PortMap) (remaining : Nat)
    (checked : Checked) (accepted : check source destination map remaining = .ok checked) :
    Layout.PortsMatch (layout source destination map) := by
  have valid := (check_structure source destination map remaining checked accepted).1
  simp only [Layout.structureValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.2

/-- The checked coordinate operation has a two-sided inverse and leaves an
arbitrary reference untouched. This says nothing about product-state inputs. -/
theorem check_reference_round_trip (source destination : Side) (map : PortMap) (remaining : Nat)
    (checked : Checked) (accepted : check source destination map remaining = .ok checked) {R C : Type}
    (amplitude : (Fin (Layout.wires (coordinates source)).length → Bool) → R → C) :
    let h := check_axes source destination map remaining checked accepted
    (fun bits reference => amplitude
      (Layout.reindex map.axes.toList h.forwardBound
        (Layout.reindex (witness source map).inverseAxes h.backwardBound bits)) reference) = amplitude := by
  dsimp
  funext bits reference
  rw [Layout.reindex_round_trip (check_axes source destination map remaining checked accepted)]

/- Bounded independently authored structural regressions for the complete
existing predicate and exact identity selector. -/
namespace PositionalIdentityRegression

private def zeroOwners : Side :=
  ⟨#[⟨11, #[.unit], #[]⟩, ⟨12, #[.bits 0], #[]⟩], #[]⟩
private def oneZeroOwner : Side := ⟨#[⟨11, #[.unit], #[]⟩], #[]⟩
private def zeroMap : PortMap := ⟨#[0,1], #[], #[]⟩
private def bitBefore : Side := ⟨#[⟨31, #[.bit], #[9]⟩], #[]⟩
private def bitAfter : Side := ⟨#[⟨47, #[.bit], #[4]⟩], #[]⟩
private def bitMap : PortMap := ⟨#[0], #[0], #[]⟩
private def tupleBefore : Side := ⟨#[⟨3, #[.tuple 2,.unit,.bit], #[8]⟩], #[]⟩
private def tupleWrong : Side := ⟨#[⟨3, #[.tuple 2,.bit,.unit], #[8]⟩], #[]⟩
private def twoBits : Side := ⟨#[⟨6, #[.bit], #[5]⟩, ⟨7, #[.bit], #[1]⟩], #[]⟩
private def swapMap : PortMap := ⟨#[1,0], #[1,0], #[]⟩
private def disagreeingMap : PortMap := ⟨#[1,0], #[0,1], #[]⟩
private def classicalBefore : Side := ⟨#[], #[⟨2, #[.bit]⟩]⟩
private def classicalAfter : Side := ⟨#[], #[⟨9, #[.bit]⟩]⟩
private def classicalWrong : Side := ⟨#[], #[⟨9, #[.bits 1]⟩]⟩
private def classicalMap : PortMap := ⟨#[], #[], #[0]⟩

private theorem zero_owners_are_retained :
    positionalIdentity zeroOwners zeroOwners zeroMap = true ∧
      shapeAfterHeaders zeroOwners zeroOwners zeroMap = shapeValid zeroOwners zeroOwners zeroMap := by
  decide +kernel

private theorem dropping_a_zero_owner_is_rejected :
    positionalIdentity zeroOwners oneZeroOwner zeroMap = false ∧
      shapeAfterHeaders zeroOwners oneZeroOwner zeroMap = false := by
  decide +kernel

private theorem canonical_positions_allow_separately_checked_renaming :
    positionalIdentity bitBefore bitAfter bitMap = true ∧
      shapeAfterHeaders bitBefore bitAfter bitMap = shapeValid bitBefore bitAfter bitMap := by
  decide +kernel

private theorem exact_tuple_tree_is_preserved :
    positionalIdentity tupleBefore tupleBefore bitMap = true ∧
      shapeAfterHeaders tupleBefore tupleBefore bitMap = true := by
  decide +kernel

private theorem equal_width_reordered_type_tree_is_rejected :
    positionalIdentity tupleBefore tupleWrong bitMap = false ∧
      shapeAfterHeaders tupleBefore tupleWrong bitMap = false := by
  decide +kernel

private theorem nonidentity_maps_retain_complete_old_fallback :
    positionalIdentity twoBits twoBits swapMap = false ∧
      shapeAfterHeaders twoBits twoBits swapMap = true := by
  decide +kernel

private theorem owner_axis_disagreement_is_rejected :
    positionalIdentity twoBits twoBits disagreeingMap = false ∧
      shapeAfterHeaders twoBits twoBits disagreeingMap = false := by
  decide +kernel

private theorem classical_bases_are_complete_types :
    positionalIdentity classicalBefore classicalAfter classicalMap = true ∧
      shapeAfterHeaders classicalBefore classicalAfter classicalMap = true ∧
      positionalIdentity classicalBefore classicalWrong classicalMap = false ∧
      shapeAfterHeaders classicalBefore classicalWrong classicalMap = false := by
  decide +kernel

end PositionalIdentityRegression

end QleisliKernel.Hierarchical.Ports
