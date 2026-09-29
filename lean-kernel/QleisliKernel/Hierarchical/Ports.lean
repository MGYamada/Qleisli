import QleisliKernel.Hierarchical.Artifact

/-! Complete typed side maps, used by hierarchical calls and rewires.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
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

def layout (source destination : Side) (map : PortMap) : Layout.Rewire :=
  ⟨coordinates source, coordinates destination, map.owners.toList, map.axes.toList⟩

/-- A candidate inverse is computed from the actual map, never supplied by an
untrusted producer. Missing or duplicated positions fail the two inverse laws. -/
def inverse (n : Nat) (map : Array Nat) : List Nat :=
  let forward := map.toList
  (List.range n).map (fun i => forward.findIdx (· == i))

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

structure Checked where
  visits : Nat
  deriving Repr

/-- `remaining` comes from the enclosing verifier's shared budget. This result
is ordinary structural data and never authorizes a quantum semantic equation. -/
def check (source destination : Side) (map : PortMap) (remaining : Nat) :
    Except Error Checked :=
  if remaining > 2000000 || scanCharge source destination map > remaining then .error .limit
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

end QleisliKernel.Hierarchical.Ports
