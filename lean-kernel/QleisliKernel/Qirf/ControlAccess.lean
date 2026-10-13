import QleisliKernel.Qirf.Contract
import QleisliKernel.Semantics.ControlAccess

/-! Internal bounded control-sector obligation for the original QIRF root.
No protocol/CLI/source access path is added by this component. Its caller must
still establish original source places, lifetimes, locality and resource links.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ControlAccess
open Semantics.Exact Semantics.Finite Semantics.ControlAccess Finite

def sectors (matrix : Matrix) (axes : List Nat) : Bool :=
  (List.range matrix.rows).all fun row =>
    (List.range matrix.cols).all fun col =>
      (gather row axes == gather col axes) || decide (Zero (matrix.entry row col))

theorem sectors_sound (matrix : Matrix) (axes : List Nat)
    (ok : sectors matrix axes = true) : PreservesSectors matrix axes := by
  simp only [sectors, List.all_eq_true] at ok
  intro row hr col hc different
  have result := ok row hr col hc
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at result
  exact result.resolve_left different

/-- Validate the finite coordinate domain before charging and traversing it.
Missing entries cannot masquerade as zeros; axes are original, unique and in range. -/
def checkMatrix (bits : Nat) (matrix : Matrix) (axes : List Nat) : WorkM Unit := do
  guard (bits ≤ 6 && matrix.rows == 2^bits && matrix.cols == 2^bits &&
    matrix.entries.length == matrix.rows * matrix.cols) .limit
  guard (axesValid bits axes) .request
  exactWork (Exact.charge (matrix.rows * matrix.cols * (axes.length + 4)))
  guard (sectors matrix axes) .equation

/-- The freshly checked root and its reconstructed action remain available to
execution-view consumers without a second graph validation. -/
structure Retained where
  root : Validity.Root
  actual : Matrix

/-- A matrix supplied by the producer is never substituted for reconstruction.
Fresh graph/root acceptance, exact tree identity and actual dependencies precede
unitarity and the requested sector obligation. The finite profile remains six bits. -/
def checkRetained (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (axes : List Nat) : WorkM Retained := do
  let root ← Validity.checkRoot artifact order
  guard (artifact.rootInterface == some (signature,signature)) .request
  guard (Raw.BranchFunction.preflight signature root.program) .limit
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  wholeSpace actual
  checkMatrix (width signature) actual axes
  return ⟨root,actual⟩

def check (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (axes : List Nat) : WorkM Matrix := do
  return (← checkRetained artifact order signature axes).actual

/-- Projecting the retained result leaves every original check and work state unchanged. -/
theorem check_projection (artifact : Artifact) (order : Array Nat)
    (signature : Basis) (axes : List Nat) :
    check artifact order signature axes = (do
  let root ← Validity.checkRoot artifact order
  guard (artifact.rootInterface == some (signature,signature)) .request
  guard (Raw.BranchFunction.preflight signature root.program) .limit
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  wholeSpace actual
  checkMatrix (width signature) actual axes
  return actual) := by
  simp only [check, checkRetained, bind_assoc, pure_bind]

theorem checkMatrix_sectors (bits : Nat) (matrix : Matrix) (axes : List Nat)
    (work left : Nat) (ok : (checkMatrix bits matrix axes).run work = (.ok (),left)) :
    PreservesSectors matrix axes := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  exact sectors_sound matrix axes (guard_success _ _ _ _ h).1

/-- Bind this condition to the same actual root and matrix, not an unrelated
accepted handle or a theorem about a desired replacement operator. -/
theorem check_bound (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (axes : List Nat) (actual : Matrix) (work left : Nat)
    (ok : (check artifact order signature axes).run work = (.ok actual,left)) :
    ∃ root a b c,
      (Validity.checkRoot artifact order).run work = (.ok root,a) ∧
      artifact.rootInterface = some (signature,signature) ∧
      Raw.BranchFunction.preflight signature root.program = true ∧
      (Raw.BranchFunction.reconstruct root.dependencies root.program).run a = (.ok actual,b) ∧
      (wholeSpace actual).run b = (.ok (),c) ∧
      (checkMatrix (width signature) actual axes).run c = (.ok (),left) ∧
      PreservesSectors actual axes := by
  rw [check_projection] at ok
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,a₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨interface,same₁⟩ := guard_success _ _ _ _ hi
  subst a₁
  obtain ⟨_,a₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨preflight,same₂⟩ := guard_success _ _ _ _ hp
  subst a₂
  obtain ⟨matrix,b,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨value,same⟩ := pure_success _ _ _ _ h
  subst actual
  subst d
  exact ⟨root,a,b,c,hr,beq_iff_eq.mp interface,preflight,hm,hu,hs,
    checkMatrix_sectors _ _ _ _ _ hs⟩

/-- Preserve the exact owner forest rather than flattening its type trees.
This describes the requested interface, not source-type inference from widths. -/
def ownerSignature (signatures : List Basis) : Basis :=
  match signatures with
  | [signature] => signature
  | [left,right] => .pair :: (left ++ right)
  | _ => .tuple signatures.length :: signatures.flatten

/-- Ordered ports are taken from the original checked root. Zero-width owners
still occupy a forest position. Equal total bit width cannot replace a port. -/
def ownerInterface (root : Validity.Root) (signatures : List Basis) : Bool :=
  !signatures.isEmpty && signatures.length ≤ 64 &&
    root.program.inputs.length == signatures.length &&
    root.program.outputs.length == signatures.length &&
    (root.program.inputs.zip signatures).all (fun (port,signature) =>
      basisValid signature && port.bits == width signature && port.wires.length == width signature) &&
    (root.program.outputs.zip signatures).all (fun (token,signature) =>
      ((root.checked.state.quantum.live.find? (·.token == token)).map fun port =>
        port.bits == width signature && port.wires.length == width signature).getD false)

def ownersPreflight (program : Semantics.Observation.Program) : Bool :=
  program.effect == .unitary && program.classicalInputs.isEmpty &&
    program.classicalOutputs.isEmpty && (Raw.BranchFunction.preflightOps 33 program.operations).isSome

/-- The original multi-owner call is checked directly. No synthetic packing,
routing, matrix or producer receipt is substituted for its emitted operations.
The optional ordinary single-port root interface is absent for this request. -/
def checkOwnersRetained (artifact : Artifact) (order : Array Nat) (signatures : List Basis)
    (axes : List Nat) : WorkM Retained := do
  let root ← Validity.checkRoot artifact order
  guard (artifact.rootInterface.isNone && ownerInterface root signatures) .request
  guard (ownersPreflight root.program) .limit
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  wholeSpace actual
  checkMatrix (width (ownerSignature signatures)) actual axes
  return ⟨root,actual⟩

def checkOwners (artifact : Artifact) (order : Array Nat) (signatures : List Basis)
    (axes : List Nat) : WorkM Matrix := do
  return (← checkOwnersRetained artifact order signatures axes).actual

/-- Projecting the retained result leaves every original check and work state unchanged. -/
theorem checkOwners_projection (artifact : Artifact) (order : Array Nat)
    (signatures : List Basis) (axes : List Nat) :
    checkOwners artifact order signatures axes = (do
  let root ← Validity.checkRoot artifact order
  guard (artifact.rootInterface.isNone && ownerInterface root signatures) .request
  guard (ownersPreflight root.program) .limit
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  wholeSpace actual
  checkMatrix (width (ownerSignature signatures)) actual axes
  return actual) := by
  simp only [checkOwners, checkOwnersRetained, bind_assoc, pure_bind]

/-- Bind the forest/sector result to the same original root, dependencies,
returned ports, reconstructed action and continuous work states. -/
theorem checkOwners_bound (artifact : Artifact) (order : Array Nat) (signatures : List Basis)
    (axes : List Nat) (actual : Matrix) (work left : Nat)
    (ok : (checkOwners artifact order signatures axes).run work = (.ok actual,left)) :
    ∃ root a b c,
      (Validity.checkRoot artifact order).run work = (.ok root,a) ∧
      artifact.rootInterface.isNone = true ∧ ownerInterface root signatures = true ∧
      ownersPreflight root.program = true ∧
      (Raw.BranchFunction.reconstruct root.dependencies root.program).run a = (.ok actual,b) ∧
      (wholeSpace actual).run b = (.ok (),c) ∧
      (checkMatrix (width (ownerSignature signatures)) actual axes).run c = (.ok (),left) ∧
      PreservesSectors actual axes := by
  rw [checkOwners_projection] at ok
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,a₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨interface,same₁⟩ := guard_success _ _ _ _ hi
  subst a₁
  obtain ⟨_,a₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨preflight,same₂⟩ := guard_success _ _ _ _ hp
  subst a₂
  obtain ⟨matrix,b,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨value,same⟩ := pure_success _ _ _ _ h
  subst actual
  subst d
  simp only [Bool.and_eq_true] at interface
  exact ⟨root,a,b,c,hr,interface.1,interface.2,preflight,hm,hu,hs,
    checkMatrix_sectors _ _ _ _ _ hs⟩

/-- The retained root and action come from this exact fresh check. -/
theorem checkRetained_bound (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (axes : List Nat) (checked : Retained) (work left : Nat)
    (ok : (checkRetained artifact order signature axes).run work = (.ok checked,left)) :
    ∃ a b c,
      (Validity.checkRoot artifact order).run work = (.ok checked.root,a) ∧
      artifact.rootInterface = some (signature,signature) ∧
      Raw.BranchFunction.preflight signature checked.root.program = true ∧
      (Raw.BranchFunction.reconstruct checked.root.dependencies checked.root.program).run a = (.ok checked.actual,b) ∧
      (wholeSpace checked.actual).run b = (.ok (),c) ∧
      (checkMatrix (width signature) checked.actual axes).run c = (.ok (),left) ∧
      PreservesSectors checked.actual axes := by
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,a₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨interface,same₁⟩ := guard_success _ _ _ _ hi
  subst a₁
  obtain ⟨_,a₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨preflight,same₂⟩ := guard_success _ _ _ _ hp
  subst a₂
  obtain ⟨matrix,b,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨value,same⟩ := pure_success _ _ _ _ h
  subst checked
  subst d
  exact ⟨a,b,c,hr,beq_iff_eq.mp interface,preflight,hm,hu,hs,
    checkMatrix_sectors _ _ _ _ _ hs⟩

/-- The retained root and action come from this exact fresh check. -/
theorem checkOwnersRetained_bound (artifact : Artifact) (order : Array Nat) (signatures : List Basis)
    (axes : List Nat) (checked : Retained) (work left : Nat)
    (ok : (checkOwnersRetained artifact order signatures axes).run work = (.ok checked,left)) :
    ∃ a b c,
      (Validity.checkRoot artifact order).run work = (.ok checked.root,a) ∧
      artifact.rootInterface.isNone = true ∧ ownerInterface checked.root signatures = true ∧
      ownersPreflight checked.root.program = true ∧
      (Raw.BranchFunction.reconstruct checked.root.dependencies checked.root.program).run a = (.ok checked.actual,b) ∧
      (wholeSpace checked.actual).run b = (.ok (),c) ∧
      (checkMatrix (width (ownerSignature signatures)) checked.actual axes).run c = (.ok (),left) ∧
      PreservesSectors checked.actual axes := by
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,a₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨interface,same₁⟩ := guard_success _ _ _ _ hi
  subst a₁
  obtain ⟨_,a₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨preflight,same₂⟩ := guard_success _ _ _ _ hp
  subst a₂
  obtain ⟨matrix,b,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨value,same⟩ := pure_success _ _ _ _ h
  subst checked
  subst d
  simp only [Bool.and_eq_true] at interface
  exact ⟨a,b,c,hr,interface.1,interface.2,preflight,hm,hu,hs,
    checkMatrix_sectors _ _ _ _ _ hs⟩

end QleisliKernel.Qirf.ControlAccess
