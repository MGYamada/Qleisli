import QleisliKernel.Qirf.Validity
import QleisliKernel.FiniteCarrier
import QleisliKernel.Semantics.CarrierInterface

/-! Bind finite carrier codes to a freshly checked original QIRF root and its
dependencies. This component has no native entry point or accepted-handle API.
The Protocol.Carrier caller independently checks source declarations and typed
interfaces; equal proposed/requested metadata is not an AST-to-body preservation
theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.Carrier
open Semantics.Exact Semantics.CarrierInterface Finite

def readOwner (owner : Owner) : WorkM Semantics.FiniteCarrier.Layout := do
  let layout ← FiniteCarrier.read owner.basis
  guard (owner.port.bits == layout.bits && owner.port.wires.length == layout.bits) .request
  return layout

def readOwners (owners : List Owner) : WorkM Unit :=
  owners.foldlM (fun (_ : Unit) owner => do
    let _ ← readOwner owner
    pure ()) ()

/-- Bound the complete forest before interpreting any child. An empty basis in
one owner cannot borrow nodes from a neighbour to complete its prefix tree. -/
def ownerCode (owners : List Owner) : WorkM Matrix := do
  guard (owners.length ≤ 128) .limit
  let code ← FiniteCarrier.code (forest owners)
  readOwners owners
  return code

/-- Exact source rows referenced by the four typed owner forests. This does
not include helper/import-only dependencies or arbitrary project rows. The
protocol independently checks these original declarations before this gate. -/
def sourceRows (attached required : Interface) : List (String × String) :=
  ([attached.inputs,attached.outputs,required.inputs,required.outputs].flatten.flatMap
    fun owner => owner.basis).filterMap fun atom => match atom with
      | .enumeration origin _ | .record origin _ => some (origin.moduleName,origin.source)
      | _ => none

/-- Count on the borrowed forests before allocating concatenated source rows.
The four owner/code checks have already bounded and charged these forests. -/
def sourceNodes (attached required : Interface) : Nat :=
  [attached.inputs,attached.outputs,required.inputs,required.outputs].foldl
    (fun total owners => owners.foldl (fun count owner => count + 1 + owner.basis.length) total) 0

/-- Charge the exact-row coverage comparisons before traversing them. Ordinary
graph checking keeps its original zero-extra accounting and strict source use. -/
def sourceRootFromRoots (artifact : Artifact) (order : Array Nat) (attached required : Interface) (roots : List Nat) :
    WorkM Validity.Root := do
  exactWork (Exact.charge (4 * sourceNodes attached required + 5))
  let extra := sourceRows attached required
  let bytes := (artifact.sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum
  exactWork (Exact.charge ((bytes + artifact.sources.size + 1) * (extra.length + 1)))
  Validity.checkRootFromRoots artifact order extra roots

def sourceRoot (artifact : Artifact) (order : Array Nat) (attached required : Interface) :
    WorkM Validity.Root :=
  sourceRootFromRoots artifact order attached required [artifact.root]

structure Checked where
  root : Validity.Root
  interface : Interface
  inputCode : Matrix
  outputCode : Matrix
  logical : Matrix
  physical : Matrix

/-- The logical map is an independently requested exact matrix. Checking this
equation establishes neither a general source theorem nor inverse/control access.
Public Isometry is not sharpened by a square implementation; Observe refuses. -/
def check (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (logical : Matrix) : WorkM Checked := do
  let inputCode ← ownerCode attached.inputs
  let outputCode ← ownerCode attached.outputs
  let _ ← ownerCode required.inputs
  let _ ← ownerCode required.outputs
  exactWork (Exact.charge ((forest attached.inputs).length + (forest attached.outputs).length + 1))
  guard (attached == required) .request
  guard (required.publicEffect == .unitary || required.publicEffect == .iso) .request
  let logical ← matrixRead logical
  guard (logical.cols == inputCode.cols && logical.rows == outputCode.cols) .request
  guard (required.publicEffect != .unitary || logical.rows == logical.cols) .request
  let iso ← exactWork (Exact.Matrix.isometryWork logical)
  guard iso .notIsometric
  let root ← sourceRoot artifact order attached required
  guard (root.program.inputs == attached.inputs.map (·.port) &&
    root.program.outputs == attached.outputs.map (·.port.token) &&
    root.program.classicalInputs.isEmpty && root.program.classicalOutputs.isEmpty &&
    (root.program.effect == .unitary || root.program.effect == .iso)) .request
  exactWork (Exact.charge (attached.outputs.length * root.checked.state.quantum.live.length + 1))
  guard (attached.outputs.all fun owner => root.checked.state.quantum.live.contains owner.port) .request
  let physical ← Raw.BranchFunction.reconstruct root.dependencies root.program
  guard (physical.cols == inputCode.rows && physical.rows == outputCode.rows) .request
  let actual ← exactWork (Exact.Matrix.composeWork physical inputCode)
  let specified ← exactWork (Exact.Matrix.composeWork outputCode logical)
  exactWork (Exact.charge actual.entries.length)
  guard (actual == specified) .equation
  return ⟨root,required,inputCode,outputCode,logical,physical⟩

structure Postcondition (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (logical : Matrix) (checked : Checked) : Prop where
  interface : attached = required
  retainedInterface : checked.interface = required
  inputCode : ∃ a b, (ownerCode attached.inputs).run a = (.ok checked.inputCode,b)
  outputCode : ∃ a b, (ownerCode attached.outputs).run a = (.ok checked.outputCode,b)
  logicalBinding : checked.logical = logical
  logicalShape : logical.cols = checked.inputCode.cols ∧ logical.rows = checked.outputCode.cols
  publicPure : required.publicEffect = .unitary ∨ required.publicEffect = .iso
  publicUnitary : required.publicEffect = .unitary → logical.rows = logical.cols
  logicalGram : ∃ a b, Exact.Matrix.isometry logical a = (.ok true,b)
  root : ∃ a b, (sourceRoot artifact order attached required).run a = (.ok checked.root,b)
  inputs : checked.root.program.inputs = attached.inputs.map (·.port)
  outputs : checked.root.program.outputs = attached.outputs.map (·.port.token)
  classicalInputs : checked.root.program.classicalInputs = []
  classicalOutputs : checked.root.program.classicalOutputs = []
  physicalPure : checked.root.program.effect = .unitary ∨ checked.root.program.effect = .iso
  live : attached.outputs.all (fun owner => checked.root.checked.state.quantum.live.contains owner.port) = true
  body : ∃ a b, (Raw.BranchFunction.reconstruct checked.root.dependencies checked.root.program).run a =
    (.ok checked.physical,b)
  physicalShape : checked.physical.cols = checked.inputCode.rows ∧ checked.physical.rows = checked.outputCode.rows
  equation : ∃ result a b c d,
    Exact.Matrix.compose checked.physical checked.inputCode a = (.ok result,b) ∧
    Exact.Matrix.compose checked.outputCode logical c = (.ok result,d)

theorem sourceRootFromRoots_result (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) (root : Validity.Root) (work left : Nat)
    (ok : (sourceRootFromRoots artifact order attached required roots).run work = (.ok root,left)) :
    ∃ after, (Validity.checkRootFromRoots artifact order (sourceRows attached required) roots).run after =
      (.ok root,left) := by
  obtain ⟨_,charged,_,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,after,_,checked⟩ := bind_success _ _ _ _ _ rest
  exact ⟨after,checked⟩

theorem sourceRoot_result (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (root : Validity.Root) (work left : Nat)
    (ok : (sourceRoot artifact order attached required).run work = (.ok root,left)) :
    ∃ after, (Validity.checkRootWithSources artifact order (sourceRows attached required)).run after =
      (.ok root,left) := by
  exact sourceRootFromRoots_result artifact order attached required [artifact.root] root work left ok

theorem readOwner_conditions (owner : Owner) (code : Semantics.FiniteCarrier.Layout)
    (work left : Nat) (ok : (readOwner owner).run work = (.ok code,left)) :
    Semantics.FiniteCarrier.layout owner.basis = some code ∧
    owner.port.bits = code.bits ∧ owner.port.wires.length = code.bits := by
  obtain ⟨read,w₁,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst code
  have ports := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true,beq_iff_eq] at ports
  exact ⟨FiniteCarrier.read_reference _ _ _ _ hr,ports⟩

theorem readOwners_conditions (owners : List Owner) (work left : Nat)
    (ok : (readOwners owners).run work = (.ok (),left)) :
    ∀ owner ∈ owners, ∃ code, Semantics.FiniteCarrier.layout owner.basis = some code ∧
      owner.port.bits = code.bits ∧ owner.port.wires.length = code.bits := by
  induction owners generalizing work with
  | nil => simp
  | cons first rest ih =>
    simp only [readOwners,List.foldlM_cons] at ok
    obtain ⟨step,middle,hc,hr⟩ := bind_success _ _ _ _ _ ok
    cases step
    obtain ⟨code,after,hc,_⟩ := bind_success _ _ _ _ _ hc
    intro owner member
    rcases List.mem_cons.mp member with same | member
    · subst owner
      exact ⟨code,readOwner_conditions _ _ _ _ hc⟩
    · exact ih middle hr owner member

theorem ownerCode_conditions (owners : List Owner) (code : Matrix) (work left : Nat)
    (ok : (ownerCode owners).run work = (.ok code,left)) :
    (∃ a b, (FiniteCarrier.code (forest owners)).run a = (.ok code,b)) ∧
    ∀ owner ∈ owners, ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout ∧
      owner.port.bits = layout.bits ∧ owner.port.wires.length = layout.bits := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨readCode,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,ho,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst code
  exact ⟨⟨w₁,w₂,hc⟩,readOwners_conditions _ _ _ ho⟩

theorem check_postcondition (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (logical : Matrix) (checked : Checked) (work left : Nat)
    (ok : (check artifact order attached required logical).run work = (.ok checked,left)) :
    Postcondition artifact order attached required logical checked := by
  obtain ⟨inputCode,w₁,hin,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨outputCode,w₂,hout,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hif,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,hpub,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨read,w₈,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,hshape,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₀,huni,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨iso,w₁₁,hgram,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₂,hiso,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨root,w₁₃,hroot,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₄,hports,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₆,hlive,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨physical,w₁₇,hbody,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₈,hphysical,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₁₉,hactual,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specified,w₂₀,hspecified,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₂₁,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₂₂,heq,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have readSame := (matrixRead_value _ _ _ _ hr).1
  subst read
  have isoTrue := (guard_success _ _ _ _ hiso).1
  subst iso
  have ports := (guard_success _ _ _ _ hports).1
  have shape := (guard_success _ _ _ _ hshape).1
  have physicalShape := (guard_success _ _ _ _ hphysical).1
  have publicPure := (guard_success _ _ _ _ hpub).1
  have publicUnitary := (guard_success _ _ _ _ huni).1
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,List.isEmpty_iff] at ports shape physicalShape publicPure
  have eq := beq_iff_eq.mp (guard_success _ _ _ _ heq).1
  rw [← eq] at hspecified
  refine ⟨beq_iff_eq.mp (guard_success _ _ _ _ hif).1,rfl,⟨work,w₁,hin⟩,⟨w₁,w₂,hout⟩,
    rfl,shape,publicPure,?_,⟨w₁₀,w₁₁,exactWork_success _ _ _ _ hgram⟩,
    ⟨w₁₂,w₁₃,hroot⟩,ports.1.1.1.1,ports.1.1.1.2,ports.1.1.2,ports.1.2,ports.2,
    (guard_success _ _ _ _ hlive).1,⟨w₁₆,w₁₇,hbody⟩,physicalShape,
    ⟨actual,w₁₈,w₁₉,w₁₉,w₂₀,exactWork_success _ _ _ _ hactual,
      exactWork_success _ _ _ _ hspecified⟩⟩
  intro unitary
  simpa [unitary] using publicUnitary

end QleisliKernel.Qirf.Carrier
