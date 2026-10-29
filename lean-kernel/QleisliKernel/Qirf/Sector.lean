import QleisliKernel.Qirf.Validity
import QleisliKernel.Raw.Sector
import QleisliKernel.Semantics.Ownership

/-! Original-QIRF binding for exact sectors. Reuse actual
fresh dependency/root checks, retain the entire original pure body, and reject
every observing/classical/branch constructor in this straight-line component.
Source-arm/type/nominal binding and native/QDV integration remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.Sector
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact QleisliKernel.Finite

def pureOp : Semantics.Observation.Op → Option Semantics.Raw.Op
  | .pure operation => some operation
  | _ => none

def pureOps (operations : List Semantics.Observation.Op) : Option (List Semantics.Raw.Op) :=
  operations.mapM pureOp

theorem option_bind_success {α β : Type} (first : Option α) (next : α → Option β)
    (result : β) (ok : first.bind next = some result) :
    ∃ value, first = some value ∧ next value = some result := by
  cases first with
  | none => simp at ok
  | some value => exact ⟨value,rfl,ok⟩

theorem pureOp_bound (original : Semantics.Observation.Op) (operation : Semantics.Raw.Op)
    (ok : pureOp original = some operation) : original = .pure operation := by
  cases original <;> simp_all [pureOp]

theorem pureOps_bound (original : List Semantics.Observation.Op) (operations : List Semantics.Raw.Op)
    (ok : pureOps original = some operations) : original = operations.map Semantics.Observation.Op.pure := by
  induction original generalizing operations with
  | nil =>
    simp [pureOps] at ok
    subst operations
    rfl
  | cons first rest ih =>
    simp only [pureOps,List.mapM_cons] at ok
    obtain ⟨operation,ho,h⟩ := option_bind_success _ _ _ ok
    obtain ⟨tail,ht,h⟩ := option_bind_success _ _ _ h
    simp only [pure,Option.some.injEq] at h
    subst operations
    rw [pureOp_bound _ _ ho,ih tail ht]
    rfl

/-- This is an exact inverse of the independent pure-program embedding. It
does not select a classical branch or erase any instruction/effect/history. -/
def project (program : Semantics.Observation.Program) : Option Semantics.Raw.Program := do
  if !(program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty && program.effect == .unitary)
    then none else
  let operations ← pureOps program.operations
  return ⟨program.inputs,operations,program.outputs,program.effect⟩

theorem project_bound (original : Semantics.Observation.Program) (program : Semantics.Raw.Program)
    (ok : project original = some program) :
    original = Semantics.Ownership.pureProgram program ∧ program.effect = .unitary := by
  by_cases valid : (original.classicalInputs.isEmpty && original.classicalOutputs.isEmpty &&
      original.effect == .unitary) = true
  · simp only [project,valid,Bool.not_true] at ok
    obtain ⟨operations,ho,h⟩ := option_bind_success _ _ _ ok
    simp only [pure,Option.some.injEq] at h
    subst program
    have guards := valid
    simp only [Bool.and_eq_true,List.isEmpty_iff,beq_iff_eq] at guards
    have body := pureOps_bound _ _ ho
    constructor
    · cases original
      simp_all [Semantics.Ownership.pureProgram]
    · exact guards.2
  · have invalid : (original.classicalInputs.isEmpty && original.classicalOutputs.isEmpty &&
        original.effect == .unitary) = false := Bool.eq_false_iff.mpr valid
    simp [project,invalid] at ok

structure Checked where
  root : Validity.Root
  program : Semantics.Raw.Program
  sectors : QleisliKernel.Raw.Sector.Retained

/-- The caller supplies original artifact data and required sector
matrices, never dependency matrices or a prechecked root. This strict component
keeps evidence-only source use; future source-row allowances need their own
independent original-source reader before native dispatch. -/
def check (artifact : Artifact) (order : Array Nat) (selector target : Basis)
    (required : List Matrix) : WorkM Checked := do
  let root ← Validity.checkRoot artifact order
  exactWork (Exact.charge (root.program.operations.length + 1))
  let program ← lift (readOption (project root.program))
  let sectors ← QleisliKernel.Raw.Sector.check root.dependencies selector target program required
  return ⟨root,program,sectors⟩

structure Postcondition (artifact : Artifact) (order : Array Nat) (selector target : Basis)
    (required : List Matrix) (checked : Checked) (work : Nat) : Prop where
  root : Validity.RootPostcondition artifact order checked.root work
  exactOriginal : checked.root.program = Semantics.Ownership.pureProgram checked.program
  pureEffect : checked.program.effect = .unitary
  restriction : QleisliKernel.Raw.Sector.Binding checked.root.dependencies selector target
    checked.program required checked.sectors

theorem check_bound (artifact : Artifact) (order : Array Nat) (selector target : Basis)
    (required : List Matrix) (checked : Checked) (work left : Nat)
    (ok : (check artifact order selector target required).run work = (.ok checked,left)) :
    Postcondition artifact order selector target required checked work := by
  obtain ⟨root,w₁,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,w₃,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨sectors,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have projected : project root.program = some program := by
    have read := (lift_success _ _ _ _ hp).1
    cases original : project root.program <;> simp_all [readOption]
  have original := project_bound _ _ projected
  exact ⟨Validity.checkRoot_postcondition _ _ _ _ _ hr,original.1,original.2,
    QleisliKernel.Raw.Sector.check_bound _ _ _ _ _ _ _ _ hs⟩

end QleisliKernel.Qirf.Sector
