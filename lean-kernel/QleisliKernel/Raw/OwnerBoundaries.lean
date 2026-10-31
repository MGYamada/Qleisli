import QleisliKernel.Raw.OwnerFlow

/-! One traversal of the literal Raw operations retains every complete logical
owner frame. The indexed trace binds each stored boundary to the original
reference step. No producer cache, width comparison or owner renaming supplies
that binding. Raw validity, source typing and interval equations remain separate
requirements; this component alone grants no accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.OwnerBoundaries
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics.RawOwnerFlow

inductive Trace : Frame → List Semantics.Raw.Op → List Frame → Type where
  | nil (frame : Frame) : Trace frame [] [frame]
  | cons {before after operations frames} (operation : Semantics.Raw.Op)
      (original : step before operation = some after)
      (rest : Trace after operations frames) :
      Trace before (operation::operations) (before::frames)

theorem Trace.lengths {initial operations frames} (trace : Trace initial operations frames) :
    frames.length = operations.length+1 := by
  induction trace with
  | nil => rfl
  | cons operation original rest ih => simpa using congrArg Nat.succ ih

/-- Every retained entry is the result of executing exactly the original
prefix. This includes zero-width owners, ordered pairs and consumed tokens. -/
theorem Trace.originalPrefix {initial operations frames} (trace : Trace initial operations frames)
    (offset : Nat) {frame : Frame} (found : frames[offset]? = some frame) :
    (operations.take offset).foldlM step initial = some frame := by
  induction trace generalizing offset with
  | nil initial =>
    cases offset with
    | zero => simpa using found
    | succ offset => simp at found
  | @cons before after operations frames operation original rest ih =>
    cases offset with
    | zero => simpa using found
    | succ offset =>
      simp only [List.getElem?_cons_succ] at found
      simpa only [List.take_succ_cons,List.foldlM_cons,original,Option.bind_some] using ih offset found

structure Checked (roles : List Semantics.SourceOwners.Owner)
    (inputs : List Semantics.Raw.Port) (operations : List Semantics.Raw.Op) where
  initial : Frame
  seeded : seed roles inputs = some initial
  frames : List Frame
  trace : Nonempty (Trace initial operations frames)

theorem Checked.lengths {roles inputs operations} (checked : Checked roles inputs operations) :
    checked.frames.length = operations.length+1 := by
  obtain ⟨trace⟩ := checked.trace
  exact trace.lengths

theorem Checked.originalPrefix {roles inputs operations} (checked : Checked roles inputs operations)
    (offset : Nat) {frame : Frame} (found : checked.frames[offset]? = some frame) :
    (seed roles inputs >>= fun initial => (operations.take offset).foldlM step initial) =
      some frame := by
  obtain ⟨trace⟩ := checked.trace
  simpa only [checked.seeded,Option.bind_some] using trace.originalPrefix offset found

abbrev Boundary (roles : List Semantics.SourceOwners.Owner) (inputs : List Semantics.Raw.Port)
    (operations : List Semantics.Raw.Op) (offset : Nat) :=
  {frame : Frame //
    (seed roles inputs >>= fun initial => (operations.take offset).foldlM step initial) = some frame}

/-- Select from the freshly computed table; retain the exact original prefix
equation without executing that prefix again. List indexing is still charged. -/
def lookup {roles inputs operations} (checked : Checked roles inputs operations) (offset : Nat) :
    WorkM (Boundary roles inputs operations offset) := do
  exactWork (Exact.charge (8*(offset+1)))
  match found : checked.frames[offset]? with
  | none => throw .request
  | some frame => return ⟨frame,checked.originalPrefix offset found⟩

/-- Charge the actual frame search and target moves once per literal step. -/
def targetCount : Semantics.Raw.Op → Nat
  | .cnot .. | .quantumIf .. => 2
  | .toffoli .. => 3
  | .computeUseUncompute _ _ targets .. => targets.length+1
  | .join .. | .split .. => 2
  | _ => 1

/-- The reference step reads liftBasis's wire-list length. Its truth table
and the other instructions' operator bodies remain opaque to owner transport. -/
def payloadFields : Semantics.Raw.Op → Nat
  | .liftBasis _ _ wires _ => wires.length
  | _ => 0

def readTrace (initial : Frame) (operations : List Semantics.Raw.Op) :
    WorkM {frames : List Frame // Nonempty (Trace initial operations frames)} :=
  let traverse : Nat → (initial : Frame) → (operations : List Semantics.Raw.Op) →
      WorkM {frames : List Frame // Nonempty (Trace initial operations frames)} :=
    Nat.rec (fun _ _ => throw .limit) (fun _ next initial operations => do
      match operations with
      | [] => return ⟨[initial],⟨.nil initial⟩⟩
      | operation::operations =>
        exactWork (Exact.charge (8*payloadFields operation+
          128*(targetCount operation+1)*(initial.length+1)^2))
        match original : step initial operation with
        | none => throw .request
        | some after =>
          let result ← next after operations
          return ⟨initial::result.val, by
            obtain ⟨rest⟩ := result.property
            exact ⟨.cons operation original rest⟩⟩)
  traverse (operations.length+1) initial operations

def check (roles : List Semantics.SourceOwners.Owner) (inputs : List Semantics.Raw.Port)
    (operations : List Semantics.Raw.Op) :
    WorkM (Checked roles inputs operations) := do
  exactWork (Exact.charge (8*(Raw.OwnerFlow.fields roles+1)+
    128*(roles.length+inputs.length+1)^2))
  match seeded : seed roles inputs with
  | none => throw .request
  | some initial =>
    let result ← readTrace initial operations
    return ⟨initial,seeded,result.val,result.property⟩

end QleisliKernel.Raw.OwnerBoundaries
