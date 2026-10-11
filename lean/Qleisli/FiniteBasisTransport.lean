import QleisliKernel.Qirf.Checked
import QleisliKernel.Semantics.Ownership
import QleisliKernel.Semantics.ClassicalScope
import Mathlib.Data.List.Basic

/-! Transport for the pre-Bits Unit/Bit/product prefix representation.
This preserves the old domain; it neither equates Bits with equal-width trees
nor claims source preservation, decoder correspondence or guarantee admission.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.FiniteBasisTransport
open QleisliKernel.Semantics.Finite

/-- The four constructors of the immutable admitted finite-basis profile. -/
inductive LegacyAtom where
  | unit | bit | pair | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for LegacyAtom

def encodeAtom : LegacyAtom → Atom
  | .unit => .unit
  | .bit => .bit
  | .pair => .pair
  | .tuple n => .tuple n

def encodeBasis (basis : List LegacyAtom) : Basis := basis.map encodeAtom

def legacyWidth (basis : List LegacyAtom) : Nat :=
  (basis.filter (· == .bit)).length

def legacyTreeStep (maxDepth maxArity : Nat)
    (stack : Option (List Nat)) (atom : LegacyAtom) : Option (List Nat) := do
  let depth :: rest ← stack | none
  if depth > maxDepth then none else
  match atom with
  | .unit | .bit => some rest
  | .pair => some ((depth+1) :: (depth+1) :: rest)
  | .tuple n =>
    if n < 3 || n > maxArity then none
    else some (List.replicate n (depth+1) ++ rest)

def legacyValid (basis : List LegacyAtom) : Bool :=
  basis.length ≤ 128 && legacyWidth basis ≤ 6 &&
    basis.foldl (legacyTreeStep 32 128) (some [0]) == some []

theorem encodeAtom_injective : Function.Injective encodeAtom := by
  intro left right equal
  cases left <;> cases right <;> simp_all [encodeAtom]

theorem encodeBasis_injective : Function.Injective encodeBasis := by
  exact List.map_injective_iff.mpr encodeAtom_injective

theorem width_preserved (basis : List LegacyAtom) :
    width (encodeBasis basis) = legacyWidth basis := by
  induction basis with
  | nil => rfl
  | cons atom tail ih =>
    cases atom <;> simp_all [encodeBasis, encodeAtom, width, legacyWidth, Nat.add_comm]

theorem treeStep_preserved (stack : Option (List Nat)) (atom : LegacyAtom) :
    QleisliKernel.Finite.treeStep stack (encodeAtom atom) =
      legacyTreeStep 32 128 stack atom := by
  cases atom <;> rfl

theorem treeFold_preserved (basis : List LegacyAtom) (stack : Option (List Nat)) :
    (encodeBasis basis).foldl QleisliKernel.Finite.treeStep stack =
      basis.foldl (legacyTreeStep 32 128) stack := by
  induction basis generalizing stack with
  | nil => rfl
  | cons atom tail ih =>
    simp only [encodeBasis, List.map_cons, List.foldl_cons]
    rw [treeStep_preserved]
    exact ih _

theorem basisValid_preserved (basis : List LegacyAtom) :
    QleisliKernel.Finite.basisValid (encodeBasis basis) = legacyValid basis := by
  unfold QleisliKernel.Finite.basisValid legacyValid
  rw [width_preserved, treeFold_preserved]
  simp only [encodeBasis, List.length_map]

def legacyRootValid (basis : List LegacyAtom) : Bool :=
  basis.length ≤ 4096 && legacyWidth basis ≤ 12 &&
    basis.foldl (legacyTreeStep 64 4096) (some [1]) == some []

private def currentRootStep (pending : Option (List Nat)) (atom : Atom) :
    Option (List Nat) := do
  let depth :: rest ← pending | none
  if depth > 64 then none else
  match atom with
  | .unit | .bit | .bits _ => some rest
  | .pair => some ((depth+1) :: (depth+1) :: rest)
  | .tuple n =>
    if n < 3 || n > 4096 then none
    else some (List.replicate n (depth+1) ++ rest)

private theorem rootStep_preserved (stack : Option (List Nat)) (atom : LegacyAtom) :
    currentRootStep stack (encodeAtom atom) =
      legacyTreeStep 64 4096 stack atom := by
  cases atom <;> rfl

private theorem rootFold_preserved (basis : List LegacyAtom) (stack : Option (List Nat)) :
    (encodeBasis basis).foldl currentRootStep stack =
      basis.foldl (legacyTreeStep 64 4096) stack := by
  induction basis generalizing stack with
  | nil => rfl
  | cons atom tail ih =>
    simp only [encodeBasis, List.map_cons, List.foldl_cons]
    rw [rootStep_preserved]
    exact ih _

/-- The actual QIRF root type gate preserves the complete old tree domain,
including both twelve-bit width and structural depth/node bounds. -/
theorem rootBasis_preserved (basis : List LegacyAtom) :
    QleisliKernel.Qirf.Validity.rootBasis (encodeBasis basis) = legacyRootValid basis := by
  change ((encodeBasis basis).length ≤ 4096 && width (encodeBasis basis) ≤ 12 &&
    (encodeBasis basis).foldl currentRootStep (some [1]) == some []) = _
  unfold legacyRootValid
  rw [width_preserved, rootFold_preserved]
  simp only [encodeBasis, List.length_map]

/-- Historical requested-table semantics with the original bit-count rule. -/
def legacyTargetProgram (basis : List LegacyAtom) (target : QleisliKernel.Qirf.Target) :
    Option QleisliKernel.Semantics.Observation.Program := do
  let bits := legacyWidth basis
  let (permutation, phases) ← match target with
    | .permutation table => some (table, List.replicate table.length 0)
    | .phase8 table => some (List.range table.length, table)
    | .circuit _ => none
  let step : Step := ⟨[], .monomial (List.range bits) permutation phases⟩
  return ⟨[⟨0, List.range bits, bits⟩], [], [.pure (.applyUnitary 0 1 [step])],
    [1], [], .unitary⟩

/-- Complete original table action, including phases and low-axis ordering,
commutes with the injective basis embedding. -/
theorem targetProgram_preserved (basis : List LegacyAtom) (target : QleisliKernel.Qirf.Target) :
    QleisliKernel.Semantics.Qirf.targetProgram (encodeBasis basis) target =
      legacyTargetProgram basis target := by
  unfold QleisliKernel.Semantics.Qirf.targetProgram legacyTargetProgram
  rw [width_preserved]
  rfl

/-- Same original QIRF fields, with the historical basis type substituted.
The defining source is identical to the admitted archive, apart from that type. -/
structure LegacyEntry where
  signature : List LegacyAtom
  implementation : Nat
  target : QleisliKernel.Qirf.Target
  implementationName : String
  specificationName : String
  sources : List Nat

structure LegacyArtifact where
  programs : Array QleisliKernel.Semantics.Observation.Program
  entries : Array LegacyEntry
  sources : Array (String × String)
  root : Nat
  rootInterface : Option (List LegacyAtom × List LegacyAtom)

def encodeEntry (entry : LegacyEntry) : QleisliKernel.Qirf.Entry :=
  ⟨encodeBasis entry.signature, entry.implementation, entry.target,
    entry.implementationName, entry.specificationName, entry.sources⟩

def encodeArtifact (artifact : LegacyArtifact) : QleisliKernel.Qirf.Artifact :=
  ⟨artifact.programs, artifact.entries.map encodeEntry, artifact.sources, artifact.root,
    artifact.rootInterface.map fun (input, output) => (encodeBasis input, encodeBasis output)⟩

/-- The original decoded root is retained literally, not reconstructed from
an accepted result, a width summary, or a producer's description. -/
theorem originalRoot_preserved (artifact : LegacyArtifact) :
    (encodeArtifact artifact).programs[(encodeArtifact artifact).root]? =
      artifact.programs[artifact.root]? := rfl

theorem ownership_preserved (artifact : LegacyArtifact)
    (program : QleisliKernel.Semantics.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some program ∧
      QleisliKernel.Semantics.Ownership.OwnershipSafe program) ↔
    (artifact.programs[artifact.root]? = some program ∧
      QleisliKernel.Semantics.Ownership.OwnershipSafe program) := Iff.rfl

theorem scope_preserved (artifact : LegacyArtifact)
    (program : QleisliKernel.Semantics.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some program ∧
      QleisliKernel.Semantics.ClassicalScope.ScopeSafe program) ↔
    (artifact.programs[artifact.root]? = some program ∧
      QleisliKernel.Semantics.ClassicalScope.ScopeSafe program) := Iff.rfl

def legacyInterfaceValid (artifact : LegacyArtifact)
    (program : QleisliKernel.Semantics.Observation.Program) : Bool :=
  match artifact.rootInterface with
  | none => true
  | some (input, output) =>
    legacyRootValid input && legacyRootValid output && program.effect == .unitary &&
    program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty &&
    program.inputs.length == 1 && program.outputs.length == 1 &&
    ((program.inputs[0]?).map fun port =>
      port.bits == legacyWidth input && port.bits == legacyWidth output).getD false

theorem interfaceValid_preserved (artifact : LegacyArtifact)
    (program : QleisliKernel.Semantics.Observation.Program) :
    QleisliKernel.Qirf.Validity.interfaceValid (encodeArtifact artifact) program =
      legacyInterfaceValid artifact program := by
  cases h : artifact.rootInterface with
  | none => simp [encodeArtifact, QleisliKernel.Qirf.Validity.interfaceValid, legacyInterfaceValid, h]
  | some pair =>
    rcases pair with ⟨input, output⟩
    simp [encodeArtifact, QleisliKernel.Qirf.Validity.interfaceValid, legacyInterfaceValid,
      h, rootBasis_preserved, width_preserved]

end Qleisli.FiniteBasisTransport
