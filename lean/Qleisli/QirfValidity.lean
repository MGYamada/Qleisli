import Qleisli.Qirf
import Qleisli.Semantics.Qirf
import QleisliKernel.Qirf.Validity
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! Composition from production QIRF acceptance to original-body semantics.
Ordinary roots have independent linear ResourceSafe and lexical ScopeSafe; the finite contract and
full production EffectSound/hierarchical theorems remain distinct.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Qirf.Validity
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Qirf.Validity
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.ObservingFunction
open Qleisli.Semantics.ObservingFunction
open scoped Matrix

structure RootMeaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (root : Root) : Prop where
  graph : ∃ slots, GraphDenotation artifact (Array.replicate artifact.entries.size none) order.toList slots ∧
    slots.all Option.isSome = true ∧ root.dependencies = (before slots).map Receipt.dependency
  original : artifact.programs[artifact.root]? = some root.program
  observation : QleisliKernel.Raw.Observation.Postcondition root.program root.checked
  resources : QleisliKernel.Semantics.Ownership.ResourceSafe root.program
  scopes : QleisliKernel.Semantics.ClassicalScope.ScopeSafe root.program
  interface : interfaceValid artifact root.program = true
  sources : sourcesUsed artifact = true

structure RequestMeaning (artifact : QleisliKernel.Qirf.Artifact) (root : Root)
    (request : Request) (equation : Equation) : Prop where
  interface : artifact.rootInterface = some (request.signature,request.signature)
  sources : request.sources = none ∨ request.sources = some artifact.sources
  target : QleisliKernel.Semantics.Qirf.targetProgram request.signature request.target = some equation.target
  contract : Qleisli.Semantics.Qirf.FiniteContract root.dependencies root.program
    request.signature request.target equation.actual

/-- Ordinary roots retain structural/refinement facts; a caller-supplied finite
request additionally gets independent original-instrument semantics. -/
structure VerifiedMeaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (checked : Checked) : Prop where
  root : RootMeaning artifact order checked.root
  requested : match request with
    | none => checked.equation = none
    | some request => ∃ equation, checked.equation = some equation ∧ RequestMeaning artifact checked.root request equation

theorem root_meaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (root : Root) (work : Nat) (facts : RootPostcondition artifact order root work) :
    RootMeaning artifact order root := by
  obtain ⟨left,graph⟩ := facts.graph
  obtain ⟨a,b,verified⟩ := facts.verification
  exact ⟨checkGraph_semantics _ _ _ _ _ graph,facts.original,
    QleisliKernel.Raw.Observation.verify_postcondition _ _ _ _ _ verified,
    QleisliKernel.Raw.Observation.verify_resourceSafe _ _ _ _ _ verified,
    QleisliKernel.Raw.Observation.verify_scopeSafe _ _ _ _ _ verified,facts.interface,facts.sources⟩

theorem request_meaning (artifact : QleisliKernel.Qirf.Artifact) (root : Root)
    (request : Request) (equation : Equation)
    (facts : EquationPostcondition artifact root.dependencies root.program request equation) :
    RequestMeaning artifact root request equation := by
  obtain ⟨a,b,target⟩ := facts.target
  obtain ⟨c,d,implementation⟩ := facts.implementation
  obtain ⟨e,f,specification⟩ := facts.specification
  obtain ⟨g,h,unitary⟩ := facts.unitary
  have closed : root.program.classicalInputs = [] := by
    have preflight := facts.preflight
    simp only [QleisliKernel.Raw.BranchFunction.preflight,Bool.and_eq_true,List.isEmpty_iff] at preflight
    exact preflight.1.1.1.2
  have canonical := meaningProgram_target _ _ _ _ _ target
  have inverses := Qleisli.Finite.wholeSpace_unitary _ _ _ unitary
  exact ⟨facts.interface,facts.sources,canonical,
    ⟨Qleisli.Raw.BranchFunction.reconstruct_denotes _ _ closed _ _ _ implementation,
      ⟨equation.target,canonical,Qleisli.Raw.BranchFunction.reconstruct_denotes _ _
        (meaningProgram_closed _ _ _ _ _ target) _ _ _ specification⟩,inverses.1,inverses.2⟩⟩

theorem check_sound (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (checked : Checked) (work left : Nat)
    (ok : (check artifact order request).run work = (.ok checked,left)) :
    VerifiedMeaning artifact order request checked := by
  have facts := check_postcondition _ _ _ _ _ _ ok
  refine ⟨root_meaning _ _ _ _ facts.root,?_⟩
  cases request with
  | none => exact facts.equation
  | some request =>
    obtain ⟨equation,present,meaning⟩ := facts.equation
    exact ⟨equation,present,request_meaning _ _ _ _ meaning⟩

/-- The actual production compatibility API discharges the theorem, with no
Rust correctness, producer-certificate or isometry premise. -/
theorem inspect_sound (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (work left : Nat)
    (ok : (inspect artifact order request).run work = (.ok (),left)) :
    ∃ checked, (check artifact order request).run work = (.ok checked,left) ∧
      VerifiedMeaning artifact order request checked := by
  obtain ⟨checked,accepted,_⟩ := inspect_result _ _ _ _ _ ok
  exact ⟨checked,accepted,check_sound _ _ _ _ _ _ accepted⟩

/-- Arbitrarily entangled finite references retain both whole-space inverse
laws. Equality is phase-sensitive before taking any density interpretation. -/
theorem requested_reference_laws {R : Type} [Fintype R] [DecidableEq R]
    (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat) (request : Request)
    (checked : Checked) (work left : Nat)
    (ok : (check artifact order (some request)).run work = (.ok checked,left)) :
    ∃ equation, checked.equation = some equation ∧
      Qleisli.Semantics.Qirf.FiniteContract checked.root.dependencies checked.root.program
        request.signature request.target equation.actual ∧
      let joint := _root_.Matrix.kronecker (square equation.actual) (1 : _root_.Matrix R R ℂ)
      jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 := by
  obtain ⟨equation,present,meaning⟩ := (check_sound _ _ _ _ _ _ ok).requested
  have first := HierarchicalUnitary.reference_isometry (R := R) _ meaning.contract.leftInverse
  exact ⟨equation,present,meaning.contract,first,mul_eq_one_comm.mp first⟩

end Qleisli.Qirf.Validity
