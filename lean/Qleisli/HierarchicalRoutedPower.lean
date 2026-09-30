import Qleisli.HierarchicalFourierRoot
import QleisliKernel.Hierarchical.RoutedPower

/-! Constructed semantics of actual controlled provider powers through renames.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The provider premise concerns evaluation of its actual definition. Independent
provider/request equality, unitarity and full artifact acceptance remain separate;
no whole-stage interpretation or producer-controlled semantic environment is assumed. -/

namespace Qleisli.HierarchicalRoutedPower
open QleisliKernel.Hierarchical
open Artifact HierarchicalFiniteEvaluation HierarchicalOperators HierarchicalSemantics
open HierarchicalFourier
open scoped Matrix

/-- Explicit first-bit coherent control, retaining provider global phase. -/
noncomputable def controlled (n : Nat) (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Matrix (Fin (n+1) → Bool) (Fin (n+1) → Bool) ℂ :=
  let route := (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm
  (ControlledPowers.controlled U).submatrix route route

theorem apply_control_matrix (interface : Interface) (n : Nat) (child : Operator)
    (hi : width interface.inputs = n+1) (ho : width interface.outputs = n+1) :
    matrixAt (n+1) (n+1) (apply interface (.control true) [child]) =
      controlled n (matrixAt n n child) := by
  ext output input
  conv_lhs => rw [← Fin.cons_self_tail output,← Fin.cons_self_tail input]
  simp only [controlled,ControlledPowers.controlled,ControlledPowers.block,Matrix.submatrix]
  simp [matrixAt,apply,bounded,raw,hi,ho,List.ofFn_inj]
  by_cases same : output 0 = input 0
  · by_cases active : input 0 = true
    · simp only [same,active,ite_true]
      rfl
    · simp only [same,active,ite_true]
      rfl
  · simp [same]

theorem core_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (index : Nat) (request : RoutedPower.Request) (v : RoutedPower.View)
    (bound : RoutedPower.Bound artifact index request.provider v)
    (checked : RoutedPower.shape request v = true)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.width) (ho : provider.outputWidth = request.width) :
    ∃ fuel core, physical algebra leaves artifact fuel v.coreIndex = some core ∧
      core.inputWidth = request.width ∧ core.outputWidth = request.width ∧
      matrixAt request.width request.width core =
        (matrixAt request.width request.width provider)^(2^request.exponent) := by
  have fields := RoutedPower.shape_fields request v checked
  have dimensions := RoutedPower.sized_fields request.width v.core fields.2.2.2.1
  rcases RoutedPower.coreMatches_cases request v fields.2.2.2.2.2 with direct | repeated
  · refine ⟨providerFuel,provider,by simpa only [direct.1] using evaluated,hi,ho,?_⟩
    simp only [direct.2,pow_zero,pow_one]
  · have code : physicalCode v.core = some (.power (2^request.exponent),[request.provider]) := by
      simp [physicalCode,repeated]
    have step := physical_step algebra leaves artifact providerFuel v.coreIndex v.core
      (.power (2^request.exponent)) [request.provider] bound.2.2.2.1 code
    simp only [List.mapM_cons,evaluated,List.mapM_nil,bind,Option.bind,pure] at step
    refine ⟨providerFuel+1,apply v.core.interface (.power (2^request.exponent)) [provider],
      step,dimensions.2.2.1,dimensions.2.2.2,?_⟩
    have same : matrixAt request.width request.width
        (apply v.core.interface (.power (2^request.exponent)) [provider]) =
        matrixAt request.width request.width (power provider (2^request.exponent)) := by
      ext output input
      simp [matrixAt,apply,bounded,raw,width,dimensions.2.2.1,dimensions.2.2.2]
    rw [same,matrix_power provider request.width (2^request.exponent) hi ho]

theorem shell_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (index : Nat) (request : RoutedPower.Request) (v : RoutedPower.View)
    (bound : RoutedPower.Bound artifact index request.provider v)
    (checked : RoutedPower.shape request v = true) (cache : Wiring.Cache)
    (sound : Wiring.Sound artifact cache)
    (routes : RoutedPower.identityRoutes request.width v cache = true)
    (coreFuel : Nat) (core : Operator)
    (evaluated : physical algebra leaves artifact coreFuel v.coreIndex = some core)
    (hi : core.inputWidth = request.width) (ho : core.outputWidth = request.width) :
    ∃ fuel child, physical algebra leaves artifact fuel v.childIndex = some child ∧
      child.inputWidth = request.width ∧ child.outputWidth = request.width ∧
      matrixAt request.width request.width child = matrixAt request.width request.width core := by
  rcases bound.2.2.2.2.2 with direct | ⟨enter,leave,routeIndices,body⟩
  · exact ⟨coreFuel,core,by simpa only [direct.2.1] using evaluated,hi,ho,rfl⟩
  · have routeChecks : (cache[enter]?).bind id = some (List.range request.width) ∧
        (cache[leave]?).bind id = some (List.range request.width) := by
      simpa only [RoutedPower.identityRoutes,routeIndices,List.all_cons,List.all_nil,
        Bool.and_true,Bool.and_eq_true,beq_iff_eq] using routes
    obtain ⟨enterFuel,enterOp,enterEvaluated,enterAt⟩ :=
      HierarchicalWiring.derives_evaluates leaves artifact enter _ (sound _ _ routeChecks.1)
    obtain ⟨leaveFuel,leaveOp,leaveEvaluated,leaveAt⟩ :=
      HierarchicalWiring.derives_evaluates leaves artifact leave _ (sound _ _ routeChecks.2)
    have enterAt : HierarchicalWiring.At request.width (List.range request.width) enterOp := by
      simpa only [List.length_range] using enterAt
    have leaveAt : HierarchicalWiring.At request.width (List.range request.width) leaveOp := by
      simpa only [List.length_range] using leaveAt
    let fuel := enterFuel+coreFuel+leaveFuel
    have enterMore := evaluate_more algebra (definition leaves artifact) enterFuel enter enterOp
      enterEvaluated fuel (by dsimp [fuel]; omega)
    have coreMore := evaluate_more algebra (definition leaves artifact) coreFuel v.coreIndex core
      evaluated fuel (by dsimp [fuel]; omega)
    have leaveMore := evaluate_more algebra (definition leaves artifact) leaveFuel leave leaveOp
      leaveEvaluated fuel (by dsimp [fuel]; omega)
    change physical algebra leaves artifact fuel enter = some enterOp at enterMore
    change physical algebra leaves artifact fuel v.coreIndex = some core at coreMore
    change physical algebra leaves artifact fuel leave = some leaveOp at leaveMore
    have code : physicalCode v.child = some (.sequence,[enter,v.coreIndex,leave]) := by
      simp [physicalCode,body]
    have step := physical_step algebra leaves artifact fuel v.childIndex v.child .sequence
      [enter,v.coreIndex,leave] bound.2.2.1 code
    simp only [List.mapM_cons,enterMore,coreMore,leaveMore,List.mapM_nil,bind,Option.bind,pure] at step
    have dimensions := RoutedPower.sized_fields request.width v.child
      (RoutedPower.shape_fields request v checked).2.2.1
    refine ⟨fuel+1,apply v.child.interface .sequence [enterOp,core,leaveOp],step,
      dimensions.2.2.1,dimensions.2.2.2,?_⟩
    have all : ∀ op ∈ [enterOp,core,leaveOp],
        op.inputWidth = request.width ∧ op.outputWidth = request.width := by
      intro op member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨enterAt.2.2.1,enterAt.2.2.2.1⟩
      · exact ⟨hi,ho⟩
      · exact ⟨leaveAt.2.2.1,leaveAt.2.2.2.1⟩
    rw [apply_sequence_matrix v.child.interface request.width _ dimensions.2.2.1 dimensions.2.2.2 all]
    simp only [List.foldl_cons,List.foldl_nil,
      HierarchicalFourierRoot.identity_matrix request.width enterOp enterAt,
      HierarchicalFourierRoot.identity_matrix request.width leaveOp leaveAt,Matrix.mul_one,Matrix.one_mul]

/-- The actual root evaluates to coherent control of the actual provider power.
The caller supplies only that provider's constructed evaluation and dimensions;
the complete stage, renames and repetition are derived from checked IR bodies. -/
theorem inspect_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (index : Nat) (request : RoutedPower.Request) (order : Array Nat)
    (remaining : Nat) (pending : RoutedPower.Pending)
    (accepted : RoutedPower.inspect artifact index request order remaining = .ok pending)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.width) (ho : provider.outputWidth = request.width) :
    ∃ fuel actual, physical algebra leaves artifact fuel index = some actual ∧
      actual.inputWidth = request.width+1 ∧ actual.outputWidth = request.width+1 ∧
      matrixAt (request.width+1) (request.width+1) actual =
        controlled request.width ((matrixAt request.width request.width provider)^(2^request.exponent)) := by
  obtain ⟨bound,checked,wiring,routes,_⟩ :=
    RoutedPower.inspect_conditions artifact index request order remaining pending accepted
  obtain ⟨coreFuel,core,coreEvaluated,coreInput,coreOutput,coreMatrix⟩ :=
    core_evaluates leaves artifact index request pending.view bound checked providerFuel provider evaluated hi ho
  obtain ⟨fuel,child,childEvaluated,_,_,childMatrix⟩ := shell_evaluates leaves artifact index request
    pending.view bound checked pending.wiring.cache
    (Wiring.inspect_sound artifact order _ pending.wiring wiring).1 routes
    coreFuel core coreEvaluated coreInput coreOutput
  have code : physicalCode pending.view.root = some (.control true,[pending.view.childIndex]) := by
    simp [physicalCode,bound.2.1]
  have step := physical_step algebra leaves artifact fuel index pending.view.root (.control true)
    [pending.view.childIndex] bound.1 code
  simp only [List.mapM_cons,childEvaluated,List.mapM_nil,bind,Option.bind,pure] at step
  have dimensions := RoutedPower.sized_fields (request.width+1) pending.view.root
    (RoutedPower.shape_fields request pending.view checked).2.1
  refine ⟨fuel+1,apply pending.view.root.interface (.control true) [child],step,
    dimensions.2.2.1,dimensions.2.2.2,?_⟩
  rw [apply_control_matrix _ request.width child dimensions.2.2.1 dimensions.2.2.2,
    childMatrix,coreMatrix]

/-- An independently established provider matrix equation binds the entire
controlled stage on arbitrary, possibly entangled, control/target/reference
inputs. The provider equation is exact, including its global phase. -/
theorem inspect_reference {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (leaves : Leaves Operator) (artifact : Artifact)
    (index : Nat) (request : RoutedPower.Request) (order : Array Nat)
    (remaining : Nat) (pending : RoutedPower.Pending)
    (accepted : RoutedPower.inspect artifact index request order remaining = .ok pending)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.width) (ho : provider.outputWidth = request.width)
    (required : Matrix (Fin request.width → Bool) (Fin request.width → Bool) ℂ)
    (providerEquation : matrixAt request.width request.width provider = required)
    (rho : Matrix ((Fin (request.width+1) → Bool) × Reference)
      ((Fin (request.width+1) → Bool) × Reference) ℂ) :
    ∃ fuel actual, physical algebra leaves artifact fuel index = some actual ∧
      referenceMap (matrixAt (request.width+1) (request.width+1) actual) rho =
        referenceMap (controlled request.width (required^(2^request.exponent))) rho := by
  obtain ⟨fuel,actual,computed,_,_,equation⟩ :=
    inspect_evaluates leaves artifact index request order remaining pending accepted
      providerFuel provider evaluated hi ho
  exact ⟨fuel,actual,computed,by rw [equation,providerEquation]⟩

/-- A provider global sign is observable as a relative phase after control.
The actual-IR theorem above uses this same exact matrix convention. -/
theorem controlled_global_sign (n : Nat) :
    controlled n (-1) (Fin.cons true (fun _ => false)) (Fin.cons true (fun _ => false)) = -1 ∧
    controlled n (-1) (Fin.cons false (fun _ => false)) (Fin.cons false (fun _ => false)) = 1 := by
  simp [controlled,ControlledPowers.controlled,ControlledPowers.block,Matrix.submatrix]

end Qleisli.HierarchicalRoutedPower
