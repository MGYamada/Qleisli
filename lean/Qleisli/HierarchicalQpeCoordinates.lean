import Qleisli.HierarchicalQpeCircuit
import Qleisli.HierarchicalRoutedPower
import Qleisli.HierarchicalCircuitTrace

/-! Ordered physical coordinates for phase-sensitive QPE composition.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Every H, controlled-provider power and inverse-Fourier equation remains an
explicit component premise. No whole-circuit equation or checking flag is used
as the meaning of a proposed QPE implementation.
-/
namespace Qleisli.HierarchicalQpeCoordinates
open CoordinateOperators
open scoped BigOperators Matrix

/-- Canonical flattened order is phase first, then the complete target. -/
noncomputable def flatten (m n : Nat) (A : Matrix (Bits m × Bits n) (Bits m × Bits n) ℂ) :
    Matrix (Bits (m+n)) (Bits (m+n)) ℂ :=
  A.submatrix (Fin.appendEquiv m n).symm (Fin.appendEquiv m n).symm

theorem flatten_apply (m n : Nat) (A : Matrix (Bits m × Bits n) (Bits m × Bits n) ℂ)
    (output input : Bits (m+n)) :
    flatten m n A output input =
      A (fun i => output (i.castAdd n),fun i => output (i.natAdd m))
        (fun i => input (i.castAdd n),fun i => input (i.natAdd m)) := rfl

theorem flatten_mul (m n : Nat) (A B : Matrix (Bits m × Bits n) (Bits m × Bits n) ℂ) :
    flatten m n (A*B) = flatten m n A * flatten m n B :=
  (Matrix.submatrix_mul_equiv A B _ (Fin.appendEquiv m n).symm _).symm

theorem flatten_one (m n : Nat) :
    flatten m n (1 : Matrix (Bits m × Bits n) (Bits m × Bits n) ℂ) = 1 :=
  Matrix.submatrix_one_equiv _

/-- One control coordinate followed by every target coordinate in target order. -/
def controlPositions (m n : Nat) (axis : Fin m) : Fin (n+1) → Fin (m+n) :=
  Fin.cons (axis.castAdd n) (Fin.natAdd m)

theorem outside_control (m n : Nat) (axis : Fin m) (output input : Bits (m+n)) :
    outside (controlPositions m n axis) output input ↔
      ∀ i : Fin m, i ≠ axis → output (i.castAdd n) = input (i.castAdd n) := by
  constructor
  · intro same i different
    apply same (i.castAdd n)
    intro selected equal
    refine Fin.cases (fun equal => ?_) (fun j equal => ?_) selected equal
    · apply different
      exact Fin.ext (congrArg Fin.val equal).symm
    · have values := congrArg Fin.val equal
      simp only [controlPositions,Fin.cons_succ,Fin.val_natAdd,Fin.val_castAdd] at values
      omega
  · intro same coordinate absent
    refine Fin.addCases (fun i absent => ?_) (fun j absent => ?_) coordinate absent
    · apply same i
      intro equal
      subst i
      exact absent 0 rfl
    · exact False.elim (absent j.succ rfl)

theorem control_labels (m n : Nat) (axis : Fin m) (output input : Bits (m+n)) :
    (outside (controlPositions m n axis) output input ∧
      output (axis.castAdd n) = input (axis.castAdd n)) ↔
      (fun i : Fin m => output (i.castAdd n)) = (fun i => input (i.castAdd n)) := by
  rw [outside_control]
  constructor
  · rintro ⟨rest,selected⟩
    funext i
    by_cases same : i = axis
    · simpa only [same] using selected
    · exact rest i same
  · intro same
    exact ⟨fun i _ => congrFun same i,congrFun same axis⟩

theorem select_control (m n : Nat) (axis : Fin m) (input : Bits (m+n)) :
    input ∘ controlPositions m n axis =
      Fin.cons (input (axis.castAdd n)) (fun i => input (i.natAdd m)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem controlled_cons (n : Nat) (U : Matrix (Bits n) (Bits n) ℂ)
    (a b : Bool) (output input : Bits n) :
    HierarchicalRoutedPower.controlled n U (Fin.cons a output) (Fin.cons b input) =
      if a = b then (if a then U output input else (1 : Matrix (Bits n) (Bits n) ℂ) output input) else 0 := by
  cases a <;> cases b <;>
    simp [HierarchicalRoutedPower.controlled,ControlledPowers.controlled,ControlledPowers.block,
      Matrix.submatrix,Fin.consEquiv]
  all_goals rfl

/-- The canonical local controlled atom is exactly the independent QPE stage,
including the provider's full global phase when the control is one. -/
theorem control_stage (m n : Nat) (U : Matrix (Bits n) (Bits n) ℂ) (axis : Fin m) :
    lift (controlPositions m n axis)
      (HierarchicalRoutedPower.controlled n (U^(2^axis.val))) =
      flatten m n (HierarchicalQpeCircuit.stage m U axis) := by
  classical
  ext output input
  simp only [lift,select_control,controlled_cons,flatten_apply,HierarchicalQpeCircuit.stage,
    HierarchicalQpeCircuit.blocks]
  by_cases labels : (fun i : Fin m => output (i.castAdd n)) = (fun i => input (i.castAdd n))
  · have compatible := (control_labels m n axis output input).mpr labels
    rw [if_pos compatible.1,if_pos compatible.2,if_pos labels,compatible.2]
    by_cases bit : input (axis.castAdd n) = true
    · simp only [if_pos bit]
    · simp only [if_neg bit,pow_zero]
  · by_cases unchanged : outside (controlPositions m n axis) output input
    · have different : output (axis.castAdd n) ≠ input (axis.castAdd n) :=
        fun same => labels ((control_labels m n axis output input).mp ⟨unchanged,same⟩)
      simp only [if_pos unchanged,if_neg different,if_neg labels]
    · simp only [if_neg unchanged,if_neg labels]

/-- A lifted phase-register operator retains all target coherences. -/
theorem phase_onPhase (m n : Nat) (A : Matrix (Bits m) (Bits m) ℂ) :
    lift (Fin.castAdd n) A = flatten m n (HierarchicalQpeCircuit.onPhase A) := by
  ext output input
  rw [lift_left,flatten_apply]
  rfl

theorem onPhase_conj (m n : Nat) (A : Matrix (Bits m) (Bits m) ℂ) :
    HierarchicalQpeCircuit.onPhase (T := Bits n) Aᴴ = (HierarchicalQpeCircuit.onPhase A)ᴴ := by
  ext ⟨p,t⟩ ⟨q,u⟩
  by_cases same : t = u
  · subst u
    simp [HierarchicalQpeCircuit.onPhase,Matrix.conjTranspose_apply]
  · simp [HierarchicalQpeCircuit.onPhase,Matrix.conjTranspose_apply,same,Ne.symm same]

theorem flatten_fold (m n : Nat)
    (operators : List (Matrix (Bits m × Bits n) (Bits m × Bits n) ℂ))
    (initial : Matrix (Bits m × Bits n) (Bits m × Bits n) ℂ) :
    flatten m n (operators.foldl (fun before operator => operator * before) initial) =
      operators.foldl (fun before operator => flatten m n operator * before) (flatten m n initial) := by
  induction operators generalizing initial with
  | nil => rfl
  | cons operator rest ih => simp only [List.foldl_cons,ih,flatten_mul]

theorem fold_initial {I : Type} [Fintype I] [DecidableEq I]
    (operators : List (Matrix I I ℂ)) (initial : Matrix I I ℂ) :
    operators.foldl (fun before operator => operator * before) initial =
      operators.foldl (fun before operator => operator * before) 1 * initial := by
  induction operators generalizing initial with
  | nil => simp
  | cons operator rest ih =>
    change rest.foldl (fun before operator => operator * before) (operator * initial) =
      rest.foldl (fun before operator => operator * before) (operator * 1) * initial
    rw [ih (operator*initial),ih (operator*1)]
    simp only [Matrix.mul_one,Matrix.mul_assoc]

theorem fold_append {I : Type} [Fintype I] [DecidableEq I]
    (first second : List (Matrix I I ℂ)) :
    (first++second).foldl (fun before operator => operator * before) 1 =
      second.foldl (fun before operator => operator * before) 1 *
        first.foldl (fun before operator => operator * before) 1 := by
  rw [List.foldl_append,fold_initial]

theorem phase_hadamard_schedule (m n : Nat) :
    (List.ofFn (fun axis : Fin m =>
      lift (fun _ : Fin 1 => axis.castAdd n) HierarchicalQpeCircuit.oneHadamard)).foldl
        (fun before operator => operator * before) 1 =
      flatten m n (HierarchicalQpeCircuit.onPhase (HierarchicalQpeCircuit.hadamards m)) := by
  have mapped :
      List.ofFn (fun axis : Fin m => lift (fun _ : Fin 1 => axis.castAdd n) HierarchicalQpeCircuit.oneHadamard) =
      (List.ofFn (fun axis : Fin m => lift (fun _ : Fin 1 => axis) HierarchicalQpeCircuit.oneHadamard)).map
        (lift (Fin.castAdd n)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext axis
    change lift (fun _ : Fin 1 => axis.castAdd n) HierarchicalQpeCircuit.oneHadamard =
      lift (Fin.castAdd n) (lift (fun _ : Fin 1 => axis) HierarchicalQpeCircuit.oneHadamard)
    rw [lift_compose _ (Fin.castAdd_injective m n)]
    rfl
  rw [mapped,List.foldl_map]
  rw [← lift_one (Fin.castAdd n),← lift_left_fold,HierarchicalQpeCircuit.hadamard_schedule,phase_onPhase]

theorem power_schedule (m n : Nat) (U : Matrix (Bits n) (Bits n) ℂ) :
    (List.ofFn (fun axis : Fin m =>
      lift (controlPositions m n axis) (HierarchicalRoutedPower.controlled n (U^(2^axis.val))))).foldl
        (fun before operator => operator * before) 1 =
      flatten m n (HierarchicalQpeCircuit.powers m U) := by
  simp only [control_stage]
  have mapped : (List.ofFn (fun axis : Fin m => flatten m n (HierarchicalQpeCircuit.stage m U axis))) =
      (List.ofFn (HierarchicalQpeCircuit.stage m U)).map (flatten m n) := by
    rw [List.map_ofFn]
    rfl
  rw [mapped,List.foldl_map,← flatten_one m n,← flatten_fold]
  rw [List.ofFn_eq_map,List.foldl_map,HierarchicalQpeCircuit.stage_schedule]

/-- Canonical event order; no composed-circuit meaning is an input. -/
noncomputable def schedule (m n : Nat)
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ) : List (Matrix (Bits (m+n)) (Bits (m+n)) ℂ) :=
  List.ofFn (fun axis => lift (fun _ : Fin 1 => axis.castAdd n) (H axis)) ++
  List.ofFn (fun axis => lift (controlPositions m n axis) (P axis)) ++ [lift (Fin.castAdd n) F]

/-- Individual actual atom equations compose to the phase-fixed QPE circuit.
The provider need not be an eigenstate; its full matrix and all phases remain. -/
theorem schedule_circuit (m n : Nat) (U : Matrix (Bits n) (Bits n) ℂ)
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ)
    (hadamards : ∀ axis, H axis = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, P axis = HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : F = (HierarchicalFourier.fourier m)ᴴ) :
    (schedule m n H P F).foldl (fun before operator => operator * before) 1 =
      flatten m n (HierarchicalQpeCircuit.circuit m (HierarchicalQpeCircuit.hadamards m) U) := by
  unfold schedule
  simp only [hadamards,powers,fourier]
  rw [fold_append,fold_append]
  simp only [List.foldl_cons,List.foldl_nil,Matrix.mul_one]
  rw [phase_hadamard_schedule,power_schedule,phase_onPhase]
  simp only [← flatten_mul,HierarchicalQpeCircuit.circuit,Matrix.mul_assoc]

/-- The input permutation maps each canonical phase/target position to its
actual physical input position. Every event is placed on those same coordinates. -/
noncomputable def scheduleAt (m n : Nat) (inputRoute : Equiv.Perm (Fin (m+n)))
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ) : List (Matrix (Bits (m+n)) (Bits (m+n)) ℂ) :=
  List.ofFn (fun axis => lift (fun _ : Fin 1 => inputRoute (axis.castAdd n)) (H axis)) ++
  List.ofFn (fun axis => lift (inputRoute ∘ controlPositions m n axis) (P axis)) ++
    [lift (inputRoute ∘ Fin.castAdd n) F]

theorem scheduleAt_map (m n : Nat) (inputRoute : Equiv.Perm (Fin (m+n)))
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ) :
    scheduleAt m n inputRoute H P F = (schedule m n H P F).map
      (fun A => A.submatrix (basisEquiv inputRoute) (basisEquiv inputRoute)) := by
  simp only [scheduleAt,schedule,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,
    Function.comp_def,local_reindex]

theorem reindex_fold {I : Type} [Fintype I] [DecidableEq I] (route : Equiv.Perm I)
    (operators : List (Matrix I I ℂ)) (initial : Matrix I I ℂ) :
    (operators.foldl (fun before operator => operator * before) initial).submatrix route route =
      operators.foldl (fun before operator => operator.submatrix route route * before)
        (initial.submatrix route route) := by
  induction operators generalizing initial with
  | nil => rfl
  | cons operator rest ih =>
    simp only [List.foldl_cons,ih,Matrix.submatrix_mul_equiv]

theorem scheduleAt_circuit (m n : Nat) (inputRoute : Equiv.Perm (Fin (m+n)))
    (U : Matrix (Bits n) (Bits n) ℂ)
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ)
    (hadamards : ∀ axis, H axis = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, P axis = HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : F = (HierarchicalFourier.fourier m)ᴴ) :
    (scheduleAt m n inputRoute H P F).foldl (fun before operator => operator * before) 1 =
      (flatten m n (HierarchicalQpeCircuit.circuit m (HierarchicalQpeCircuit.hadamards m) U)).submatrix
        (basisEquiv inputRoute) (basisEquiv inputRoute) := by
  rw [scheduleAt_map,List.foldl_map,← Matrix.submatrix_one_equiv (basisEquiv inputRoute),← reindex_fold,
    schedule_circuit m n U H P F hadamards powers fourier]

/-- Exact output/input coordinate equation for an explicit final physical route.
The output route is retained, even when it reverses the physical phase order. -/
theorem routed_schedule_coefficient (m n : Nat)
    (inputRoute outputRoute : Equiv.Perm (Fin (m+n))) (U : Matrix (Bits n) (Bits n) ℂ)
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ)
    (hadamards : ∀ axis, H axis = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, P axis = HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : F = (HierarchicalFourier.fourier m)ᴴ) (output input : Bits (m+n)) :
    (routeMatrix outputRoute *
      (scheduleAt m n inputRoute H P F).foldl (fun before operator => operator * before) 1 :
        Matrix (Bits (m+n)) (Bits (m+n)) ℂ) output input =
      flatten m n (HierarchicalQpeCircuit.circuit m (HierarchicalQpeCircuit.hadamards m) U)
        (basisEquiv inputRoute ((basisEquiv outputRoute).symm output)) (basisEquiv inputRoute input) := by
  rw [scheduleAt_circuit m n inputRoute U H P F hadamards powers fourier,route_mul]
  rfl

/-- Full target Kraus coefficients in explicit physical input/output frames.
This initializes only the phase bits and retains arbitrary target amplitudes;
there is no eigenstate, product-reference or probability-only assumption. -/
theorem routed_schedule_branch (m n : Nat)
    (inputRoute outputRoute : Equiv.Perm (Fin (m+n))) (U : Matrix (Bits n) (Bits n) ℂ)
    (H : Fin m → Matrix (Bits 1) (Bits 1) ℂ)
    (P : Fin m → Matrix (Bits (n+1)) (Bits (n+1)) ℂ)
    (F : Matrix (Bits m) (Bits m) ℂ)
    (hadamards : ∀ axis, H axis = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, P axis = HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : F = (HierarchicalFourier.fourier m)ᴴ)
    (outcome : Bits m) (output input : Bits n) :
    (routeMatrix outputRoute *
      (scheduleAt m n inputRoute H P F).foldl (fun before operator => operator * before) 1 :
        Matrix (Bits (m+n)) (Bits (m+n)) ℂ)
      (basisEquiv outputRoute ((basisEquiv inputRoute).symm (Fin.append outcome output)))
      ((basisEquiv inputRoute).symm (Fin.append (fun _ => false) input)) =
        Qpe.kraus m U (HierarchicalGradient.number m outcome) output input := by
  rw [routed_schedule_coefficient m n inputRoute outputRoute U H P F hadamards powers fourier]
  simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,flatten_apply,Fin.append_left,Fin.append_right]
  exact congrFun (congrFun (HierarchicalQpeCircuit.circuit_branch m (HierarchicalQpeCircuit.hadamards m)
    (HierarchicalQpeCircuit.hadamards_zero m) U outcome) output) input

open QleisliKernel.Hierarchical
open HierarchicalOperators

/-- The exact event list requested by the QPE binder. Atom indices are actual
artifact definition indices; the control vector always includes the full target. -/
def expectedEvents (m n : Nat) (inputRoute : Equiv.Perm (Fin (m+n)))
    (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat) : List CircuitTrace.Event :=
  List.ofFn (fun axis => ⟨hIndices axis,List.ofFn (fun _ : Fin 1 => (inputRoute (axis.castAdd n)).val)⟩) ++
  List.ofFn (fun axis => ⟨powerIndices axis,
    List.ofFn (fun i : Fin (n+1) => (inputRoute (controlPositions m n axis i)).val)⟩) ++
  [⟨fourierIndex,List.ofFn (fun i : Fin m => (inputRoute (i.castAdd n)).val)⟩]

/-- The expected event list has precisely the local-operator schedule semantics. -/
theorem expectedEvents_matrix (m n : Nat) (inputRoute : Equiv.Perm (Fin (m+n)))
    (atoms : Nat → Operator) (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat) :
    (expectedEvents m n inputRoute hIndices powerIndices fourierIndex).map
      (HierarchicalCircuitTrace.eventMatrix atoms (m+n)) =
    scheduleAt m n inputRoute
      (fun axis => matrixAt 1 1 (atoms (hIndices axis)))
      (fun axis => matrixAt (n+1) (n+1) (atoms (powerIndices axis)))
      (matrixAt m m (atoms fourierIndex)) := by
  simp only [expectedEvents,scheduleAt,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,
    Function.comp_def,HierarchicalCircuitTrace.event_ofFn]

/-- Canonical request-shaped trace with explicit physical input and output
frames. Its interpretation is a theorem about the events, not a supplied meaning. -/
def expectedTrace (m n : Nat) (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat) : CircuitTrace.Trace :=
  ⟨m+n,List.ofFn (fun i => (outputRoute i).val),
    (expectedEvents m n inputRoute hIndices powerIndices fourierIndex).toArray⟩

theorem expectedTrace_meaning (m n : Nat) (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (atoms : Nat → Operator) (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat) :
    HierarchicalCircuitTrace.meaning atoms
      (expectedTrace m n inputRoute outputRoute hIndices powerIndices fourierIndex) =
      routeMatrix outputRoute *
        (scheduleAt m n inputRoute
          (fun axis => matrixAt 1 1 (atoms (hIndices axis)))
          (fun axis => matrixAt (n+1) (n+1) (atoms (powerIndices axis)))
          (matrixAt m m (atoms fourierIndex))).foldl (fun before operator => operator * before) 1 := by
  unfold HierarchicalCircuitTrace.meaning expectedTrace
  dsimp only
  rw [HierarchicalCircuitTrace.route_ofFn]
  congr 1
  unfold HierarchicalCircuitTrace.eventsMatrix
  rw [← expectedEvents_matrix,List.foldl_map]

/-- Direct exact branch theorem for a trace constructed from the independently
requested QPE coordinates and actual bound atom indices. A checker must still
establish that the actual artifact derives this trace and discharge these atom
equations. There is no whole-program interpretation premise. -/
theorem trace_branch (m n : Nat)
    (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (atoms : Nat → Operator) (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat)
    (U : Matrix (Bits n) (Bits n) ℂ)
    (hadamards : ∀ axis, matrixAt 1 1 (atoms (hIndices axis)) = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, matrixAt (n+1) (n+1) (atoms (powerIndices axis)) =
      HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : matrixAt m m (atoms fourierIndex) = (HierarchicalFourier.fourier m)ᴴ)
    (outcome : Bits m) (output input : Bits n) :
    HierarchicalCircuitTrace.meaning atoms
      (expectedTrace m n inputRoute outputRoute hIndices powerIndices fourierIndex)
      (basisEquiv outputRoute ((basisEquiv inputRoute).symm (Fin.append outcome output)))
      ((basisEquiv inputRoute).symm (Fin.append (fun _ => false) input)) =
        Qpe.kraus m U (HierarchicalGradient.number m outcome) output input := by
  rw [expectedTrace_meaning]
  exact routed_schedule_branch m n inputRoute outputRoute U _ _ _ hadamards powers fourier outcome output input

/-- The retained target operator for one physical readout row of the exact
request-shaped trace. Only the phase-register input is initialized to zero. -/
noncomputable def traceKraus (m n : Nat)
    (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (atoms : Nat → Operator) (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat)
    (outcome : Bits m) : Matrix (Bits n) (Bits n) ℂ := fun output input =>
  HierarchicalCircuitTrace.meaning atoms
    (expectedTrace m n inputRoute outputRoute hIndices powerIndices fourierIndex)
    (basisEquiv outputRoute ((basisEquiv inputRoute).symm (Fin.append outcome output)))
    ((basisEquiv inputRoute).symm (Fin.append (fun _ => false) input))

theorem trace_kraus (m n : Nat)
    (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (atoms : Nat → Operator) (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat)
    (U : Matrix (Bits n) (Bits n) ℂ)
    (hadamards : ∀ axis, matrixAt 1 1 (atoms (hIndices axis)) = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, matrixAt (n+1) (n+1) (atoms (powerIndices axis)) =
      HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : matrixAt m m (atoms fourierIndex) = (HierarchicalFourier.fourier m)ᴴ)
    (outcome : Bits m) :
    traceKraus m n inputRoute outputRoute atoms hIndices powerIndices fourierIndex outcome =
      Qpe.kraus m U (HierarchicalGradient.number m outcome) := by
  ext output input
  exact trace_branch m n inputRoute outputRoute atoms hIndices powerIndices fourierIndex U
    hadamards powers fourier outcome output input

/-- Equality of the complete target/reference outcome map, for arbitrary joint
input matrices. This preserves target coherences and pre-existing entanglement. -/
theorem trace_reference {R : Type} [Fintype R] [DecidableEq R] (m n : Nat)
    (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (atoms : Nat → Operator) (hIndices powerIndices : Fin m → Nat) (fourierIndex : Nat)
    (U : Matrix (Bits n) (Bits n) ℂ)
    (hadamards : ∀ axis, matrixAt 1 1 (atoms (hIndices axis)) = HierarchicalQpeCircuit.oneHadamard)
    (powers : ∀ axis, matrixAt (n+1) (n+1) (atoms (powerIndices axis)) =
      HierarchicalRoutedPower.controlled n (U^(2^axis.val)))
    (fourier : matrixAt m m (atoms fourierIndex) = (HierarchicalFourier.fourier m)ᴴ)
    (outcome : Bits m) (rho : Matrix (Bits n × R) (Bits n × R) ℂ) :
    Qpe.outcomeMap (traceKraus m n inputRoute outputRoute atoms hIndices powerIndices fourierIndex outcome) rho =
      Qpe.outcomeMap (Qpe.kraus m U (HierarchicalGradient.number m outcome)) rho := by
  rw [trace_kraus m n inputRoute outputRoute atoms hIndices powerIndices fourierIndex U
    hadamards powers fourier outcome]

end Qleisli.HierarchicalQpeCoordinates
