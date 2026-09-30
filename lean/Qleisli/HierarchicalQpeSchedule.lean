import Qleisli.HierarchicalCircuitTraceEvaluation
import Qleisli.HierarchicalQpeLayout
import Qleisli.HierarchicalRoutedPower
import QleisliKernel.Hierarchical.QpeSchedule

/-! Actual component equations for the coherent QPE schedule inspector.
Finite readers consume the exact retained bytes; provider evaluation refers to
the same artifact and still requires its independent requested meaning.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.HierarchicalQpeSchedule
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalSemantics HierarchicalFiniteEvaluation
open scoped Matrix

def LeafEquation (leaves : Leaves Operator) (leaf : QpeSchedule.Leaf) : Prop :=
  ∃ value, leaves.implementation leaf.definition.interface leaf.program = some value ∧
    value.inputWidth = 1 ∧ value.outputWidth = 1 ∧
    matrixAt 1 1 value = HierarchicalQpeCircuit.oneHadamard

theorem leaf_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (atom : CircuitTrace.Atom) (leaf : QpeSchedule.Leaf)
    (bound : QpeSchedule.leaf artifact atom = some leaf)
    (equation : LeafEquation leaves leaf) :
    ∃ op, physical algebra leaves artifact 1 atom.index = some op ∧
      op.inputWidth = 1 ∧ op.outputWidth = 1 ∧
      matrixAt 1 1 op = HierarchicalQpeCircuit.oneHadamard := by
  obtain ⟨found,body,_⟩ := QpeSchedule.leaf_bound artifact atom leaf bound
  obtain ⟨op,read,meaning⟩ := equation
  exact ⟨op,by simp [HierarchicalFiniteEvaluation.physical,evaluate,definition,found,body,read],meaning⟩

theorem part_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (h power : CircuitTrace.Atom) (axis : Nat)
    (order : Array Nat) (remaining : Nat) (part : QpeSchedule.Part)
    (checked : QpeSchedule.checkPart artifact request h power axis order remaining = .ok part)
    (equation : LeafEquation leaves part.hadamard)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size) :
    (∃ op, physical algebra leaves artifact 1 h.index = some op ∧
      op.inputWidth = 1 ∧ op.outputWidth = 1 ∧
      matrixAt 1 1 op = HierarchicalQpeCircuit.oneHadamard) ∧
    (∃ fuel op, physical algebra leaves artifact fuel power.index = some op ∧
      op.inputWidth = request.target.size+1 ∧ op.outputWidth = request.target.size+1 ∧
      matrixAt (request.target.size+1) (request.target.size+1) op =
        HierarchicalRoutedPower.controlled request.target.size
          ((matrixAt request.target.size request.target.size provider)^(2^axis))) := by
  have facts := QpeSchedule.checkPart_conditions artifact request h power axis order remaining part checked
  exact ⟨leaf_evaluates leaves artifact h part.hadamard facts.1 equation,
    HierarchicalRoutedPower.inspect_evaluates leaves artifact power.index
      (QpeSchedule.powerRequest request power axis) order remaining part.power facts.2.1
      providerFuel provider evaluated hi ho⟩

theorem inverse_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (width : Nat) (atom : CircuitTrace.Atom) (order : Array Nat)
    (remaining : Nat) (inverse : QpeSchedule.Inverse)
    (checked : QpeSchedule.checkInverse artifact width atom order remaining = .ok inverse)
    (equations : ∀ r ∈ inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r) :
    ∃ fuel op, physical algebra leaves artifact fuel atom.index = some op ∧
      op.inputWidth = width ∧ op.outputWidth = width ∧
      matrixAt width width op = (HierarchicalFourier.fourier width)ᴴ := by
  have facts := QpeSchedule.checkInverse_conditions artifact width atom order remaining inverse checked
  obtain ⟨found,body,_,_,sized⟩ := QpeSchedule.inverseView_bound artifact width atom inverse.view facts.1
  obtain ⟨fuel,forward,actual,hi,ho,matrix⟩ := HierarchicalFourierRoot.inspect_evaluates leaves
    (QpeSchedule.atEntry artifact inverse.view.child) ⟨width,inverse.view.forward.interface⟩ order
    remaining inverse.fourier facts.2.1 equations
  rw [physical_ir_only algebra leaves (QpeSchedule.atEntry artifact inverse.view.child) artifact rfl] at actual
  change physical algebra leaves artifact fuel inverse.view.child = some forward at actual
  have dims := RoutedPower.sized_fields width inverse.view.definition sized
  refine ⟨fuel+1,apply inverse.view.definition.interface .inverse [forward],?_,dims.2.2.1,dims.2.2.2,?_⟩
  · rw [physical_step algebra leaves artifact fuel atom.index inverse.view.definition .inverse
      [inverse.view.child] found (by simp [physicalCode,body])]
    simp only [List.mapM_cons,actual,List.mapM_nil,bind,Option.bind,pure]
    rfl
  · rw [HierarchicalUnitary.matrix_inverse _ _ width dims.2.2.1 dims.2.2.2,matrix]

/-- Unique actual evaluation, independent of fuel. This mathematical choice is
outside the executable kernel. -/
noncomputable def selected (leaves : Leaves Operator) (artifact : Artifact) (index : Nat) : Operator := by
  classical
  exact if existsValue : ∃ op, ∃ fuel, physical algebra leaves artifact fuel index = some op then
    Classical.choose existsValue else identity 0

theorem selected_eq (leaves : Leaves Operator) (artifact : Artifact) (index fuel : Nat)
    (op : Operator) (evaluated : physical algebra leaves artifact fuel index = some op) :
    selected leaves artifact index = op := by
  have existsValue : ∃ value, ∃ depth, physical algebra leaves artifact depth index = some value :=
    ⟨op,fuel,evaluated⟩
  rw [selected,dif_pos existsValue]
  obtain ⟨depth,found⟩ := Classical.choose_spec existsValue
  exact evaluate_unique algebra (definition leaves artifact) depth fuel index _ op found evaluated

/-- Every requested stage is backed by a retained, actually checked part. -/
theorem parts_find (artifact : Artifact) (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate)
    (axes : List Nat) (parts : List QpeSchedule.Part)
    (ready : QpeSchedule.PartsChecked artifact request candidate axes parts)
    (axis : Nat) (member : axis ∈ axes) :
    ∃ part ∈ parts, QpeSchedule.PartChecked artifact request candidate axis part := by
  induction axes generalizing parts with
  | nil => simp at member
  | cons head rest ih =>
    cases parts with
    | nil => exact False.elim ready
    | cons part tail =>
      rcases List.mem_cons.mp member with same | later
      · subst axis
        exact ⟨part,List.mem_cons_self,ready.1⟩
      · obtain ⟨found,inside,checked⟩ := ih tail ready.2 later
        exact ⟨found,List.mem_cons_of_mem part inside,checked⟩

/-- Evaluation and full requested interface dimensions for a selected atom. -/
def ActualAtom (leaves : Leaves Operator) (artifact : Artifact) (atom : CircuitTrace.Atom) : Prop :=
  ∃ fuel, physical algebra leaves artifact fuel atom.index = some (selected leaves artifact atom.index) ∧
    (selected leaves artifact atom.index).inputWidth = width atom.interface.inputs ∧
    (selected leaves artifact atom.index).outputWidth = width atom.interface.outputs

theorem part_selected (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (h power : CircuitTrace.Atom) (axis : Nat)
    (order : Array Nat) (remaining : Nat) (part : QpeSchedule.Part)
    (checked : QpeSchedule.checkPart artifact request h power axis order remaining = .ok part)
    (equation : LeafEquation leaves part.hadamard)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size) :
    ActualAtom leaves artifact h ∧ ActualAtom leaves artifact power ∧
    matrixAt 1 1 (selected leaves artifact h.index) = HierarchicalQpeCircuit.oneHadamard ∧
    matrixAt (request.target.size+1) (request.target.size+1) (selected leaves artifact power.index) =
      HierarchicalRoutedPower.controlled request.target.size
        ((matrixAt request.target.size request.target.size provider)^(2^axis)) := by
  have checkedFacts := QpeSchedule.checkPart_conditions artifact request h power axis order remaining part checked
  obtain ⟨_,_,header,hsize,_⟩ := QpeSchedule.leaf_bound artifact h part.hadamard checkedFacts.1
  have hdims := RoutedPower.sized_fields 1 part.hadamard.definition hsize
  have powerFacts := RoutedPower.inspect_conditions artifact power.index
    (QpeSchedule.powerRequest request power axis) order remaining part.power checkedFacts.2.1
  obtain ⟨pheader,psize,_⟩ := RoutedPower.shape_fields _ _ powerFacts.2.1
  change part.power.view.root.interface = power.interface at pheader
  have pdims := RoutedPower.sized_fields (request.target.size+1) part.power.view.root psize
  obtain ⟨⟨hop,hactual,hin,hout,hmatrix⟩,⟨pfuel,pop,pactual,pin,pout,pmatrix⟩⟩ :=
    part_evaluates leaves artifact request h power axis order remaining part checked equation
      providerFuel provider evaluated hi ho
  have hs := selected_eq leaves artifact h.index 1 hop hactual
  have ps := selected_eq leaves artifact power.index pfuel pop pactual
  refine ⟨⟨1,?_,?_,?_⟩,⟨pfuel,?_,?_,?_⟩,?_,?_⟩
  · simpa only [hs] using hactual
  · rw [hs,hin,← header]; exact hdims.2.2.1.symm
  · rw [hs,hout,← header]; exact hdims.2.2.2.symm
  · simpa only [ps] using pactual
  · rw [ps,pin,← pheader]; exact pdims.2.2.1.symm
  · rw [ps,pout,← pheader]; exact pdims.2.2.2.symm
  · simpa only [hs] using hmatrix
  · simpa only [ps] using pmatrix

theorem inverse_selected (leaves : Leaves Operator) (artifact : Artifact)
    (width : Nat) (atom : CircuitTrace.Atom) (order : Array Nat)
    (remaining : Nat) (inverse : QpeSchedule.Inverse)
    (checked : QpeSchedule.checkInverse artifact width atom order remaining = .ok inverse)
    (equations : ∀ r ∈ inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r) :
    ActualAtom leaves artifact atom ∧
      matrixAt width width (selected leaves artifact atom.index) = (HierarchicalFourier.fourier width)ᴴ := by
  have facts := QpeSchedule.checkInverse_conditions artifact width atom order remaining inverse checked
  obtain ⟨_,_,_,header,sized⟩ := QpeSchedule.inverseView_bound artifact width atom inverse.view facts.1
  have dims := RoutedPower.sized_fields width inverse.view.definition sized
  obtain ⟨fuel,op,actual,hi,ho,matrix⟩ :=
    inverse_evaluates leaves artifact width atom order remaining inverse checked equations
  have same := selected_eq leaves artifact atom.index fuel op actual
  refine ⟨⟨fuel,?_,?_,?_⟩,?_⟩
  · simpa only [same] using actual
  · rw [same,hi,← header]; exact dims.2.2.1.symm
  · rw [same,ho,← header]; exact dims.2.2.2.symm
  · simpa only [same] using matrix

/-- A precise stage-index lookup from the actual recursive part checker. -/
theorem parts_at (artifact : Artifact) (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate)
    (parts : QpeSchedule.Parts)
    (ready : QpeSchedule.PartsChecked artifact request candidate (List.range request.phase.size) parts.values)
    (axis : Nat) (bound : axis < request.phase.size) :
    ∃ part ∈ parts.values, ∃ h power order remaining,
      candidate.hadamards[axis]? = some h ∧ candidate.powers[axis]? = some power ∧
      QpeSchedule.checkPart artifact request h power axis order remaining = .ok part := by
  obtain ⟨part,member,h,power,order,remaining,hh,hp,_,checked⟩ :=
    parts_find artifact request candidate _ parts.values ready axis (List.mem_range.mpr bound)
  exact ⟨part,member,h,power,order,remaining,hh,hp,checked⟩

/-- Selected actual stage meanings, obtained from each retained checker part. -/
theorem inspected_stages (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate) (remaining : Nat)
    (pending : QpeSchedule.Pending)
    (checked : QpeSchedule.inspect artifact request candidate remaining = .ok pending)
    (equations : ∀ part ∈ pending.parts.values, LeafEquation leaves part.hadamard)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size)
    (axis : Nat) (bound : axis < request.phase.size) :
    ∃ h power, candidate.hadamards[axis]? = some h ∧ candidate.powers[axis]? = some power ∧
      ActualAtom leaves artifact h ∧ ActualAtom leaves artifact power ∧
      matrixAt 1 1 (selected leaves artifact h.index) = HierarchicalQpeCircuit.oneHadamard ∧
      matrixAt (request.target.size+1) (request.target.size+1) (selected leaves artifact power.index) =
        HierarchicalRoutedPower.controlled request.target.size
          ((matrixAt request.target.size request.target.size provider)^(2^axis)) := by
  have facts := QpeSchedule.inspect_conditions artifact request candidate remaining pending checked
  have ready := (QpeSchedule.checkParts_conditions _ _ _ _ _ _ facts.2.2.2.2.2.1).2
  obtain ⟨part,member,h,power,order,allowance,hh,hp,partChecked⟩ :=
    parts_at artifact request candidate pending.parts ready axis bound
  exact ⟨h,power,hh,hp,part_selected leaves artifact request h power axis order allowance part partChecked
    (equations part member) providerFuel provider evaluated hi ho⟩

/-- All opaque trace atoms are bound to the same artifact's actual definitions. -/
theorem inspected_atoms (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate) (remaining : Nat)
    (pending : QpeSchedule.Pending)
    (checked : QpeSchedule.inspect artifact request candidate remaining = .ok pending)
    (equations : ∀ part ∈ pending.parts.values, LeafEquation leaves part.hadamard)
    (fourierEquations : ∀ r ∈ pending.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size) :
    HierarchicalCircuitTrace.AtomEquations leaves artifact (QpeSchedule.atoms candidate) (selected leaves artifact) := by
  have facts := QpeSchedule.inspect_conditions artifact request candidate remaining pending checked
  have inverse := inverse_selected leaves artifact request.phase.size candidate.inverseFourier
    candidate.fourierOrder _ pending.inverse facts.2.2.2.2.2.2.1 fourierEquations
  intro atom member
  have member : atom ∈ candidate.hadamards ∨ atom ∈ candidate.powers ∨ atom = candidate.inverseFourier := by
    simpa [QpeSchedule.atoms,or_assoc] using member
  rcases member with hm | pm | fm
  · obtain ⟨axis,bound,same⟩ := Array.mem_iff_getElem.mp hm
    have inPhase : axis < request.phase.size := by omega
    obtain ⟨h,power,hh,_,actual,_⟩ := inspected_stages leaves artifact request candidate remaining pending checked
      equations providerFuel provider evaluated hi ho axis inPhase
    have equal : h = atom := by
      rw [Array.getElem?_eq_getElem bound] at hh
      exact (Option.some.inj hh).symm.trans same
    simpa only [equal] using actual
  · obtain ⟨axis,bound,same⟩ := Array.mem_iff_getElem.mp pm
    have inPhase : axis < request.phase.size := by omega
    obtain ⟨h,power,_,hp,_,actual,_⟩ := inspected_stages leaves artifact request candidate remaining pending checked
      equations providerFuel provider evaluated hi ho axis inPhase
    have equal : power = atom := by
      rw [Array.getElem?_eq_getElem bound] at hp
      exact (Option.some.inj hp).symm.trans same
    simpa only [equal] using actual
  · subst atom
    exact inverse.1

theorem inspected_matrices (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate) (remaining : Nat)
    (pending : QpeSchedule.Pending)
    (checked : QpeSchedule.inspect artifact request candidate remaining = .ok pending)
    (equations : ∀ part ∈ pending.parts.values, LeafEquation leaves part.hadamard)
    (fourierEquations : ∀ r ∈ pending.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size)
    (hs : candidate.hadamards.size = request.phase.size) (ps : candidate.powers.size = request.phase.size) :
    (∀ axis, matrixAt 1 1 (selected leaves artifact
        (HierarchicalQpeLayout.indices request.phase.size candidate.hadamards hs axis)) =
      HierarchicalQpeCircuit.oneHadamard) ∧
    (∀ axis, matrixAt (request.target.size+1) (request.target.size+1) (selected leaves artifact
        (HierarchicalQpeLayout.indices request.phase.size candidate.powers ps axis)) =
      HierarchicalRoutedPower.controlled request.target.size
        ((matrixAt request.target.size request.target.size provider)^(2^axis.val))) ∧
    matrixAt request.phase.size request.phase.size (selected leaves artifact candidate.inverseFourier.index) =
      (HierarchicalFourier.fourier request.phase.size)ᴴ := by
  have stages (axis : Fin request.phase.size) :
      matrixAt 1 1 (selected leaves artifact
          (HierarchicalQpeLayout.indices request.phase.size candidate.hadamards hs axis)) =
        HierarchicalQpeCircuit.oneHadamard ∧
      matrixAt (request.target.size+1) (request.target.size+1) (selected leaves artifact
          (HierarchicalQpeLayout.indices request.phase.size candidate.powers ps axis)) =
        HierarchicalRoutedPower.controlled request.target.size
          ((matrixAt request.target.size request.target.size provider)^(2^axis.val)) := by
    obtain ⟨h,power,hh,hp,_,_,hm,pm⟩ := inspected_stages leaves artifact request candidate remaining pending checked
      equations providerFuel provider evaluated hi ho axis.val axis.isLt
    have hb : axis.val < candidate.hadamards.size := by omega
    have pb : axis.val < candidate.powers.size := by omega
    rw [Array.getElem?_eq_getElem hb] at hh
    rw [Array.getElem?_eq_getElem pb] at hp
    dsimp only [HierarchicalQpeLayout.indices]
    rw [Option.some.inj hh,Option.some.inj hp]
    exact ⟨hm,pm⟩
  have facts := QpeSchedule.inspect_conditions artifact request candidate remaining pending checked
  exact ⟨fun axis => (stages axis).1,fun axis => (stages axis).2,
    (inverse_selected leaves artifact request.phase.size candidate.inverseFourier candidate.fourierOrder _
      pending.inverse facts.2.2.2.2.2.2.1 fourierEquations).2⟩

/-- The actual coherent root evaluates to its freshly derived exact schedule.
The only semantic premises concern its actual finite leaves and provider. -/
theorem inspect_evaluates (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate) (remaining : Nat)
    (pending : QpeSchedule.Pending)
    (checked : QpeSchedule.inspect artifact request candidate remaining = .ok pending)
    (equations : ∀ part ∈ pending.parts.values, LeafEquation leaves part.hadamard)
    (fourierEquations : ∀ r ∈ pending.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size) :
    ∃ fuel op, physical algebra leaves artifact fuel artifact.entry.implementation = some op ∧
      HierarchicalCircuitTrace.At (selected leaves artifact) (QpeSchedule.expected request candidate) op := by
  exact HierarchicalCircuitTrace.derives_evaluates leaves artifact (QpeSchedule.atoms candidate)
    (selected leaves artifact) (inspected_atoms leaves artifact request candidate remaining pending checked
      equations fourierEquations providerFuel provider evaluated hi ho) _ _
    (QpeSchedule.inspect_derives artifact request candidate remaining pending checked)

/-- A complete target branch of an actual root in the request's checked physical
frames. The frame proof is obtained from `QpeSchedule.inspect_conditions`. -/
noncomputable def branch (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (op : Operator) (outcome : CoordinateOperators.Bits request.phase.size) :
    Matrix (CoordinateOperators.Bits request.target.size) (CoordinateOperators.Bits request.target.size) ℂ :=
  fun output input => matrixAt (request.phase.size+request.target.size) (request.phase.size+request.target.size) op
    (CoordinateOperators.basisEquiv (HierarchicalQpeLayout.outputRoute request valid)
      ((CoordinateOperators.basisEquiv (HierarchicalQpeLayout.inputRoute request valid)).symm (Fin.append outcome output)))
    ((CoordinateOperators.basisEquiv (HierarchicalQpeLayout.inputRoute request valid)).symm (Fin.append (fun _ => false) input))

/-- An accepted actual coherent root has the independently named QPE target
Kraus operators. The provider's independent requested matrix is explicit; the
whole-root matrix is derived, never supplied. Layout validity is also returned
from actual acceptance, not added as an independent geometry premise. -/
theorem inspect_kraus (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate) (remaining : Nat)
    (pending : QpeSchedule.Pending)
    (checked : QpeSchedule.inspect artifact request candidate remaining = .ok pending)
    (equations : ∀ part ∈ pending.parts.values, LeafEquation leaves part.hadamard)
    (fourierEquations : ∀ r ∈ pending.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size)
    (U : Matrix (CoordinateOperators.Bits request.target.size) (CoordinateOperators.Bits request.target.size) ℂ)
    (providerMeaning : matrixAt request.target.size request.target.size provider = U) :
    ∃ (valid : QpeSchedule.layout request = true), ∃ fuel op,
      physical algebra leaves artifact fuel artifact.entry.implementation = some op ∧
      op.inputWidth = request.phase.size+request.target.size ∧
      op.outputWidth = request.phase.size+request.target.size ∧
      ∀ outcome, branch request valid op outcome =
        Qpe.kraus request.phase.size U (HierarchicalGradient.number request.phase.size outcome) := by
  have facts := QpeSchedule.inspect_conditions artifact request candidate remaining pending checked
  obtain ⟨fuel,op,actual,traceMeaning⟩ := inspect_evaluates leaves artifact request candidate remaining pending checked
    equations fourierEquations providerFuel provider evaluated hi ho
  have matrices := inspected_matrices leaves artifact request candidate remaining pending checked
    equations fourierEquations providerFuel provider evaluated hi ho facts.2.1 facts.2.2.1
  rw [providerMeaning] at matrices
  rw [HierarchicalQpeLayout.expected_eq request facts.1 candidate facts.2.1 facts.2.2.1] at traceMeaning
  refine ⟨facts.1,fuel,op,actual,traceMeaning.1,traceMeaning.2.1,?_⟩
  intro outcome
  ext output input
  unfold branch
  have rootMatrix := traceMeaning.2.2
  change matrixAt (request.phase.size+request.target.size) (request.phase.size+request.target.size) op = _ at rootMatrix
  rw [rootMatrix]
  exact HierarchicalQpeCoordinates.trace_branch request.phase.size request.target.size
    (HierarchicalQpeLayout.inputRoute request facts.1) (HierarchicalQpeLayout.outputRoute request facts.1)
    (selected leaves artifact) _ _ _ U matrices.1 matrices.2.1 matrices.2.2 outcome output input

/-- Full target/reference outcome-map equality for arbitrary joint input state.
This is derived from the actual accepted coherent root and exact atom bindings. -/
theorem inspect_reference {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves Operator) (artifact : Artifact)
    (request : QpeSchedule.Request) (candidate : QpeSchedule.Candidate) (remaining : Nat)
    (pending : QpeSchedule.Pending)
    (checked : QpeSchedule.inspect artifact request candidate remaining = .ok pending)
    (equations : ∀ part ∈ pending.parts.values, LeafEquation leaves part.hadamard)
    (fourierEquations : ∀ r ∈ pending.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves artifact providerFuel request.provider = some provider)
    (hi : provider.inputWidth = request.target.size) (ho : provider.outputWidth = request.target.size)
    (U : Matrix (CoordinateOperators.Bits request.target.size) (CoordinateOperators.Bits request.target.size) ℂ)
    (providerMeaning : matrixAt request.target.size request.target.size provider = U) :
    ∃ (valid : QpeSchedule.layout request = true), ∃ fuel op,
      physical algebra leaves artifact fuel artifact.entry.implementation = some op ∧
      ∀ outcome (rho : Matrix (CoordinateOperators.Bits request.target.size × R)
          (CoordinateOperators.Bits request.target.size × R) ℂ),
        Qpe.outcomeMap (branch request valid op outcome) rho =
          Qpe.outcomeMap (Qpe.kraus request.phase.size U
            (HierarchicalGradient.number request.phase.size outcome)) rho := by
  obtain ⟨valid,fuel,op,actual,_,_,meaning⟩ := inspect_kraus leaves artifact request candidate remaining pending checked
    equations fourierEquations providerFuel provider evaluated hi ho U providerMeaning
  refine ⟨valid,fuel,op,actual,?_⟩
  intro outcome rho
  rw [meaning]

end Qleisli.HierarchicalQpeSchedule
