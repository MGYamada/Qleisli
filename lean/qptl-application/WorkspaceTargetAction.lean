import Qleisli.FiniteMatrixAction
import Qleisli.RawDenotation
import QleisliKernel.Target.CanonicalOpenQasmWorkspace
import Protocol.NativeContext.Bindings
import QPTL.CleanMarginal

/-! Relate a decoded target workspace slice to the actual checked Raw body
in its ordered data-then-scratch interface, including untouched references.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.WorkspaceTargetAction

open QleisliKernel Qirf Target.CanonicalOpenQasmWorkspace
open QleisliKernel.Semantics.Finite

private theorem rows {deps bits steps actual}
    (meaning : Qleisli.Semantics.Raw.CircuitMeaning deps bits steps actual) :
    actual.rows = 2^bits := by
  obtain ⟨_,_,matrix⟩ := meaning
  exact congrArg Semantics.Exact.Matrix.rows matrix

/-- The equality is on the complete local physical interface, including
scratch. The literal Raw body and the decoded target gates both realize the
original source body, retaining its phase on each joint reference column. -/
theorem decoded_action {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {layout start count} (checked : Checked map target layout start count)
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R)
    (inside : row < 2^(original.layout.bits+1)) :
    Semantics.RawAction.circuit deps checked.gates (fun input => joint input reference) row =
      Semantics.RawAction.circuit deps literal.emitted.steps (fun input => joint input reference) row := by
  obtain ⟨rawWork,rawLeft,rawRead⟩ := literal.equation.checked
  obtain ⟨targetWork,targetLeft,targetRead⟩ := checked.equation.checked
  obtain ⟨rawOriginal,rawAfter,rawChecked⟩ :=
    Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ rawWork rawLeft rawRead
  obtain ⟨targetOriginal,targetAfter,targetChecked⟩ :=
    Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ targetWork targetLeft targetRead
  obtain ⟨_,_,rawCircuitWork,rawCircuitLeft,_,_,_,_,_,rawCircuit,_,_,_⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ rawWork rawAfter rawChecked
  obtain ⟨_,_,targetCircuitWork,targetCircuitLeft,_,_,_,_,_,targetCircuit,_,_,_⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ targetWork targetAfter targetChecked
  have rawRows := rows (Qleisli.Raw.circuit_denotes _ _ _ _ _ _ rawCircuit)
  have targetRows := rows (Qleisli.Raw.circuit_denotes _ _ _ _ _ _ targetCircuit)
  have rawBound : row < literal.equation.actual.rows := rawRows.symm ▸ inside
  have targetBound : row < checked.equation.actual.rows := targetRows.symm ▸ inside
  have rawAction := Qleisli.Finite.circuitMatrix_action deps _ _
    rawCircuitWork rawCircuitLeft rawCircuit joint row reference rawBound
  have targetAction := Qleisli.Finite.circuitMatrix_action deps _ _
    targetCircuitWork targetCircuitLeft targetCircuit joint row reference targetBound
  rw [rawOriginal] at rawAction
  rw [targetOriginal] at targetAction
  exact targetAction.symm.trans rawAction

private theorem cleanEncoding {bits logical contract work left}
    (ran : (Raw.Workspace.required false bits logical).run work = (.ok contract,left)) :
    ∃ encoding before after,
      (Raw.zeroEncoding bits 1).run before = (.ok encoding,after) ∧
      contract = ⟨encoding,encoding,logical⟩ := by
  simp only [Raw.Workspace.required, Bool.false_eq_true, if_false] at ran
  obtain ⟨_,before,_,ran⟩ := Finite.bind_success _ _ _ _ _ ran
  obtain ⟨encoding,after,read,ret⟩ := Finite.bind_success _ _ _ _ _ ran
  exact ⟨encoding,before,after,read,(Finite.pure_success _ _ _ _ ret).1⟩

/-- Coefficient layout of the single clean circuit branch, after insertion of the
designated zero scratch. Data are the low axes in the original workspace. -/
noncomputable def cleanCoefficients (bits : Nat) (effective : Semantics.Exact.Matrix) :
    Unit → Fin 2 → Fin (2^bits) → Fin effective.cols → ℂ :=
  fun _ scratch output input =>
    Qleisli.Semantics.Exact.entry effective (output.val + scratch.val * 2^bits) input

/-- Actual successful workspace checking gives exact separation for every
reference density after inserting the initial clean owner. The matrix here is
the composition checked by the executable reader, including the actual body. -/
theorem clean_checked_separates {dependencies bits steps logical body actual work left}
    (ran : (Raw.Workspace.checkOriginal dependencies false bits steps logical body).run work =
      (.ok actual,left)) :
    ∃ (encoding : Encoding) (effective : Semantics.Exact.Matrix) (encodeWork encodeLeft before after : Nat),
      (Raw.zeroEncoding bits 1).run encodeWork = (.ok encoding,encodeLeft) ∧
      QleisliKernel.Exact.Matrix.compose actual encoding.map before = (.ok effective,after) ∧
      ∀ (R : Type) (input : _root_.Matrix (Fin effective.cols × R) (Fin effective.cols × R) ℂ)
        (a b : Fin 2) (o p : Fin (2^bits)) (r s : R),
        QPTL.FiniteMatrix.jointOutput (cleanCoefficients bits effective) input (a,o,r) (b,p,s) =
          if a = 0 ∧ b = 0 then
            QPTL.FiniteMatrix.jointOutput (cleanCoefficients bits effective) input (0,o,r) (0,p,s)
          else 0 := by
  obtain ⟨_,afterCheck,checked⟩ := Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ _ _ ran
  obtain ⟨contract,middle,_,afterCircuit,effective,afterEffective,required,afterRequired,
    read,_,actualCompose,requiredCompose,equal⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ _ afterCheck checked
  obtain ⟨encoding,encodeWork,encodeLeft,encoded,rfl⟩ := cleanEncoding read
  refine ⟨encoding,effective,encodeWork,encodeLeft,afterCircuit,afterEffective,encoded,actualCompose,?_⟩
  intro R input a b o p r s
  apply QPTL.FiniteMatrix.fixedScratch_separates (cleanCoefficients bits effective) 0 ?_ input a b o p r s
  intro scratch nonzero column
  apply (QPTL.FiniteMatrix.scratchPopulation_eq_zero_iff _ _ _).mpr
  intro history output
  have high : scratch.val = 1 := by
    have bound := scratch.isLt
    have positive : scratch.val ≠ 0 := fun zero => nonzero (Fin.ext zero)
    omega
  obtain ⟨_,_,mapWork,mapLeft,mapped⟩ := Raw.zeroEncoding_value _ _ _ _ _ encoded
  have shape := Raw.mapping_value _ _ _ _ _ _ mapped
  have rows : encoding.map.rows = 2^(bits+1) := congrArg Semantics.Exact.Matrix.rows shape
  have outputBound : output.val < 2^bits := output.isLt
  have dirty : 2^bits ≤ output.val + scratch.val * 2^bits := by simp [high]
  have inRange : output.val + scratch.val * 2^bits < encoding.map.rows := by
    rw [rows, high, Nat.one_mul, Nat.pow_succ]
    omega
  obtain ⟨_,_,cols,meaning⟩ := Qleisli.Exact.compose_meaning _ _ _ _ _ requiredCompose
  have columnBound : column.val < logical.cols := by
    rw [← cols,← equal]
    exact column.isLt
  let index := column.val
  change Qleisli.Semantics.Exact.entry effective (output.val + scratch.val * 2^bits) index = 0
  rw [congrArg (fun matrix => Qleisli.Semantics.Exact.entry matrix
    (output.val + scratch.val * 2^bits) index) equal, meaning _ _ inRange columnBound]
  apply List.sum_eq_zero
  intro term member
  obtain ⟨index,indexBound,rfl⟩ := List.mem_map.mp member
  rw [Qleisli.Raw.zeroEncoding_dirty _ _ _ _ _ encoded _ _ dirty inRange
    (List.mem_range.mp indexBound), zero_mul]

private theorem dirtyEncoding {bits logical contract work left}
    (ran : (Raw.Workspace.required true bits logical).run work = (.ok contract,left)) :
    ∃ identity expected mapWork promoteWork after,
      (Raw.mapping (bits+1) (bits+1) (List.range (2^(bits+1)))).run mapWork =
        (.ok identity,promoteWork) ∧
      (Raw.promote (bits+1) (List.range bits) logical).run promoteWork = (.ok expected,after) ∧
      contract = ⟨⟨Raw.registerBasis (bits+1),Raw.registerBasis (bits+1),identity⟩,
        ⟨Raw.registerBasis (bits+1),Raw.registerBasis (bits+1),identity⟩,expected⟩ := by
  simp only [Raw.Workspace.required] at ran
  obtain ⟨_,mapWork,_,ran⟩ := Finite.bind_success _ _ _ _ _ ran
  obtain ⟨identity,promoteWork,mapped,ran⟩ := Finite.bind_success _ _ _ _ _ ran
  obtain ⟨expected,after,promoted,ret⟩ := Finite.bind_success _ _ _ _ _ ran
  exact ⟨identity,expected,mapWork,promoteWork,after,mapped,promoted,(Finite.pure_success _ _ _ _ ret).1⟩

/-- Successful dirty checking fixes every actual matrix entry to the logical
matrix promoted on the ordered low data axes. The complete high scratch
coordinate participates, including its off-diagonal reference correlations. -/
theorem dirty_checked_promotion {dependencies bits steps logical body actual work left}
    (ran : (Raw.Workspace.checkOriginal dependencies true bits steps logical body).run work =
      (.ok actual,left)) :
    ∃ expected before after,
      (Raw.promote (bits+1) (List.range bits) logical).run before = (.ok expected,after) ∧
      ∀ (row col : Nat), row < 2^(bits+1) → col < 2^(bits+1) →
        Qleisli.Semantics.Exact.entry actual row col = Qleisli.Semantics.Exact.entry expected row col := by
  obtain ⟨_,afterCheck,checked⟩ := Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ _ _ ran
  obtain ⟨contract,_,circuitWork,afterCircuit,lhs,afterLeft,rhs,afterRight,
    read,circuit,actualCompose,requiredCompose,equal⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ _ afterCheck checked
  obtain ⟨identity,expected,mapWork,promoteWork,after,mapped,promoted,rfl⟩ := dirtyEncoding read
  refine ⟨expected,promoteWork,after,promoted,?_⟩
  intro row col hr hc
  let dim := 2^(bits+1)
  have mapping := Raw.mapping_value _ _ _ _ _ _ mapped
  have mapRows : identity.rows = dim := congrArg Semantics.Exact.Matrix.rows mapping
  have mapCols : identity.cols = dim := congrArg Semantics.Exact.Matrix.cols mapping
  have literal := Qleisli.Raw.circuit_denotes dependencies (bits+1) steps actual circuitWork afterCircuit circuit
  have rawRows : actual.rows = dim := rows literal
  have expectedCols : expected.cols = dim :=
    congrArg Semantics.Exact.Matrix.cols (Raw.promote_value _ _ _ _ _ _ promoted)
  have idEntry (r c : Nat) (insideR : r < dim) (insideC : c < dim) :
      Qleisli.Semantics.Exact.entry identity r c = if r = c then 1 else 0 := by
    rw [Qleisli.Raw.mapping_meaning _ _ _ _ _ _ mapped r c insideR insideC]
    rw [List.getElem?_range]
    · by_cases same : r = c
      · subst r
        simp
      · simp only [beq_iff_eq, Option.some.injEq, Ne.symm same, same, if_false]
    · exact insideC
  obtain ⟨actualCols,_,_,lhsEntry⟩ := Qleisli.Exact.compose_meaning _ _ _ _ _ actualCompose
  obtain ⟨_,_,_,rhsEntry⟩ := Qleisli.Exact.compose_meaning _ _ _ _ _ requiredCompose
  change actual.cols = identity.rows at actualCols
  have left : Qleisli.Semantics.Exact.entry lhs row col = Qleisli.Semantics.Exact.entry actual row col := by
    rw [lhsEntry row col (rawRows.symm ▸ hr) (mapCols.symm ▸ hc), actualCols, mapRows]
    refine (Qleisli.Exact.sum_map_congr _ _ _ ?_).trans
      (Qleisli.Exact.range_delta_sum dim col (Qleisli.Semantics.Exact.entry actual row) hc)
    intro k inRange
    rw [idEntry k col (List.mem_range.mp inRange) hc]
    by_cases same : col = k <;> simp [same,eq_comm]
  have right : Qleisli.Semantics.Exact.entry rhs row col = Qleisli.Semantics.Exact.entry expected row col := by
    rw [rhsEntry row col (mapRows.symm ▸ hr) (expectedCols.symm ▸ hc)]
    change ((List.range identity.cols).map _).sum = _
    rw [mapCols]
    refine (Qleisli.Exact.sum_map_congr _ _ _ ?_).trans
      (Qleisli.Exact.range_delta_sum dim row (fun k => Qleisli.Semantics.Exact.entry expected k col) hr)
    intro k inRange
    rw [idEntry row k hr (List.mem_range.mp inRange)]
    by_cases same : row = k <;> simp [same]
  exact left.symm.trans ((congrArg (fun matrix => Qleisli.Semantics.Exact.entry matrix row col) equal).trans right)

private theorem unique_slice {circuit scratch}
    {uses : List (CleanUse circuit scratch)} (ordered : uses.Pairwise CleanUse.before)
    {first second : CleanUse circuit scratch} (firstMember : first ∈ uses) (secondMember : second ∈ uses)
    {index : Nat} (firstStart : first.start ≤ index) (firstStop : index < first.start+first.count)
    (secondStart : second.start ≤ index) (secondStop : index < second.start+second.count) :
    first = second := by
  induction ordered with
  | nil => simp at firstMember
  | cons separate _ recurse =>
    simp only [List.mem_cons] at firstMember secondMember
    rcases firstMember with rfl | firstMember <;> rcases secondMember with rfl | secondMember
    · rfl
    · have gap := separate second secondMember
      unfold CleanUse.before at gap
      omega
    · have gap := separate first firstMember
      unfold CleanUse.before at gap
      omega
    · exact recurse firstMember secondMember

/-- Each gate touching a reused clean wire belongs to exactly one counted
restoration interval. The position is in the original target word, and the
interval contains its checked number of literal steps. -/
theorem clean_access_counted_once {bytes capacity}
    {target : Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {scratch uses} (reuse : Reuse target scratch uses)
    (index : Nat) (gate : Target.CanonicalOpenQasmResources.Instruction)
    (actual : target.circuit.gates[index]? = some gate) (touches : scratch ∈ gate.wires) :
    ∃! use, use ∈ uses ∧ use.start ≤ index ∧ index < use.start+use.count ∧
      use.steps.length = use.count ∧ use.start+use.count ≤ target.circuit.counts.gates := by
  obtain ⟨use,member,start,stop,length,bounded⟩ :=
    reuse.prepared_and_counted.2.2 index gate actual touches
  refine ⟨use,⟨member,start,stop,length,bounded⟩,?_⟩
  rintro other ⟨present,otherStart,otherStop,_,_⟩
  exact unique_slice reuse.ordered present member otherStart otherStop start stop

/-- Successful native placement binds each use of the reserved clean
location to a unique restoration slice counted in the decoded artifact.
The wire is prepared by the literal reset and absent from terminal readout. -/
theorem native_clean_access_counted_once (product : String) (bytes : ByteArray)
    (decision : Protocol.NativeContext.Decision .openQasmPlacement) (work left : Nat)
    (ok : (Protocol.NativeContext.run .openQasmPlacement product bytes).run work = (.ok decision,left)) :
    let placed := decision.value.2
    let circuit := placed.target.circuit
    ∀ scratch ∈ placed.proposal.reserved,
      scratch < circuit.counts.reset ∧ scratch ∉ circuit.measurements ∧
      ∀ index gate, circuit.gates[index]? = some gate → scratch ∈ gate.wires →
        ∃! use, use ∈ placed.placement.trace.recorded.cleanUses scratch ∧
          use.start ≤ index ∧ index < use.start+use.count ∧ use.steps.length = use.count ∧
          use.start+use.count ≤ circuit.counts.gates := by
  obtain ⟨checked,_,_,rfl⟩ := Protocol.NativeContext.run_openqasm_placement_binding product bytes decision work left ok
  dsimp only
  intro scratch member
  obtain ⟨reuse⟩ := checked.placement.trace.restored scratch member
  exact ⟨reuse.prepared_and_counted.2.1,reuse.unmeasured,clean_access_counted_once reuse⟩

/-- A failed placement work check serializes only the limit rejection.
Neither the checked prefix nor partial resource counts are published. -/
theorem native_limit_has_no_resources (product : String) (bytes : ByteArray) (work left : Nat)
    (ran : (Protocol.NativeContext.run .openQasmPlacement product bytes).run work =
      (.error (.native (.arithmetic .workLimit)),left)) :
    let result := (Protocol.NativeContext.run .openQasmPlacement product bytes).run work
    let reply := Protocol.NativeContext.reply .openQasmPlacement work result.1 result.2
    reply.success = false ∧ reply.lines = ["qleisli.native-result 3","error","limit"] := by
  dsimp only
  rw [ran]
  exact ⟨rfl,rfl⟩

#print axioms native_limit_has_no_resources
#print axioms native_clean_access_counted_once
#print axioms dirty_checked_promotion
#print axioms clean_checked_separates
#print axioms decoded_action
end Qleisli.WorkspaceTargetAction
