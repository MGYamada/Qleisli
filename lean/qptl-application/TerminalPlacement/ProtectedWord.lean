import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimeScatterTransport
import QleisliKernel.Raw.Structure
import Qleisli.RawFiniteRows
import Qleisli.RuntimeFiniteTargetScatter
import Qleisli.FinitePull
import Qleisli.ExactMatrix
import Qleisli.RawProtected

/-! The same literal single-axis gate occurs in the packed protected carrier
and its independent coefficient semantics.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.ProtectedComputeAction
open QleisliKernel
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Gate)
open QleisliKernel.Qirf.RuntimeScatterTransport (scatter_gather write bit_write bit_lt)

private theorem bit_xor_singleton (row axis index : Nat) :
    bit (row ^^^ 2^axis) index = if index = axis then 1 - bit row index else bit row index := by
  rw [show bit (row ^^^ 2^axis) index = ((row ^^^ 2^axis).testBit index).toNat from
    (Nat.toNat_testBit _ _).symm,
    show bit row index = (row.testBit index).toNat from (Nat.toNat_testBit _ _).symm,
    Nat.testBit_xor,Nat.testBit_two_pow]
  by_cases same : index = axis
  · subst index
    cases row.testBit axis <;> simp
  · simp [same,Ne.symm same]

theorem write_toggle (row axis : Nat) :
    write row axis (1 - bit row axis) = row ^^^ 2^axis := by
  apply Nat.eq_of_testBit_eq
  intro index
  have equal : bit (write row axis (1 - bit row axis)) index = bit (row ^^^ 2^axis) index := by
    have bounded : 1 - bit row axis < 2 := by omega
    rw [bit_write _ _ _ _ bounded,bit_xor_singleton]
    by_cases same : index = axis
    · subst index
      simp
    · simp [same]
  have injective (first second : Bool) (same : first.toNat = second.toNat) : first = second := by
    cases first <;> cases second <;> simp_all
  apply injective
  rw [Nat.toNat_testBit,Nat.toNat_testBit]
  exact equal

private theorem scatter_toggle (row axis : Nat) :
    scatter row [axis] (1 - bit row axis) = row ^^^ 2^axis := by
  have low : bit (1 - bit row axis) 0 = 1 - bit row axis := by simp [bit]
  change write row axis (bit (1 - bit row axis) 0) = _
  rw [low,write_toggle]

/-- Executing the literal primitive word reads precisely the independent
focused gate action, including the original complex coefficient at each row. -/
theorem literal_gate (dependencies : List Dependency) (gate : Gate) (axis row : Nat)
    (amplitudes : Nat → ℂ) :
    Semantics.RawAction.step dependencies (Raw.gateStep gate axis) amplitudes row =
    Semantics.Protected.gate gate axis amplitudes row := by
  have gatherBit : gather row [axis] = bit row axis := by simp [gather,List.zipIdx_cons,List.zipIdx_nil]
  have same : scatter row [axis] (bit row axis) = row := by
    rw [← gatherBit]
    exact scatter_gather row [axis] (by simp)
  have toggle := scatter_toggle row axis
  have indices : List.range 2 = [0,1] := by decide
  have phaseZero : Semantics.Finite.phase 0 = 1 := rfl
  have bound := bit_lt row axis
  have bitCases : bit row axis = 0 ∨ bit row axis = 1 := by omega
  cases gate with
  | h => rfl
  | x =>
    rcases bitCases with off | on
    · simp [off] at toggle
      simp [Semantics.RawAction.step,Raw.gateStep,enabled,indices,gatherBit,off,toggle,phaseZero,Semantics.Protected.gate]
    · simp [on] at toggle
      simp [Semantics.RawAction.step,Raw.gateStep,enabled,indices,gatherBit,on,toggle,phaseZero,Semantics.Protected.gate]
  | z =>
    rcases bitCases with off | on
    · simp [off] at same
      simp [Semantics.RawAction.step,Raw.gateStep,enabled,indices,gatherBit,off,same,phaseZero,Semantics.Protected.gate]
    · simp [on] at same
      simp [Semantics.RawAction.step,Raw.gateStep,enabled,indices,gatherBit,on,same,Semantics.Protected.gate]
  | t =>
    rcases bitCases with off | on
    · simp [off] at same
      simp [Semantics.RawAction.step,Raw.gateStep,enabled,indices,gatherBit,off,same,phaseZero,Semantics.Protected.gate]
    · simp [on] at same
      simp [Semantics.RawAction.step,Raw.gateStep,enabled,indices,gatherBit,on,same,Semantics.Protected.gate]

#print axioms literal_gate
end Qleisli.ProtectedComputeAction

/-! The exact action of protected use words on the original packed source,
target and auxiliary coordinates.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.ProtectedComputeAction
open QleisliKernel
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Gate ProtectedBit ProtectedControl Use)
open QleisliKernel.FiniteRestriction (pack pack_low pack_high bit_target bit_selector)
open QleisliKernel.Qirf.RuntimeScatterTransport (write)
open Qleisli.Semantics.Protected (gate blockUse blocks)

/-- Source occupies the low data bits, then targets, then private auxiliary
bits. It is the order used by the literal table word. -/
def carrier (sourceBits targetBits source auxiliary target : Nat) : Nat :=
  pack (sourceBits+targetBits) (pack sourceBits source target) auxiliary

theorem pack_in {width highBits low high : Nat} (lowIn : low < 2^width) (highIn : high < 2^highBits) :
    pack width low high < 2^(width+highBits) := by
  unfold pack
  rw [Nat.pow_add]
  have below : low + 2^width*high < 2^width*(high+1) := by rw [Nat.mul_succ]; omega
  exact Nat.lt_of_lt_of_le below (Nat.mul_le_mul_left _ (by omega))

private theorem carrier_assoc (sourceBits targetBits source auxiliary target : Nat) :
    carrier sourceBits targetBits source auxiliary target = pack sourceBits source (pack targetBits target auxiliary) := by
  simp only [carrier,pack,Nat.pow_add,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]

private theorem packed_target_bit {sourceBits targetBits source auxiliary target axis : Nat}
    (sourceIn : source < 2^sourceBits) (inside : axis < targetBits) :
    bit (carrier sourceBits targetBits source auxiliary target) (sourceBits+axis) = bit target axis := by
  rw [carrier_assoc,bit_target _ _ _ _ sourceIn,bit_selector _ _ _ _ inside]

private theorem packed_protected_bit {sourceBits targetBits auxiliaryBits source auxiliary target : Nat}
    (sourceIn : source < 2^sourceBits) (targetIn : target < 2^targetBits)
    (location : ProtectedBit) (valid : Raw.protectedValid sourceBits auxiliaryBits location = true) :
    (bit (carrier sourceBits targetBits source auxiliary target) (Raw.protectedAxis (sourceBits+targetBits) location) == 1) =
      QleisliKernel.Semantics.Protected.value source auxiliary location := by
  rcases location with ⟨region,index⟩
  cases region with
  | source =>
    have within : index < sourceBits := by simpa [Raw.protectedValid] using valid
    change (bit (carrier sourceBits targetBits source auxiliary target) index == 1) = (bit source index == 1)
    rw [carrier_assoc,bit_selector _ _ _ _ within]
  | ancilla =>
    change (bit (carrier sourceBits targetBits source auxiliary target) (sourceBits+targetBits+index) == 1) =
      (bit auxiliary index == 1)
    rw [carrier,bit_target _ _ _ _ (pack_in sourceIn targetIn)]

private theorem packed_controls {sourceBits targetBits auxiliaryBits source auxiliary target : Nat}
    (sourceIn : source < 2^sourceBits) (targetIn : target < 2^targetBits)
    (controls : List ProtectedControl) (valid : Raw.protectedControlsValid sourceBits auxiliaryBits controls = true) :
    enabled (controls.map fun c => ⟨Raw.protectedAxis (sourceBits+targetBits) c.bit,c.whenOne⟩)
      (carrier sourceBits targetBits source auxiliary target) =
    QleisliKernel.Semantics.Protected.enabled source auxiliary controls := by
  have check := (Bool.and_eq_true_iff.mp valid).1
  unfold enabled QleisliKernel.Semantics.Protected.enabled
  rw [List.all_map]
  clear valid
  induction controls with
  | nil => rfl
  | cons control rest ih =>
    simp only [List.all_cons,Bool.and_eq_true] at check
    simp only [List.all_cons,Function.comp_apply,packed_protected_bit sourceIn targetIn control.bit check.1,ih check.2]

private theorem write_low_pack {width row high axis value : Nat} (inside : axis < width) :
    write (pack width row high) axis value = pack width (write row axis value) high := by
  unfold write
  rw [bit_selector _ _ _ _ inside]
  unfold pack
  rw [Nat.add_comm row (2^width * high),Nat.add_sub_assoc (QleisliKernel.FiniteRestriction.bit_weight_le row axis)]
  ac_rfl

private theorem write_target {sourceBits targetBits source auxiliary target axis value : Nat}
    (sourceIn : source < 2^sourceBits) (inside : axis < targetBits) (valid : value < 2) :
    write (carrier sourceBits targetBits source auxiliary target) (sourceBits+axis) value =
    carrier sourceBits targetBits source auxiliary (write target axis value) := by
  rw [carrier_assoc,carrier_assoc]
  have low : bit value 0 = value := by simp [bit,Nat.mod_eq_of_lt valid]
  have action := QleisliKernel.FiniteRestriction.update_pack sourceBits source (pack targetBits target auxiliary)
    axis value 0 sourceIn
  rw [low] at action
  calc
    _ = pack sourceBits source (write (pack targetBits target auxiliary) axis value) := action
    _ = _ := by rw [write_low_pack inside]

private theorem gate_target {sourceBits targetBits source auxiliary target axis : Nat}
    (sourceIn : source < 2^sourceBits) (inside : axis < targetBits)
    (operation : Gate) (amplitudes : Nat → ℂ) :
    gate operation (sourceBits+axis) amplitudes (carrier sourceBits targetBits source auxiliary target) =
      gate operation axis (fun input => amplitudes (carrier sourceBits targetBits source auxiliary input)) target := by
  let bitRead := packed_target_bit (auxiliary := auxiliary) (target := target) sourceIn inside
  cases operation with
  | z | t => simp only [gate,bitRead]
  | x =>
    simp only [gate,← write_toggle]
    rw [bitRead,write_target sourceIn inside (by omega)]
  | h =>
    have low := write_target (auxiliary := auxiliary) (target := target) sourceIn inside (value := 0) (by decide)
    have high := write_target (auxiliary := auxiliary) (target := target) sourceIn inside (value := 1) (by decide)
    simp only [write,Nat.zero_mul,Nat.add_zero,Nat.one_mul] at low high
    simp only [gate]
    rw [high,low,bitRead]

private theorem controlled (dependencies : List Dependency) (operation : Gate) (axis row : Nat)
    (controls : List Control) (amplitudes : Nat → ℂ) :
    Semantics.RawAction.step dependencies {Raw.gateStep operation axis with controls} amplitudes row =
    if enabled controls row then gate operation axis amplitudes row else amplitudes row := by
  rw [← literal_gate dependencies operation axis row amplitudes]
  cases operation <;> simp [Semantics.RawAction.step,Raw.gateStep,show enabled [] row = true from rfl] <;>
    cases enabled controls row <;> rfl

private theorem phase_use (dependencies : List Dependency) (controls : List Control) (exponent row : Nat)
    (amplitudes : Nat → ℂ) :
    Semantics.RawAction.step dependencies ⟨controls,.monomial [] [0] [exponent]⟩ amplitudes row =
      amplitudes row * (if enabled controls row then Semantics.Finite.phase exponent else 1) := by
  have one : List.range 1 = [0] := by decide
  cases active : enabled controls row <;>
    simp [Semantics.RawAction.step,active,one,gather,scatter,List.zipIdx_nil]

/-- Each literal protected use acts on its chosen target fibre with the same
protected inputs, phase and control polarities as the independent Raw action. -/
theorem literal_use (dependencies : List Dependency) {sourceBits targetBits auxiliaryBits source auxiliary target : Nat}
    (sourceIn : source < 2^sourceBits) (targetIn : target < 2^targetBits)
    (operation : Use) (valid : Raw.usesValid sourceBits auxiliaryBits targetBits [operation] = true)
    (amplitudes : Nat → ℂ) :
    Semantics.RawAction.step dependencies (Raw.physicalUse sourceBits (sourceBits+targetBits) operation) amplitudes
      (carrier sourceBits targetBits source auxiliary target) =
    blockUse source auxiliary operation (fun input (_ : Unit) => amplitudes (carrier sourceBits targetBits source auxiliary input))
      target () := by
  simp only [Raw.usesValid,List.all_cons,List.all_nil,Bool.and_true] at valid
  cases operation with
  | protectedGate location operation =>
    obtain ⟨inside,allowed⟩ := Bool.and_eq_true_iff.mp valid
    have read := packed_protected_bit (auxiliary := auxiliary) sourceIn targetIn location inside
    have diagonal : operation = .z ∨ operation = .t := by simpa only [Bool.or_eq_true,beq_iff_eq] using allowed
    rcases diagonal with rfl | rfl <;> simp [Raw.physicalUse,literal_gate,blockUse,gate,read]
  | targetGate controls axis operation =>
    obtain ⟨targetBound,allowed⟩ := Bool.and_eq_true_iff.mp valid
    have controlEq := packed_controls (auxiliary := auxiliary) sourceIn targetIn controls allowed
    have gateEq := gate_target (target := target) (auxiliary := auxiliary) sourceIn (of_decide_eq_true targetBound)
      operation amplitudes
    simp [Raw.physicalUse,controlled,controlEq,blockUse,gateEq]
  | phase controls operation =>
    have controlEq := packed_controls (auxiliary := auxiliary) sourceIn targetIn controls valid
    simp [Raw.physicalUse,phase_use,controlEq,blockUse,show Raw.phaseExponent operation =
      QleisliKernel.Semantics.Protected.phaseExponent operation from by cases operation <;> rfl]

private theorem blockUse_on_rows {source sourceBits auxiliary auxiliaryBits targetBits : Nat}
    (operation : Use) (valid : Raw.usesValid sourceBits auxiliaryBits targetBits [operation] = true)
    (left right : Nat → ℂ) (equal : Qleisli.RawFiniteRows.OnRows targetBits left right) :
    Qleisli.RawFiniteRows.OnRows targetBits
      (fun row => blockUse source auxiliary operation (fun input (_ : Unit) => left input) row ())
      (fun row => blockUse source auxiliary operation (fun input (_ : Unit) => right input) row ()) := by
  intro row inside
  cases operation with
  | protectedGate location operation => simp only [blockUse,equal row inside]
  | phase controls operation => simp only [blockUse,equal row inside]
  | targetGate controls axis operation =>
    have bounded : axis < targetBits := by
      have shape : (decide (axis < targetBits) && Raw.protectedControlsValid sourceBits auxiliaryBits controls) = true := by
        simpa [Raw.usesValid] using valid
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp shape).1
    have targets : QleisliKernel.Finite.targets (Raw.gateStep operation axis).action = [axis] := by cases operation <;> rfl
    have boundedCircuit : Qleisli.RawFiniteRows.BoundedEvent targetBits (.circuit targetBits [Raw.gateStep operation axis]) targetBits := by
      apply Qleisli.RawFiniteRows.BoundedEvent.circuit
      intro step appears selected present
      obtain rfl := List.mem_singleton.mp appears
      rw [targets,List.mem_singleton] at present
      exact present.symm ▸ bounded
    have stepEqual := boundedCircuit.congr [] left right equal row inside
    change Semantics.RawAction.step [] (Raw.gateStep operation axis) left row =
      Semantics.RawAction.step [] (Raw.gateStep operation axis) right row at stepEqual
    rw [literal_gate,literal_gate] at stepEqual
    simp only [blockUse,stepEqual,equal row inside]

/-- The complete literal sequence of protected uses preserves the same fixed
source and auxiliary labels and acts on the exact same target coefficients. -/
theorem literal_uses (dependencies : List Dependency) {sourceBits targetBits auxiliaryBits source auxiliary target : Nat}
    (sourceIn : source < 2^sourceBits) (targetIn : target < 2^targetBits)
    (uses : List Use) (valid : Raw.usesValid sourceBits auxiliaryBits targetBits uses = true)
    (amplitudes initial : Nat → ℂ)
    (agrees : Qleisli.RawFiniteRows.OnRows targetBits
      (fun input => amplitudes (carrier sourceBits targetBits source auxiliary input)) initial) :
    Semantics.RawAction.circuit dependencies (uses.map (Raw.physicalUse sourceBits (sourceBits+targetBits))) amplitudes
      (carrier sourceBits targetBits source auxiliary target) =
    blocks source auxiliary uses (fun input (_ : Unit) => initial input) target () := by
  induction uses using List.reverseRecOn generalizing target with
  | nil => exact agrees target targetIn
  | append_singleton before operation ih =>
    have checks : Raw.usesValid sourceBits auxiliaryBits targetBits before = true ∧
        Raw.usesValid sourceBits auxiliaryBits targetBits [operation] = true := by
      simpa only [Raw.usesValid,List.all_append,Bool.and_eq_true] using valid
    let prior := Semantics.RawAction.circuit dependencies (before.map (Raw.physicalUse sourceBits (sourceBits+targetBits))) amplitudes
    have equal : Qleisli.RawFiniteRows.OnRows targetBits
        (fun input => prior (carrier sourceBits targetBits source auxiliary input))
        (fun input => blocks source auxiliary before (fun i (_ : Unit) => initial i) input ()) := by
      intro input inRange
      exact ih inRange checks.1
    have last : Semantics.RawAction.circuit dependencies ((before ++ [operation]).map
        (Raw.physicalUse sourceBits (sourceBits+targetBits))) amplitudes =
        Semantics.RawAction.step dependencies (Raw.physicalUse sourceBits (sourceBits+targetBits) operation) prior := by
      simp only [Semantics.RawAction.circuit,prior,List.map_append,List.map_cons,List.map_nil,
        List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [last]
    rw [literal_use dependencies sourceIn targetIn operation checks.2]
    have same := blockUse_on_rows (source := source) (auxiliary := auxiliary) operation checks.2 _ _ equal target targetIn
    dsimp only at same
    rw [same]
    simp only [blocks,List.foldl_append,List.foldl_cons,List.foldl_nil]

#print axioms literal_use
#print axioms literal_uses
end Qleisli.ProtectedComputeAction

/-! The exact row action of the literal reversible table word.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.ProtectedComputeAction
open QleisliKernel
open QleisliKernel.Semantics.Finite

private theorem full_scatter {bits output input : Nat} (accepted : output < 2^bits) (valid : input < 2^bits) :
    scatter output (List.range bits) input = input := by
  have within := Qleisli.Finite.Pull.scatter_bound output bits input (List.range bits) accepted
    (fun _ present => List.mem_range.mp present)
  have read := Qleisli.RuntimeFiniteTargetScatter.gather_scatter output input (List.range bits)
    List.nodup_range (by simpa only [List.length_range] using valid)
  rwa [Raw.Sector.gather_range,Nat.mod_eq_of_lt within] at read

/-- The actual table monomial XORs the high auxiliary bits while retaining
all low data coordinates and the original coefficient. -/
theorem literal_compute (dependencies : List Dependency) {sourceBits dataBits auxiliaryBits : Nat}
    (within : sourceBits ≤ dataBits) (table : List Nat)
    (bounded : ∀ source < 2^sourceBits, table[source]?.getD 0 < 2^auxiliaryBits)
    (amplitudes : Nat → ℂ) {output : Nat} (outputIn : output < 2^(dataBits+auxiliaryBits)) :
    Semantics.RawAction.step dependencies (Raw.computeStep sourceBits dataBits auxiliaryBits table) amplitudes output =
      amplitudes (output ^^^ (table[output % 2^sourceBits]?.getD 0 * 2^dataBits)) := by
  let width := dataBits+auxiliaryBits
  let mask := fun label => table[label % 2^sourceBits]?.getD 0 * 2^dataBits
  let flip := fun label => label ^^^ mask label
  have maskIn (label : Nat) : mask label < 2^width := by
    have entry := bounded _ (Nat.mod_lt label (Nat.two_pow_pos _))
    have scaled := Nat.mul_lt_mul_of_pos_right entry (Nat.two_pow_pos dataBits)
    simpa only [mask,width,Nat.pow_add,Nat.mul_comm (2^dataBits) (2^auxiliaryBits)] using scaled
  have flipIn {label : Nat} (inside : label < 2^width) : flip label < 2^width :=
    Nat.xor_lt_two_pow inside (maskIn label)
  have stable (label : Nat) : flip label % 2^sourceBits = label % 2^sourceBits := by
    have factor : 2^sourceBits ∣ 2^dataBits := Nat.pow_dvd_pow 2 within
    have divisible : 2^sourceBits ∣ mask label :=
      Nat.dvd_trans factor (Nat.dvd_mul_left _ _)
    change (label ^^^ mask label) % 2^sourceBits = _
    rw [Nat.xor_mod_two_pow,Nat.mod_eq_zero_of_dvd divisible,Nat.xor_zero]
  have twice (label : Nat) : flip (flip label) = label := by
    change (label ^^^ mask label) ^^^
      (table[flip label % 2^sourceBits]?.getD 0 * 2^dataBits) = label
    rw [stable]
    change (label ^^^ mask label) ^^^ mask label = label
    rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  have chosen (input : Nat) : flip input = output ↔ flip output = input := by
    constructor
    · intro same
      rw [← same,twice]
    · intro same
      rw [← same,twice]
  have project : gather output (List.range width) = output := by
    rw [Raw.Sector.gather_range,Nat.mod_eq_of_lt outputIn]
  simp only [Semantics.RawAction.step, Raw.computeStep, QleisliKernel.Semantics.Raw.computeStep,
    enabled,List.all_nil,Bool.not_true,Bool.false_eq_true,if_false,List.length_map,List.length_range]
  change ((List.range (2^width)).map fun input =>
      if ((List.range (2^width)).map flip)[input]? == some (gather output (List.range width)) then
        amplitudes (scatter output (List.range width) input) *
          Qleisli.Semantics.Finite.phase ((List.replicate (2^width) 0)[input]?.getD 0)
      else 0).sum = amplitudes (flip output)
  rw [project]
  calc
    _ = ((List.range (2^width)).map fun input => if flip output = input then amplitudes input else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro input member
      have inputIn : input < 2^width := List.mem_range.mp member
      have scatterFull := full_scatter (bits := width) outputIn inputIn
      simp only [List.getElem?_map,List.getElem?_range inputIn,Option.map_some,
        beq_iff_eq,Option.some.injEq,chosen,scatterFull]
      have phaseRead : (List.replicate (2^width) 0)[input]? = some 0 := by simp [inputIn]
      simp [phaseRead,Qleisli.Semantics.Finite.phase]
    _ = _ := Qleisli.Exact.range_delta_sum _ _ _ (flipIn outputIn)

private theorem xor_auxiliary (width data auxiliary toggle : Nat) (inside : data < 2^width) :
    FiniteRestriction.pack width data auxiliary ^^^ (toggle * 2^width) =
      FiniteRestriction.pack width data (auxiliary ^^^ toggle) := by
  apply Nat.eq_of_testBit_eq
  intro axis
  simp only [Nat.testBit_xor,Nat.testBit_mul_two_pow,FiniteRestriction.pack,
    Nat.add_comm data, Nat.testBit_two_pow_mul_add _ inside]
  by_cases low : axis < width
  · simp [low,Nat.not_le_of_lt low]
  · simp [low,Nat.le_of_not_gt low]

/-- The same executable compute step on separate data and auxiliary
coordinates. The source address uses the low source bits of the data. -/
theorem literal_compute_carrier (dependencies : List Dependency) {sourceBits dataBits auxiliaryBits : Nat}
    (within : sourceBits ≤ dataBits) (table : List Nat)
    (bounded : ∀ source < 2^sourceBits, table[source]?.getD 0 < 2^auxiliaryBits)
    (amplitudes : Nat → ℂ) {data auxiliary : Nat}
    (dataIn : data < 2^dataBits) (auxiliaryIn : auxiliary < 2^auxiliaryBits) :
    Semantics.RawAction.step dependencies (Raw.computeStep sourceBits dataBits auxiliaryBits table) amplitudes
      (FiniteRestriction.pack dataBits data auxiliary) =
    amplitudes (FiniteRestriction.pack dataBits data
      (auxiliary ^^^ table[data % 2^sourceBits]?.getD 0)) := by
  have next : FiniteRestriction.pack dataBits data auxiliary < 2^dataBits * (auxiliary+1) := by
    unfold FiniteRestriction.pack
    rw [Nat.mul_succ]
    omega
  have packed : FiniteRestriction.pack dataBits data auxiliary < 2^(dataBits+auxiliaryBits) := by
    rw [Nat.pow_add]
    exact Nat.lt_of_lt_of_le next (Nat.mul_le_mul_left _ (by omega))
  have source : FiniteRestriction.pack dataBits data auxiliary % 2^sourceBits = data % 2^sourceBits := by
    let width : 2^sourceBits ∣ 2^dataBits := Nat.pow_dvd_pow 2 within
    calc
      _ = (FiniteRestriction.pack dataBits data auxiliary % 2^dataBits) % 2^sourceBits :=
        (Nat.mod_mod_of_dvd _ width).symm
      _ = _ := by rw [FiniteRestriction.pack_low _ _ _ dataIn]
  rw [literal_compute dependencies within table bounded amplitudes packed,source,xor_auxiliary _ _ _ _ dataIn]

/-- The original executable table bound is sufficient for each actually
selected source address, including a zero-width auxiliary register. -/
theorem checked_table_entries {sourceBits auxiliaryBits : Nat} {table : List Nat}
    (valid : Raw.tableValid sourceBits auxiliaryBits table false = true) :
    ∀ source < 2^sourceBits, table[source]?.getD 0 < 2^auxiliaryBits := by
  have tableChecks : table.length = 2^sourceBits ∧ table.all (· < 2^auxiliaryBits) = true := by
    simpa only [Raw.tableValid,Bool.not_false,Bool.true_or,Bool.and_true,Bool.and_eq_true,beq_iff_eq] using valid
  intro source present
  have inside : source < table.length := tableChecks.1.symm ▸ present
  rw [List.getElem?_eq_getElem inside,Option.getD_some]
  exact of_decide_eq_true (List.all_eq_true.mp tableChecks.2 _ (List.getElem_mem inside))

#print axioms checked_table_entries
#print axioms literal_compute
#print axioms literal_compute_carrier
end Qleisli.ProtectedComputeAction

/-! The literal protected-table word returns all of its original auxiliary
coordinates to zero, with the same logical coefficient action as Raw.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.ProtectedComputeAction
open QleisliKernel
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Use)
open QleisliKernel.FiniteRestriction (pack pack_low)
open Qleisli.Semantics.Protected (blocks)

/-- The local block selected by the original source coordinate. -/
noncomputable def logical (sourceBits : Nat) (table : List Nat) (uses : List Use)
    (data : Nat → ℂ) (row : Nat) : ℂ :=
  let source := row % 2^sourceBits
  blocks source (table[source]?.getD 0) uses
    (fun input (_ : Unit) => data (pack sourceBits source input)) (row / 2^sourceBits) ()

/-- The independently read protected event uses the same local action on its
actual ordered axes without a physical auxiliary coordinate at its boundary. -/
theorem raw_event_embed (dependencies : List Dependency) {bits sourceBits auxiliaryBits : Nat}
    (axes : List Nat) (table : List Nat) (uses : List Use)
    (valid : Raw.usesValid sourceBits auxiliaryBits (axes.length-sourceBits) uses = true)
    (amplitudes : Nat → ℂ) :
    Semantics.RawAction.event dependencies (.protectedComputed bits axes sourceBits auxiliaryBits table uses) amplitudes =
      Semantics.RawAction.embed axes (logical sourceBits table uses) amplitudes := by
  funext row
  simp only [Semantics.RawAction.event,Semantics.RawAction.embed]
  rw [Semantics.Protected.clean_factorization _ uses (Qleisli.Raw.uses_valid_diagonal _ _ _ _ valid)]
  simp [Semantics.Protected.zero,Semantics.Protected.logical,logical,pack,Nat.mul_comm]

private theorem packed_small {width data auxiliary : Nat} (dataIn : data < 2^width) :
    pack width data auxiliary < 2^width ↔ auxiliary = 0 := by
  constructor
  · intro below
    by_contra dirty
    have high := Nat.le_mul_of_pos_right (2^width) (Nat.pos_of_ne_zero dirty)
    unfold pack at below
    omega
  · rintro rfl
    simpa [pack] using dataIn

private theorem packed_clean (dependencies : List Dependency)
    {sourceBits targetBits auxiliaryBits source auxiliary target : Nat}
    (sourceIn : source < 2^sourceBits) (targetIn : target < 2^targetBits) (auxiliaryIn : auxiliary < 2^auxiliaryBits)
    (table : List Nat) (tableValid : Raw.tableValid sourceBits auxiliaryBits table false = true)
    (uses : List Use) (usesValid : Raw.usesValid sourceBits auxiliaryBits targetBits uses = true)
    (data : Nat → ℂ) :
    let dataBits := sourceBits+targetBits
    let compute := Raw.computeStep sourceBits dataBits auxiliaryBits table
    Semantics.RawAction.circuit dependencies ([compute] ++ uses.map (Raw.physicalUse sourceBits dataBits) ++ [compute])
      (Semantics.RawAction.event [] (.init0 dataBits) data) (carrier sourceBits targetBits source auxiliary target) =
    if auxiliary = 0 then blocks source (table[source]?.getD 0) uses
      (fun input (_ : Unit) => data (pack sourceBits source input)) target () else 0 := by
  let dataBits := sourceBits+targetBits
  let compute := Raw.computeStep sourceBits dataBits auxiliaryBits table
  let initial := Semantics.RawAction.event [] (.init0 dataBits) data
  let afterCompute := Semantics.RawAction.step dependencies compute initial
  let afterUse := Semantics.RawAction.circuit dependencies (uses.map (Raw.physicalUse sourceBits dataBits)) afterCompute
  let chosen := table[source]?.getD 0
  let shifted := auxiliary ^^^ chosen
  let bounded := checked_table_entries tableValid
  have shiftedIn : shifted < 2^auxiliaryBits := Nat.xor_lt_two_pow auxiliaryIn (bounded _ sourceIn)
  have first : Semantics.RawAction.circuit dependencies ([compute] ++ uses.map (Raw.physicalUse sourceBits dataBits) ++ [compute]) initial =
      Semantics.RawAction.step dependencies compute afterUse := by
    simp only [Semantics.RawAction.circuit,afterUse,afterCompute,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change Semantics.RawAction.circuit dependencies ([compute] ++ uses.map (Raw.physicalUse sourceBits dataBits) ++ [compute]) initial _ = _
  rw [first]
  have final := literal_compute_carrier dependencies (Nat.le_add_right sourceBits targetBits) table bounded afterUse
    (data := pack sourceBits source target) (auxiliary := auxiliary) (pack_in sourceIn targetIn) auxiliaryIn
  rw [pack_low _ _ _ sourceIn] at final
  change Semantics.RawAction.step dependencies compute afterUse (carrier sourceBits targetBits source auxiliary target) =
    afterUse (carrier sourceBits targetBits source shifted target) at final
  rw [final]
  have fibre : Qleisli.RawFiniteRows.OnRows targetBits
      (fun input => afterCompute (carrier sourceBits targetBits source shifted input))
      (fun input => if auxiliary = 0 then data (pack sourceBits source input) else 0) := by
    intro input inside
    have one := literal_compute_carrier dependencies (Nat.le_add_right sourceBits targetBits) table bounded initial
      (data := pack sourceBits source input) (auxiliary := shifted) (pack_in sourceIn inside) shiftedIn
    rw [pack_low _ _ _ sourceIn] at one
    have undo : shifted ^^^ table[source]?.getD 0 = auxiliary := by simp [shifted,chosen]
    rw [undo] at one
    change afterCompute (carrier sourceBits targetBits source shifted input) =
      initial (pack dataBits (pack sourceBits source input) auxiliary) at one
    dsimp only
    rw [one]
    have reset := packed_small (width := dataBits) (auxiliary := auxiliary) (pack_in sourceIn inside)
    simp only [initial,Semantics.RawAction.event,reset]
    by_cases zero : auxiliary = 0 <;> simp [zero,pack]
  have used := literal_uses dependencies (auxiliary := shifted) sourceIn targetIn uses usesValid afterCompute _ fibre
  change afterUse (carrier sourceBits targetBits source shifted target) = _ at used
  rw [used]
  by_cases zero : auxiliary = 0
  · simp [shifted,chosen,zero]
  · simp [zero,Semantics.Protected.blocks_zero]

/-- The actual compute/use/uncompute tape has the original local action and
returns its entire private auxiliary register to zero on every finite row. -/
theorem literal_clean (dependencies : List Dependency) {sourceBits dataBits auxiliaryBits : Nat}
    (width : sourceBits ≤ dataBits) (table : List Nat) (tableValid : Raw.tableValid sourceBits auxiliaryBits table false = true)
    (uses : List Use) (usesValid : Raw.usesValid sourceBits auxiliaryBits (dataBits-sourceBits) uses = true)
    (data : Nat → ℂ) (row : Nat) (inside : row < 2^(dataBits+auxiliaryBits)) :
    let compute := Raw.computeStep sourceBits dataBits auxiliaryBits table
    Semantics.RawAction.circuit dependencies ([compute] ++ uses.map (Raw.physicalUse sourceBits dataBits) ++ [compute])
      (Semantics.RawAction.event [] (.init0 dataBits) data) row =
    Semantics.RawAction.event [] (.init0 dataBits) (logical sourceBits table uses data) row := by
  let output := row % 2^dataBits
  let auxiliary := row / 2^dataBits
  let source := output % 2^sourceBits
  let target := output / 2^sourceBits
  have total : sourceBits+(dataBits-sourceBits) = dataBits := Nat.add_sub_of_le width
  have outputIn : output < 2^dataBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have auxIn : auxiliary < 2^auxiliaryBits := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos dataBits)).mpr
    simpa [Nat.pow_add,Nat.mul_comm] using inside
  have sourceIn : source < 2^sourceBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have targetIn : target < 2^(dataBits-sourceBits) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos sourceBits)).mpr
    rw [Nat.mul_comm,← Nat.pow_add,total]
    exact outputIn
  have inner : pack sourceBits source target = output := Nat.mod_add_div output (2^sourceBits)
  have outer : pack dataBits output auxiliary = row := Nat.mod_add_div row (2^dataBits)
  have same := packed_clean dependencies sourceIn targetIn auxIn table tableValid uses usesValid data
  simp only [carrier,total,inner,outer] at same
  dsimp only
  rw [same]
  conv => rhs; rw [← outer]
  simp only [Semantics.RawAction.event,packed_small outputIn]
  split <;> rename_i zero
  · simp [zero,pack,logical,source,target]
  · rfl

#print axioms raw_event_embed
#print axioms literal_clean
end Qleisli.ProtectedComputeAction
