import QleisliKernel.Semantics.Protected
import Qleisli.Semantics.Finite
import Qleisli.Semantics.ProtectedMatrix

/-! Independent pure raw complex denotation. Original interfaces/actions are
read by RawTrace, and each event has literal coefficients or a complete literal
circuit trace. Clean scopes retain both their original physical body and their
requested logical action. No acceptance, arithmetic, budgets or transport is
imported here.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.Raw
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw Qleisli.Semantics.Exact

def BasisColumn (bits column : Nat) : List Scalar :=
  (List.range (2^bits)).map fun row => if row == column then Scalar.one else Scalar.zero

/-- Complete literal complex evolution of every original input basis vector,
including phase, control polarity, local axes and ordered dependency actions. -/
def CircuitMeaning (dependencies : List Dependency) (bits : Nat) (steps : List Step) (actual : Matrix) : Prop :=
  ∃ columns, List.Forall₂ (fun column values => Finite.Trace dependencies steps
      (BasisColumn bits column) values) (List.range (2^bits)) columns ∧
    actual = ⟨2^bits,2^bits,(List.range (2^bits * 2^bits)).map fun index =>
      ((columns[index % 2^bits]?).getD [])[index / 2^bits]?.getD Scalar.zero⟩

noncomputable def MapMeaning (inputBits outputBits : Nat) (labels : List Nat) (actual : Matrix) : Prop :=
  actual.rows = 2^outputBits ∧ actual.cols = 2^inputBits ∧
    ∀ row col, row < actual.rows → col < actual.cols →
      entry actual row col = if labels[col]? == some row then 1 else 0

noncomputable def Embedded (bits : Nat) (axes : List Nat) (logical actual : Matrix) : Prop :=
  actual.rows = 2^bits ∧ actual.cols = 2^bits ∧
    ∀ row col, row < actual.rows → col < actual.cols →
      entry actual row col = if scatter col axes (gather row axes) == row then
        entry logical (gather row axes) (gather col axes) else 0

/-- Exact return of every physical amplitude to the zero-auxiliary image. The
physical circuit is the original compute/use/inverse-compute, not a claimed
logical replacement or an equality only after discarding dirty coordinates. -/
noncomputable def CleanMeaning (dependencies : List Dependency)
    (sourceBits dataBits ancillaBits : Nat) (function : List Nat)
    (uses logicalSteps : List Step) (logical : Matrix) : Prop :=
  CircuitMeaning dependencies dataBits logicalSteps logical ∧
  ∃ encoding physical,
    MapMeaning dataBits (dataBits+ancillaBits) (List.range (2^dataBits)) encoding ∧
    CircuitMeaning dependencies (dataBits+ancillaBits)
      ([computeStep sourceBits dataBits ancillaBits function] ++ uses ++
        [computeStep sourceBits dataBits ancillaBits function]) physical ∧
    Finite.Encoded physical ⟨⟨registerBasis dataBits,registerBasis (dataBits+ancillaBits),encoding⟩,
      ⟨registerBasis dataBits,registerBasis (dataBits+ancillaBits),encoding⟩,logical⟩

noncomputable def EventMeaning (dependencies : List Dependency) (event : Event) (actual : Matrix) : Prop :=
  match event with
  | .circuit bits steps => CircuitMeaning dependencies bits steps actual
  | .init0 bits => MapMeaning bits (bits+1) (List.range (2^bits)) actual
  | .liftBasis before after inputAxes outputAxes table =>
    MapMeaning before after ((List.range (2^before)).map fun label =>
      scatter label outputAxes (table[gather label inputAxes]?.getD 0)) actual
  | .reorder bits axes => MapMeaning bits bits ((List.range (2^bits)).map fun label => gather label axes) actual
  | .computed bits axes sourceBits ancillaBits function uses logicalSteps =>
    ∃ logical, CleanMeaning dependencies sourceBits axes.length ancillaBits function uses logicalSteps logical ∧
      Embedded bits axes logical actual
  | .protectedComputed bits axes sourceBits ancillaBits function uses =>
    ∃ logical, (CleanMeaning dependencies sourceBits axes.length ancillaBits function
      (uses.map (QleisliKernel.Semantics.Protected.physical sourceBits axes.length))
      (uses.flatMap (QleisliKernel.Semantics.Protected.logical sourceBits function)) logical ∨
      ProtectedMatrix.Meaning sourceBits axes.length function uses logical) ∧
      Embedded bits axes logical actual

noncomputable def Composition (localMap input output : Matrix) : Prop :=
  localMap.cols = input.rows ∧ output.rows = localMap.rows ∧ output.cols = input.cols ∧
    ∀ row col, row < localMap.rows → col < input.cols →
      entry output row col = ((List.range localMap.cols).map
        (fun index => entry localMap row index * entry input index col)).sum

inductive EventsMeaning (dependencies : List Dependency) : List Event → Matrix → Matrix → Prop
  | nil (input) : EventsMeaning dependencies [] input input
  | cons (event events input next output localMap)
      (localMeaning : EventMeaning dependencies event localMap)
      (composed : Composition localMap input next)
      (rest : EventsMeaning dependencies events next output) :
      EventsMeaning dependencies (event :: events) input output

noncomputable def IdentityMeaning (bits : Nat) (actual : Matrix) : Prop :=
  actual.rows = 2^bits ∧ actual.cols = 2^bits ∧
    ∀ row col, row < actual.rows → col < actual.cols →
      entry actual row col = if row = col then 1 else 0

/-- Denotation of the complete original raw program. This relation has no
checker-success premise and contains no producer-supplied extracted trace. -/
noncomputable def ProgramMeaning (dependencies : List Dependency) (program : Program) (actual : Matrix) : Prop :=
  ∃ trace initial, QleisliKernel.Semantics.RawTrace.run program = some trace ∧
    IdentityMeaning trace.inputBits initial ∧ EventsMeaning dependencies trace.events initial actual

end Qleisli.Semantics.Raw
