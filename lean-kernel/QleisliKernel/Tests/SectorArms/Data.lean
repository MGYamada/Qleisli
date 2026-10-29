import QleisliKernel.Qirf.SectorArms
import QleisliKernel.Tests.NominalSector

/-! Small original-arm/control regression stages. Exact original definitions
and theorem bodies are retained in separately compiled modules to bound kernel
reduction memory. No proof/native policy or semantic oracle is weakened.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SectorArms
open Semantics.Exact Semantics.Finite Semantics.CarrierInterface
open QleisliKernel.Tests.FiniteRestriction

def implementation (phase : Nat) : Semantics.Observation.Program := Semantics.Ownership.pureProgram {
  inputs := [⟨10,[],0⟩]
  operations := [.applyUnitary 10 11 [⟨[],.monomial [] [0] [phase]⟩]]
  outputs := [11]
  effect := .unitary
}

def controlled (phase : Nat) (polarity : Bool := true) : Semantics.Observation.Program :=
  Semantics.Ownership.pureProgram {
    inputs := [⟨10,[7],1⟩,⟨11,[],0⟩]
    operations := [.join 10 11 12,.applyUnitary 12 13 [⟨[⟨0,polarity⟩],.monomial [] [0] [phase]⟩],
      .split 13 14 15 1]
    outputs := [14,15]
    effect := .unitary
  }

def artifact (body : Semantics.Observation.Program := implementation 2)
    (control : Semantics.Observation.Program := controlled 2) : Qirf.Artifact :=
  ⟨#[body,control],#[],#[],0,none⟩
def reference : Qirf.SectorArm.Reference := ⟨0,[.unit],.unitary,0,1⟩
def one := scalar Scalar.one
def outcome (data : Qirf.Artifact := artifact) (ref : Qirf.SectorArm.Reference := reference) :
    Except Finite.Error (List Matrix) :=
  ((Qirf.SectorArm.read data [] [.unit] 0 one one ref).run 1000000).1.map fun checked => [checked.logical]

def two : Qirf.Artifact :=
  ⟨#[implementation 0,controlled 0,implementation 2,controlled 2],#[],#[],0,none⟩
def zeroRef : Qirf.SectorArm.Reference := ⟨0,[.unit],.unitary,0,1⟩
def oneRef : Qirf.SectorArm.Reference := ⟨1,[.unit],.unitary,2,3⟩
def allOutcome (refs : List Qirf.SectorArm.Reference) (count : Nat := 2) :
    Except Finite.Error (List Matrix) :=
  ((Qirf.SectorArms.readAll two [] [.unit] 0 one one count refs).run 1000000).1.map fun arms =>
    arms.map (·.checked.logical)

def cycleBody : Semantics.Observation.Program := Semantics.Ownership.pureProgram {
  inputs := [⟨10,[7,91],2⟩]
  operations := [.applyUnitary 10 11 [⟨[],.monomial [0,1] [1,2,0,3] [0,0,0,0]⟩]]
  outputs := [11]
  effect := .unitary
}
def cycleControl : Semantics.Observation.Program := Semantics.Ownership.pureProgram {
  inputs := [⟨10,[3],1⟩,⟨11,[7,91],2⟩]
  operations := [.join 10 11 12,.applyUnitary 12 13
    [⟨[⟨0,true⟩],.monomial [1,2] [1,2,0,3] [0,0,0,0]⟩],.split 13 14 15 1]
  outputs := [14,15]
  effect := .unitary
}
def cycleRef : Qirf.SectorArm.Reference := ⟨0,NominalSector.tri,.unitary,0,1⟩
def cycleOutcome (data : Qirf.Artifact := artifact cycleBody cycleControl)
    (ref : Qirf.SectorArm.Reference := cycleRef) : Except Finite.Error (List Matrix) :=
  ((Qirf.SectorArm.read data [] NominalSector.tri 2 NominalSector.code NominalSector.code ref).run 1000000).1.map
    fun checked => [checked.logical]

def interface : Interface := ⟨[⟨⟨10,[7],1⟩,[.bit]⟩,⟨⟨11,[],0⟩,[.unit]⟩],
  [⟨⟨14,[7],1⟩,[.bit]⟩,⟨⟨15,[],0⟩,[.unit]⟩],.unitary⟩
def whole (main : Semantics.Observation.Program := controlled 2)
    (body : Semantics.Observation.Program := implementation 2)
    (control : Semantics.Observation.Program := controlled 2) : Qirf.Artifact :=
  ⟨#[main,implementation 0,controlled 0,body,control],#[],#[],0,none⟩
def references : List Qirf.SectorArm.Reference :=
  [⟨1,[.unit],.unitary,3,4⟩,⟨0,[.unit],.unitary,1,2⟩]
def wholeOutcome (data : Qirf.Artifact := whole) : Except Finite.Error (List Matrix) :=
  ((Qirf.SectorArms.check data #[1,2,3,4,0] interface interface references).run 1000000).1.map (·.logical)

def unrelated : Qirf.Artifact := {whole with programs := whole.programs.push (implementation 0)}

def unusedSource : Qirf.Artifact := {whole with sources := #[("unrelated","pub fn unused(){}")]}

end QleisliKernel.Tests.SectorArms
