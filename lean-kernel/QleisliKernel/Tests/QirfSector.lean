import QleisliKernel.Qirf.Sector
import QleisliKernel.Tests.RawSector

/-! Retained small fresh-QIRF regression theorems.
At most two physical bits. Original source-arm/type binding, native transport
and nominal execution are not established by these bounded tests.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QirfSector
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Observation QleisliKernel.Qirf
open QleisliKernel.Tests.FiniteRestriction

def original : Program := Semantics.Ownership.pureProgram RawSector.subject
def artifact (program : Program) : QleisliKernel.Qirf.Artifact := ⟨#[program],#[],#[],0,none⟩

def outcomeWith (selector target : Basis) (input : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (required : List Matrix) : Except QleisliKernel.Finite.Error (List Matrix) :=
  ((QleisliKernel.Qirf.Sector.check input order selector target required).run 1000000).1.map
    (·.sectors.sectors)

def outcome (input : QleisliKernel.Qirf.Artifact) (order : Array Nat) (required : List Matrix) :=
  outcomeWith bitBasis bitBasis input order required

theorem case1 : (outcome (artifact original) #[0] [hadamard,flip] == .ok [hadamard,flip]) = true := by
  decide +kernel

theorem case2 : (outcome (artifact original) #[0] [flip,hadamard] == .error .equation) = true := by
  decide +kernel

theorem case3 : (outcome (artifact {original with outputs := [15,14]}) #[0]
    [hadamard,flip] == .error .request) = true := by decide +kernel

-- Projection itself rejects every non-pure instruction, without choosing an
-- arm or dropping a hidden history. The generic inverse-embedding proof is
-- separate from these concrete constructor checks.
theorem case4 : (QleisliKernel.Qirf.Sector.project {original with operations := [.measure 10 100]} ==
    none) = true := by decide +kernel

theorem case5 : (QleisliKernel.Qirf.Sector.project {original with operations := [.reset 10 12 92]} ==
    none) = true := by decide +kernel

theorem case6 : (QleisliKernel.Qirf.Sector.project {original with operations := [.discard 10]} ==
    none) = true := by decide +kernel

theorem case7 : (QleisliKernel.Qirf.Sector.project {original with operations := [.branch 0 [] [] [] []]} ==
    none) = true := by decide +kernel

theorem case8 : (QleisliKernel.Qirf.Sector.project {original with operations := [.constant false 100]} ==
    none) = true := by decide +kernel

theorem case9 : (QleisliKernel.Qirf.Sector.project {original with effect := .iso} ==
    none) = true := by decide +kernel

def gate (kind : Semantics.Raw.Gate) : Program :=
  ⟨[⟨0,[0],1⟩],[],[.pure (.gate kind 0 1)],[1],[],.unitary⟩

def caller (adjoint : Bool := false) : Program :=
  Semantics.Ownership.pureProgram {RawSector.subject with operations := [
    .join 10 11 12,
    .applyUnitary 12 13 [⟨[⟨0,true⟩],.contract [1] 0 adjoint⟩],
    .split 13 14 15 1]}

def xArtifact : QleisliKernel.Qirf.Artifact :=
  ⟨#[caller,gate .x,gate .x],#[⟨bitBasis,1,.circuit 2,"actual","required",[]⟩],#[],0,none⟩

theorem case10 : (outcome xArtifact #[1,2,3,0] [identity,flip] == .ok [identity,flip]) = true := by
  decide +kernel

-- A new original implementation cannot reuse the former X dependency matrix.
theorem case11 : (outcome {xArtifact with programs := #[caller,gate .h,gate .x]}
    #[1,2,3,0] [identity,flip] == .error .equation) = true := by decide +kernel

theorem case12 : (outcome {xArtifact with entries := #[]} #[1,2,0]
    [identity,flip] == .error .invalid) = true := by decide +kernel

theorem case13 : (outcome xArtifact #[0,1,2,3] [identity,flip] ==
    .error .invalid) = true := by decide +kernel

def sBody : Program := ⟨[⟨0,[0],1⟩],[],[
  .pure (.gate .t 0 1),.pure (.gate .t 1 2)],[2],[],.unitary⟩
def sMatrix : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,imaginaryOne]⟩
def sArtifact : QleisliKernel.Qirf.Artifact :=
  ⟨#[caller,sBody],#[⟨bitBasis,1,.phase8 [0,2],"actual","required",[]⟩],#[],0,none⟩

theorem case14 : (outcome sArtifact #[1,2,0] [identity,sMatrix] == .ok [identity,sMatrix]) = true := by
  decide +kernel

theorem case15 : (outcome {sArtifact with programs := #[caller true,sBody]} #[1,2,0]
    [identity,sMatrix] == .error .equation) = true := by decide +kernel

theorem case16 : (outcome {sArtifact with entries := #[⟨bitBasis,1,.phase8 [0,1],"actual","required",[]⟩]}
    #[1,2,0] [identity,sMatrix] == .error .equation) = true := by decide +kernel

-- These complete original roots restore the physical port count, but their
-- actual measurement/reset/discard still contradicts the declared pure effect.
def hidden (operation : Op) : Program := {original with
  operations := [operation,.pure (.init0 12 92)]
  outputs := [12,11]}

theorem case17 : (outcome (artifact (hidden (.measure 10 100))) #[0]
    [identity,identity] == .error .invalid) = true := by decide +kernel

theorem case18 : (outcome (artifact {original with operations := [.reset 10 12 92],outputs := [12,11]})
    #[0] [identity,identity] == .error .invalid) = true := by decide +kernel

theorem case19 : (outcome (artifact (hidden (.discard 10))) #[0]
    [identity,identity] == .error .invalid) = true := by decide +kernel

theorem case20 : (QleisliKernel.Qirf.Sector.project original == some RawSector.subject) = true := by
  decide +kernel

theorem case21 : (outcomeWith unitBasis unitBasis
    (artifact (Semantics.Ownership.pureProgram RawSector.zeroOwners)) #[0]
    [scalar Scalar.one] == .ok [scalar Scalar.one]) = true := by decide +kernel

theorem case22 : (outcome {artifact original with sources := #[("unrelated","pub fn unused(){}")]}
    #[0] [hadamard,flip] == .error .invalid) = true := by
  have size : "pub fn unused(){}".utf8ByteSize ≤ 1048576 := by decide +kernel
  have budget : (get : QleisliKernel.Finite.WorkM Nat).run 1000000 = (.ok 1000000,1000000) := rfl
  have guarded (condition : Bool) (error : QleisliKernel.Finite.Error) (work : Nat) :
      (QleisliKernel.Finite.guard condition error).run work =
        (if condition then (.ok (),work) else (.error error,work)) := by
    cases condition <;> rfl
  have chargeZero (work : Nat) :
      (QleisliKernel.Finite.exactWork (QleisliKernel.Exact.charge 0)).run work = (.ok (),work) := rfl
  cases valid : QleisliKernel.Qirf.sourceValid ("unrelated","pub fn unused(){}") <;>
    simp [outcome,outcomeWith,QleisliKernel.Qirf.Sector.check,
      Validity.checkRoot,Validity.checkRootWithSources,Validity.checkRootFromRoots,
      QleisliKernel.Qirf.checkGraphReceiptsFromRoots,
      QleisliKernel.Finite.bind_run,QleisliKernel.Qirf.sourceUses,artifact,
      guarded,budget,chargeZero,valid,size] <;> decide +kernel

theorem case23 : (((QleisliKernel.Qirf.Sector.check (artifact original) #[0] bitBasis bitBasis
    [hadamard,flip]).run 0).1.map (·.sectors.sectors) == .error (.arithmetic .workLimit)) = true := by
  decide +kernel

theorem case24 : (outcome (artifact (Semantics.Ownership.pureProgram {RawSector.subject with operations := [
    .join 10 11 12,.applyUnitary 12 13 [⟨[],.hadamard 0⟩],.split 13 14 15 1]}))
    #[0] [hadamard,hadamard] == .error .invalid) = true := by decide +kernel

end QleisliKernel.Tests.QirfSector
