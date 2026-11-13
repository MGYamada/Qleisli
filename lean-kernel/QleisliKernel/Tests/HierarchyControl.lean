import QleisliKernel.Hierarchical.ControlAccess

/-! Exact ordered hierarchy sector regressions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.HierarchyControl

open QleisliKernel.Hierarchical Artifact ControlAccess
open QleisliKernel.Semantics.Exact

private def two : Side := ⟨#[⟨10,#[.bit],#[4]⟩,⟨11,#[.bit],#[7]⟩],#[]⟩
private def first : Side := ⟨#[⟨10,#[.bit],#[4]⟩],#[]⟩
private def one : Side := ⟨#[⟨11,#[.bit],#[7]⟩],#[]⟩
private def zero : Side := ⟨#[⟨12,#[.bits 0],#[]⟩],#[]⟩
private def three : Side := NodeTyping.append two zero

private def phaseThenControl : Array Definition := #[
  ⟨⟨one,one⟩,.unitary,.dyadicPhase 11 1 3⟩,
  ⟨⟨two,two⟩,.unitary,.control 0 true⟩,
  ⟨⟨two,two⟩,.unitary,.control 0 false⟩,
  ⟨⟨two,two⟩,.unitary,.rewire ⟨#[1,0],#[1,0],#[]⟩⟩,
  ⟨⟨two,two⟩,.unitary,.call 1 ⟨#[1,0],#[1,0],#[]⟩ ⟨#[1,0],#[1,0],#[]⟩⟩,
  ⟨⟨two,two⟩,.unitary,.sequence #[1,3]⟩,
  ⟨⟨zero,zero⟩,.unitary,.rewire ⟨#[0],#[],#[]⟩⟩,
  ⟨⟨three,three⟩,.unitary,.tensor 1 6⟩,
  ⟨⟨two,two⟩,.unitary,.inverse 1⟩,
  ⟨⟨two,two⟩,.unitary,.sequence #[1,8]⟩,
  ⟨⟨two,two⟩,.unitary,.repeatOp 2 1⟩,
  ⟨⟨two,two⟩,.unitary,.repeatOp 0 1⟩,
  ⟨⟨one,one⟩,.unitary,.dyadicPhase 11 2 4⟩,
  ⟨⟨two,two⟩,.unitary,.control 12 true⟩,
  ⟨⟨one,one⟩,.unitary,.dyadicPhase 11 1 4⟩,
  ⟨⟨two,two⟩,.unitary,.control 14 true⟩,
  ⟨⟨first,first⟩,.unitary,.rewire ⟨#[0],#[0],#[]⟩⟩,
  ⟨⟨two,two⟩,.unitary,.tensor 16 0⟩,
  ⟨⟨two,two⟩,.unitary,.call 17 ⟨#[1,0],#[1,0],#[]⟩ ⟨#[1,0],#[1,0],#[]⟩⟩
]

private def artifact : Artifact :=
  ⟨phaseThenControl,#[],#[],#[],⟨1,0⟩⟩

#guard artifact.definitions.all (NodeTyping.conditions artifact)

private def checkAt (root : Nat) (roles : Array Bool) (ports : Array Basis := #[#[.bit],#[.bit]]) :
    Except QleisliKernel.Finite.Error Matrix :=
  ((check (fun _ _ => throw .invalid) artifact ⟨root,ports,roles⟩).run 100000).1

private def coefficient (root row col : Nat) : Option Scalar :=
  (checkAt root #[true,false]).toOption.map (·.entry row col)

#guard coefficient 1 3 3 == some (QleisliKernel.Exact.Scalar.phase 1)
#guard coefficient 1 2 2 == some Scalar.one
#guard coefficient 2 2 2 == some (QleisliKernel.Exact.Scalar.phase 1)
#guard coefficient 2 3 3 == some Scalar.one
#guard coefficient 4 3 3 == some (QleisliKernel.Exact.Scalar.phase 1)
#guard coefficient 8 3 3 == some (QleisliKernel.Exact.Scalar.phase 7)
#guard coefficient 9 3 3 == some Scalar.one
#guard coefficient 10 3 3 == some (QleisliKernel.Exact.Scalar.phase 2)
#guard coefficient 11 3 3 == some Scalar.one
#guard coefficient 13 3 3 == some (QleisliKernel.Exact.Scalar.phase 1)
-- The target phase sits on the high axis of the tensor and moves to the low
-- axis after routing both sides of the original call.
#guard coefficient 17 1 1 == some Scalar.one
#guard coefficient 17 2 2 == some (QleisliKernel.Exact.Scalar.phase 1)
#guard coefficient 18 1 1 == some (QleisliKernel.Exact.Scalar.phase 1)
#guard coefficient 18 2 2 == some Scalar.one

private def errorIs (result : Except QleisliKernel.Finite.Error Matrix)
    (expected : QleisliKernel.Finite.Error) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

-- An actual axis permutation crosses the sector, even under a unitary label.
#guard errorIs (checkAt 3 #[true,false]) .equation
#guard errorIs (checkAt 5 #[true,false]) .equation
#guard errorIs (checkAt 15 #[true,false]) .limit
-- Port trees and positions are checked even when widths match or are zero.
#guard errorIs (checkAt 1 #[true,false] #[#[.bits 1],#[.bit]]) .request
#guard errorIs (checkAt 1 #[false,false]) .request
#guard checkAt 7 #[false,false,true] #[#[.bit],#[.bit],#[.bits 0]] |>.isOk
#guard errorIs (checkAt 7 #[false,false,true] #[#[.bit],#[.bit],#[.unit]]) .request
#guard errorIs ((check (fun _ _ => throw .invalid) artifact ⟨1,#[#[.bit],#[.bit]],#[true,false]⟩).run 0).1 (.arithmetic .workLimit)

end QleisliKernel.Tests.HierarchyControl
