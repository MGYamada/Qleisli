import QleisliKernel.FiniteRestriction.Check

/-! Small executable checks of the actual bounded sector component, at most
three joined physical bits. These are tests, separate from its generic proofs.
No original source/Raw transport, native handle or nominal integration follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.FiniteRestriction
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.FiniteRestriction

instance : BEq (Except QleisliKernel.Finite.Error (List Matrix)) where
  beq
    | .ok left,.ok right => left == right
    | .error left,.error right => left == right
    | _,_ => false

def bitBasis : Basis := [.bit]
def unitBasis : Basis := [.unit]
def negativeOne : Scalar := ⟨.integer (-1),.integer 0,.integer 0,.integer 0⟩
def imaginaryOne : Scalar := ⟨.integer 0,.integer 0,.integer 1,.integer 0⟩
def negativeImaginary : Scalar := ⟨.integer 0,.integer 0,.integer (-1),.integer 0⟩
def halfRoot : Scalar := ⟨.integer 0,⟨1,1⟩,.integer 0,.integer 0⟩
def negativeHalfRoot : Scalar := ⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩
def hadamard : Matrix := ⟨2,2,[halfRoot,halfRoot,halfRoot,negativeHalfRoot]⟩
def flip : Matrix := ⟨2,2,[Scalar.zero,Scalar.one,Scalar.one,Scalar.zero]⟩
def identity : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
def scalar (value : Scalar) : Matrix := ⟨1,1,[value]⟩
def hxSteps : List Step := [⟨[⟨0,false⟩],.hadamard 1⟩,
  ⟨[⟨0,true⟩],.monomial [1] [1,0] [0,0]⟩]
def hxCircuit : Circuit := ⟨joinedBasis bitBasis bitBasis,hxSteps⟩

example : (((checkSectors [] bitBasis bitBasis hxCircuit [hadamard,flip]).run 100000).1 ==
    .ok [hadamard,flip]) = true := by decide +kernel

example : (((checkSectors [] bitBasis bitBasis hxCircuit [flip,hadamard]).run 100000).1 ==
    .error .equation) = true := by decide +kernel

example : (((checkSectors [] bitBasis bitBasis hxCircuit [hadamard]).run 100000).1 ==
    .error .request) = true := by decide +kernel

example : (((checkSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,[⟨[],.hadamard 0⟩]⟩ [hadamard,hadamard]).run 100000).1 ==
    .error .invalid) = true := by decide +kernel

example : (((checkSectors [] unitBasis bitBasis
    ⟨joinedBasis unitBasis bitBasis,[⟨[],.hadamard 0⟩]⟩ [hadamard]).run 100000).1 ==
    .ok [hadamard]) = true := by decide +kernel

example : (((checkSectors [] unitBasis bitBasis
    ⟨joinedBasis [.bits 0] bitBasis,[⟨[],.hadamard 0⟩]⟩ [hadamard]).run 100000).1 ==
    .error .request) = true := by decide +kernel

def scalarSteps : List Step := [⟨[⟨0,false⟩],.monomial [] [0] [4]⟩,
  ⟨[⟨0,true⟩],.monomial [] [0] [2]⟩]
def scalarCircuit : Circuit := ⟨joinedBasis bitBasis unitBasis,scalarSteps⟩

example : (((checkSectors [] bitBasis unitBasis scalarCircuit
    [scalar negativeOne,scalar imaginaryOne]).run 100000).1 ==
    .ok [scalar negativeOne,scalar imaginaryOne]) = true := by decide +kernel

example : (((checkSectors [] bitBasis unitBasis scalarCircuit
    [scalar Scalar.one,scalar imaginaryOne]).run 100000).1 ==
    .error .equation) = true := by decide +kernel

def fourLabels : Basis := [.bits 2]
def fourSteps : List Step := [
  ⟨[⟨0,false⟩,⟨1,false⟩],.monomial [] [0] [0]⟩,
  ⟨[⟨0,true⟩,⟨1,false⟩],.monomial [] [0] [4]⟩,
  ⟨[⟨0,false⟩,⟨1,true⟩],.monomial [] [0] [2]⟩,
  ⟨[⟨0,true⟩,⟨1,true⟩],.monomial [] [0] [6]⟩]
def fourMeanings : List Matrix :=
  [scalar Scalar.one,scalar negativeOne,scalar imaginaryOne,scalar negativeImaginary]

example : (((checkSectors [] fourLabels unitBasis
    ⟨joinedBasis fourLabels unitBasis,fourSteps⟩ fourMeanings).run 100000).1 ==
    .ok fourMeanings) = true := by decide +kernel

def conjugated : List Step := [⟨[],.hadamard 1⟩,
  ⟨[⟨0,true⟩],.monomial [1] [0,1] [0,4]⟩,⟨[],.hadamard 1⟩]

example : (((checkSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,conjugated⟩ [identity,flip]).run 100000).1 ==
    .ok [identity,flip]) = true := by decide +kernel

example : (((checkSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,conjugated.dropLast⟩ [identity,flip]).run 100000).1 ==
    .error .equation) = true := by decide +kernel

example : (((checkSectors [] bitBasis bitBasis
    ⟨joinedBasis bitBasis bitBasis,[⟨[⟨0,true⟩],.monomial [1] [0,0] [0,0]⟩]⟩
    [identity,identity]).run 100000).1 == .error .request) = true := by decide +kernel

def contractSteps : List Step := [⟨[⟨0,true⟩],.contract [] 0 true⟩]

example : (((checkSectors [⟨unitBasis,scalar imaginaryOne⟩] bitBasis unitBasis
    ⟨joinedBasis bitBasis unitBasis,contractSteps⟩
    [scalar Scalar.one,scalar negativeImaginary]).run 100000).1 ==
    .ok [scalar Scalar.one,scalar negativeImaginary]) = true := by decide +kernel

example : (((checkSectors [] bitBasis unitBasis
    ⟨joinedBasis bitBasis unitBasis,contractSteps⟩
    [scalar Scalar.one,scalar negativeImaginary]).run 100000).1 ==
    .error .request) = true := by decide +kernel

example : (((checkSectors [] bitBasis bitBasis hxCircuit [hadamard,flip]).run 0).1 ==
    .error (.arithmetic .workLimit)) = true := by decide +kernel

def twoTargets : Basis := [.bits 2]
def identity4 : Matrix := ⟨4,4,[
  Scalar.one,Scalar.zero,Scalar.zero,Scalar.zero,
  Scalar.zero,Scalar.one,Scalar.zero,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.one,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.zero,Scalar.one]⟩
def firstControlsSecond : Matrix := ⟨4,4,[
  Scalar.one,Scalar.zero,Scalar.zero,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.zero,Scalar.one,
  Scalar.zero,Scalar.zero,Scalar.one,Scalar.zero,
  Scalar.zero,Scalar.one,Scalar.zero,Scalar.zero]⟩

/-- Original axes [2,1] interpret the local input in the opposite order from
the retained target tree. The explicit matrix fixes low-target control. -/
example : (((checkSectors [] bitBasis twoTargets
    ⟨joinedBasis bitBasis twoTargets,[⟨[⟨0,true⟩],.monomial [2,1] [0,1,3,2] [0,0,0,0]⟩]⟩
    [identity4,firstControlsSecond]).run 1000000).1 ==
    .ok [identity4,firstControlsSecond]) = true := by decide +kernel

example : (((checkSectors [] bitBasis twoTargets
    ⟨joinedBasis bitBasis twoTargets,[⟨[⟨0,true⟩],.monomial [1,2] [0,1,3,2] [0,0,0,0]⟩]⟩
    [identity4,firstControlsSecond]).run 1000000).1 ==
    .error .equation) = true := by decide +kernel

end QleisliKernel.Tests.FiniteRestriction
