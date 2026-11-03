import QleisliKernel.Qirf.SourceMeaningAction

/-! Exact matrix entries for complete ordinary-source Meaning graphs. The two
compositions have identical ports and differ by a global minus sign. Tensor
products additionally distinguish which field is placed on the low axes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceMeaningAction
open QleisliKernel Finite SourceTypes Qirf
open Semantics.Exact

private def text (result : String) : String :=
  "#![no_implicit_prelude]\nclassical fn flip(b:Bit)->Bit{not b}" ++
  "classical fn sign_bits(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}" ++
  "meaning X:Bit=permutation_by(flip);meaning Z:Bit=phase_by(sign_bits);" ++
  "meaning Product:" ++ result ++ ";"

private def inspect (result : String) (extra : List RuntimeProviderHeader.Request := []) : WorkM Matrix := do
  let identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
  let artifact : Artifact := ⟨#[identity],#[],#[("main",text result)],0,none⟩
  let catalogue ← GenericCatalogue.read artifact.sources
  let meaning ← SourceMeaning.read artifact.sources (some "main") "main" "Product"
  let prepared ← SourceMeaningAction.prepare artifact catalogue meaning extra
  let root ← Validity.checkRootFromRoots artifact #[0] prepared.rows (artifact.root :: prepared.roots).eraseDups
  return (← SourceMeaningAction.read prepared root).action

private def snapshot (result : String) (extra : List RuntimeProviderHeader.Request := []) :=
  ((inspect result extra).run 10000000).1

private def minus := Semantics.PrimitiveOperator.phase 4
private def z := Scalar.zero
private def o := Scalar.one

#guard (snapshot "Bit=compose(Z,X)").toOption == some ⟨2,2,[z,minus,o,z]⟩
#guard (snapshot "Bit=compose(X,Z)").toOption == some ⟨2,2,[z,o,minus,z]⟩
#guard (snapshot "(Bit,Bit)=tensor(X,Z)").toOption ==
  some ⟨4,4,[z,o,z,z, o,z,z,z, z,z,z,minus, z,z,minus,z]⟩
#guard (snapshot "(Bit,Bit)=tensor(Z,X)").toOption ==
  some ⟨4,4,[z,z,o,z, z,z,z,minus, o,z,z,z, z,minus,z,z]⟩
#guard match snapshot "Bit=compose(Z,X)" [(.pure 0,.mk [] [] [] [] [])] with
  | .error .request => true | _ => false

end QleisliKernel.Tests.SourceMeaningAction
