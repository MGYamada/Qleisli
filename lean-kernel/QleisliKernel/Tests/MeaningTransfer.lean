import QleisliKernel.SourceTypes.SourceOperation
import QleisliKernel.SourceTypes.QuantumSignature

/-! Small original Meaning-transfer regressions. These inspect pending exact
requests, never establish Meaning equality or grant a native accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.MeaningTransfer
open SourceTypes Semantics.FiniteCarrier OperationDescription

private def source :=
  "pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)} " ++
  "pub unitary fn bits(q:Q<Bits<1>>)->Q<Bits<1>>{q} " ++
  "pub meaning Identity:Bit=reference(keep); " ++
  "pub unitary fn unused[const U:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn caller(q:Q<Bit>)->Q<Bit>{q}"

private def sources : Sources := #[("main",source)]
private def named (name : String) : Description := provider "main" name [] [] []
private def requested (name : String) : Description :=
  (named name).unary (fun child => .requested child "main" "Identity")

private def requests (description : Description) : Option (List (Nat × String × String)) :=
  ((SourceTypes.StaticOperation.check sources .external description).run 10000000).1.toOption.map
    (fun graph => graph.requirements.map fun (subject,request) => (subject,request.moduleName,request.declarationName))

-- An original request retains the child subject, canonical Meaning and paths.
#guard requests (requested "keep") = some [(0,"main","Identity")]
#guard
  ((SourceTypes.StaticOperation.check sources .external (requested "keep")).run 10000000).1.toOption.map
    (fun graph => (graph.root.paths,graph.hasMeaningRequirements)) = some (⟨true,true,true⟩,true)

-- Zero repetition and construction keep the independent child request.
#guard requests ((requested "keep").unary (fun child => .power child 0)) = some [(0,"main","Identity")]

-- Equal physical width does not match a declared Meaning's exact port tree.
#guard requests (requested "bits") = none

-- Metadata retains a false-phase request; equality still needs the native gate.
#guard requests (requested "sign") = some [(0,"main","Identity")]

-- The original unused formal's refinement binds to its exact argument node.
#guard
  requests (provider "main" "unused" [] [] [("U",named "keep")]) = some [(0,"main","Identity")]

-- Host root arguments retain their formal requests independently of body use.
#guard
  ((QuantumSignature.readWithArguments sources "main" "unused"
      {operations := [("U",named "keep")]}).run 10000000).1.toOption.map
    (fun signature => (signature.operations.rootRequirements.map fun (name,request) =>
      (name,request.moduleName,request.declarationName),signature.operations.hasMeaningRequirements)) =
    some ([("U","main","Identity")],true)

end QleisliKernel.Tests.MeaningTransfer
