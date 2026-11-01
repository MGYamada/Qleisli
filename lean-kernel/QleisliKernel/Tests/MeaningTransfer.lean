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
  "pub meaning BitsIdentity:Bits<1>=reference(bits); " ++
  "pub unitary fn unused[const U:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn wrong_kind[const A:Basis,const U:Op<A,Identity>](q:Q<A>)->Q<A>{q} " ++
  "pub unitary fn sized[const n:Nat,const U:Op<Bits<n>,BitsIdentity>](q:Q<Bits<n>>)->Q<Bits<n>> requires n==1{q} " ++
  "pub unitary fn unguarded_size[const n:Nat,const U:Op<Bits<n>,BitsIdentity>](q:Q<Bits<n>>)->Q<Bits<n>>{q} " ++
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

-- Raw descriptors obey the same identifier-only requested-operand profile.
#guard requests ((Description.binary .thenOp (named "keep") (named "keep")).unary
  (fun child => .requested child "main" "Identity")) = none

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

-- The original kind is checked for all opaque Basis interpretations, rather
-- than repaired by selecting A=Bit and a convenient concrete implementation.
#guard
  ((QuantumSignature.readWithArguments sources "main" "wrong_kind"
    {bases := [("A",[.bit])],operations := [("U",named "keep")]}).run 10000000).1.isOk = false

-- Exact symbolic width equality needs the original premise, even for n=1.
#guard
  ((QuantumSignature.readWithArguments sources "main" "sized"
    {naturals := [("n",1)],operations := [("U",named "bits")]}).run 10000000).1.isOk = true
#guard
  ((QuantumSignature.readWithArguments sources "main" "unguarded_size"
    {naturals := [("n",1)],operations := [("U",named "bits")]}).run 10000000).1.isOk = false

private def sourceExpression (expression : String) : Bool :=
  let action : Finite.WorkM Unit := do
    let sources : Sources := #[("main",source ++
      " pub unitary fn probe(q:Q<Bit>)->Q<Bit>{apply[" ++ expression ++ "](q)}")]
    let signature ← QuantumSignatureCore.read sources "main" "probe"
    let helpers ← NaturalHelpers.prepare sources
    let call ← Finite.lift ((CallSyntax.read signature.original.occurrence.body).mapError fun _ => .request)
    let written ← Finite.lift ((CallSyntax.readStatic call.call.callee).mapError fun _ => .request)
    let [argument] := written.call.arguments | throw .request
    let checked ← SourceOperation.read signature helpers (LexicalNatural.empty helpers) ["q"] argument.tokens
    Finite.guard checked.graph.hasMeaningRequirements .request
  (action.run 10000000).1.isOk

-- The original checked_op grammar admits names only, even when a broader
-- static description could have the same full ports and mathematical matrix.
#guard sourceExpression "checked_op(keep,Identity)" = true
#guard sourceExpression "checked_op(then_op(keep,keep),Identity)" = false
#guard sourceExpression "checked_op(keep[type(Bit)],Identity)" = false
#guard sourceExpression "checked_op(h,Identity)" = false

end QleisliKernel.Tests.MeaningTransfer
