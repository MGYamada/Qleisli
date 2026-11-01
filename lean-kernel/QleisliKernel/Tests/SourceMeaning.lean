import QleisliKernel.SourceTypes.SourceMeaning

/-! Small original Meaning graph metadata regressions. Reference bodies,
monomial truth tables, Gram checks and actual provider equations are separate
native obligations; these tests do not certify their semantic equality.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceMeaning
open SourceTypes Semantics.FiniteCarrier

private def source : String :=
  "// λ original bytes\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q} meaning Identity:Bit=reference(keep);"

private def view (text : String) (name : String := "Identity") :=
  (((SourceTypes.SourceMeaning.read #[ ("main",text) ] (some "main") "main" name).run 10000000).1.toOption).map
    fun checked => (checked.graph.input,checked.graph.output,checked.graph.nodes.length,
      checked.graph.references.map fun reference => (reference.resolution.result.moduleName,reference.resolution.result.declaration.name))

#guard view source = some ([.bit],[.bit],1,[("main","keep")])

#guard (((SourceTypes.SourceMeaning.read #[ ("main",source) ] none "main" "Identity").run 10000000).1.isOk) = false

#guard (view (source ++ " meaning Twice:Bit=compose(Identity,Identity);") "Twice") =
  some ([.bit],[.bit],3,[("main","keep"),("main","keep")])

#guard (view (source ++ " meaning Both:(Bit,Bit)=tensor(Identity,Identity);") "Both") =
  some ([.pair,.bit,.bit],[.pair,.bit,.bit],3,[("main","keep"),("main","keep")])

-- Equal physical width cannot replace the complete Meaning/reference ports.
#guard view "unitary fn keep(q:Q<Bit>)->Q<Bit>{q} meaning Identity:Bits<1>=reference(keep);" = none

-- Reference expressions cannot infer a missing, even unused, static actual.
#guard view "unitary fn keep[const n:Nat](q:Q<Bit>)->Q<Bit>{q} meaning Identity:Bit=reference(keep);" = none

#guard view "meaning Identity:Bit=compose(Other,Other);meaning Other:Bit=compose(Identity,Identity);" = none

private def classical : String :=
  "classical fn flip(b:Bit)->Bit{not b} meaning Flip:Bit=permutation_by(flip); " ++
  "classical fn phase_bits(b:Bit)->(Bit,(Bit,Bit)){(b,(0,0))} meaning Sign:Bit=phase_by(phase_bits);"

#guard (((SourceTypes.SourceMeaning.read #[ ("main",classical) ] (some "main") "main" "Flip").run 10000000).1.toOption).map
  (fun checked => checked.graph.classical.length) = some 1

#guard (((SourceTypes.SourceMeaning.read #[ ("main",classical) ] (some "main") "main" "Sign").run 10000000).1.toOption).map
  (fun checked => checked.graph.classical.length) = some 1

-- Phase output nesting is exact, not merely three physical bits.
#guard view "classical fn bad(b:Bit)->(Bit,Bit,Bit){(b,0,0)} meaning Identity:Bit=phase_by(bad);" = none

private def helper : String := "pub observe fn keep(q:Q<Bit>)->Q<Bit>{q}"
private def outside : String := "use helper::keep; meaning Identity:Bit=reference(keep);"

#guard (((SourceTypes.SourceMeaning.read #[ ("main",outside),("helper",helper) ] (some "main") "main" "Identity").run 10000000).1.isOk) = false

-- Internal inference is retained as an obligation while the public annotation remains unchanged.
#guard (((SourceTypes.SourceMeaning.read #[ ("main",helper ++ " meaning Identity:Bit=reference(keep);") ]
    (some "main") "main" "Identity").run 10000000).1.toOption).map
    (fun checked => checked.graph.references.map fun reference =>
      (reference.signature.original.parsedHeader.effect,reference.expectedEffect,reference.internalInference)) =
    some [(some .observe,.unitary,true)]

end QleisliKernel.Tests.SourceMeaning
