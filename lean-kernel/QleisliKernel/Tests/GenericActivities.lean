import QleisliKernel.SourceTypes.GenericCatalogue

/-! Source-derived interleaving of original calls and semantic duties.
Byte offsets and independently sorted projections cannot reconstruct these
orders. These controls produce metadata only, with no native admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericActivities
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

private def sourcePrelude := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn ignore[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn need[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){invoke[checked_op(U,Identity)](q)}\n"

private def describe {sources} : GenericOperation.Activity sources → String
  | .application application => "call:" ++ application.name
  | .duty duty => match duty.requirement with
    | .meaning _ => "M:" ++ duty.origin.state.name
    | .access paths =>
      (if paths.applicable then "A" else "") ++ (if paths.adjointable then "J" else "") ++
        (if paths.controllable then "C" else "")

private def activities (body : String) : WorkM (List String) := do
  let catalogue ← GenericCatalogue.read #[("main",sourcePrelude ++ body)]
  let some caller := catalogue.records.find? (·.name == "caller") | throw .request
  pure ((GenericCatalogue.bodyActivities caller).map describe)

-- The need call occupies a genuine point between actual duties and the next
-- source expression. Its callee stream must be expanded there, not afterward.
#guard (activities "unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{let q=need[sign](q);invoke[checked_op(keep,Identity)](q)}").run
  10000000 |>.1.toOption == some ["call:sign","A","call:need","call:keep","M:caller","A","call:invoke"]

-- Inner runtime arguments evaluate before the outer action, although the
-- outer callee token occurs earlier in the original byte string.
#guard (activities "unitary fn caller(q:Q<Bit>)->Q<Bit>{need[sign](need[keep](q))}").run 10000000
  |>.1.toOption == some ["call:keep","A","call:need","call:sign","A","call:need"]

-- Both source arms retain their streams in original branch order.
#guard (activities "unitary fn caller(c:Bit,q:Q<Bit>)->Q<Bit>{if c{need[sign](q)}else{need[keep](q)}}").run
  10000000 |>.1.toOption == some ["call:sign","A","call:need","call:keep","A","call:need"]

-- Unused actuals and zero-power children still precede the containing call.
#guard (activities "unitary fn caller(q:Q<Bit>)->Q<Bit>{ignore[then_op(checked_op(sign,Identity),keep)](q)}").run
  10000000 |>.1.toOption == some ["call:sign","M:caller","call:keep","call:ignore"]
#guard (activities "unitary fn caller(q:Q<Bit>)->Q<Bit>{ignore[power(checked_op(sign,Identity),0)](q)}").run
  10000000 |>.1.toOption == some ["call:sign","M:caller","call:ignore"]

end QleisliKernel.Tests.GenericActivities
