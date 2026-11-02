import QleisliKernel.SourceTypes.GenericCatalogue

/-! Original duty association before native Meaning/path consumption.
These tests inspect pending obligations and never certify an equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericDuties
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

private def sourcePrelude := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn ignore[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn need[const U:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit>{q}\n"

private def pending (suffix : String) : WorkM (List (String × String × String)) := do
  let catalogue ← GenericCatalogue.read #[("main",sourcePrelude ++ suffix)]
  let duties ← GenericCatalogue.readDuties catalogue
  return duties.entries.filterMap fun entry =>
    match entry.duty.requirement,entry.status with
    | .meaning request,.closed _ =>
      some (entry.duty.origin.state.name,request.declarationName,
        entry.duty.bindings.getLast?.map (·.actual.state.name) |>.getD "")
    | _,_ => none

-- The first real counterstudy has this closed subject inside an unused Nat
-- generic. n is not assigned a convenient value to obtain this classification.
#guard (pending "unitary fn dormant[const n:Nat](q:Q<Bit>)->Q<Bit>{invoke[checked_op(sign,Identity)](q)}").run
  10000000 |>.1.toOption == some [("dormant","Identity","dormant")]

-- An uninstantiated original Op remains conditional, despite closed Bit ports
-- and a fully resolved Meaning name. A header/request-count test would fail.
#guard (pending "unitary fn conditional[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){invoke[checked_op(U,Identity)](q)}").run
  10000000 |>.1.toOption == some []

-- Formal refinement is paired with the supplied sign occurrence. It cannot
-- survive as an unattached request about the callee's original abstract U.
#guard (pending "unitary fn dormant[const n:Nat](q:Q<Bit>)->Q<Bit>{need[sign](q)}").run
  10000000 |>.1.toOption == some [("need","Identity","dormant")]

-- A genuine closed child remains pending when its formal is never executed.
#guard (pending "unitary fn dormant[const n:Nat](q:Q<Bit>)->Q<Bit>{ignore[checked_op(sign,Identity)](q)}").run
  10000000 |>.1.toOption == some [("dormant","Identity","dormant")]

-- Repetition, including a zero count proved by an original helper and lexical
-- alias, retains the child's false Meaning assertion and its binding chain.
#guard (pending "static fn zero(x:Nat)->Nat{x-x}\nunitary fn dormant[const n:Nat](q:Q<Bit>)->Q<Bit>{static let count=zero(n);invoke[power(checked_op(sign,Identity),count)](q)}").run
  10000000 |>.1.toOption == some [("dormant","Identity","dormant")]

private def subject : WorkM (String × Nat × List String × List (String × String)) := do
  let suffix := "unitary fn dormant[const n:Nat](q:Q<Bit>)->Q<Bit>{need[sign](q)}"
  let catalogue ← GenericCatalogue.read #[("main",sourcePrelude ++ suffix)]
  let duties ← GenericCatalogue.readDuties catalogue
  let some entry := duties.entries.find? (fun entry => match entry.duty.requirement,entry.status with
    | .meaning _,.closed _ => true | _,_ => false)
    | throw .request
  let .closed closed := entry.status | throw .request
  let some (.provider owner name _ _ _) := closed.data.description.nodes[closed.data.description.root]?
    | throw .request
  let some binding := entry.duty.bindings.getLast? | throw .request
  return (owner ++ "::" ++ name,binding.formal.ordinal,
    binding.actual.tokens.map (·.text),entry.duty.suppliers.map fun (_,origin) => (origin.state.owner,origin.state.name))

#guard subject.run 10000000 |>.1.toOption == some ("main::sign",0,["sign"],[("main","dormant")])


-- Exact frozen counterstudy e797b3c2..., including its harmless selected
-- qmatch and original checked_op byte offset. Native rejection is separate.
private def firstSource : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nmeaning Identity: Bit = reference(keep);\nunitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { U(q) }\nunitary fn dormant[const n: Nat](q: Q<Bit>) -> Q<Bit> {\n    invoke[checked_op(sign, Identity)](q)\n}\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"

private def firstOffsets : WorkM (List Nat) := do
  let catalogue ← GenericCatalogue.read #[("main",firstSource)]
  let duties ← GenericCatalogue.readDuties catalogue
  return duties.entries.filterMap fun entry => match entry.duty.requirement,entry.status with
    | .meaning _,.closed _ => some entry.duty.origin.offset
    | _,_ => none

#guard firstOffsets.run 10000000 |>.1.toOption == some [345]

end QleisliKernel.Tests.GenericDuties
