import QleisliKernel.Qirf.SourcePendingMeaning

/-! Original closed Meaning assertions remain withheld even in unused generic
bodies and zero-power children. A genuinely unbound Op formal remains symbolic
despite its closed ports. No native equation, quantum instance or handle is
constructed by these fixed-budget source-closure controls.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourcePendingMeaning
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes

-- Exact first dormant-closed-meaning source retained by the caller study.
private def first := r#"#![no_implicit_prelude]
pub enum Tag { A, B }
unitary fn keep(q: Q<Bit>) -> Q<Bit> { q }
unitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }
meaning Identity: Bit = reference(keep);
unitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>
    requires Applicable(U) { U(q) }
unitary fn dormant[const n: Nat](q: Q<Bit>) -> Q<Bit> {
    invoke[checked_op(sign, Identity)](q)
}
pub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {
    qmatch(s, q) { Tag::B => sign, Tag::A => keep }
}
fn main() -> Unit { () }
"#

private def read (text : String) : WorkM (List GenericOperation.Key) := do
  let catalogue ← GenericCatalogue.read #[("main",text)]
  let checked ← Qirf.SourcePendingMeaning.read catalogue
  return checked.entries.flatMap (·.conditionalKeys)

#guard (match (read first).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (read (first.replace "invoke[checked_op(sign, Identity)]"
  "invoke[power(checked_op(sign, Identity), 0)]")).run 10000000 with
    | (.error .request,_) => true | _ => false)

-- A Meaning declaration by itself is no assertion that sign implements it.
#guard (read (first.replace "invoke[checked_op(sign, Identity)]" "invoke[sign]")).run
  10000000 |>.1.toOption == some []

private def conditional :=
  let header := first.replace
    "unitary fn dormant[const n: Nat](q: Q<Bit>) -> Q<Bit> {"
    "unitary fn dormant[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit> requires Applicable(U) {"
  header.replace "checked_op(sign, Identity)" "checked_op(U, Identity)"

#guard (read conditional).run 10000000 |>.1.toOption == some [.operation ⟨"main","dormant",0⟩]


-- Exact 619-byte transitive-binding first. Its original CLI rejection points
-- at need's written U assertion; prepared paths formerly omitted this binding.
private def transitive := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nmeaning Identity: Bit = reference(keep);\nunitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { U(q) }\nunitary fn need[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { invoke[checked_op(U, Identity)](q) }\nunitary fn dormant[const n: Nat](q: Q<Bit>) -> Q<Bit> {\n    need[sign](q)\n}\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"

#guard (match (read transitive).run 10000000 with | (.error .request,_) => true | _ => false)

private def openNeed := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nmeaning Identity: Bit = reference(keep);\nunitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { U(q) }\nunitary fn need[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { invoke[checked_op(U, Identity)](q) }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"
private def refinedNeed := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nmeaning Identity: Bit = reference(keep);\nunitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { U(q) }\nunitary fn need[const U: Op<Bit,Identity>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { invoke[checked_op(U, Identity)](q) }\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"
private def closedKeep := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nmeaning Identity: Bit = reference(keep);\nunitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { U(q) }\nunitary fn need[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { invoke[checked_op(U, Identity)](q) }\nunitary fn dormant[const n: Nat](q: Q<Bit>) -> Q<Bit> {\n    need[keep](q)\n}\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"

-- Both originally admitted open-formal cases stay conditional. A refinement
-- is a separate original assumption; it does not erase the written assertion.
#guard (read openNeed).run 10000000 |>.1.toOption == some [.operation ⟨"main","need",0⟩]
#guard (read refinedNeed).run 10000000 |>.1.toOption ==
  some [.operation ⟨"main","need",0⟩,.operation ⟨"main","need",0⟩]

-- This honest CLI-positive closed request is also withheld until the SAME
-- native equation consumer exists. Withholding is not a claim it is false.
#guard (match (read closedKeep).run 10000000 with | (.error .request,_) => true | _ => false)

private def inactiveSource := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn middle[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0{adjoint(leaf[n-1])(q)}else{q}}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{middle[0](q)}"

private def inactiveCount : WorkM Nat := do
  let catalogue ← GenericCatalogue.read #[("main",inactiveSource)]
  let checked ← Qirf.SourcePendingMeaning.read catalogue
  pure (checked.entries.filter (·.inactive)).length

-- -1 came from the original n-1 under the actual false source guard. It is
-- retained conditionally, with an all-valuations contradiction certificate.
#guard inactiveCount.run 10000000 |>.1.toOption == some 1


private def inactiveMeaning : String := "#![no_implicit_prelude]\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q}\nunitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit>{q}\nmeaning Identity:Bit=reference(keep);\nunitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\nunitary fn need[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){invoke[checked_op(U,Identity)](q)}\nunitary fn middle[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0{need[leaf[n-1]](q)}else{q}}\nunitary fn dormant[const unused:Nat](q:Q<Bit>)->Q<Bit>{middle[0](q)}\nfn main()->Unit{()}\n"

private def inactiveMeaningStatus {sources catalogue} (item : @GenericDutyQueue.Item sources catalogue) :
    Qirf.SourcePendingMeaning.Assessment item → Bool :=
  match item with
  | .demand _ demand => fun assessment => match demand.source.original.requirement,assessment with
    | .meaning _,.inactive _ => true | _,_ => false
  | _ => fun _ => false

private def inactiveMeaningCount : WorkM Nat := do
  let catalogue ← GenericCatalogue.read #[("main",inactiveMeaning)]
  let checked ← Qirf.SourcePendingMeaning.read catalogue
  pure (checked.entries.filter fun entry =>
    inactiveMeaningStatus (checked.queue.items[entry.index.val]'entry.index.isLt) entry.assessment).length

-- The exception also reaches a written M in a different original callee.
-- Its exact inserted leaf[n-1] is conditional under the retained middle guard.
#guard inactiveMeaningCount.run 10000000 |>.1.toOption == some 1

private def fixedInactive := first.replace
  "invoke[checked_op(sign, Identity)](q)"
  "if static n>0{invoke[checked_op(sign, Identity)](q)}else{q}"

-- An inactive source guard does not suppress an independently fixed false M.
#guard (match (read fixedInactive).run 10000000 with | (.error .request,_) => true | _ => false)

private def recursive := "#![no_implicit_prelude]\n" ++
  "unitary fn recursive[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0{recursive[n-1](q)}else{q}}"

-- Unresolved family coverage remains an explicit queue hole; the legacy
-- safety adapter cannot reinterpret a prefix as complete source coverage.
#guard (match (read recursive).run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourcePendingMeaning
