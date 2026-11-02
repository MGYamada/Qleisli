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
  return checked.duties.entries.flatMap fun entry => match entry.duty.requirement,entry.status with
    | .meaning _,.conditional keys _ _ => keys
    | _,_ => []

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

end QleisliKernel.Tests.SourcePendingMeaning
