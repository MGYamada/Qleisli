import QleisliKernel.SourceTypes.GenericDutyQueue

/-! Finite original call-duty expansion, with no native Meaning admission.
The 619-byte first source is retained exactly. Its original CLI rejection and
older prepared-path omission are external first observations, not changed here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericDutyQueue
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite
open GenericOperation

private def firstSource : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nmeaning Identity: Bit = reference(keep);\nunitary fn invoke[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { U(q) }\nunitary fn need[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit>\n    requires Applicable(U) { invoke[checked_op(U, Identity)](q) }\nunitary fn dormant[const n: Nat](q: Q<Bit>) -> Q<Bit> {\n    need[sign](q)\n}\npub unitary fn route(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    qmatch(s, q) { Tag::B => sign, Tag::A => keep }\n}\nfn main() -> Unit { () }\n"

private def sourcePrelude := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn need[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){invoke[checked_op(U,Identity)](q)}\n"

private def closedAt (source name : String) : WorkM (List (String × Nat × String × Nat)) := do
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← SourceTypes.GenericDutyQueue.read catalogue
  let some root := queue.roots.find? (fun root =>
    (catalogue.records[root.record.val]'root.record.isLt).name == name) | throw .request
  root.items.foldlM (fun previous item => do
    match item with
    | .demand invocation demand =>
      match demand.source.original.requirement with
      | .access _ => pure previous
      | .meaning _ =>
        match ← GenericOperation.close demand.transported.subject.description with
        | .conditional .. => pure previous
        | .closed closed =>
          let some (.provider owner name _ _ _) :=
            closed.data.description.nodes[closed.data.description.root]? | throw .request
          pure (previous ++ [(demand.source.original.origin.state.name,demand.source.original.origin.offset,
            owner ++ "::" ++ name,invocation.id.calls.length)])
    | _ => pure previous) []

-- One genuine original-call substitution closes need's U to dormant's sign.
-- The original checked_op offset and callee environment remain attached.
#guard (closedAt firstSource "dormant").run 10000000 |>.1.toOption ==
  some [("need",369,"main::sign",1)]

private def namedClosed (suffix : String) : WorkM (List (String × String × Nat)) := do
  pure (← closedAt (sourcePrelude ++ suffix) "caller").map fun (origin,_,provider,depth) =>
    (origin,provider,depth)

-- No header-empty heuristic or choice for the unused n closes this subject.
#guard (namedClosed "unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{need[sign](q)}").run
  10000000 |>.1.toOption == some [("need","main::sign",1)]

-- Two original substitutions are retained in order, rather than rebuilding a
-- fake combined ApplicationSource with a changed lexical environment.
#guard (namedClosed ("unitary fn layer[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){need[V](q)}\n" ++
  "unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{layer[sign](q)}")).run 10000000
  |>.1.toOption == some [("need","main::sign",2)]

-- An unrefined original U is legitimately conditional. Deferral is no M proof.
#guard (namedClosed "unitary fn caller[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){need[V](q)}").run
  10000000 |>.1.toOption == some []

-- The honest closed counterpart still carries its exact pending equation.
#guard (namedClosed "unitary fn caller(q:Q<Bit>)->Q<Bit>{need[keep](q)}").run
  10000000 |>.1.toOption == some [("need","main::keep",1)]

private def headerSharing : WorkM (Nat × Bool × Nat) := do
  let source := sourcePrelude ++
    "unitary fn refined[const U:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit> requires Applicable(U){invoke[checked_op(U,Identity)](q)}\n" ++
    "unitary fn caller(q:Q<Bit>)->Q<Bit>{refined[keep](q)}"
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← SourceTypes.GenericDutyQueue.read catalogue
  let some root := queue.roots.find? (fun root =>
    (catalogue.records[root.record.val]'root.record.isLt).name == "caller") | throw .request
  let demands := root.items.filterMap fun item => match item with
    | .demand _ checked => some checked.id | _ => none
  let references := root.items.filterMap fun item => match item with
    | .header _ reference => some reference.id | _ => none
  let meaningIds := root.items.filterMap fun item => match item with
    | .demand _ checked => match checked.source.original.requirement with
      | .meaning _ => some checked.id | _ => none
    | _ => none
  pure (references.length,references.all (fun reference => (demands.filter (· == reference)).length == 1),
    meaningIds.eraseDups.length)

-- Header premise at caller and callee reuse one source-instance ID. The
-- explicit assertion has another ID, even though it requests Identity too.
#guard headerSharing.run 10000000 |>.1.toOption == some (3,true,2)

private def partialSource := sourcePrelude ++
  "unitary fn ignore[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn caller[const V:Op<Bit>](q:Q<Bit>)->Q<Bit>{ignore[then_op(checked_op(sign,Identity),V)](q)}"

-- A free sibling and an unused supplied actual do not hide the closed M.
#guard (closedAt partialSource "caller").run 10000000 |>.1.toOption.map (·.map fun (origin,_,provider,depth) =>
  (origin,provider,depth)) == some [("caller","main::sign",0)]


private def zeroSource := sourcePrelude ++
  "static fn zero[const x:Nat]()->Nat{x-x}\n" ++
  "unitary fn ignore[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{static let count=zero[n]();ignore[power(checked_op(sign,Identity),count)](q)}"

-- The original helper and local alias prove the count is zero; neither the
-- zero repetition nor the unused formal erases its child's written M.
#guard (closedAt zeroSource "caller").run 10000000 |>.1.toOption.map (·.map fun (origin,_,provider,depth) =>
  (origin,provider,depth)) == some [("caller","main::sign",0)]

private def inactiveSource := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn middle[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0{adjoint(leaf[n-1])(q)}else{q}}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{middle[0](q)}"

private def inactiveForm : WorkM (Int × List Int × String × Nat) := do
  let catalogue ← GenericCatalogue.read #[("main",inactiveSource)]
  let queue ← SourceTypes.GenericDutyQueue.read catalogue
  let some root := queue.roots.find? (fun root =>
    (catalogue.records[root.record.val]'root.record.isLt).name == "caller") | throw .request
  let selected : Option (Int × List Int × String × Nat) ← root.items.foldlM (fun previous item => do
    match item with
    | .demand invocation demand =>
      if demand.source.original.kind == .runtimeTransform then
        let description := demand.transported.subject.description
        let some (.provider _ _ _ [(_,count)] _ _) := description.nodes[description.root]? | throw .request
        pure (some (count.constant,count.coefficients,demand.source.original.origin.state.name,
          invocation.id.calls.length))
      else pure previous
    | _ => pure previous) none
  lift (readOption selected)

-- The original guarded environment and signed substitution survive. Queue
-- construction does not attempt to close -1 or erase independent fixed duties.
#guard inactiveForm.run 10000000 |>.1.toOption == some (-1,[],"middle",1)

private def recursive : WorkM (Bool × Nat) := do
  let source := sourcePrelude ++
    "unitary fn recursive[const n:Nat,const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){" ++
    "if static n>0{recursive[n-1,U](q)}else{need[U](q)}}"
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← SourceTypes.GenericDutyQueue.read catalogue
  pure (queue.complete,(queue.items.filter SourceTypes.GenericDutyQueue.Item.unresolved).length)

-- Source completeness is explicitly withheld for an open recursive family.
-- No small selected n or successful truncated expansion repairs that hole.
#guard recursive.run 10000000 |>.1.toOption == some (false,1)

end QleisliKernel.Tests.GenericDutyQueue
