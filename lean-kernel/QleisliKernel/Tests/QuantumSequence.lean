import QleisliKernel.SourceTypes.QuantumSequence

/-! Bounded executable owner/occurrence regressions using the actual checker.
These observations are not kernel-proved source/algorithm theorems, arm
capabilities, matrix equations or native integration. Generic postconditions
remain separate proofs over the executable definitions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QuantumSequence
open SourceTypes Semantics.SourceOwners

def choose := "qmatch(s,q){Tag::B=>keep,Tag::A=>keep}"

def source (body : String) (result : String := "(Q<Unit>,Q<Tag>,Q<Bit>)")
    (effect : String := "unitary") : String :=
  "// λ qmatch here is a comment, not a source occurrence\npub enum Tag{A,B} " ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q} pub " ++ effect ++
  " fn route(s:Q<Tag>,q:Q<Bit>,u:Q<Unit>)->" ++ result ++ "{" ++ body ++ "}"

def body := "let(s,q)=" ++ choose ++ ";let(q,s)=(q,s);let(s,q)=" ++ choose ++ ";(u,s,q)"

def view (text : String) :=
  ((SourceTypes.QuantumSequence.read #[("main",text)] "main" "route").run 10000000).1.toOption.map
    fun checked => (checked.outcome.events.length,
      checked.outcome.events.map fun event => (event.selector.ordinal,event.target.ordinal),
      (valueOwners checked.outcome.value).map (·.ordinal))

def rejected (text : String) : Bool :=
  match (SourceTypes.QuantumSequence.read #[("main",text)] "main" "route").run 10000000 with
  | (.ok _,_) => false | _ => true

def effectView (text : String) :=
  ((SourceTypes.QuantumSequence.read #[("main",text)] "main" "route").run 10000000).1.toOption.map
    (·.signature.original.parsedHeader.effect)

def controls : List (String × Bool) := [
  ("two original sites and the zero-width spectator keep their exact roles",
    view (source body) == some (2,[(0,1),(0,1)],[2,0,1])),
  ("later selections respect the original reordered bindings",
    view (source ("let(a,b)=" ++ choose ++ ";let(s,q)=(a,b);let(q,s)=" ++ choose ++ ";(u,q,s)")) ==
      some (2,[(0,1),(0,1)],[2,0,1])),
  ("missing zero-width owner refuses",
    rejected (source ("let(s,q)=" ++ choose ++ ";(s,q)") "(Q<Tag>,Q<Bit>)")),
  ("duplicated result owner refuses",rejected (source ("let(s,q)=" ++ choose ++ ";(u,s,s)"))),
  ("the same consumed source owner cannot be both operands",
    rejected (source "let(s,q)=qmatch(s,s){Tag::A=>keep,Tag::B=>keep};(u,s,q)")),
  ("a tuple of separate owners is not one target owner",
    rejected (source "let(s,q)=qmatch(s,(q,u)){Tag::A=>keep,Tag::B=>keep};(u,s,q)")),
  ("old bindings cannot explain the second site",rejected (source ("let(a,b)=" ++ choose ++ ";" ++ choose))),
  ("wildcard cannot discard a zero-width owner",
    rejected (source ("let _=u;let(s,q)=" ++ choose ++ ";(s,q)") "(Q<Tag>,Q<Bit>)")),
  ("unknown prefix call is not skipped",rejected (source ("let q=h(q);let(s,q)=" ++ choose ++ ";(u,s,q)"))),
  ("unknown suffix call is not skipped",rejected (source ("let(s,q)=" ++ choose ++ ";(u,s,h(q))"))),
  ("hidden observation is not a structural move",
    rejected (source ("let x=measure_z(q);let(s,q)=" ++ choose ++ ";(u,s,q)"))),
  ("unused extra expression cannot hide a site",rejected (source (choose ++ ";" ++ choose))),
  ("outer Unitary annotation is retained",effectView (source body) == some (some .unitary)),
  ("outer Observe annotation is retained",
    effectView (source body "(Q<Unit>,Q<Tag>,Q<Bit>)" "observe") == some (some .observe))]

example : controls.length = 14 := by decide +kernel
#guard controls.all (·.2)

end QleisliKernel.Tests.QuantumSequence
