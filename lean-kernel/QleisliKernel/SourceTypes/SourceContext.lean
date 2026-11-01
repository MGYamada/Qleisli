import QleisliKernel.SourceTypes.CallName

/-! Lazy reuse of actual original-call lookup results. A context is indexed by
the unchanged source table and caller. Each recorded result retains the first
actual CallName.read execution, including original absence, prelude policy and
resolver traces. Current lexical scope is checked before consulting that cache;
token locations remain those of the current occurrence. Only request refusals
are retained: work/depth exhaustion is never cached as absence. Request errors
include the original scanner's deterministic capacity refusals.

This component changes accounting, not the declaration resolver. Distinct
queries still execute that resolver; catalogue sharing across distinct queries
and complete source/body/IR preservation remain separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceContext
open QleisliKernel QleisliKernel.SourceTypes

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

/-- The empty scope permits recording only scope-independent source lookup.
The execution witness belongs to its actual first work state, not later hits. -/
inductive Recorded (sources : Sources) (caller : String) (tokens : List LocatedToken) where
  | accepted (checked : CallName.Checked sources caller [] tokens) (before after : Nat)
      (executed : (CallName.read sources caller [] tokens).run before = (.ok checked,after))
  | refused (before after : Nat)
      (executed : (CallName.read sources caller [] tokens).run before = (.error .request,after))

structure Entry (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  recorded : Recorded sources caller tokens

/-- Neither caller identity nor source bytes can be replaced on a cache hit. -/
structure Context (sources : Sources) (caller : String) where
  entries : List (Entry sources caller) := []

def Entry.key {sources caller} (entry : Entry sources caller) : List String :=
  entry.tokens.map (·.text)

private def capture (sources : Sources) (caller : String) (tokens : List LocatedToken) :
    Finite.WorkM (Recorded sources caller tokens) := fun before =>
  match executed : (CallName.read sources caller [] tokens).run before with
  | (.ok checked,after) => (.ok (.accepted checked before after executed),after)
  | (.error .request,after) => (.ok (.refused before after executed),after)
  | (.error error,after) => (.error error,after)

/-- Rebind only the lexical proof. Every original module/declaration, policy,
absence proof and executed resolver witness is preserved unchanged. -/
def rescope {sources caller tokens scope}
    (decision : CallName.Decision sources caller [] tokens)
    (unbound : ∀ name, tokens = [name] → name ∉ scope) :
    CallName.Decision sources caller scope tokens :=
  match decision with
  | .lexical _ _ bound => by simp at bound
  | .named resolution => .named resolution
  | .prelude name spelling _ localMissing policy enabled lookup publicExport resolution =>
    .prelude name spelling (unbound name spelling) localMissing policy enabled lookup publicExport resolution
  | .primitive name spelling _ localMissing policy preludeMissing candidate originalName =>
    .primitive name spelling (unbound name spelling) localMissing policy preludeMissing candidate originalName

/-- A replayable answer retains its recorded origin and current query equality.
A refusal is explicit and cannot be consumed as a primitive/prelude miss. -/
inductive Evidence (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) where
  | lexical (name : String) (spelling : tokens.map (·.text) = [name]) (bound : name ∈ scope)
  | original (entry : Entry sources caller) (same : entry.key = tokens.map (·.text))
      (unbound : ∀ name, tokens.map (·.text) = [name] → name ∉ scope)

structure Answer (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) where
  name : CallName.Name tokens
  evidence : Evidence sources caller scope tokens

def Answer.checked {sources caller scope tokens} (answer : Answer sources caller scope tokens) :
    Except Finite.Error (CallName.Checked sources caller scope tokens) :=
  match answer.evidence with
  | .lexical name spelling bound => .ok ⟨answer.name,.lexical name spelling bound⟩
  | .original entry same unbound =>
    match entry.recorded with
    | .refused .. => .error .request
    | .accepted checked _ _ _ =>
      have decision : CallName.Decision sources caller [] (tokens.map (·.text)) :=
        same ▸ checked.decision
      .ok ⟨answer.name,rescope decision unbound⟩

structure Lookup (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) where
  answer : Answer sources caller scope tokens
  context : Context sources caller
  reused : Bool

private def nameFields (names : List String) : Nat :=
  (names.map fun name => name.utf8ByteSize+1).sum

private def lexicalName (tokens : List String) (scope : List String) :
    Option {name : String // tokens = [name] ∧ name ∈ scope} :=
  match tokens with
  | [name] => if bound : name ∈ scope then some ⟨name,rfl,bound⟩ else none
  | _ => none

private theorem lexicalName_unbound (tokens : List String) (scope : List String)
    (missing : lexicalName tokens scope = none) :
    ∀ name, tokens = [name] → name ∉ scope := by
  intro name spelling bound
  subst tokens
  simp [lexicalName,bound] at missing

private structure Match (sources : Sources) (caller : String) (tokens : List String) where
  entry : Entry sources caller
  same : entry.key = tokens

private def find {sources : Sources} {caller : String}
    (context : Context sources caller) (tokens : List String) :
    Option (Match sources caller tokens) :=
  context.entries.findSome? fun entry =>
    if same : entry.key = tokens then some ⟨entry,same⟩ else none

/-- Charge fresh token/name parsing and lexical comparisons first. Only after
the lexical decision, charge actual cache-key comparisons. A miss executes and
charges the unchanged original reader exactly once. No module is scanned merely
because it is present in the supplied source table. -/
def read (sources : Sources) (caller : String) (context : Context sources caller)
    (scope : List String) (tokens : List LocatedToken) :
    Finite.WorkM (Lookup sources caller scope tokens) := do
  let texts := tokens.map (·.text)
  Finite.exactWork (Exact.charge (8*(nameFields texts+1)+2*(nameFields scope+1)))
  let name ← adapt (CallName.readName tokens)
  match localName : lexicalName texts scope with
  | some binding =>
    return ⟨⟨name,.lexical binding.val binding.property.1 binding.property.2⟩,context,false⟩
  | none =>
    have unbound := lexicalName_unbound texts scope localName
    Finite.exactWork (Exact.charge (1+(context.entries.map fun entry =>
      nameFields entry.key + nameFields texts + 1).sum))
    match find context texts with
    | some matched =>
      return ⟨⟨name,.original matched.entry matched.same unbound⟩,context,true⟩
    | none =>
      Finite.exactWork (Exact.charge (nameFields texts+1))
      let recorded ← capture sources caller tokens
      let entry : Entry sources caller := ⟨tokens,recorded⟩
      return ⟨⟨name,.original entry rfl unbound⟩,⟨entry :: context.entries⟩,false⟩

def Recorded.response {sources caller tokens} : Recorded sources caller tokens →
    Except Finite.Error (CallName.Checked sources caller [] tokens)
  | .accepted checked .. => .ok checked
  | .refused .. => .error .request

theorem Recorded.original {sources caller tokens} (recorded : Recorded sources caller tokens) :
    ∃ first last, (CallName.read sources caller [] tokens).run first = (recorded.response,last) := by
  cases recorded with
  | accepted checked first last executed => exact ⟨first,last,executed⟩
  | refused first last executed => exact ⟨first,last,executed⟩

theorem Answer.originalSpelling {sources caller scope tokens}
    (answer : Answer sources caller scope tokens) :
    answer.name.segments.intersperse "::" = tokens.map (·.text) := answer.name.original

end QleisliKernel.SourceTypes.SourceContext
