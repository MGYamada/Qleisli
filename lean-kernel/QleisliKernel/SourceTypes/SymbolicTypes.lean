import QleisliKernel.Semantics.SymbolicBasis
import QleisliKernel.SourceTypes.StaticCallPremises
import QleisliKernel.SourceTypes.QuantumSignatureCore

/-! Original symbolic basis trees. Opaque parameters retain their exact mixed
ordinal/declaration identity; affine widths are compared under original caller
premises. The shared basis grammar and original nominal reader are reused.
These type obligations grant no body, inverse/control or runtime acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SymbolicTypes
open Finite Semantics.SourceAffine Semantics.SymbolicBasis

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

structure Read where
  code : Code
  rows : List (String × String)

private def closed (variables : Nat) (basis : Semantics.FiniteCarrier.Basis) : WorkM Code :=
  basis.mapM fun atom => do
    match atom with
    | .bits width => pure (.bits (← NaturalAffine.constant variables width))
    | _ => pure (.fixed atom)

def readCode {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (ordinal : Nat) : Nat → List String → WorkM Read :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    exactWork (Exact.charge (32*((tokens.map String.utf8ByteSize).sum+tokens.length+1)))
    match ← readBasisSyntax tokens with
    | .unit => pure ⟨[.fixed .unit],[]⟩
    | .bit => pure ⟨[.fixed .bit],[]⟩
    | .bits tokens =>
      let expression ← adapt (NaturalSyntax.read tokens)
      let normalized ← GenericLexicalNatural.read state.prepared state.environment scope expression
      let rows ← NaturalRows.expression sources state.owner state.prepared.helpers scope expression
      pure ⟨[.bits normalized.normalized.form],rows⟩
    | .tuple parts =>
      let children ← parts.mapM next
      let code := (.fixed (if parts.length == 2 then .pair else .tuple parts.length)) :: children.flatMap (·.code)
      guard (code.length ≤ 4096) .limit
      exactWork (Exact.charge (code.length+(children.flatMap (·.rows)).length+1))
      pure ⟨code,children.flatMap (·.rows)⟩
    | .named tokens =>
      let formal := match tokens with
        | [name] => state.prepared.original.header.formals.find? (fun formal => formal.name == name && formal.ordinal < ordinal)
        | _ => none
      match formal with
      | some formal =>
        guard (formal.kind == .basis) .request
        pure ⟨[.parameter ⟨state.owner,state.name,formal.ordinal⟩],[]⟩
      | none =>
        let query ← typeExpressionWithSources sources state.owner tokens
        let code ← closed (StaticHeaders.frame state.prepared.original).binders.length query.basis
        let rows ← NaturalRows.typeRead sources state.owner state.prepared.helpers [] tokens query
        pure ⟨code,rows⟩)

structure Checked {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (ordinal : Nat) (tokens : List String) where
  result : Read
  original : ∃ before after,(readCode state scope ordinal 65 tokens).run before = (.ok result,after)

def read {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (ordinal : Nat) (tokens : List String) : WorkM (Checked state scope ordinal tokens) := do
  let result ← NaturalAffine.witness (readCode state scope ordinal 65 tokens)
  pure ⟨result.val,by with_reducible exact result.property⟩

private def equateAtom {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (left right : Atom) : WorkM (NaturalPredicates.Established (∀ values,
      StaticCallPremises.Meaning state values → ∀ parameters,
      left.evaluate parameters values = right.evaluate parameters values)) := do
  exactWork (Exact.charge 4)
  match left,right with
  | .fixed a,.fixed b =>
    if same : a = b then pure ⟨by intro values held parameters; simp [Atom.evaluate,same]⟩
    else throw .request
  | .parameter a,.parameter b =>
    if same : a = b then pure ⟨by intro values held parameters; simp [Atom.evaluate,same]⟩
    else throw .request
  | .bits a,.bits b =>
    let proved ← NaturalPredicates.implies state.prepared.scope.context a .eq b
    pure ⟨by
      intro values held parameters
      have same : a.evaluate values = b.evaluate values := proved.proof values held
      simp only [Atom.evaluate,same]⟩
  | _,_ => throw .request

private def equateLoop {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources) :
    Nat → (left right : Code) → WorkM (NaturalPredicates.Established (∀ values,
      StaticCallPremises.Meaning state values → ∀ parameters,
      evaluate parameters values left = evaluate parameters values right)) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next left right => do
    match left,right with
    | [],[] => pure ⟨by intro values held parameters; rfl⟩
    | a :: rest,b :: tail =>
      let head ← equateAtom state a b
      let remaining ← next rest tail
      pure ⟨by
        intro values held parameters
        simp only [evaluate,head.proof values held parameters,remaining.proof values held parameters]⟩
    | _,_ => throw .request)

def equate {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (left right : Code) : WorkM (NaturalPredicates.Established (∀ values,
      StaticCallPremises.Meaning state values → ∀ parameters,
      evaluate parameters values left = evaluate parameters values right)) :=
  equateLoop state (left.length+1) left right

def replacementParameters (bases : List (Parameter × Code)) (parameters : Parameters) (values : Valuation) : Parameters :=
  fun parameter => do
    let (_,code) ← bases.find? (·.1 == parameter)
    evaluate parameters values code

structure Substituted (bases : List (Parameter × Code)) (naturals : List Form) (original : Code) where
  code : Code
  correct : ∀ parameters values,evaluate parameters values code =
    evaluate (replacementParameters bases parameters values) (NaturalSubstitute.replacementValues naturals values) original

private def substituteAtom (variables : Nat) (bases : List (Parameter × Code)) (naturals : List Form)
    (atom : Atom) : WorkM (Substituted bases naturals [atom]) := do
  match atom with
  | .fixed atom => pure ⟨[.fixed atom],by intro parameters values; rfl⟩
  | .parameter parameter =>
    match found : bases.find? (·.1 == parameter) with
    | none => throw .request
    | some (_,code) => pure ⟨code,by
      intro parameters values
      cases computed : evaluate parameters values code <;>
        simp [evaluate,Atom.evaluate,replacementParameters,found,computed]⟩
  | .bits width =>
    let result ← NaturalSubstitute.substitute variables width naturals
    pure ⟨[.bits result.form],by
      intro parameters values
      simp only [evaluate,Atom.evaluate,result.correct values]⟩

private def substituteLoop (variables : Nat) (bases : List (Parameter × Code)) (naturals : List Form) :
    Nat → (original : Code) → WorkM (Substituted bases naturals original) :=
  Nat.rec (fun _ => throw .limit) (fun _ next original => do
    match original with
    | [] => pure ⟨[],by intro parameters values; rfl⟩
    | atom :: rest =>
      let head ← substituteAtom variables bases naturals atom
      let remaining ← next rest
      guard (head.code.length+remaining.code.length ≤ 4096) .limit
      exactWork (Exact.charge (head.code.length+remaining.code.length+1))
      pure ⟨head.code ++ remaining.code,by
        intro parameters values
        rw [evaluate_append,head.correct,remaining.correct]
        exact (evaluate_append _ _ [atom] rest).symm⟩)

/-- Simultaneous substitution does not revisit the inserted caller types.
Original Basis identities and canonical Nat frame positions are independent. -/
def substitute (variables : Nat) (bases : List (Parameter × Code)) (naturals : List Form)
    (original : Code) : WorkM (Substituted bases naturals original) :=
  substituteLoop variables bases naturals (original.length+1) original

structure Signature {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) where
  state : GenericLexicalNatural.SomeEnvironment sources
  stateRead : ∃ before after,(StaticCallPremises.callerState signature.instantiation none).run before = (.ok state,after)
  inputs : List Read
  outputs : List Read
  inputRead : ∃ before after,((signature.original.parsedHeader.parameterTypes).mapM fun tokens => do
    let inner ← adapt (QuantumSignatureCore.quantumTokens tokens)
    readCode state signature.staticNames signature.staticNames.length 65 inner).run before = (.ok inputs,after)
  outputRead : ∃ before after,(signature.parts.clauses.mapM fun tokens => do
    let inner ← adapt (QuantumSignatureCore.quantumTokens tokens)
    readCode state signature.staticNames signature.staticNames.length 65 inner).run before = (.ok outputs,after)

def readSignature {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) : WorkM (Signature signature) := do
  let state ← NaturalAffine.witness (StaticCallPremises.callerState signature.instantiation none)
  let inputs ← NaturalAffine.witness (signature.original.parsedHeader.parameterTypes.mapM fun tokens => do
    let inner ← adapt (QuantumSignatureCore.quantumTokens tokens)
    readCode state.val signature.staticNames signature.staticNames.length 65 inner)
  let outputs ← NaturalAffine.witness (signature.parts.clauses.mapM fun tokens => do
    let inner ← adapt (QuantumSignatureCore.quantumTokens tokens)
    readCode state.val signature.staticNames signature.staticNames.length 65 inner)
  pure ⟨state.val,by with_reducible exact state.property,inputs.val,outputs.val,
    by with_reducible exact inputs.property,by with_reducible exact outputs.property⟩

end QleisliKernel.SourceTypes.SymbolicTypes
