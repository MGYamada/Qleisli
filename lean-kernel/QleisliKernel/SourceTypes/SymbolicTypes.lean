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

structure Closed (basis : Semantics.FiniteCarrier.Basis) where
  code : Code
  correct : ∀ parameters values,evaluate parameters values code = some basis

private structure ClosedAtom (original : Semantics.FiniteCarrier.Atom) where
  atom : Atom
  correct : ∀ parameters values,atom.evaluate parameters values = some [original]

private def closedAtom (variables : Nat) (original : Semantics.FiniteCarrier.Atom) : WorkM (ClosedAtom original) := do
  match original with
  | .bits width =>
    let constant ← NaturalAffine.witness (NaturalAffine.constant variables width)
    pure ⟨.bits constant.val,by
      intro parameters values
      obtain ⟨before,after,ran⟩ := constant.property
      simp only [Atom.evaluate,NaturalAffine.constant_meaning _ _ _ _ _ ran]
      simp⟩
  | atom => pure ⟨.fixed atom,by intro parameters values; rfl⟩

private def closedLoop (variables : Nat) :
    Nat → (basis : Semantics.FiniteCarrier.Basis) → WorkM (Closed basis) :=
  Nat.rec (fun _ => throw .limit) (fun _ next basis => do
    match basis with
    | [] => pure ⟨[],by intro parameters values; rfl⟩
    | atom :: rest =>
      let head ← closedAtom variables atom
      let remaining ← next rest
      pure ⟨head.atom :: remaining.code,by
        intro parameters values
        simp [evaluate,head.correct,remaining.correct]⟩)

/-- Lift an independently checked closed type without changing its meaning.
No nominal origin, tuple node or zero-width field is replaced by bit width. -/
def ofClosed (variables : Nat) (basis : Semantics.FiniteCarrier.Basis) : WorkM (Closed basis) :=
  closedLoop variables (basis.length+1) basis

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
      let formal : Option StaticHeaders.Formal := match tokens with
        | [name] => state.prepared.original.header.formals.find?
          (fun (formal : StaticHeaders.Formal) => formal.name == name && formal.ordinal < ordinal)
        | _ => none
      match formal with
      | some formal =>
        guard (formal.kind == StaticHeaders.Kind.basis) .request
        pure ⟨[.parameter ⟨state.owner,state.name,formal.ordinal⟩],[]⟩
      | none =>
        let helpers : NaturalHelpers.Checked sources := ⟨state.prepared.helpers,state.prepared.helpersPrepared⟩
        let query ← typeExpressionWithCheckedHelpers sources helpers state.owner tokens
        let closed ← ofClosed (StaticHeaders.frame state.prepared.original).binders.length query.basis
        let rows ← NaturalRows.typeRead sources state.owner state.prepared.helpers [] tokens query
        pure ⟨closed.code,rows⟩)

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
    let proved ← NaturalPredicates.implies state.environment.context a .eq b
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

/-- Failure to prove exact original equality leaves two ports. Limits and
arithmetic failures are never turned into a successful comparison result. -/
def optionalEquality {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (left right : Code) : WorkM (Option (NaturalPredicates.Established (∀ values,
      StaticCallPremises.Meaning state values → ∀ parameters,
      evaluate parameters values left = evaluate parameters values right))) := do
  try
    pure (some (← equate state left right))
  catch error =>
    match error with
    | .request => pure none
    | error => throw error

structure Ports (sources : Sources) where
  state : GenericLexicalNatural.SomeEnvironment sources
  scope : List String
  ordinal : Nat
  inputTokens : List String
  outputTokens : List String
  input : Checked state scope ordinal inputTokens
  output : Checked state scope ordinal outputTokens
  same : Option (NaturalPredicates.Established (∀ values,
    StaticCallPremises.Meaning state values → ∀ parameters,
    evaluate parameters values input.result.code = evaluate parameters values output.result.code))

def readPorts {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (ordinal : Nat) (inputTokens outputTokens : List String) : WorkM (Ports sources) := do
  let input ← read state scope ordinal inputTokens
  let output ← read state scope ordinal outputTokens
  let same ← optionalEquality state input.result.code output.result.code
  pure ⟨state,scope,ordinal,inputTokens,outputTokens,input,output,same⟩

structure Refinement {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (ordinal : Nat) (inputTokens outputTokens : List String)
    (targetInput targetOutput : Semantics.FiniteCarrier.Basis) where
  input : Checked state scope ordinal inputTokens
  output : Checked state scope ordinal outputTokens
  inputMeaning : ∀ values,StaticCallPremises.Meaning state values → ∀ parameters,
    evaluate parameters values input.result.code = some targetInput
  outputMeaning : ∀ values,StaticCallPremises.Meaning state values → ∀ parameters,
    evaluate parameters values output.result.code = some targetOutput

def checkRefinement {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (ordinal : Nat) (inputTokens outputTokens : List String)
    (targetInput targetOutput : Semantics.FiniteCarrier.Basis) :
    WorkM (Refinement state scope ordinal inputTokens outputTokens targetInput targetOutput) := do
  let input ← read state scope ordinal inputTokens
  let output ← read state scope ordinal outputTokens
  let variables := (StaticHeaders.frame state.prepared.original).binders.length
  let targetInputCode ← ofClosed variables targetInput
  let targetOutputCode ← ofClosed variables targetOutput
  let inputEquality ← equate state input.result.code targetInputCode.code
  let outputEquality ← equate state output.result.code targetOutputCode.code
  pure ⟨input,output,by
    intro values held parameters
    exact (inputEquality.proof values held parameters).trans (targetInputCode.correct parameters values),by
    intro values held parameters
    exact (outputEquality.proof values held parameters).trans (targetOutputCode.correct parameters values)⟩

structure SomeRefinement (sources : Sources) where
  state : GenericLexicalNatural.SomeEnvironment sources
  scope : List String
  ordinal : Nat
  inputTokens : List String
  outputTokens : List String
  targetInput : Semantics.FiniteCarrier.Basis
  targetOutput : Semantics.FiniteCarrier.Basis
  checked : Refinement state scope ordinal inputTokens outputTokens targetInput targetOutput

def replacementParameters (bases : List (Parameter × Code)) (parameters : Parameters) (values : Valuation) : Parameters :=
  fun binderKey => do
    let (_,code) ← bases.find? (·.1 == binderKey)
    evaluate parameters values code

structure Substituted (bases : List (Parameter × Code)) (naturals : List Form) (original : Code) where
  code : Code
  correct : ∀ parameters values,evaluate parameters values code =
    evaluate (replacementParameters bases parameters values) (NaturalSubstitute.replacementValues naturals values) original

private def substituteAtom (variables : Nat) (bases : List (Parameter × Code)) (naturals : List Form)
    (atom : Atom) : WorkM (Substituted bases naturals [atom]) := do
  match atom with
  | .fixed atom => pure ⟨[.fixed atom],by intro parameters values; rfl⟩
  | .parameter binderKey =>
    match found : bases.find? (·.1 == binderKey) with
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

def readQuantumTypes {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (clauses : List (List String)) : WorkM (List Read) :=
  clauses.mapM fun tokens => do
    let inner ← adapt (QuantumSignatureCore.quantumTokens tokens)
    readCode state scope scope.length 65 inner

structure Signature {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) where
  state : GenericLexicalNatural.SomeEnvironment sources
  stateRead : ∃ before after,(StaticCallPremises.callerState signature.instantiation none).run before = (.ok state,after)
  inputs : List Read
  outputs : List Read
  inputRead : ∃ before after,
    (readQuantumTypes state signature.staticNames signature.original.parsedHeader.parameterTypes).run before = (.ok inputs,after)
  outputRead : ∃ before after,
    (readQuantumTypes state signature.staticNames signature.parts.clauses).run before = (.ok outputs,after)

def readSignature {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) : WorkM (Signature signature) := do
  let state ← NaturalAffine.witness (StaticCallPremises.callerState signature.instantiation none)
  let inputs ← NaturalAffine.witness (readQuantumTypes state.val signature.staticNames signature.original.parsedHeader.parameterTypes)
  let outputs ← NaturalAffine.witness (readQuantumTypes state.val signature.staticNames signature.parts.clauses)
  pure ⟨state.val,by with_reducible exact state.property,inputs.val,outputs.val,
    by with_reducible exact inputs.property,by with_reducible exact outputs.property⟩

end QleisliKernel.SourceTypes.SymbolicTypes
