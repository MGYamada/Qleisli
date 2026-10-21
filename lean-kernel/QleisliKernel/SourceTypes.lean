import QleisliKernel.SourceTypes.Declarations
import QleisliKernel.SourceTypes.NaturalSyntax
import QleisliKernel.SourceTypes.NaturalAffine
import QleisliKernel.SourceTypes.NaturalConstraints
import QleisliKernel.SourceTypes.NaturalPredicates
import QleisliKernel.SourceTypes.NaturalHeaders
import QleisliKernel.SourceTypes.NaturalCatalog
import QleisliKernel.SourceTypes.NaturalNormalize
import QleisliKernel.SourceTypes.NaturalFrames
import QleisliKernel.SourceTypes.NaturalSubstitute
import QleisliKernel.SourceTypes.NaturalPrepare
import QleisliKernel.SourceTypes.NaturalHelpers
import QleisliKernel.FiniteCarrier

/-! Reconstruct a nominal carrier from original top-level source declarations.
The independent reader preserves canonical declarations through explicit imports
and public reexports. Existing field Nat expressions use original checked helpers
and exact symbolic arithmetic. It grants no source-function preservation guarantee.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes
open Semantics.FiniteCarrier

private structure Parts where
  stack : List String := []
  current : List String := []
  parts : List (List String) := []

private def part (s : Parts) (token : String) : Except String Parts := do
  if token == "(" || token == "<" || token == "[" then
    return {s with stack := (if token == "(" then ")" else if token == "[" then "]" else ">") :: s.stack,current := token :: s.current}
  if token == ")" || token == ">" || token == "]" then
    let expected :: rest := s.stack | throw "unmatched type delimiter"
    if token != expected then throw "mismatched type delimiter"
    return {s with stack := rest,current := token :: s.current}
  if token == "," && s.stack.isEmpty then
    if s.current.isEmpty then throw "empty member"
    return {s with current := [],parts := s.current.reverse :: s.parts}
  return {s with current := token :: s.current}

def splitMembers (tokens : List String) : Except String (List (List String)) := do
  let s ← tokens.foldlM part {}
  if !s.stack.isEmpty then throw "incomplete member type"
  return (if s.current.isEmpty then s.parts else s.current.reverse :: s.parts).reverse

/-- Origin lookup is canonical: an alias never becomes a new declaration. -/
def lookup (sources : Sources) (moduleName name : String) : Except String (String × Declaration) := do
  let (source,decl) ← originalBinding sources moduleName name
  if decl.kind != "enum" && decl.kind != "struct" then throw "source name is not a finite type"
  return (source,decl)

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

private theorem adapt_value {α : Type} (value : Except String α) (result : α) (work left : Nat)
    (ok : (adapt value).run work = (.ok result,left)) : value = .ok result := by
  have bound := (Finite.lift_success _ _ _ _ ok).1
  cases value <;> simp_all [Except.mapError]

private def load (sources : Sources) (moduleName name : String) : Finite.WorkM (String × Declaration) := do
  Finite.exactWork (Exact.charge ((sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum + name.utf8ByteSize + moduleName.utf8ByteSize + 1))
  adapt (lookup sources moduleName name)

private def combine (first second : Basis) : Finite.WorkM Basis := do
  Finite.guard (first.length + second.length ≤ 128) .limit
  pure (first ++ second)

/-- Canonical decimal reading for the existing zero-to-six width profile.
The common grammar permits a leading zero only for the literal `0`. Bound every
prefix before extending it; introduce no general Nat-expression or const form. -/
def literalWidth (literal : String) : Finite.WorkM Nat := do
  Finite.guard (!literal.isEmpty) .request
  Finite.exactWork (Exact.charge (literal.utf8ByteSize + 1))
  let chars := literal.toList
  Finite.guard (chars == ['0'] || chars.head? != some '0') .request
  chars.foldlM (fun value char => do
    Finite.guard ('0' ≤ char && char ≤ '9') .request
    let width := value * 10 + (char.toNat - '0'.toNat)
    Finite.guard (width ≤ 6) .limit
    pure width) 0

private structure Readers where
  ty : Sources → String → List String → Finite.WorkM Basis
  decl : Sources → String → String → Finite.WorkM Basis

private structure WidthExpression (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) where
  expression : Semantics.SourceNatural.Expr
  bindings : List (Semantics.SourceNatural.Path × NaturalCatalog.Key)
  parsed : NaturalSyntax.read tokens = .ok expression
  resolved : ∃ work left,
    (NaturalCatalog.expressionBindings sources (helpers.map (·.original)) moduleName expression).run work = (.ok bindings,left)

private def widthExpression (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) :
    Finite.WorkM (WidthExpression sources helpers moduleName tokens) := do
  Finite.exactWork (Exact.charge ((tokens.map String.utf8ByteSize).sum+tokens.length+1))
  let parsedValue ← NaturalAffine.witness (adapt (NaturalSyntax.read tokens))
  have parsed : NaturalSyntax.read tokens = .ok parsedValue.val := by
    obtain ⟨work,left,ok⟩ := parsedValue.property
    exact adapt_value _ _ _ _ ok
  let bound ← NaturalAffine.witness (NaturalCatalog.expressionBindings sources (helpers.map (·.original)) moduleName parsedValue.val)
  return ({expression := parsedValue.val,bindings := bound.val,parsed := parsed,
           resolved := by with_reducible exact bound.property} : WidthExpression sources helpers moduleName tokens)

private structure CheckedWidth (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) where
  original : WidthExpression sources helpers moduleName tokens
  value : Nat
  meaning : Semantics.SourceNatural.Value (NaturalFrames.names ⟨[]⟩ (fun _ => 0))
    (NaturalHelpers.interpretation helpers original.bindings) original.expression value

private def naturalWidth (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) :
    Finite.WorkM (CheckedWidth sources helpers moduleName tokens) := do
  let original ← widthExpression sources helpers moduleName tokens
  let frame : NaturalFrames.Frame := ⟨[]⟩
  let calls := NaturalHelpers.interpretation helpers original.bindings
  let context ← NaturalFrames.initial frame
  let result ← NaturalNormalize.normalize 0 context
    ⟨NaturalFrames.readName frame calls (fun _ held => held),
      (NaturalHelpers.reader frame helpers original.bindings).read context (fun _ held => held)⟩ 128 original.expression
  if shape : result.form.coefficients = [] then
    if bounds : 0 ≤ result.form.constant ∧ result.form.constant ≤ 4294967295 then
      let width := result.form.constant.toNat
      Finite.guard (width ≤ 6) .limit
      return ⟨original,width,by
        obtain ⟨n,computed,same⟩ := result.correct (fun _ => 0) (by intro _ _; exact Int.le_refl 0)
        have integer : result.form.constant = (n : Int) := by
          simpa only [Semantics.SourceAffine.Form.evaluate,shape,Semantics.SourceAffine.dot_nil,Int.add_zero] using same
        have equal : width = n := by omega
        rw [equal]
        exact Semantics.SourceNatural.evaluate_value _ _ _ _ _ computed⟩
    else throw .limit
  else throw .request

private def readers (helpers : List NaturalHelpers.Entry) : Nat → Readers :=
  Nat.rec ⟨fun _ _ _ => throw .limit,fun _ _ _ => throw .limit⟩
    (fun _ recurse => ⟨fun sources current tokens => do
      match tokens with
      | ["Unit"] => return [.unit]
      | ["Bit"] => return [.bit]
      | "Bits" :: "<" :: rest =>
        Finite.guard (rest.getLast? == some ">") .request
        return [.bits (← naturalWidth sources helpers current rest.dropLast).value]
      | "(" :: rest =>
        if rest.getLast? != some ")" || rest.dropLast.getLast? == some "," then
          throw .request
        let parts ← adapt (splitMembers rest.dropLast)
        Finite.guard (2 ≤ parts.length && parts.length ≤ 64) .limit
        let children ← parts.foldlM (fun acc part => do combine acc (← recurse.ty sources current part)) []
        combine [if parts.length == 2 then Atom.pair else .tuple parts.length] children
      | _ =>
        let original ← resolveReference sources current tokens
        recurse.decl sources original.moduleName original.declaration.name,
      fun sources moduleName name => do
        let (source,decl) ← load sources moduleName name
        let origin : Origin := ⟨moduleName,name,source⟩
        let members ← adapt (splitMembers decl.body)
        Finite.guard (members.length ≤ 64) .limit
        if decl.kind == "enum" then
          let names ← members.mapM fun tokens => do
            let [name] := tokens | throw .request
            Finite.guard (identifier name) .request
            return name
          Finite.guard (!names.isEmpty && FiniteCarrier.namesValid names) .request
          return [.enumeration origin names]
        let (names,children) ← members.foldlM (fun (names,children) tokens => do
          let tokens := if tokens.head? == some "pub" then tokens.drop 1 else tokens
          let field :: ":" :: ty := tokens | throw .request
          Finite.guard (identifier field) .request
          return (names ++ [field],← combine children (← recurse.ty sources moduleName ty))) ([],[])
        Finite.guard (FiniteCarrier.namesValid names) .request
        combine [.record origin names] children⟩)

/-- Reconstruct from actual source, never by finding a matching producer row.
The existing carrier reader separately bounds the complete tree/code. -/
private def readNominal (helpers : List NaturalHelpers.Entry) (sources : Sources)
    (origin : Origin) (nodes : Nat) : Finite.WorkM Basis := do
  let (source,_) ← load sources origin.moduleName origin.declarationName
  Finite.exactWork (Exact.charge (origin.source.utf8ByteSize + 1))
  Finite.guard (source == origin.source) .request
  -- A matching subtree cannot contain more nodes than the supplied complete
  -- tree. Two reader steps per node suffice; the existing depth ceiling remains.
  (readers helpers (min 65 (2*nodes+1))).decl sources origin.moduleName origin.declarationName

def nominal (sources : Sources) (origin : Origin) (nodes : Nat := 128) : Finite.WorkM Basis := do
  readNominal (← NaturalHelpers.prepare sources) sources origin nodes

private def checkAtom (helpers : List NaturalHelpers.Entry) (sources : Sources) (nodes : Nat) (remaining : Basis) (atom : Atom) :
    Finite.WorkM Basis := do
  match atom with
  | .enumeration origin _ | .record origin _ =>
    let original ← readNominal helpers sources origin nodes
    Finite.guard (remaining.take original.length == original) .request
  | _ => pure ()
  pure (remaining.drop 1)

/-- Compare every nominal subtree to its independently reconstructed source
tree. Prefix validation occurs first, so a neighbour cannot supply missing nodes. -/
private def sourceHelpers (sources : Sources) : Finite.WorkM (List NaturalHelpers.Entry) := do
  Finite.guard (sources.size ≤ 128 && (sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum ≤ 1048576) .limit
  NaturalHelpers.prepare sources

private def checkBasis (helpers : List NaturalHelpers.Entry) (sources : Sources) (basis : Basis) : Finite.WorkM Unit := do
  let _ ← FiniteCarrier.read basis
  let _ ← basis.foldlM (checkAtom helpers sources basis.length) basis
  pure ()

def check (sources : Sources) (basis : Basis) : Finite.WorkM Unit := do
  checkBasis (← sourceHelpers sources) sources basis

/-- Validate one original helper environment for every ordered owner forest.
No caller-supplied checked template can enter this public source boundary. -/
def checkMany (sources : Sources) (forests : List Basis) : Finite.WorkM Unit := do
  let helpers ← sourceHelpers sources
  forests.forM (checkBasis helpers sources)

private theorem load_value (sources : Sources) (moduleName name : String)
    (result : String × Declaration) (work left : Nat)
    (ok : (load sources moduleName name).run work = (.ok result,left)) :
    lookup sources moduleName name = .ok result := by
  obtain ⟨_,middle,_,bound⟩ := Finite.bind_success _ _ _ _ _ ok
  exact adapt_value _ _ _ _ bound

/-- Success names the original module/declaration lookup and exact source
bytes. It does not assert that the function body has its source meaning. -/
private theorem readNominal_original (helpers : List NaturalHelpers.Entry) (sources : Sources) (origin : Origin) (nodes : Nat)
    (result : Basis) (work left : Nat)
    (ok : (readNominal helpers sources origin nodes).run work = (.ok result,left)) :
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl) := by
  obtain ⟨entry,a,loaded,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,c,same,_⟩ := Finite.bind_success _ _ _ _ _ h
  have equal := beq_iff_eq.mp (Finite.guard_success _ _ _ _ same).1
  refine ⟨entry.2,?_⟩
  have sameEntry : (origin.source,entry.2) = entry := by
    apply Prod.ext
    · exact equal.symm
    · rfl
  rw [sameEntry]
  exact load_value _ _ _ _ _ _ loaded

theorem nominal_original (sources : Sources) (origin : Origin) (nodes : Nat)
    (result : Basis) (work left : Nat)
    (ok : (nominal sources origin nodes).run work = (.ok result,left)) :
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl) := by
  obtain ⟨helpers,middle,_,read⟩ := Finite.bind_success _ _ _ _ _ ok
  exact readNominal_original helpers _ _ _ _ _ _ read

/-- Literal source-declaration identity only, not source-function correctness. -/
def OriginalDeclaration (sources : Sources) : Atom → Prop
  | .enumeration origin _ | .record origin _ =>
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl)
  | _ => True

private theorem checkAtom_original (helpers : List NaturalHelpers.Entry) (sources : Sources) (nodes : Nat) (remaining : Basis)
    (atom : Atom) (result : Basis) (work left : Nat)
    (ok : (checkAtom helpers sources nodes remaining atom).run work = (.ok result,left)) :
    OriginalDeclaration sources atom := by
  cases atom <;> try trivial
  all_goals
    obtain ⟨original,after,read,_⟩ := Finite.bind_success _ _ _ _ _ ok
    exact readNominal_original helpers _ _ _ _ _ _ read

private theorem fold_original (helpers : List NaturalHelpers.Entry) (sources : Sources) (nodes : Nat) (atoms remaining result : Basis)
    (work left : Nat)
    (ok : (atoms.foldlM (checkAtom helpers sources nodes) remaining).run work = (.ok result,left)) :
    ∀ atom ∈ atoms, OriginalDeclaration sources atom := by
  induction atoms generalizing remaining work with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,after,head,tail⟩ := Finite.bind_success _ _ _ _ _ ok
    intro atom member
    rcases List.mem_cons.mp member with same | member
    · subst atom
      exact checkAtom_original helpers _ _ _ _ _ _ _ head
    · exact ih next after tail atom member

theorem check_original_declarations (sources : Sources) (basis : Basis) (work left : Nat)
    (ok : (check sources basis).run work = (.ok (),left)) :
    ∀ atom ∈ basis, OriginalDeclaration sources atom := by
  obtain ⟨_,a,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  unfold checkBasis at h
  obtain ⟨_,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨remaining,c,fold,_⟩ := Finite.bind_success _ _ _ _ _ h
  exact fold_original _ sources basis.length basis basis remaining b c fold

end QleisliKernel.SourceTypes
