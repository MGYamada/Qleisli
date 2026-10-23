import QleisliKernel.SourceTypes.Members

/-! Exact statement/proof probes. These refer to the actual candidate
reader and theorem declarations, not locally assumed successes or substitute
functions. Copyright 2026 Qleisli Project Contributors. Apache-2.0. -/
namespace MemberBoundaryProbes
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.Members

#check (readOriginal_facts :
  ∀ (sources : Sources) (moduleName declarationName : String) (result : Catalogue)
    (work left : Nat),
    (readOriginal sources moduleName declarationName).run work = (.ok result,left) →
      Boundary sources moduleName declarationName result ∧ ReaderBindings sources result)
#check (readOriginal_boundary :
  ∀ (sources : Sources) (moduleName declarationName : String) (result : Catalogue)
    (work left : Nat),
    (readOriginal sources moduleName declarationName).run work = (.ok result,left) →
      Boundary sources moduleName declarationName result)
#check (LocatedFacts.checkOrdered_sound :
  ∀ (bytes : ByteArray) (lower : Nat) (tokens : List LocatedToken),
    LocatedFacts.checkOrdered bytes lower tokens = true →
      LocatedFacts.OrderedSlices bytes lower tokens)

-- Direct conclusions expose byte and member-name bindings without a success
-- predicate hidden inside the advertised property.
example (sources : Sources) (moduleName declarationName : String) (result : Catalogue)
    (work left : Nat)
    (ok : (readOriginal sources moduleName declarationName).run work = (.ok result,left)) :
    sources.toList.filter (fun row => row.1 == moduleName) = [(moduleName,result.origin.source)] ∧
      LocatedFacts.OrderedSlices result.origin.source.toUTF8 0
        (result.occurrence.header ++ [result.occurrence.openBrace] ++
          result.occurrence.body ++ [result.occurrence.closeBrace]) := by
  have actual := readOriginal_boundary sources moduleName declarationName result work left ok
  exact ⟨actual.sourceRows,actual.located⟩

#print Boundary
#print ReaderBindings
#print PartMember
#print member_refines
#print axioms LocatedFacts.checkOrdered_sound
#print axioms member_refines
#print axioms readOriginal_facts
#print axioms readOriginal_boundary
end MemberBoundaryProbes
