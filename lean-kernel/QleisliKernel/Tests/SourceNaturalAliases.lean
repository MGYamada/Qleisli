import QleisliKernel.SourceTypes.LexicalNatural

/-! Small controls for per-expression static helper resolution.
Complete original-body authentication remains the enclosing source reader duty.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceNaturalAliases
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite
open QleisliKernel.Semantics.SourceNatural

def sources : Sources := #[ ("main",
  "static fn f[const n:Nat]()->Nat{n+1} static fn g[const n:Nat]()->Nat{n+2} " ++
  "static fn first[const a:Nat,const b:Nat]()->Nat{a} " ++
  "static fn subtract[const a:Nat,const b:Nat]()->Nat requires a<=b{b-a}") ]

def reads : WorkM (List Nat) := do
  let entries ← NaturalHelpers.prepare sources
  let initial := LexicalNatural.empty entries
  let alias ← LexicalNatural.bind sources "main" entries initial [] "alias" (.call ["f"] [.number 1])
  let later ← LexicalNatural.read sources "main" entries alias.environment ["alias"]
    (.call ["g"] [.name ["alias"]])
  let withoutCall ← LexicalNatural.read sources "main" entries alias.environment ["alias"]
    (.add (.name ["alias"]) (.number 1))
  let shadow ← LexicalNatural.bind sources "main" entries alias.environment ["alias"] "f" (.number 9)
  let original ← LexicalNatural.read sources "main" entries shadow.environment ["f","alias"] (.name ["alias"])
  let current ← LexicalNatural.read sources "main" entries shadow.environment ["f","alias"] (.name ["f"])
  return [later.result.value,withoutCall.result.value,original.result.value,current.result.value]

#guard (reads.run 10000000).1.toOption == some [4,3,2,9]

def shadowedCall : WorkM Nat := do
  let entries ← NaturalHelpers.prepare sources
  let value ← LexicalNatural.bind sources "main" entries (LexicalNatural.empty entries) [] "f" (.number 9)
  let result ← LexicalNatural.read sources "main" entries value.environment ["f"] (.call ["f"] [.number 1])
  return result.result.value
#guard (shadowedCall.run 10000000).1.toOption == none

def direct (expression : Expr) : Option Nat :=
  ((do
    let entries ← NaturalHelpers.prepare sources
    let result ← LexicalNatural.read sources "main" entries (LexicalNatural.empty entries) [] expression
    return result.result.value : WorkM Nat).run 10000000).1.toOption

#guard direct (.call ["subtract"] [.number 3,.number 5]) == some 2
#guard direct (.call ["subtract"] [.number 5,.number 3]) == none
#guard direct (.call ["first"] [.number 1,.sub (.number 4294967296) (.number 1)]) == none
#guard direct (.mul (.number 0) (.sub (.number 4294967296) (.number 4294967295))) == none

def blocked : Option Nat :=
  ((do
    let entries ← NaturalHelpers.prepare sources
    let result ← LexicalNatural.bind sources "main" entries (LexicalNatural.empty entries) ["q"] "q" (.number 1)
    return result.checked.result.value : WorkM Nat).run 10000000).1.toOption
#guard blocked == none

-- Initializers are evaluated once, as ordinary static bindings specify.
-- Replaying the previous +0 tree at every read would grow exponentially.
def chain : Option Nat :=
  ((do
    let entries ← NaturalHelpers.prepare sources
    let (_,environment,scope) ← (List.range 21).foldlM
      (fun (previous,environment,scope) index => do
        let name := "n" ++ toString index
        let expression := if index == 0 then Expr.number 1
          else Expr.add (.name [previous]) (.number 0)
        let bound ← LexicalNatural.bind sources "main" entries environment scope name expression
        return (name,bound.environment,name :: scope))
      ("",LexicalNatural.empty entries,([] : List String))
    let result ← LexicalNatural.read sources "main" entries environment scope (.name ["n20"])
    return result.result.value : WorkM Nat).run 1000000).1.toOption
#guard chain == some 1

end QleisliKernel.Tests.SourceNaturalAliases
