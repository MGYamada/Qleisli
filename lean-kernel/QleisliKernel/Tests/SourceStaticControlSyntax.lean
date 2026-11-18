import QleisliKernel.SourceTypes.SourceSyntax
import QleisliKernel.SourceTypes.SourceStaticFold

/-! Original static comparisons and both untouched branch slices. These syntax
checks grant neither a chosen-instance typing rescue nor recursive access.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceStaticControlSyntax
open QleisliKernel QleisliKernel.SourceTypes

private def read (source : String) := do
  let tokens ← lexLocated source
  let checked ← QleisliKernel.SourceTypes.SourceStaticControlSyntax.read tokens
  return (⟨tokens,checked⟩ : Sigma SourceStaticControlSyntax.Checked)

#guard (read "if static n==0{q}else{f[n-1](q)}").isOk
#guard (read "if static n+1>=next[n](){h(q)}else{q}").isOk
#guard (read "if n==0{q}else{q}").toOption.isNone
#guard (read "if static n{q}else{q}").toOption.isNone
#guard (read "if static n==0{q}else{q}q").toOption.isNone
#guard (read "if static n==0{q}else{q}").toOption.map (fun checked =>
  (checked.2.parts.condition.map (·.text),checked.2.parts.thenBody.map (·.text),
    checked.2.parts.elseBody.map (·.text))) = some (["n","=","=","0"],["q"],["q"])

private def tree := do
  let tokens ← lexLocated "if static n==0{f(q)}else{g(q)}"
  let tree ← SourceSyntax.read (tokens.length+1) 0 true tokens
  return (⟨tokens,tree⟩ : Sigma SourceSyntax.Tree)
#guard tree.toOption.map (fun tree => match tree.2 with
  | .staticConditional .. => true | _ => false) = some true
#guard (tree.bind (fun packed => packed.2.calls)).toOption.map List.length = some 2

private def fold (source : String) := do
  let tokens ← lexLocated source
  let checked ← SourceStaticFoldSyntax.read tokens
  return (⟨tokens,checked⟩ : Sigma SourceStaticFoldSyntax.Checked)

#guard (fold "qfor static i in 0..n carry q=prepare(q) {let q=h(q); yield q;}").isOk
#guard (fold "for static i in carry..carry carry ()=() {yield}").isOk
#guard (fold "qfor static i in 0..n carry q=if static n==0 {q} else {q} {yield q}").isOk
#guard (fold "qfor static i in 0 . . n carry q=q {yield q;}").toOption.isNone
#guard (fold "qfor static i in 0..n carry q=q {q}").toOption.isNone
#guard (fold "qfor static i in 0..n carry q=q {yield q; h(q);}").toOption.isNone
#guard (fold "for static i in 0..n carry ()=() {yield;}").toOption.isNone

private def foldCalls (source : String) : Except String (List Nat) := do
  let tokens ← lexLocated source
  let tree ← SourceSyntax.read (tokens.length+1) 0 true tokens
  tree.calls

#guard (foldCalls "qfor static i in 0..n carry q=f(q) {let q=g(q); yield h(q);}").toOption = some [30,42,54]

private def coordinates (bounds : String) : Finite.WorkM (List (Nat × Nat)) := do
  let source := "for static i in " ++ bounds ++ " carry ()=() {yield}"
  let parsed ← Finite.lift ((fold source).mapError fun _ => Finite.Error.request)
  let sources : Sources := #[("main","pub fn route()->Unit{" ++ source ++ "}")]
  let naturals ← PhaseApplication.prepare sources
  let naturals := {naturals with environment := LexicalNatural.ofBindings naturals.helpers.val [("carry",2)]}
  let checked ← SourceStaticFold.read sources "main" naturals ["carry"] parsed.2
  (List.finRange checked.count).mapM fun step => do
    let context := checked.environment step
    let index ← LexicalNatural.read sources "main" context.helpers.val context.environment ["i","carry"]
      (.name ["i"])
    let retained ← LexicalNatural.read sources "main" context.helpers.val context.environment ["i","carry"]
      (.name ["carry"])
    return (index.result.value,retained.result.value)

#guard ((coordinates "1..carry+carry").run 1000000).1.toOption = some [(1,2),(2,2),(3,2)]
#guard ((coordinates "carry..carry").run 1000000).1.toOption = some []
#guard ((coordinates "carry..1").run 1000000).1.toOption.isNone

#print axioms SourceStaticFold.Checked.coordinate_bounds
#print axioms SourceStaticFoldSyntax.read
#print axioms StaticFoldBounds.iteration
#print axioms QleisliKernel.SourceTypes.SourceStaticControlSyntax.read
end QleisliKernel.Tests.SourceStaticControlSyntax
