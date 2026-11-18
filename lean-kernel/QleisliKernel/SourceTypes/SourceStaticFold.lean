import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.SourceStaticFoldSyntax

/-! Concrete coordinates of one already symbolically checked static fold.
The written bounds use the enclosing lexical environment. Each coordinate
extends that exact environment and retains the common affine body premises.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceStaticFold
open Finite

structure Checked (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) {tokens} (written : SourceStaticFoldSyntax.Checked tokens) where
  start : LexicalNatural.Checked sources caller naturals.helpers.val naturals.environment scope written.start
  stop : LexicalNatural.Checked sources caller naturals.helpers.val naturals.environment scope written.stop
  ordered : start.result.value ≤ stop.result.value
  unbound : written.parts.index.text ∉ scope
  symbolic : Option (GenericLexicalNatural.SomeEnvironment sources)
  rows : List (String × String)

def Checked.count {sources caller naturals scope tokens written}
    (checked : @Checked sources caller naturals scope tokens written) : Nat :=
  checked.stop.result.value - checked.start.result.value

def Checked.coordinate {sources caller naturals scope tokens written}
    (checked : @Checked sources caller naturals scope tokens written) (step : Fin checked.count) : Nat :=
  checked.start.result.value + step.val

theorem Checked.coordinate_bounds {sources caller naturals scope tokens written}
    (checked : @Checked sources caller naturals scope tokens written) (step : Fin checked.count) :
    checked.start.result.value ≤ checked.coordinate step ∧ checked.coordinate step < checked.stop.result.value := by
  have within := step.isLt
  have ordered := checked.ordered
  unfold coordinate
  unfold count at within
  omega

def Checked.environment {sources caller naturals scope tokens written}
    (checked : @Checked sources caller naturals scope tokens written) (step : Fin checked.count) :
    PhaseApplication.Naturals sources :=
  {naturals with
    environment := LexicalNatural.withCoordinate naturals.helpers.val naturals.environment written.parts.index.text
      (checked.coordinate step),
    staticNames := written.parts.index.text :: naturals.staticNames,
    generic := checked.symbolic,
    sourceRows := naturals.sourceRows ++ checked.rows}

def read (sources : Sources) (caller : String) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) {tokens} (written : SourceStaticFoldSyntax.Checked tokens) :
    WorkM (Checked sources caller naturals scope written) := do
  exactWork (Exact.charge (32*((tokens.map fun token => token.text.utf8ByteSize+4).sum+
    (scope.map String.utf8ByteSize).sum+1)))
  let index := written.parts.index.text
  if unbound : index ∉ scope then
    let start ← LexicalNatural.read sources caller naturals.helpers.val naturals.environment scope written.start
    let stop ← LexicalNatural.read sources caller naturals.helpers.val naturals.environment scope written.stop
    if ordered : start.result.value ≤ stop.result.value then
      let symbolic ← match naturals.generic with
        | none => pure none
        | some state => do
          guard (state.owner == caller) .request
          let (environment,_) ← GenericLexicalNatural.underFold state.prepared state.environment scope index
            written.start written.stop
          pure (some {state with environment})
      let rows ← NaturalRows.bindings sources caller naturals.helpers.val (start.bindings.val ++ stop.bindings.val)
      pure ⟨start,stop,ordered,unbound,symbolic,rows⟩
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.SourceStaticFold
