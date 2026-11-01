import QleisliKernel.Qirf.SelectionContract

/-! Untrusted literal requests for each original source-body occurrence.
Children are ordered by the independently read source, rather than shared by
an evidence index: distinct static instances must each check their own body.
This datatype supplies no source name, meaning, success receipt or capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceContextRequest

abbrev Position := SourceSequence.Position
abbrev Site := SelectionContract.Request

inductive Context where
  | mk (positions : List Position) (sites : List Site)
      (calls : List (Position × Context)) (bodies : List Context)
  deriving BEq, Repr

def Context.positions : Context → List Position
  | .mk positions _ _ _ => positions

def Context.sites : Context → List Site
  | .mk _ sites _ _ => sites

def Context.calls : Context → List (Position × Context)
  | .mk _ _ calls _ => calls

def Context.bodies : Context → List Context
  | .mk _ _ _ bodies => bodies

end QleisliKernel.Qirf.SourceContextRequest
