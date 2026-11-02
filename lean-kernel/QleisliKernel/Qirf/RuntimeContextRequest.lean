import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.Qirf.SourceProviderSubject

/-! Plain untrusted request data for complete original runtime body contexts.
The paired transport reader and common native continuations share these exact
objects. No capability, source assertion, owner map or acceptance result is
transported. Every body slot represents one independently derived occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeContextRequest
open QleisliKernel Semantics.CarrierInterface
abbrev Provider := SourceProviderSubject.Subject

structure Arm where
  implementation : Nat
  controlled : Nat
  deriving BEq, DecidableEq, Repr

structure Site where
  attached : Interface
  required : Interface
  position : SourceSequence.Position
  arms : List Arm
  deriving BEq, DecidableEq, Repr

-- Recursive data stays plain. Readers and walkers use explicit total fuel;
-- no generated partial equality or printing helper is part of this contract.
inductive Context where
  | mk (positions : List SourceSequence.Position) (sites : List Site)
      (calls : List (SourceSequence.Position × Context))
      (branches : List (SourceSequence.Position × Context × Context)) (bodies : List (Provider × Context))

def Context.positions : Context → List SourceSequence.Position
  | .mk positions _ _ _ _ => positions
def Context.sites : Context → List Site
  | .mk _ sites _ _ _ => sites
def Context.calls : Context → List (SourceSequence.Position × Context)
  | .mk _ _ calls _ _ => calls
def Context.branches : Context → List (SourceSequence.Position × Context × Context)
  | .mk _ _ _ branches _ => branches
def Context.bodies : Context → List (Provider × Context)
  | .mk _ _ _ _ bodies => bodies

end QleisliKernel.Qirf.RuntimeContextRequest
