import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.Qirf.SourceProviderSubject
import QleisliKernel.Semantics.CarrierInterface

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
  | withReferences (positions : List SourceSequence.Position) (sites : List Site)
      (calls : List (SourceSequence.Position × Context))
      (branches : List (SourceSequence.Position × Context × Context)) (bodies : List (Provider × Context))
      (references : List (List (List (Provider × Context))))

/-- Construct a local context with no transported Meaning groups. The wire
decoder requires the reference field even when its value is empty. -/
def Context.mk (positions : List SourceSequence.Position) (sites : List Site)
    (calls : List (SourceSequence.Position × Context))
    (branches : List (SourceSequence.Position × Context × Context)) (bodies : List (Provider × Context)) : Context :=
  .withReferences positions sites calls branches bodies []

def Context.positions : Context → List SourceSequence.Position
  | .withReferences positions _ _ _ _ _ => positions
def Context.sites : Context → List Site
  | .withReferences _ sites _ _ _ _ => sites
def Context.calls : Context → List (SourceSequence.Position × Context)
  | .withReferences _ _ calls _ _ _ => calls
def Context.branches : Context → List (SourceSequence.Position × Context × Context)
  | .withReferences _ _ _ branches _ _ => branches
def Context.bodies : Context → List (Provider × Context)
  | .withReferences _ _ _ _ bodies _ => bodies

/-- One group list per original operation graph. Each group supplies the
quantum leaves of one original Meaning in written order. -/
def Context.references : Context → List (List (List (Provider × Context)))
  | .withReferences _ _ _ _ _ references => references

/-- Preserve the original request while passing the remaining provider slots
to the body after its original function-level operation supplies. -/
def Context.withBodies (context : Context) (bodies : List (Provider × Context)) : Context :=
  .withReferences context.positions context.sites context.calls context.branches bodies context.references

end QleisliKernel.Qirf.RuntimeContextRequest
