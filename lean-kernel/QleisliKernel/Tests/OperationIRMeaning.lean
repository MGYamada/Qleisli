import QleisliKernel.Qirf.OperationIRMeaning

/-! Tiny exact constructor controls (at most two qubits). Supplied provider
maps are calculation inputs here, not native provider/body evidence. Original
source/IR/control binding and production dispatch require separate checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.OperationIRMeaning
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Semantics.Exact
open QleisliKernel.Qirf.OperationIRMeaning OperationDescription Finite

def sources : Sources := #[("m",
  "#![no_implicit_prelude]\npub unitary fn spin(q:Q<Unit>)->Q<Unit>{global_phase_eighth(q)}\n" ++
  "pub unitary fn idle(q:Q<Bit>)->Q<Bit>{q}\n")]

def run (description : Description) (providers : List Matrix) : Except Finite.Error Matrix :=
  ((do
    let graph ← StaticOperation.check sources (.source "m") description
    compute graph providers : Finite.WorkM Matrix).run 16000000).1

def result (description : Description) (providers : List Matrix) : Option Matrix :=
  (run description providers).toOption

def requestFailure (description : Description) (providers : List Matrix) : Bool :=
  match run description providers with | .error .request => true | _ => false

def scalar (exponent : Nat) : Matrix := ⟨1,1,[Exact.Scalar.phase exponent]⟩
def identity : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
def spin : Node := .provider "m" "spin" [] [] []
def idle : Node := .provider "m" "idle" [] [] []

-- Exact full phase survives power and inverse, including a zero-width target.
#guard result ⟨[spin,.power 0 4],1⟩ [scalar 1] == some (scalar 4)
#guard result ⟨[spin,.power 0 4],1⟩ [scalar 0] == some (scalar 0)
#guard result ⟨[spin,.inverse 0],1⟩ [scalar 1] == some (scalar 7)
#guard result ⟨[spin,.power 0 0],1⟩ [scalar 1] == some (scalar 0)
-- The inactive power still requires its original provider occurrence.
#guard requestFailure ⟨[spin,.power 0 0],1⟩ []
-- A shared DAG node is two source occurrences, with two body/map slots.
#guard result ⟨[spin,.thenOp 0 0],1⟩ [scalar 1,scalar 1] == some (scalar 2)
#guard requestFailure ⟨[spin,.thenOp 0 0],1⟩ [scalar 1]

def h : Node := .primitive .h [.bit]
#guard result ⟨[h,h,.thenOp 0 1],2⟩ [] == some identity

def leftTensor := result ⟨[h,idle,.tensor 0 1],2⟩ [identity]
def rightTensor := result ⟨[h,idle,.tensor 1 0],2⟩ [identity]
-- The source's first owner is the least significant axis.
#guard leftTensor.map (fun matrix => matrix.entry 0 1) == some halfRoot
#guard rightTensor.map (fun matrix => matrix.entry 0 1) == some Scalar.zero
#guard leftTensor != rightTensor

def scalarControl : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 1]⟩
#guard result ⟨[spin,.controlled 0],1⟩ [scalar 1] == some scalarControl

-- Conjugation uses A B A†. Phase conjugation leaves the middle exact action.
#guard result ⟨[spin,spin,.conjugate 0 1],2⟩ [scalar 1,scalar 4] == some (scalar 4)

end QleisliKernel.Tests.OperationIRMeaning
