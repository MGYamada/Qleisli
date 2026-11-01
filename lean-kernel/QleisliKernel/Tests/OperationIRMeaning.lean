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

def scalar (exponent : Nat) : Matrix := ⟨1,1,[Exact.Scalar.phase exponent]⟩
def identity : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
def spin : Node := .provider "m" "spin" [] [] []
def idle : Node := .provider "m" "idle" [] [] []

-- Exact full phase survives power and inverse, including a zero-width target.
#guard run ⟨[spin,.power 0 4],1⟩ [scalar 1] == .ok (scalar 4)
#guard run ⟨[spin,.power 0 4],1⟩ [scalar 0] == .ok (scalar 0)
#guard run ⟨[spin,.inverse 0],1⟩ [scalar 1] == .ok (scalar 7)
#guard run ⟨[spin,.power 0 0],1⟩ [scalar 1] == .ok (scalar 0)
-- The inactive power still requires its original provider occurrence.
#guard run ⟨[spin,.power 0 0],1⟩ [] == .error .request
-- A shared DAG node is two source occurrences, with two body/map slots.
#guard run ⟨[spin,.thenOp 0 0],1⟩ [scalar 1,scalar 1] == .ok (scalar 2)
#guard run ⟨[spin,.thenOp 0 0],1⟩ [scalar 1] == .error .request

def h : Node := .primitive .h [.bit]
#guard run ⟨[h,h,.thenOp 0 1],2⟩ [] == .ok identity

def leftTensor := run ⟨[h,idle,.tensor 0 1],2⟩ [identity]
def rightTensor := run ⟨[h,idle,.tensor 1 0],2⟩ [identity]
-- The source's first owner is the least significant axis.
#guard leftTensor.map (fun matrix => matrix.entry 0 1) == .ok halfRoot
#guard rightTensor.map (fun matrix => matrix.entry 0 1) == .ok Scalar.zero
#guard leftTensor != rightTensor

def scalarControl : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 1]⟩
#guard run ⟨[spin,.controlled 0],1⟩ [scalar 1] == .ok scalarControl

-- Conjugation uses A B A†. Phase conjugation leaves the middle exact action.
#guard run ⟨[spin,spin,.conjugate 0 1],2⟩ [scalar 1,scalar 4] == .ok (scalar 4)

end QleisliKernel.Tests.OperationIRMeaning
