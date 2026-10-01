import QleisliKernel.Semantics.Exact

/-! Data for the existing finite circuit/encoding contract. No acceptance,
arithmetic, producer receipt or work policy occurs in this reference module.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Finite
open Exact

/-- Prefix spelling of the legacy Unit/Bit/Pair/arity-preserving Tuple tree. -/
inductive Atom where
  | unit | bit | pair | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr
abbrev Basis := List Atom

def width (basis : Basis) : Nat := (basis.filter (· == .bit)).length

structure Control where
  index : Nat
  whenOne : Bool
  deriving BEq, DecidableEq, Repr

inductive Action where
  | hadamard (target : Nat)
  | monomial (indices permutation phases : List Nat)
  | contract (indices : List Nat) (dependency : Nat) (adjoint : Bool)
  deriving BEq, DecidableEq, Repr

structure Step where
  controls : List Control
  action : Action
  deriving BEq, DecidableEq, Repr

structure Circuit where
  basis : Basis
  steps : List Step
  deriving BEq, DecidableEq, Repr

structure Encoding where
  logical : Basis
  physical : Basis
  map : Matrix
  deriving BEq, DecidableEq, Repr

structure Contract where
  input : Encoding
  output : Encoding
  logical : Matrix
  deriving BEq, DecidableEq, Repr

structure DyadicDescription where
  numerator : String
  denominatorBits : Nat
  deriving BEq, DecidableEq, Repr

structure MatrixDescription where
  rows : Nat
  cols : Nat
  entries : List (List DyadicDescription)
  deriving BEq, DecidableEq, Repr

/-- Original dependency data, not an evidence or success flag. The enclosing
checker freshly derives and binds its interpretation. -/
structure Dependency where
  signature : Basis
  meaning : Matrix
  deriving BEq, DecidableEq, Repr

def bit (label axis : Nat) : Nat := label / 2^axis % 2

def gather (label : Nat) (axes : List Nat) : Nat :=
  ((axes.zipIdx).map (fun (axis, place) => bit label axis * 2^place)).sum

def scatter (label : Nat) (axes : List Nat) (value : Nat) : Nat :=
  (axes.zipIdx).foldl (fun result (axis, place) =>
    result - bit result axis * 2^axis + bit value place * 2^axis) label

def enabled (controls : List Control) (label : Nat) : Bool :=
  controls.all fun c => (bit label c.index == 1) == c.whenOne

deriving instance ReflBEq, LawfulBEq for Atom, Control, Action, Step, Circuit, Encoding, Contract, Dependency
structure Evidence where
  circuit : Circuit
  claim : Contract
  deriving BEq, DecidableEq, Repr

structure Artifact where
  evidence : List Evidence
  root : Nat
  deriving BEq, DecidableEq, Repr

end QleisliKernel.Semantics.Finite
