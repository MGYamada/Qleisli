import QleisliKernel.Semantics.Finite

/-! Complete finite result-type data for the observing contract family.
Ordinary Unit/Bit/Bits are distinct from quantum owners. Prefix products keep
the entire tuple tree and every zero-width owner. No acceptance or work policy.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.InstrumentContract

inductive ResultAtom where
  | unit | bit | bits (width : Nat)
  | quantum (basis : Finite.Basis)
  | pair | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

structure Signature where
  input : Finite.Basis
  result : List ResultAtom
  deriving BEq, DecidableEq, Repr

structure Projection where
  quantum : List Finite.Basis
  classicalBits : Nat
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for ResultAtom, Signature, Projection

end QleisliKernel.Semantics.InstrumentContract
