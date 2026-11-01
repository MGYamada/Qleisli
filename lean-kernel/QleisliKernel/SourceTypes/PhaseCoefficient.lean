import QleisliKernel.Finite

/-! Exact coefficients for the existing ordinary finite phase rule.
No acceptance handle, new coefficient domain or phase approximation is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.PhaseCoefficient
open QleisliKernel QleisliKernel.Finite

structure Checked (j k : Nat) where
  denominatorBound : k ≤ 8
  canonical : j < 2^k
  integralEighth : (j*8) % (2^k) = 0
  exponent : Nat
  quotient : exponent = j*8 / (2^k)
  exponentBound : exponent < 8
  exact : exponent * (2^k) = j*8

/-- Check the denominator bound before exponentiation. The accepted domain
includes all unreduced canonical dyadics and zero at each existing k ≤ 8.
In particular, no k ≤ 3 restriction or modulo-one repair is substituted. -/
def read (j k : Nat) : WorkM (Checked j k) := do
  exactWork (Exact.charge 32)
  if denominatorBound : k ≤ 8 then
    if canonical : j < 2^k then
      if integralEighth : (j*8) % (2^k) = 0 then
        let exponent := j*8 / (2^k)
        if exponentBound : exponent < 8 then
          if exact : exponent * (2^k) = j*8 then
            return ⟨denominatorBound,canonical,integralEighth,exponent,rfl,exponentBound,exact⟩
          else throw .equation
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Reuse the existing exact eighth-root scalar; its phase is not erased. -/
def Checked.scalar {j k} (checked : Checked j k) : Semantics.Exact.Scalar :=
  Exact.Scalar.phase checked.exponent

end QleisliKernel.SourceTypes.PhaseCoefficient
