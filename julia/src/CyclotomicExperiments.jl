# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
module CyclotomicExperiments

using Cyclotomics

export exact_root, exact_scalar

const QQ = Rational{BigInt}

"""The distinguished n-th root to exponent k, with exact big rational coefficients."""
function exact_root(n::Integer, k::Integer = 1)
    n > 0 || throw(ArgumentError("the root order must be positive"))
    return Cyclotomic{QQ}(E(Int(n), Int(mod(k, n))))
end

"""Embed an integer or rational into the exact cyclotomic coefficient field."""
exact_scalar(x::Union{Integer, Rational}) = QQ(x) * exact_root(1)

end
