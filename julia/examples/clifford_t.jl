# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
using Cyclotomics
using LinearAlgebra

include(joinpath(@__DIR__, "..", "src", "CyclotomicExperiments.jl"))
using .CyclotomicExperiments

z = exact_root(8)
sqrt2 = z + conj(z)
h = (sqrt2 // big(2)) * map(exact_scalar, [1 1; 1 -1])
t = [exact_scalar(1) exact_scalar(0); exact_scalar(0) z]
identity = map(exact_scalar, [1 0; 0 1])

println("Coefficient type: ", valtype(z))
println("Exact sqrt(2): ", sqrt2)
println("sqrt(2)^2 = 2: ", sqrt2^2 == exact_scalar(2))
println("H†H = I: ", adjoint(h) * h == identity)
println("T†T = I: ", adjoint(t) * t == identity)
println("T^8 = I: ", t^8 == identity)
println("HT differs from TH: ", h * t != t * h)
