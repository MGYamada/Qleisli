# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
# Run: julia --startup-file=no julia/examples/shor15.jl
# Exact bounded Julia reference only; no Lean/QPTL or QS/PR/RS proof is claimed.
module Shor15Reference

include(joinpath(@__DIR__, "..", "src", "ExactFiniteQuantum.jl"))
using .ExactFiniteQuantum

export shor15, decode_shor15, retry_shor15, factors_from_order

_retry(reason; order=nothing) = (status=:retry, reason=reason, order=order, factors=nothing)

"""Verify a small order candidate and both nontrivial factors using integer arithmetic.
Failure is an explicit retry result. This helper supports N ≤ 4096 and r < N.
"""
function factors_from_order(a::Integer, N::Integer, r::Integer)
    2 <= N <= 4096 || throw(ArgumentError("expected a small modulus in 2:4096"))
    1 <= r < N || throw(ArgumentError("order candidate must be in 1:N-1"))
    gcd(a,N) == 1 || throw(ArgumentError("base must be coprime to N"))
    a, N, r = big(a), big(N), Int(r)
    powermod(a, r, N) == 1 || return _retry(:unverified_order; order=r)
    iseven(r) || return _retry(:odd_order; order=r)
    root = powermod(a, div(r,2), N)
    (root == 1 || root == N-1) && return _retry(:trivial_square_root; order=r)
    p, q = minmax(gcd(root-1,N), gcd(root+1,N))
    (1 < p < N && 1 < q < N && p*q == N) || return _retry(:factor_verification; order=r)
    return (status=:success, reason=:verified_factors, order=r, factors=(p,q))
end

"""Decode y/256 via exact continued fractions; accept only verified denominators.
For this instance 64 and 192 yield r=4; 0 and 128 request another measurement.
In particular, denominator 2 is not silently promoted to 4 or accepted as an order.
"""
function decode_shor15(y::Integer)
    0 <= y < 256 || throw(ArgumentError("eight-bit measurement must be in 0:255"))
    y == 0 && return _retry(:zero_measurement)
    # Denominators of successive convergents, with Euclidean remainders.
    numerator, denominator = big(y), big(256)
    qprev, qcurrent = big(1), big(0)
    while !iszero(denominator)
        digit, remainder = divrem(numerator, denominator)
        qnext = digit*qcurrent + qprev
        qnext >= 15 && break
        if powermod(big(2), qnext, big(15)) == 1
            return factors_from_order(2, 15, qnext)
        end
        qprev, qcurrent = qcurrent, qnext
        numerator, denominator = denominator, remainder
    end
    return _retry(:unverified_order)
end

"""Consume an explicitly supplied finite measurement sequence; no random sampling.
Returns the actual attempt count, including an explicit exhausted result.
"""
function retry_shor15(outcomes::AbstractVector{<:Integer})
    length(outcomes) <= 64 || throw(ReferenceCapacityError("at most 64 retry observations"))
    for (attempt, y) in enumerate(outcomes)
        result = decode_shor15(y)
        result.status == :success && return (result=result, attempts=attempt)
    end
    return (result=(status=:exhausted, reason=:no_verified_factors,
                    order=nothing, factors=nothing), attempts=length(outcomes))
end

"""N=15, a=2, eight Fourier bits and four work bits, initially |0⟩|1⟩.
Basis index b = 16*x + w; Fourier bit j is global bit 4+j.
Compute the full 4096-entry state, then marginalize the work register exactly.
"""
function shor15(; limits::ReferenceLimits=ReferenceLimits())
    state = basis_state(12, 1; limits)
    for j in 0:7
        state = hadamard(state, 4+j)
    end
    permutation = modular_multiplication(2, 15, 4; limits)
    state = controlled_powers(state, permutation; target_offset=0,
                              control_offset=4, control_bits=8)
    state = inverse_qft(state; offset=4, width=8)
    probabilities = born_probabilities(state; offset=4, width=8)
    return (state=state, probabilities=probabilities)
end

function main()
    result = shor15()
    expected = [RInfScalar(y in (0,64,128,192) ? 1//4 : 0//1) for y in 0:255]
    @assert result.probabilities == expected
    @assert sum(result.probabilities; init=zero(RInfScalar)) == one(RInfScalar)
    println("Exact Julia Shor reference: N=15, a=2, Fourier=8 bits, work=4 bits")
    for y in (0,64,128,192)
        decoded = decode_shor15(y)
        println("y=", y, ", probability=1//4, ", decoded)
    end
    retry = retry_shor15([0,128,64])
    @assert retry.result.order == 4 && retry.result.factors == (3,5)
    @assert prod(retry.result.factors) == 15
    println("Deterministic retry example [0,128,64]: ", retry)
    println("Reference computation only; not a Lean/QPTL proof or a QS/PR/RS guarantee.")
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    Shor15Reference.main()
end
