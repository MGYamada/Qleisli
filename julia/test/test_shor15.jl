# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
using Test
include(joinpath(@__DIR__, "..", "examples", "shor15.jl"))
using .Shor15Reference
using .Shor15Reference.ExactFiniteQuantum

@testset "Exact Shor15 reference" begin
    result = shor15()
    S = RInfScalar
    expected = [S(y in (0,64,128,192) ? 1//4 : 0//1) for y in 0:255]
    @test result.probabilities == expected
    @test sum(result.probabilities; init=S(0)) == S(1)
    @test norm_squared(result.state) == S(1)
    @test count(!iszero,result.probabilities) == 4

    # Independent final joint amplitudes, retaining work-register correlations
    # and phases that a check of the symmetric marginal alone cannot distinguish.
    joint = fill(S(0),4096)
    for k in 0:3, r in 0:3
        joint[16*(64k)+(1 << r)+1] = S(1//4)*rinf_phase(-k*r,2)
    end
    @test result.state.amplitudes == joint
    @test born_probabilities(result.state) == [conj(a)*a for a in joint]
    @test born_probabilities(result.state; width=4) ==
          [S(w in (1,2,4,8) ? 1//4 : 0//1) for w in 0:15]

    for y in (64,192)
        decoded = decode_shor15(y)
        @test decoded.status == :success
        @test decoded.order == 4
        @test powermod(2,decoded.order,15) == 1
        @test all(powermod(2,r,15) != 1 for r in 1:decoded.order-1)
        @test decoded.factors == (3,5)
        @test prod(decoded.factors) == 15
        @test all(1 < p < 15 && 15 % p == 0 for p in decoded.factors)
    end
    @test decode_shor15(0).reason == :zero_measurement
    @test decode_shor15(128).reason == :unverified_order
    for y in (0,128)
        @test decode_shor15(y).status == :retry
        @test isnothing(decode_shor15(y).factors)
    end
    @test decode_shor15(1).status == :retry
    @test decode_shor15(big(192)) == decode_shor15(192)
    @test_throws ArgumentError decode_shor15(-1)
    @test_throws ArgumentError decode_shor15(256)
    @test_throws MethodError decode_shor15(64.0)
    @test factors_from_order(2,15,2).reason == :unverified_order
    @test factors_from_order(4,21,3).reason == :odd_order
    @test factors_from_order(14,15,2).reason == :trivial_square_root
    @test factors_from_order(2,15,8).reason == :trivial_square_root
    @test factors_from_order(5,12,2).reason == :factor_verification
    @test_throws ArgumentError factors_from_order(3,15,4)
    @test_throws ArgumentError factors_from_order(2,15,0)
    @test_throws ArgumentError factors_from_order(2,15,15)
    @test retry_shor15([0,128,64]).result.factors == (3,5)
    @test retry_shor15([0,128,64]).attempts == 3
    @test retry_shor15([192,0]).attempts == 1
    @test retry_shor15([0,128]).result.status == :exhausted
    @test retry_shor15([0,128]).attempts == 2
    @test retry_shor15(Int[]).result.status == :exhausted
    @test retry_shor15(Int[]).attempts == 0
    @test_throws ReferenceCapacityError retry_shor15(fill(0,65))
    @test_throws ArgumentError retry_shor15([256])
    @test_throws ReferenceCapacityError shor15(; limits=ReferenceLimits(max_basis=2048))
    @test_throws ReferenceCapacityError shor15(; limits=ReferenceLimits(max_work=20_000))
    # The documented retry policy succeeds with exactly 1/2 per independent shot.
    success_weight = sum((result.probabilities[y+1] for y in 0:255
                         if decode_shor15(y).status == :success); init=S(0))
    @test success_weight == S(1//2)
end
