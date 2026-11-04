# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
# Optional integration test. Requires an already installed Cyclotomics package.
using Test, Cyclotomics, Random
include(joinpath(@__DIR__, "..", "src", "RInfScalar.jl"))

@testset "Exact optional Cyclotomics conversion" begin
    cv=RInfScalar2Cyclotomics
    @test cv(RInfScalar(9007199254740993))==big(9007199254740993)//big(1)
    @test cv(RInfScalar(DyadicCoefficient(1,64)))==big(1)//(big(1)<<64)
    @test cv(RInfScalar(DyadicCoefficient(1,4096)))==big(1)//(big(1)<<4096)
    @test cv(zero(RInfScalar))==0
    @test eltype(coeffs(cv(RInfScalar(3//8))))==Rational{BigInt}
    @test_throws RInfCapacityError cv(rinf_phase(1,4096))
    @test_throws RInfCapacityError cv(rinf_phase(1,13))
    @test_throws ArgumentError cv(one(RInfScalar);max_phase_exponent=-1)
    @test cv(rinf_phase(1,3);root=Cyclotomics.E)==E(8)
    rng=MersenneTwister(339)
    for _ in 1:100
        a,b=(from_r3((big(rand(rng,-9:9))//(big(1)<<rand(rng,0:5)) for _ in 1:4)...) for _ in 1:2)
        @test cv(a+b)==cv(a)+cv(b)
        @test cv(a*b)==cv(a)*cv(b)
        @test cv(conj(a))==conj(cv(a))
    end
end
println("Julia ",VERSION,"; Cyclotomics ",pkgversion(Cyclotomics))
