# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
using Test
using Cyclotomics
using LinearAlgebra

include(joinpath(@__DIR__, "..", "src", "CyclotomicExperiments.jl"))
using .CyclotomicExperiments

@testset "Exact Cyclotomics experiment environment" begin
    @testset "Construction and boundaries" begin
        @test valtype(exact_root(5)) == Rational{BigInt}
        @test isone(exact_root(1))
        @test exact_root(2) == exact_scalar(-1)
        @test exact_root(8, -1) == exact_root(8, 7)
        @test exact_root(7, big(10)^80) == exact_root(7, mod(big(10)^80, 7))
        @test exact_scalar(big(10)^80) + exact_scalar(1) == exact_scalar(big(10)^80 + 1)
        @test exact_scalar(2//3) * exact_scalar(3//2) == exact_scalar(1)
        @test_throws ArgumentError exact_root(0)
        @test_throws ArgumentError exact_root(-3)
        @test_throws InexactError exact_root(big(typemax(Int)) + 1)
        @test_throws MethodError exact_scalar(0.5)
    end

    @testset "Roots, conjugation and cyclotomic relations" begin
        for n in (1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 24, 45)
            z = exact_root(n)
            @test isone(z^n)
            @test conj(z) == exact_root(n, -1)
            @test isone(z * conj(z))
            @test inv(z) == conj(z)
            @test valtype(inv(z)) == Rational{BigInt}
            if n > 1
                @test iszero(sum(z^k for k in 0:(n-1)))
            end
        end
        @test exact_root(12, 4) == exact_root(3)
        @test exact_root(8)^4 + exact_scalar(1) == exact_scalar(0)
        @test exact_root(9)^6 + exact_root(9)^3 + exact_scalar(1) == exact_scalar(0)
        @test exact_root(4)^2 == exact_scalar(-1)
        @test Rational{BigInt}(exact_root(3) + exact_root(3, 2)) == -1//big(1)
        @test_throws InexactError Rational{BigInt}(exact_root(4))
    end

    @testset "Mixed fields, exact division and normal forms" begin
        a, b = exact_root(3), exact_root(4)
        @test a + b == exact_root(12, 4) + exact_root(12, 3)
        @test conj(a + b) == a^2 - b
        @test (a + b) * (a - b) == a^2 + exact_scalar(1)
        x = exact_scalar(2) + exact_root(5)
        @test isone(x * inv(x))
        @test x / x == exact_scalar(1)
        @test valtype(x / x) == Rational{BigInt}
        @test (x // big(3)) * exact_scalar(3) == x
        @test valtype(x // big(3)) == Rational{BigInt}
        z = exact_root(45)
        expanded = sum(z^k for k in (1, 2, 8, 11, 17, 26, 29, 38, 44))
        @test expanded == z + z^5
        @test exact_root(45, 5) == exact_root(9)
        @test hash(exact_root(45, 5)) == hash(exact_root(9))
        @test length(Set([exact_root(45, 5), exact_root(9)])) == 1
    end

    @testset "Exact Clifford and T matrices" begin
        z = exact_root(8)
        sqrt2 = z + conj(z)
        a = sqrt2 // big(2)
        identity = map(exact_scalar, [1 0; 0 1])
        x = map(exact_scalar, [0 1; 1 0])
        phase_z = map(exact_scalar, [1 0; 0 -1])
        h = a * map(exact_scalar, [1 1; 1 -1])
        t = [exact_scalar(1) exact_scalar(0); exact_scalar(0) z]
        @test sqrt2^2 == exact_scalar(2)
        @test isreal(sqrt2)
        @test adjoint(h) * h == identity
        @test h * h == identity
        @test adjoint(t) * t == identity
        @test t^4 == phase_z
        @test t^8 == identity
        @test h * phase_z * h == x
        @test h * t != t * h
        @test h != -h
        @test all(v -> valtype(v) == Rational{BigInt}, h * t)

        # Basis order is 00, 01, 10, 11, with the control factor first.
        cnot = map(exact_scalar, [1 0 0 0; 0 1 0 0; 0 0 0 1; 0 0 1 0])
        ket00 = map(exact_scalar, [1, 0, 0, 0])
        bell = cnot * kron(h, identity) * ket00
        @test bell == [a, exact_scalar(0), exact_scalar(0), a]
        @test dot(bell, bell) == exact_scalar(1)
    end
end
