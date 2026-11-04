# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
using Test, Random
include(joinpath(@__DIR__, "..", "src", "RInfScalar.jl"))

const D = DyadicCoefficient
const P = PhaseKey
const S = RInfScalar
const Q = Rational{BigInt}
q(x) = big(x.numerator) // (big(1) << x.exponent)
t(p,k,n=1,e=0) = Term(P(p,k),D(n,e))
s(p,k,n=1,e=0) = S([t(p,k,n,e)])

function invariants(x)
    phases = q.([a.phase for a in x.terms])
    return all(!iszero(a.coeff) for a in x.terms) &&
        all(0 <= p < 1//2 for p in phases) &&
        all(phases[i]<phases[i+1] for i in 1:length(phases)-1) &&
        all(a.coeff.exponent==0 || isodd(a.coeff.numerator) for a in x.terms) &&
        all(iszero(a.phase.numerator) ? a.phase.exponent==0 :
            isodd(a.phase.numerator) for a in x.terms)
end

@testset "RInfScalar: exact regression and independent reference" begin
    @testset "Issue boundary cases and constructor invariants" begin
        for (n,k,en,ek) in [(0,5,0,0),(2,0,2,0),(8,2,2,0),(6,2,3,1),(-8,2,-2,0),(-6,2,-3,1)]
            c=D(n,k)
            @test (c.numerator,c.exponent)==(en,ek)
            @test q(c)==big(n)//(big(1)<<k)
            @test normalize(normalize(c))==c
        end
        for (n,k,en,ek) in [(0,4096,0,0),(2,4,1,3),(1,2,1,2),(1,4096,1,4096)]
            p=P(n,k)
            @test (p.numerator,p.exponent)==(en,ek)
            @test q(p)==big(n)//(big(1)<<k)
            @test normalize(normalize(p))==p
        end
        for (n,k) in [(1,0),(1,1),(2,2),(-1,3),(0,-1)]
            @test_throws DomainError P(n,k)
        end
        @test_throws DomainError D(1,-1)
        @test_throws DomainError D(1//3)
        @test_throws MethodError D(0.5)
        @test D(3//8)==D(3,3)
        @test D(0,4096)==zero(D)

        n = big(3)
        x = S((Term(P(n,4), D(n,1)),))
        values = Set([x])
        Base.GMP.MPZ.set!(n, big(0))
        Base.GMP.MPZ.set!(only(x.terms).phase.numerator, big(5))
        Base.GMP.MPZ.set!(only(x.terms).coeff.numerator, big(-7))
        @test x == s(3,4,3,1)
        @test s(3,4,3,1) in values
    end

    @testset "All confirmed review counterexamples" begin
        @test D(2^62,0)+D(2^62,0)==D(big(1)<<63,0)
        @test D(2^32,0)*D(2^32,0)==D(big(1)<<64,0)
        @test -D(typemin(Int64),0)==D(big(1)<<63,0)
        @test D(1,64)+D(1,0)==D((big(1)<<64)+1,64)
        @test D(2^62,0)*D(3,2)==D(3458764513820540928,0)
        @test rinf_phase(1,2)*rinf_phase(1,66)==rinf_phase((big(1)<<64)+1,66)
        x=rinf_phase((big(1)<<63)+1,65)
        @test x*x == -rinf_phase(1,64)
        @test s(0,0)+s(0,0,-1)==zero(S)
        @test isempty(S([t(1,2,0,5)]).terms)
        @test canonicalize(S(Term[]))==zero(S)
        @test zero(S)*one(S)==zero(S)
        @test zero(S)+zero(S)==zero(S)
        @test S([t(1,2),t(3,4)]).terms==(t(3,4),t(1,2))
        @test canonicalize(s(0,0))==canonicalize(s(0,0))
        @test hash(s(0,0))==hash(S(1))
        @test length(Set([s(0,0),S(1)]))==1
        @test length(Set([P(2,4),P(1,3)]))==1
        @test S([t(2,4),t(1,3)])==s(1,3,2)
        v=[t(0,0)]
        x=S(v)
        v[1]=t(1,2)
        @test x==one(S)
        @test x.terms isa Tuple
    end

    @testset "Signed phase, conjugation, large roots, actual support" begin
        @test rinf_phase(-1,3)==s(3,3,-1)
        @test rinf_phase(1,1)==S(-1)
        @test rinf_phase(5,3)==s(1,3,-1)
        @test rinf_phase(-1,0)==one(S)
        @test rinf_phase(3//8)==s(3,3)
        @test rinf_phase(1,2)^2==S(-1)
        @test rinf_phase(1,3)^8==one(S)
        @test rinf_phase(1,4)^16==one(S)
        @test_throws DomainError rinf_phase(1,3)^(-1)
        @test_throws DomainError rinf_phase(1,3)^(-2)
        negative_exponent = -1
        @test_throws DomainError rinf_phase(1,3)^negative_exponent
        @test rinf_phase(1,3)^0==one(S)
        @test_throws DomainError rinf_phase(1,-1)
        z=rinf_phase(1,4096)
        @test z.terms==(t(1,4096),)
        @test z*z==rinf_phase(1,4095)
        @test z*conj(z)==one(S)
        @test length(conj(z).terms)==1
        @test conj(conj(z))==z
        @test rinf_phase(1,2)*z==rinf_phase((big(1)<<4094)+1,4096)
        @test isless(P(1,4096),P(1,2))
        for k in 2:8
            product=one(S)
            for j in 0:k-2
                product *= one(S)+rinf_phase(1,k-j)
            end
            @test length(product.terms)==1<<(k-1)
            @test all(isone(a.coeff) for a in product.terms)
            @test invariants(product)
        end
    end

    @testset "Explicit capacity rejection (never wrap)" begin
        @test_throws RInfCapacityError D(1,typemax(UInt64))
        @test_throws RInfCapacityError D(1,typemax(Int))*D(1,1)
        @test_throws RInfCapacityError D(1,RINF_MAX_INTEGER_BITS)+D(1,0)
        @test_throws RInfCapacityError D(big(1)<<RINF_MAX_INTEGER_BITS,0)
        # This root is cheap to store, but its conjugate would require a huge numerator.
        @test length(rinf_phase(1,typemax(Int)).terms)==1
        @test_throws RInfCapacityError conj(rinf_phase(1,typemax(Int)))
        x=S(t(i,12) for i in 0:1000)
        @test_throws RInfCapacityError x*x
    end

    @testset "Representable results at the integer bit limit" begin
        M = RINF_MAX_INTEGER_BITS
        half = big(1) << (M-1)
        full = 2*half
        a, b = D(half), D(1-full,1)
        @test a+b == b+a == D(1,1)
        @test (-a)-b == D(-1,1)
        @test S(a)+S(b) == S(1//2)
        @test D(full-1,1)+D(full-1,1) == D(full-1)
        @test_throws RInfCapacityError a+D(1,1)
        @test_throws RInfCapacityError D(1)+D(-1,typemax(Int))

        z = rinf_phase(1,M)
        @test rinf_phase(-1,M) == conj(z) == s(half-1,M,-1)
        @test z*conj(z) == one(S)
        @test rinf_phase(-1,M+1) == rinf_phase(-2,M+2) == s(full-1,M+1,-1)
        @test_throws RInfCapacityError rinf_phase(-1,M+2)
        @test rinf_phase(full+1,M+1) == -rinf_phase(1,M+1)
        @test rinf_phase((full+1)//4) == rinf_phase(1,2)
        @test_throws DomainError rinf_phase(1//3)
        @test rinf_phase(half-1,M)*rinf_phase(5,M+2) == -rinf_phase(1,M+2)
    end

    # Independent finite-level model Q[X]/(X^32+1).
    # Only this small reference model allocates dense vectors.
    K=6; N=1<<(K-1)
    function rawpoly(raw)
        out=zeros(Q,N)
        for (p,k,n,e) in raw
            j=p*(1<<(K-k))
            out[j+1] += big(n)//(big(1)<<e)
        end
        return out
    end
    function poly(x)
        out=zeros(Q,N)
        for a in x.terms
            j=Int(q(a.phase)*(big(1)<<K))
            out[j+1]+=q(a.coeff)
        end
        return out
    end
    function pmul(a,b)
        out=zeros(Q,N)
        for i in 0:N-1, j in 0:N-1
            out[mod(i+j,N)+1] += (i+j<N ? 1 : -1)*a[i+1]*b[j+1]
        end
        return out
    end
    function pconj(a)
        out=zeros(Q,N)
        out[1]=a[1]
        for j in 1:N-1
            out[N-j+1]=-a[j+1]
        end
        return out
    end
    rng=MersenneTwister(339)
    function randomraw()
        [begin
            k=rand(rng,2:K)
            (rand(rng,0:(1<<(k-1))-1),k,rand(rng,-20:20),rand(rng,0:8))
        end for _ in 1:rand(rng,0:8)]
    end
    @testset "500 random pairs vs independent exact polynomial model" begin
        for _ in 1:500
            ra,rb=randomraw(),randomraw()
            a,b=(S(t(v...) for v in r) for r in (ra,rb))
            pa,pb=rawpoly(ra),rawpoly(rb)
            @test poly(a)==pa
            @test poly(b)==pb
            @test poly(a+b)==pa+pb
            @test poly(a-b)==pa-pb
            @test poly(a*b)==pmul(pa,pb)
            @test poly(conj(a))==pconj(pa)
            @test canonicalize(canonicalize(a))==a
            @test a==S(reverse(a.terms))
            @test all(invariants,(a,b,a+b,a-b,a*b,conj(a)))
            @test (a==b)==(pa==pb)
            @test conj(conj(a))==a
            @test conj(a*b)==conj(a)*conj(b)
            @test a*(b+one(S))==a*b+a
            @test decode_rinf(encode_rinf(a))==a
            @test encode_rinf(decode_rinf(encode_rinf(a)))==encode_rinf(a)
        end
    end
    @testset "1000 dyadic pairs and signed phases vs exact rationals" begin
        for _ in 1:1000
            n,m=rand(rng,Int64),rand(rng,Int64)
            k,e=rand(rng,0:128),rand(rng,0:128)
            a,b=D(n,k),D(m,e)
            @test q(a+b)==q(a)+q(b)
            @test q(a*b)==q(a)*q(b)
            @test q(a-b)==q(a)-q(b)
            p=rand(rng,-1000:1000); k=rand(rng,0:K)
            j=mod(p*(1<<(K-k)),2N)
            reference=zeros(Q,N)
            reference[mod(j,N)+1]=j<N ? 1 : -1
            @test poly(rinf_phase(p,k))==reference
        end
    end

    # Legacy arithmetic independently expressed over Q(sqrt(2)) + i Q(sqrt(2)).
    function r3mul(x,y)
        a,b,c,d=x; e,f,g,h=y
        (a*e+2b*f-c*g-2d*h,
         a*f+b*e-c*h-d*g,
         a*g+2b*h+c*e+2d*f,
         a*h+b*g+c*f+d*e)
    end
    @testset "R3 two-way bridge and independent legacy arithmetic" begin
        @test from_r3(0,1,0,0)==rinf_phase(1,3)-rinf_phase(3,3)
        @test from_r3(0,0,0,1)==rinf_phase(1,3)+rinf_phase(3,3)
        @test_throws DomainError to_r3(rinf_phase(1,4))
        for _ in 1:100
            x,y=(ntuple(_->big(rand(rng,-20:20))//(big(1)<<rand(rng,0:6)),4) for _ in 1:2)
            a,b=from_r3(x...),from_r3(y...)
            @test q.(to_r3(a))==x
            @test from_r3(to_r3(a)...)==a
            @test from_r3(r3mul(x,y)...)==a*b
            @test from_r3((x.+y)...)==a+b
            @test from_r3(x[1],x[2],-x[3],-x[4])==conj(a)
            raw=S((t(0,0,rand(rng,-9:9)),t(1,3,rand(rng,-9:9)),
                   t(1,2,rand(rng,-9:9)),t(3,3,rand(rng,-9:9))))
            @test from_r3(to_r3(raw)...)==raw
        end
    end

    @testset "R3 round trips at coefficient limits" begin
        z = zero(D)
        edge = D(big(1) << (RINF_MAX_INTEGER_BITS-1))
        @test to_r3(from_r3(0,0,0,edge)) == (z,z,z,edge)
        @test to_r3(from_r3(0,edge,0,0)) == (z,edge,z,z)
        @test to_r3(from_r3(0,1,0,-edge)) == (z,one(D),z,-edge)

        k = typemax(Int)
        b, d = D(1,k), D(1,k-1)
        @test to_r3(from_r3(0,b,0,d)) == (z,b,z,d)

        # Halving these odd numerators genuinely exceeds an exponent or bit limit.
        @test_throws RInfCapacityError to_r3(s(1,3,1,k))
        @test_throws RInfCapacityError to_r3(S((Term(P(1,3),edge), t(3,3,1,1))))
    end

    @testset "Strict, unique wire format and malformed inputs" begin
        @test encode_rinf(zero(S))=="rinfty-sparse-v1\n0\n"
        @test encode_rinf(S(2))=="rinfty-sparse-v1\n1\n0 0 2 0\n"
        framed = "[" * encode_rinf(S(2)) * "]"
        @test decode_rinf(SubString(framed, 2, lastindex(framed)-1)) == S(2)
        @test decode_rinf(encode_rinf(rinf_phase(1,4096)))==rinf_phase(1,4096)
        for line in ["2 4 1 0", "0 4096 1 0", "0 0 0 0", "0 0 0 5",
                     "0 0 8 2", "0 0 -6 2", "01 3 1 0", "1 3 +1 0",
                     "0 0 -0 0", "1 3 1 00", "1 3 1 0 ", "1  3 1 0"]
            @test_throws ArgumentError decode_rinf("rinfty-sparse-v1\n1\n"*line*"\n")
        end
        for line in ["1 1 1 0", "1 0 1 0"]
            @test_throws DomainError decode_rinf("rinfty-sparse-v1\n1\n"*line*"\n")
        end
        for wire in ["rinfty-sparse-v2\n0\n", "rinfty-sparse-v1\n0",
                     "rinfty-sparse-v1\n0\n\n", "rinfty-sparse-v1\n01\n0 0 1 0\n",
                     "rinfty-sparse-v1\r\n0\r\n", "rinfty-sparse-v1\n1\n0 0 1 0\r\n",
                     "rinfty-sparse-v1\n1\n", "rinfty-sparse-v1\n1\n\n",
                     "rinfty-sparse-v1\n1\n0 0 1 0", "rinfty-sparse-v1\n1\n0 0 1 0\n\n",
                     "rinfty-sparse-v1\n2\n1 2 1 0\n3 4 1 0\n",
                     "rinfty-sparse-v1\n2\n1 2 1 0\n1 2 1 0\n"]
            @test_throws ArgumentError decode_rinf(wire)
        end
        @test_throws RInfCapacityError decode_rinf(encode_rinf(S(1));max_bytes=1)
        @test_throws RInfCapacityError decode_rinf(encode_rinf(S(1));max_terms=0)
        @test_throws RInfCapacityError decode_rinf("rinfty-sparse-v1\n$(RINF_MAX_TERMS+1)\n")
        @test_throws RInfCapacityError decode_rinf(encode_rinf(S(123));max_digits=2)
        @test_throws RInfCapacityError decode_rinf(encode_rinf(rinf_phase(1,4096));max_exponent=4095)
        @test_throws ArgumentError decode_rinf(encode_rinf(S(1));max_terms=-1)

        # Mismatched framing takes precedence over the invalid term.
        @test_throws ArgumentError decode_rinf("rinfty-sparse-v1\n2\n1 0 1 0\n")
        function rejects_wire(wire)
            try
                decode_rinf(wire)
                return false
            catch err
                err isa ArgumentError || rethrow()
                return true
            end
        end
        for wire in ("rinfty-sparse-v1\n0\n" * repeat("\n", 1_000_000),
                     "rinfty-sparse-v1\n1\n0 0 1 0" * repeat(" ", 1_000_000) * "\n")
            @test rejects_wire(wire)
            # Warmed up, rejection should not allocate even one byte per separator.
            @test (@allocated rejects_wire(wire)) < ncodeunits(wire)
        end
    end
    @test isnothing(check())
end

println("Julia ",VERSION,"; seed 339; core requires only Julia standard libraries.")
