# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
using Test
include(joinpath(@__DIR__, "..", "src", "ExactFiniteQuantum.jl"))
using .ExactFiniteQuantum

const S = RInfScalar
const D = DyadicCoefficient

@testset "Exact finite quantum reference" begin
    @testset "States, local gates, controls and exact Born weights" begin
        original = S.([1,0])
        state = ExactState(1, original)
        original[1] = S(0)
        @test state.amplitudes == S.([1,0])
        @test basis_state(0).amplitudes == S.([1])
        @test norm_squared(basis_state(0)) == S(1)
        for b in 0:1
            s = basis_state(1,b)
            h = hadamard(s,0)
            @test hadamard(h,0).amplitudes == s.amplitudes
            @test norm_squared(h) == S(1)
            @test born_probabilities(h) == S.([1//2,1//2])
        end
        x = S.([0 1; 1 0])
        bell = apply_gate(hadamard(basis_state(2),1), 0, x; control=1)
        @test born_probabilities(bell) == S.([1//2,0,0,1//2])
        @test born_probabilities(bell; offset=1, width=1) == S.([1//2,1//2])
        @test born_probabilities(bell; width=0) == S.([1])
        i = rinf_phase(1,2)
        ygate = [S(0) -i; i S(0)]
        @test apply_gate(apply_gate(bell,0,ygate),0,ygate).amplitudes == bell.amplitudes
        @test phase_gate(phase_gate(bell,0,1,3; control=1),0,-1,3;
                         control=1).amplitudes == bell.amplitudes
        interference = hadamard(phase_gate(hadamard(state,0),0,1,3),0)
        delta = S(1//4)*(rinf_phase(1,3)+rinf_phase(-1,3))
        @test born_probabilities(interference) == [S(1//2)+delta,S(1//2)-delta]
        @test_throws ArgumentError apply_gate(state,0,S.([1 1; 0 1]))
        @test_throws DimensionMismatch apply_gate(state,0,fill(S(0),3,3))
        @test_throws ArgumentError apply_gate(state,0,x; control=0)
        @test_throws ArgumentError phase_gate(state,1,1,3)
        @test_throws ArgumentError phase_gate(state,0,1,3; control=-1)
        @test_throws ArgumentError phase_gate(state,0,1,3; control=0.5)
        @test_throws MethodError apply_gate(state,0,[1.0 0.0; 0.0 1.0])
        @test_throws MethodError ExactState(1,[1.0,0.0])
        @test_throws ArgumentError born_probabilities(ExactState(1,S.([1,1])))
        @test_throws ArgumentError born_probabilities(ExactState(1,S.([0,0])))
        @test_throws DimensionMismatch ExactState(2,S.([1,0]))
        @test_throws ArgumentError basis_state(2,4)
        @test_throws ArgumentError basis_state(-1)
    end

    @testset "Whole-basis reversible multiplication and controlled powers" begin
        p = modular_multiplication(2,15,4)
        pinv = modular_multiplication(8,15,4)
        @test sort(p) == collect(0:15)
        @test p[16] == 15
        for b in 0:15
            expected = b < 15 ? 2b % 15 : 15
            s = basis_state(4,b)
            result = apply_permutation(s,p)
            @test result.amplitudes == basis_state(4,expected).amplitudes
            @test apply_permutation(result,pinv).amplitudes == s.amplitudes
        end
        @test modular_multiplication(2,5,3) == [0,2,4,1,3,5,6,7]
        @test modular_multiplication(-13,15,4) == p
        @test modular_multiplication(big(15)*big(10)^50+2,15,4) == p
        @test_throws ArgumentError modular_multiplication(3,15,4)
        @test_throws ArgumentError modular_multiplication(2,15,3)
        @test_throws ArgumentError modular_multiplication(1,1,1)
        @test_throws ArgumentError apply_permutation(basis_state(2),[0,1,2,2])
        @test_throws ArgumentError apply_permutation(basis_state(2),[0,1,2,4])
        @test_throws ArgumentError apply_permutation(basis_state(2),[0,1,2])
        @test_throws ArgumentError apply_permutation(basis_state(2),[1,0]; control=0)
        @test_throws ArgumentError controlled_powers(basis_state(3),[1,0];
                                                     control_offset=0,control_bits=2)

        # A distinct exact coefficient on every basis vector checks every column
        # of the permutation at once, including all control values and padding.
        # This linear probe is deliberately unnormalized; no Born law is taken.
        labels = ExactState(12,S.(1:4096))
        result = controlled_powers(labels,p; control_offset=4,control_bits=8)
        for control in 0:255, work in 0:15
            multiplier = powermod(big(2),control,big(15))
            out = work < 15 ? Int(mod(multiplier*work,15)) : work
            @test result.amplitudes[16control+out+1] == S(16control+work+1)
        end
        restored = controlled_powers(result,pinv; control_offset=4,control_bits=8)
        @test restored.amplitudes == labels.amplitudes
        @test controlled_powers(labels,p; control_offset=4,control_bits=0).amplitudes ==
              labels.amplitudes
        # Unlike multiplication by 2 modulo 15, this order-eight permutation
        # has a nonidentity fourth power, exercising a third active control bit.
        cycle = [1,2,3,4,5,6,7,0]
        probe = ExactState(6,S.(1:64))
        advanced = controlled_powers(probe,cycle; control_offset=3,control_bits=3)
        for control in 0:7, work in 0:7
            @test advanced.amplitudes[8control+mod(work+control,8)+1] == S(8control+work+1)
        end
        # Target offset and spectators are independent of the Shor layout.
        for b in 0:31
            s = basis_state(5,b)
            r = apply_permutation(s,[1,0]; offset=2,control=0)
            expected = isodd(b) ? xor(b,4) : b
            @test r.amplitudes == basis_state(5,expected).amplitudes
        end
    end

    @testset "QFT sign, bit order, spectators and exact unitarity" begin
        for n in 0:3
            dim = 1 << n
            # Direct Fourier definition, independent of the gate schedule.
            scale = S(D(1,n)) * (rinf_phase(1,3)+rinf_phase(-1,3))^n
            columns = Vector{S}[]
            for x in 0:dim-1
                basis = basis_state(n,x)
                f = qft(basis)
                adj = inverse_qft(basis)
                @test f.amplitudes == [scale*rinf_phase(x*y,n) for y in 0:dim-1]
                @test adj.amplitudes == [scale*rinf_phase(-x*y,n) for y in 0:dim-1]
                @test inverse_qft(f).amplitudes == basis.amplitudes
                @test qft(adj).amplitudes == basis.amplitudes
                push!(columns,f.amplitudes)
            end
            for x in 1:dim, y in 1:dim
                gram = sum((conj(columns[x][j])*columns[y][j] for j in 1:dim); init=S(0))
                @test gram == S(x == y)
            end
        end
        for x in 0:3
            s = basis_state(4,9 + (x << 1))
            f = inverse_qft(s; offset=1,width=2)
            expected = fill(S(0),16)
            for y in 0:3
                expected[9+(y << 1)+1] = S(1//2)*rinf_phase(-x*y,2)
            end
            @test f.amplitudes == expected
            @test norm_squared(f) == S(1)
        end
        # Non-symmetric QPE control: U=diag(1,ζ8), eigenstate |1⟩.
        # Omitting swaps or reversing the Fourier sign cannot pass y=1.
        s = basis_state(4,1)
        for j in 0:2
            s = hadamard(s,1+j)
            s = phase_gate(s,0,1,3-j; control=1+j)
        end
        @test born_probabilities(inverse_qft(s; offset=1,width=3); offset=1,width=3) ==
              S.([0,1,0,0,0,0,0,0])
        @test_throws ArgumentError qft(s; offset=2,width=3)
    end

    @testset "Explicit capacity refusal, with unchanged inputs" begin
        @test_throws ReferenceCapacityError basis_state(13)
        @test_throws ReferenceCapacityError basis_state(big(typemax(Int))+1)
        @test_throws ReferenceCapacityError basis_state(4; limits=ReferenceLimits(max_basis=8))
        @test_throws ReferenceCapacityError basis_state(0; limits=ReferenceLimits(max_work=0))
        @test_throws ReferenceCapacityError basis_state(0; limits=ReferenceLimits(max_work=1))
        @test basis_state(0; limits=ReferenceLimits(max_work=2)).amplitudes == S.([1])
        @test_throws ArgumentError ReferenceLimits(max_basis=4097)
        @test_throws ArgumentError ReferenceLimits(max_work=-1)
        s = basis_state(4; limits=ReferenceLimits(max_work=512))
        @test norm_squared(hadamard(s,0)) == S(1)
        @test_throws ReferenceCapacityError qft(s)
        @test s.amplitudes == basis_state(4).amplitudes
        tiny = basis_state(2; limits=ReferenceLimits(max_work=8))
        @test_throws ReferenceCapacityError apply_permutation(tiny,[0,1,2,3])
        @test_throws ReferenceCapacityError controlled_powers(tiny,[1,0];
                                                            control_offset=1,control_bits=1)
        @test_throws ReferenceCapacityError born_probabilities(tiny)
        @test_throws ReferenceCapacityError apply_permutation(basis_state(1;
            limits=ReferenceLimits(max_basis=2)),[0,1,2,3])
        state = basis_state(1,1)
        @test_throws RInfCapacityError phase_gate(state,0,-1,
                                                 ExactFiniteQuantum.RINF_MAX_INTEGER_BITS+2)
        extreme = ExactState(0,[S(D(1,typemax(Int)))])
        @test_throws RInfCapacityError norm_squared(extreme)
        @test state.amplitudes == S.([0,1])
    end
end
