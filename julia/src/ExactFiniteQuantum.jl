# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
module ExactFiniteQuantum

include("RInfScalar.jl")

export RInfScalar, DyadicCoefficient, RInfCapacityError, rinf_phase,
       ReferenceLimits, ReferenceCapacityError, ExactState, basis_state,
       apply_gate, hadamard, phase_gate, apply_permutation,
       modular_multiplication, controlled_powers, qft, inverse_qft,
       norm_squared, born_probabilities

"""A full-state reference limit, not a quantum resource certificate."""
struct ReferenceCapacityError <: Exception
    message::String
end
Base.showerror(io::IO, e::ReferenceCapacityError) =
    print(io, "finite reference capacity exceeded: ", e.message)

"""Lowerable ceilings: dense basis entries and conservative index visits per operation.
Scalar integer/support/product limits remain those of RInfScalar, independently.
"""
struct ReferenceLimits
    max_basis::Int
    max_work::Int
    function ReferenceLimits(; max_basis::Integer=4096, max_work::Integer=1_000_000)
        1 <= max_basis <= 4096 || throw(ArgumentError("max_basis must be in 1:4096"))
        0 <= max_work <= 1_000_000 || throw(ArgumentError("max_work must be in 0:1000000"))
        new(Int(max_basis), Int(max_work))
    end
end

function _dimension(n::Integer, limits::ReferenceLimits)
    n >= 0 || throw(ArgumentError("negative register width"))
    # Compare before shifting or converting potentially enormous input integers.
    n <= 12 || throw(ReferenceCapacityError("at most 12 qubits / 4096 basis entries"))
    d = 1 << Int(n)
    d <= limits.max_basis || throw(ReferenceCapacityError("dense basis entries"))
    return d
end
function _work(limits::ReferenceLimits, count::Integer)
    count <= limits.max_work || throw(ReferenceCapacityError("operation index visits"))
end

"""Exact vector: amplitudes[b+1] is |b⟩, bit 0 is least significant.
The constructor copies its input. Operations never mutate inputs or renormalize.
The amplitude vector is inspectable; callers must not mutate it.
"""
struct ExactState
    nqubits::Int
    amplitudes::Vector{RInfScalar}
    limits::ReferenceLimits
    function ExactState(n::Integer, amplitudes::AbstractVector{RInfScalar};
                        limits::ReferenceLimits=ReferenceLimits())
        d = _dimension(n, limits)
        length(amplitudes) == d || throw(DimensionMismatch("state dimension"))
        _work(limits, d)
        new(Int(n), collect(amplitudes), limits)
    end
end

function basis_state(n::Integer, b::Integer=0; limits::ReferenceLimits=ReferenceLimits())
    d = _dimension(n, limits)
    0 <= b < d || throw(ArgumentError("basis index out of range"))
    _work(limits, 2d) # Initialization and the owned constructor copy.
    v = fill(zero(RInfScalar), d)
    v[Int(b)+1] = one(RInfScalar)
    return ExactState(n, v; limits)
end

function _register(s::ExactState, offset::Integer, width::Integer)
    0 <= offset <= s.nqubits && 0 <= width <= s.nqubits-offset ||
        throw(ArgumentError("register outside state"))
    length(s.amplitudes) == 1 << s.nqubits || throw(DimensionMismatch("state dimension"))
    return Int(offset), Int(width)
end
function _control(s::ExactState, control, offset::Int, width::Int)
    isnothing(control) && return 0
    control isa Integer || throw(ArgumentError("control must be an integer bit index"))
    c, _ = _register(s, control, 1)
    offset <= c < offset+width && throw(ArgumentError("control overlaps target"))
    return 1 << c
end
_output(s::ExactState, v) = ExactState(s.nqubits, v; limits=s.limits)

"""Apply an exactly unitary 2×2 matrix to one bit, optionally controlled on |1⟩.
Matrix rows/columns are output/input in the order |0⟩, |1⟩.
"""
function apply_gate(s::ExactState, target::Integer, gate::AbstractMatrix{RInfScalar};
                    control=nothing)
    t, _ = _register(s, target, 1)
    c = _control(s, control, t, 1)
    size(gate) == (2, 2) || throw(DimensionMismatch("single-qubit gate"))
    _work(s.limits, 4length(s.amplitudes) + 8)
    for i in 1:2, j in 1:2
        gram = conj(gate[1,i])*gate[1,j] + conj(gate[2,i])*gate[2,j]
        gram == RInfScalar(i == j) || throw(ArgumentError("gate is not exactly unitary"))
    end
    v = copy(s.amplitudes)
    mask = 1 << t
    for b in 0:length(v)-1
        iszero(b & mask) && (iszero(c) || !iszero(b & c)) || continue
        i, j = b+1, (b | mask)+1
        a, z = s.amplitudes[i], s.amplitudes[j]
        v[i] = gate[1,1]*a + gate[1,2]*z
        v[j] = gate[2,1]*a + gate[2,2]*z
    end
    return _output(s, v)
end

const INV_SQRT2 = RInfScalar(1//2) * (rinf_phase(1,3) + rinf_phase(-1,3))
hadamard(s::ExactState, target::Integer) =
    apply_gate(s, target, [INV_SQRT2 INV_SQRT2; INV_SQRT2 -INV_SQRT2])

"""Multiply the |1⟩ amplitude by exp(2πi*n/2^k), optionally with a second control."""
function phase_gate(s::ExactState, target::Integer, n::Integer, k::Integer;
                    control=nothing)
    t, _ = _register(s, target, 1)
    c = _control(s, control, t, 1)
    _work(s.limits, 2length(s.amplitudes))
    phase = rinf_phase(n, k) # Scalar capacity failures deliberately propagate.
    mask = (1 << t) | c
    return _output(s, [b & mask == mask ? a*phase : a
                       for (b,a) in zip(0:length(s.amplitudes)-1, s.amplitudes)])
end

function _permutation(p::AbstractVector{<:Integer}, limits::ReferenceLimits)
    d = length(p)
    d > 0 && ispow2(d) || throw(ArgumentError("permutation dimension must be a power of two"))
    d <= limits.max_basis || throw(ReferenceCapacityError("permutation basis entries"))
    _work(limits, 3d) # Seen-table initialization, validation and the Int copy.
    seen = falses(d)
    for y in p
        0 <= y < d || throw(ArgumentError("permutation image out of range"))
        seen[Int(y)+1] && throw(ArgumentError("non-bijective basis map"))
        seen[Int(y)+1] = true
    end
    return Int.(p), trailing_zeros(d)
end

"""p[x+1] is the output label of input x on a contiguous register.
The complete basis map must be bijective, including unused work encodings.
"""
function apply_permutation(s::ExactState, p::AbstractVector{<:Integer};
                           offset::Integer=0, control=nothing)
    p, width = _permutation(p, s.limits)
    o, _ = _register(s, offset, width)
    c = _control(s, control, o, width)
    _work(s.limits, 3length(p) + 2length(s.amplitudes))
    mask = (length(p)-1) << o
    v = similar(s.amplitudes)
    for b in 0:length(v)-1
        x = (b & mask) >> o
        out = iszero(c) || !iszero(b & c) ? (b & ~mask) | (p[x+1] << o) : b
        v[out+1] = s.amplitudes[b+1]
    end
    return _output(s, v)
end

"""x ↦ a*x mod N for 0 ≤ x < N; fix every N ≤ x < 2^work_bits.
Require gcd(a,N)=1, so this extension permutes the entire register basis.
"""
function modular_multiplication(a::Integer, N::Integer, work_bits::Integer;
                                limits::ReferenceLimits=ReferenceLimits())
    d = _dimension(work_bits, limits)
    2 <= N <= d || throw(ArgumentError("modulus must fit the work register"))
    gcd(a,N) == 1 || throw(ArgumentError("modular multiplier must be coprime to N"))
    _work(limits, d)
    multiplier = mod(big(a), N)
    return [x < N ? Int(mod(multiplier*x, N)) : x for x in 0:d-1]
end

"""Apply U^(2^j) controlled by bit control_offset+j, j=0:control_bits-1.
U is a full-basis permutation. Powers are formed by exact permutation squaring.
"""
function controlled_powers(s::ExactState, p::AbstractVector{<:Integer};
                           target_offset::Integer=0, control_offset::Integer,
                           control_bits::Integer)
    p, width = _permutation(p, s.limits)
    t, _ = _register(s, target_offset, width)
    c, n = _register(s, control_offset, control_bits)
    (n == 0 || width == 0 || t+width <= c || c+n <= t) ||
        throw(ArgumentError("control and target registers overlap"))
    _work(s.limits, 3length(p) + n*(4length(p) + 2length(s.amplitudes)))
    result = s
    for j in 0:n-1
        result = apply_permutation(result, p; offset=t, control=c+j)
        j+1 < n && (p = [p[x+1] for x in p])
    end
    return result
end

function _swap_bits(s::ExactState, a::Int, b::Int)
    v = similar(s.amplitudes)
    mask = (1 << a) | (1 << b)
    for x in 0:length(v)-1
        y = ((x >> a) & 1) == ((x >> b) & 1) ? x : xor(x, mask)
        v[y+1] = s.amplitudes[x+1]
    end
    return _output(s, v)
end

"""F[y,x] = exp(+2πi*x*y/2^width)/sqrt(2^width) on the selected register.
Includes bit reversal: both input and output labels are ordinary integers.
inverse=true applies F† (negative phase), with the swaps at the beginning.
"""
function qft(s::ExactState; offset::Integer=0, width::Integer=s.nqubits,
             inverse::Bool=false)
    o, n = _register(s, offset, width)
    d = length(s.amplitudes)
    # Includes every gate's preflight and the full sequence, not just the largest gate.
    _work(s.limits, n*(4d+8) + div(n*(n-1),2)*2d + div(n,2)*2d + d)
    result = s
    if inverse
        for j in 0:div(n,2)-1
            result = _swap_bits(result, o+j, o+n-1-j)
        end
        for t in 0:n-1
            for c in 0:t-1
                result = phase_gate(result, o+t, -1, t-c+1; control=o+c)
            end
            result = hadamard(result, o+t)
        end
    else
        for t in n-1:-1:0
            result = hadamard(result, o+t)
            for c in t-1:-1:0
                result = phase_gate(result, o+t, 1, t-c+1; control=o+c)
            end
        end
        for j in 0:div(n,2)-1
            result = _swap_bits(result, o+j, o+n-1-j)
        end
    end
    return result
end
inverse_qft(s::ExactState; kwargs...) = qft(s; inverse=true, kwargs...)

function norm_squared(s::ExactState)
    _register(s, 0, s.nqubits)
    _work(s.limits, 2length(s.amplitudes))
    return sum((conj(a)*a for a in s.amplitudes); init=zero(RInfScalar))
end

"""Exact marginal Born probabilities, indexed by y+1, summing over all spectators.
Reject unnormalized input instead of silently conditioning or dividing by its norm.
"""
function born_probabilities(s::ExactState; offset::Integer=0, width::Integer=s.nqubits)
    o, n = _register(s, offset, width)
    _work(s.limits, 4length(s.amplitudes) + (1 << n))
    isone(norm_squared(s)) || throw(ArgumentError("Born probabilities require a normalized state"))
    weights = fill(zero(RInfScalar), 1 << n)
    for b in 0:length(s.amplitudes)-1
        y = (b >> o) & ((1 << n)-1)
        a = s.amplitudes[b+1]
        weights[y+1] = weights[y+1] + conj(a)*a
    end
    return weights
end

end # module
