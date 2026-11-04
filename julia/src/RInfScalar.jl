# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
# Exact Julia reference implementation for Qleisli issue #339.
# Include this file in a fresh Julia session (or in a module of your own).
# The arithmetic core has no package dependencies and never uses floating point.
# This is NOT a Rust/Lean implementation or a Lean-kernel-checked proof.
#
# Mathematical domain: finite sums c*exp(2pi*i*p/2^k), with dyadic c and
# canonical phases in [0,1/2). The limits below are executable capacity policies,
# NOT restrictions in the definition of R_infinity. They may reject an exact
# computation; they must never silently change its value. Increase them in a
# controlled deployment if required. Exponents are also limited to Int capacity.
# Sparse arithmetic may have intrinsically exponential output support.
# At a common level K >= 1 the basis keys select distinct powers of the root
# below the degree of its minimal polynomial X^(2^(K-1)) + 1. Their dyadic
# coefficients thus determine the scalar uniquely.
#
# Compatibility: the original type/function names are retained. Constructors
# now normalize immediately. `terms` is an immutable tuple, preventing callers
# from breaking the sorted/no-duplicates/no-zero invariant by pushing to a vector.
# Constructors own their BigInts and the public numerator property returns a copy.
# Raw field access via getfield is internal and must be treated as read-only.
#
# Example:
#   include("julia/src/RInfScalar.jl")
#   x = rinf_phase(-1,3)
#   @assert x * conj(x) == one(RInfScalar)
#   @assert decode_rinf(encode_rinf(x)) == x
# Run the dependency-free tests with:
#   julia --startup-file=no julia/test/test_rinf_scalar.jl

const RINF_MAX_INTEGER_BITS = 1_000_000
const RINF_MAX_TERMS = 100_000
const RINF_MAX_WORK = 1_000_000
const RINF_WIRE_VERSION = "rinfty-sparse-v1"

struct RInfCapacityError <: Exception
    message::String
end
Base.showerror(io::IO, e::RInfCapacityError) = print(io, "RInf capacity exceeded: ", e.message)

_rinf_bits(n::Integer) = iszero(n) ? 0 : ndigits(n; base=2)
function _rinf_exponent(k::Integer)
    k >= 0 || throw(DomainError(k, "a dyadic exponent must be nonnegative"))
    k <= typemax(Int) || throw(RInfCapacityError("exponent does not fit Int"))
    return Int(k)
end
function _rinf_shift(n::BigInt, k::Int, max_bits::Int=RINF_MAX_INTEGER_BITS)
    k >= 0 || throw(ArgumentError("negative left shift"))
    iszero(n) && return big(0)
    k <= max_bits - _rinf_bits(n) ||
        throw(RInfCapacityError("shifted integer bit length"))
    return n << k
end
_rinf_pow2(k::Int) = _rinf_shift(big(1), k)
function _rinf_reduce(n::Integer, k::Integer)
    e = _rinf_exponent(k)
    z = BigInt(n)
    iszero(z) && return (big(0), 0)
    t = min(trailing_zeros(z), e)
    _rinf_bits(z) - t <= RINF_MAX_INTEGER_BITS || throw(RInfCapacityError("integer bit length"))
    # A zero shift can alias the BigInt returned by the input conversion.
    a = t == 0 ? deepcopy(z) : z >> t
    return (a, e - t)
end

"""Exact n/2^k, canonical on construction; even integer numerators are retained."""
struct DyadicCoefficient
    numerator::BigInt
    exponent::Int
    function DyadicCoefficient(n::Integer, k::Integer=0)
        a, e = _rinf_reduce(n, k)
        new(a, e)
    end
end
function _rinf_dyadic_exponent(q::Rational)
    d = denominator(q)
    ispow2(d) || throw(DomainError(q, "denominator must be a power of two"))
    return trailing_zeros(d)
end
DyadicCoefficient(q::Rational) = DyadicCoefficient(numerator(q), _rinf_dyadic_exponent(q))
DyadicCoefficient(c::DyadicCoefficient) = c
normalize(c::DyadicCoefficient) = c
Base.zero(::Type{DyadicCoefficient}) = DyadicCoefficient(0)
Base.one(::Type{DyadicCoefficient}) = DyadicCoefficient(1)
Base.zero(::DyadicCoefficient) = zero(DyadicCoefficient)
Base.one(::DyadicCoefficient) = one(DyadicCoefficient)
Base.iszero(c::DyadicCoefficient) = iszero(_rinf_numerator(c))
Base.isone(c::DyadicCoefficient) = c.exponent == 0 && isone(_rinf_numerator(c))
Base.:(==)(a::DyadicCoefficient, b::DyadicCoefficient) =
    a.exponent == b.exponent && _rinf_numerator(a) == _rinf_numerator(b)
Base.isequal(a::DyadicCoefficient, b::DyadicCoefficient) = a == b
Base.hash(c::DyadicCoefficient, h::UInt) = hash((_rinf_numerator(c), c.exponent), h)
Base.:-(c::DyadicCoefficient) = DyadicCoefficient(-_rinf_numerator(c), c.exponent)
function Base.:+(a::DyadicCoefficient, b::DyadicCoefficient)
    iszero(a) && return b
    iszero(b) && return a
    k = max(a.exponent, b.exponent)
    # The other numerator can cancel one excess bit. With unequal exponents
    # the sum is odd, so a wider aligned numerator cannot reduce back into range.
    work_bits = RINF_MAX_INTEGER_BITS + 1
    n = _rinf_shift(_rinf_numerator(a), k-a.exponent, work_bits) +
        _rinf_shift(_rinf_numerator(b), k-b.exponent, work_bits)
    return DyadicCoefficient(n, k)
end
Base.:-(a::DyadicCoefficient, b::DyadicCoefficient) = a + (-b)
function Base.:*(a::DyadicCoefficient, b::DyadicCoefficient)
    (iszero(a) || iszero(b)) && return zero(DyadicCoefficient)
    # Cancel integer powers of two across factors before sizing the product.
    k = _rinf_exponent(big(a.exponent) + b.exponent)
    na, nb = _rinf_numerator(a), _rinf_numerator(b)
    ta = min(trailing_zeros(na), k)
    na >>= ta
    k -= ta
    tb = min(trailing_zeros(nb), k)
    nb >>= tb
    k -= tb
    _rinf_bits(na) + _rinf_bits(nb) - 1 <= RINF_MAX_INTEGER_BITS ||
        throw(RInfCapacityError("coefficient product bit length"))
    return DyadicCoefficient(na * nb, k)
end

"""A basis key in [0,1/2), not a general phase constructor; out-of-range keys fail."""
struct PhaseKey
    numerator::BigInt
    exponent::Int
    function PhaseKey(n::Integer, k::Integer)
        e = _rinf_exponent(k)
        n >= 0 || throw(DomainError(n, "a basis key must be nonnegative"))
        # Use a bit-length comparison, without constructing an enormous 2^e.
        if !iszero(n) && (e == 0 || _rinf_bits(n) > e - 1)
            throw(DomainError((n,k), "PhaseKey must be in [0, 1/2)"))
        end
        p, j = _rinf_reduce(n, e)
        new(p, j)
    end
end
# Borrow the owned numerator for internal, non-mutating operations.
_rinf_numerator(x::Union{PhaseKey,DyadicCoefficient}) = getfield(x, :numerator)
function Base.getproperty(x::Union{PhaseKey,DyadicCoefficient}, name::Symbol)
    name === :numerator && return deepcopy(_rinf_numerator(x))
    return getfield(x, name)
end
normalize(p::PhaseKey) = p
Base.:(==)(a::PhaseKey, b::PhaseKey) =
    a.exponent == b.exponent && _rinf_numerator(a) == _rinf_numerator(b)
Base.isequal(a::PhaseKey, b::PhaseKey) = a == b
Base.hash(p::PhaseKey, h::UInt) = hash((_rinf_numerator(p), p.exponent), h)
function Base.isless(a::PhaseKey, b::PhaseKey)
    na, nb = _rinf_numerator(a), _rinf_numerator(b)
    iszero(na) && return !iszero(nb)
    iszero(nb) && return false
    # Different leading binary positions can be compared without a shift.
    la = _rinf_bits(na) - a.exponent
    lb = _rinf_bits(nb) - b.exponent
    la != lb && return la < lb
    k = max(a.exponent, b.exponent)
    return _rinf_shift(na, k-a.exponent) < _rinf_shift(nb, k-b.exponent)
end

struct Term
    phase::PhaseKey
    coeff::DyadicCoefficient
end
normalize(t::Term) = t
Base.:(==)(a::Term, b::Term) = a.phase == b.phase && a.coeff == b.coeff
Base.isequal(a::Term, b::Term) = a == b
Base.hash(t::Term, h::UInt) = hash((t.phase, t.coeff), h)

# Common phase reduction for signed phase construction, multiplication and conj.
function _rinf_phase_term(n::Integer, k::Integer, c::DyadicCoefficient)
    e = _rinf_exponent(k)
    if e == 0 || iszero(c)
        return Term(PhaseKey(0,0), c)
    end
    if n >= 0 && _rinf_bits(n) <= e - 1
        return Term(PhaseKey(n,e), c)
    end
    z = BigInt(n)
    t = min(trailing_zeros(z), e)
    z >>= t
    e -= t
    e == 0 && return Term(PhaseKey(0,0), c)

    # Dividing by the half-period gives a basis numerator and a quotient
    # whose parity supplies the sign. For a huge exponent, check that any
    # remainder bits above the storage limit are zero before forming the modulus.
    half_bits = e - 1
    bits = min(half_bits, RINF_MAX_INTEGER_BITS)
    high = z >> bits
    extra = half_bits - bits
    if extra > 0 && !iszero(high) && trailing_zeros(high) < extra
        throw(RInfCapacityError("phase numerator bit length"))
    end
    p = mod(z, big(1) << bits)
    return Term(PhaseKey(p,e), isodd(high >> extra) ? -c : c)
end
function Base.:*(a::Term, b::Term)
    c = a.coeff * b.coeff
    iszero(c) && return Term(PhaseKey(0,0), c)
    k = max(a.phase.exponent, b.phase.exponent)
    # With an M-bit storage limit, shifting a nonzero phase by M or more
    # places leaves it at least 2^M from both zero and the half-period.
    # Thus twice the storage width covers every alignment that can wrap into range.
    work_bits = 2 * RINF_MAX_INTEGER_BITS
    n = _rinf_shift(_rinf_numerator(a.phase), k-a.phase.exponent, work_bits) +
        _rinf_shift(_rinf_numerator(b.phase), k-b.phase.exponent, work_bits)
    return _rinf_phase_term(n, k, c)
end
Base.conj(t::Term) = _rinf_phase_term(-_rinf_numerator(t.phase), t.phase.exponent, t.coeff)

function _rinf_accumulate!(d::Dict{PhaseKey,DyadicCoefficient}, t::Term)
    iszero(t.coeff) && return d
    c = get(d, t.phase, zero(DyadicCoefficient)) + t.coeff
    if iszero(c)
        delete!(d, t.phase)
    else
        if !haskey(d, t.phase) && length(d) >= RINF_MAX_TERMS
            throw(RInfCapacityError("intermediate support size"))
        end
        d[t.phase] = c
    end
    return d
end
function _rinf_canonical_terms(terms)
    d = Dict{PhaseKey,DyadicCoefficient}()
    work = 0
    for t in terms
        t isa Term || throw(ArgumentError("RInfScalar expects Terms"))
        work += 1
        work <= RINF_MAX_WORK || throw(RInfCapacityError("input term count"))
        _rinf_accumulate!(d, t)
    end
    return Tuple(Term(p, d[p]) for p in sort!(collect(keys(d))))
end

"""Canonical, finite, exactly phase-sorted sparse scalar. Zero has no terms."""
struct RInfScalar
    terms::Tuple{Vararg{Term}}
    function RInfScalar(terms)
        new(_rinf_canonical_terms(terms))
    end
end
RInfScalar() = RInfScalar(())
RInfScalar(c::DyadicCoefficient) = RInfScalar((Term(PhaseKey(0,0), c),))
RInfScalar(n::Integer) = RInfScalar(DyadicCoefficient(n))
RInfScalar(q::Rational) = RInfScalar(DyadicCoefficient(q))
RInfScalar(x::RInfScalar) = x
canonicalize(x::RInfScalar) = x
normalize(x::RInfScalar) = x
Base.zero(::Type{RInfScalar}) = RInfScalar()
Base.one(::Type{RInfScalar}) = RInfScalar(1)
Base.zero(::RInfScalar) = zero(RInfScalar)
Base.one(::RInfScalar) = one(RInfScalar)
Base.iszero(x::RInfScalar) = isempty(x.terms)
Base.isone(x::RInfScalar) = length(x.terms) == 1 &&
    iszero(_rinf_numerator(x.terms[1].phase)) && isone(x.terms[1].coeff)
Base.:(==)(a::RInfScalar, b::RInfScalar) = a.terms == b.terms
Base.isequal(a::RInfScalar, b::RInfScalar) = a == b
Base.hash(x::RInfScalar, h::UInt) = hash(x.terms, h)
Base.:+(a::RInfScalar, b::RInfScalar) = RInfScalar(Iterators.flatten((a.terms,b.terms)))
Base.:-(x::RInfScalar) = RInfScalar(Term(t.phase,-t.coeff) for t in x.terms)
Base.:-(a::RInfScalar, b::RInfScalar) = a + (-b)
function Base.:*(a::RInfScalar, b::RInfScalar)
    (iszero(a) || iszero(b)) && return zero(RInfScalar)
    length(a.terms) <= div(RINF_MAX_WORK, length(b.terms)) ||
        throw(RInfCapacityError("pair-product count"))
    # Accumulate directly; never allocate a dense cyclotomic or pair-product array.
    d = Dict{PhaseKey,DyadicCoefficient}()
    for x in a.terms, y in b.terms
        _rinf_accumulate!(d, x*y)
    end
    return RInfScalar(Term(p,c) for (p,c) in d)
end
Base.conj(x::RInfScalar) = RInfScalar(conj(t) for t in x.terms)
function Base.:^(x::RInfScalar, n::Integer)
    n >= 0 || throw(DomainError(n, "negative powers/inversion are not implemented"))
    y = one(RInfScalar)
    b = x
    while n > 0
        isodd(n) && (y = y*b)
        n >>= 1
        n > 0 && (b = b*b)
    end
    return y
end
# Route literal negative exponents through the same explicit rejection policy.
Base.literal_pow(::typeof(^), x::RInfScalar, ::Val{n}) where {n} = x^n

"""rinf_phase(n,k): exact exp(2pi*i*n/2^k), accepting signed, unreduced n."""
rinf_phase(n::Integer, k::Integer) = RInfScalar((_rinf_phase_term(n,k,one(DyadicCoefficient)),))
rinf_phase(c::DyadicCoefficient) = rinf_phase(_rinf_numerator(c),c.exponent)
rinf_phase(q::Rational) = rinf_phase(numerator(q),_rinf_dyadic_exponent(q))

"""Legacy a+b*sqrt(2)+i*(c+d*sqrt(2)) -> the four B3 coordinates."""
function from_r3(a, b, c, d)
    a,b,c,d = map(DyadicCoefficient, (a,b,c,d))
    return RInfScalar((Term(PhaseKey(0,0),a), Term(PhaseKey(1,3),b+d),
                       Term(PhaseKey(1,2),c), Term(PhaseKey(3,3),d-b)))
end
"""Return the exact dyadic tuple (a,b,c,d); reject scalars outside the R3 subring."""
function to_r3(x::RInfScalar)
    all(t.phase.exponent <= 3 for t in x.terms) ||
        throw(DomainError(x,"scalar is outside the R3 subring"))
    d = Dict(t.phase=>t.coeff for t in x.terms)
    z = zero(DyadicCoefficient)
    a = get(d,PhaseKey(0,0),z)
    u = get(d,PhaseKey(1,3),z)
    c = get(d,PhaseKey(1,2),z)
    v = get(d,PhaseKey(3,3),z)

    # With unequal exponents both aligned results are odd, and at least one
    # is as wide as the shifted numerator. That shift must therefore fit.
    k = max(u.exponent, v.exponent)
    u_num = _rinf_shift(_rinf_numerator(u), k - u.exponent)
    v_num = _rinf_shift(_rinf_numerator(v), k - v.exponent)
    b_num, d_num = u_num - v_num, u_num + v_num

    # The sum and difference have the same parity. Apply the factor of 1/2
    # before checking the final numerators or increasing the exponent.
    if iseven(d_num)
        b_num >>= 1
        d_num >>= 1
    else
        k = _rinf_exponent(big(k) + 1)
    end
    return (a, DyadicCoefficient(b_num,k), c, DyadicCoefficient(d_num,k))
end

# Exact wire grammar (UTF-8/ASCII, LF line endings, including final LF):
# rinfty-sparse-v1\n
# <canonical unsigned decimal term count>\n
# <phase numerator> <phase exponent> <signed coefficient numerator> <coefficient exponent>\n
# Strict decoder: rejects noncanonical numeric spellings, noncanonical dyadic
# pairs, zeros, duplicates, wrong ordering, out-of-range keys and trailing data.
# It does not normalize/accept malformed wire representations. This Julia codec
# is a concrete reference format; independent Rust/Lean codecs/proofs remain work.
function encode_rinf(x::RInfScalar)
    io = IOBuffer()
    println(io,RINF_WIRE_VERSION)
    println(io,length(x.terms))
    for t in x.terms
        println(io,_rinf_numerator(t.phase),' ',t.phase.exponent,' ',_rinf_numerator(t.coeff),' ',t.coeff.exponent)
    end
    return String(take!(io))
end
function _rinf_wire_integer(s::AbstractString, signed::Bool, max_digits::Integer)
    pattern = signed ? r"\A(?:0|-?[1-9][0-9]*)\z" : r"\A(?:0|[1-9][0-9]*)\z"
    occursin(pattern,s) || throw(ArgumentError("noncanonical decimal integer"))
    ncodeunits(s) - startswith(s,"-") <= max_digits ||
        throw(RInfCapacityError("wire integer digit count"))
    return parse(BigInt,s)
end
function decode_rinf(wire::AbstractString;
        max_bytes::Integer=16_000_000, max_terms::Integer=RINF_MAX_TERMS,
        max_digits::Integer=310_000, max_exponent::Integer=1_000_000)
    all(x >= 0 for x in (max_bytes,max_terms,max_digits,max_exponent)) ||
        throw(ArgumentError("wire capacities must be nonnegative"))
    ncodeunits(wire) <= max_bytes || throw(RInfCapacityError("wire byte count"))
    header = split(wire,'\n'; limit=3, keepempty=true)
    length(header) == 3 && endswith(wire,'\n') || throw(ArgumentError("missing final LF"))
    version, count_field, body = header
    version == RINF_WIRE_VERSION || throw(ArgumentError("unknown wire version"))
    term_limit = min(max_terms,RINF_MAX_TERMS)
    count = _rinf_wire_integer(count_field,false,min(max_digits,ndigits(term_limit)))
    count <= term_limit || throw(RInfCapacityError("wire term count"))
    term_count = Int(count)

    # Check framing before parsing terms. Stop after the declared number of LFs,
    # even if the rest of the input contains millions of empty lines.
    pos = firstindex(body)
    for _ in 1:term_count
        lf = findnext(isequal('\n'), body, pos)
        isnothing(lf) && throw(ArgumentError("wire term count mismatch"))
        pos = nextind(body, lf)
    end
    pos > lastindex(body) || throw(ArgumentError("wire term count mismatch"))
    terms = Term[]
    for line in Iterators.take(eachsplit(body,'\n'; keepempty=true), term_count)
        f = split(line,' '; limit=5, keepempty=true)
        length(f) == 4 || throw(ArgumentError("expected four integer fields"))
        p,k,n,e = (_rinf_wire_integer(f[i],i==3,max_digits) for i in 1:4)
        max(k,e) <= max_exponent || throw(RInfCapacityError("wire exponent"))
        phase,coeff = PhaseKey(p,k),DyadicCoefficient(n,e)
        (_rinf_numerator(phase),phase.exponent) == (p,k) || throw(ArgumentError("noncanonical phase"))
        (_rinf_numerator(coeff),coeff.exponent) == (n,e) || throw(ArgumentError("noncanonical coefficient"))
        iszero(coeff) && throw(ArgumentError("zero wire term"))
        isempty(terms) || isless(terms[end].phase,phase) ||
            throw(ArgumentError("wire phases must be strictly increasing"))
        push!(terms,Term(phase,coeff))
    end
    return RInfScalar(terms)
end

"""
    RInfScalar2Cyclotomics(x; root=Cyclotomics.E, max_phase_exponent=12)

Optional, exact diagnostic conversion. Load Cyclotomics in the including module
or pass `root=Cyclotomics.E`. Rational{BigInt} coefficients avoid Float64. A small
explicit phase limit prevents accidental exponential work in the external
cyclotomic representation. This limit does not constrain the sparse core.
"""
function RInfScalar2Cyclotomics(x::RInfScalar; root=nothing, max_phase_exponent::Integer=12)
    max_phase_exponent >= 0 || throw(ArgumentError("negative conversion limit"))
    for t in x.terms
        t.phase.exponent <= min(max_phase_exponent,8*sizeof(Int)-2) ||
            throw(RInfCapacityError("external Cyclotomics conversion phase exponent"))
    end
    if root === nothing
        isdefined(@__MODULE__,:Cyclotomics) ||
            throw(ArgumentError("load Cyclotomics first, or pass root=Cyclotomics.E"))
        root = getfield(@__MODULE__,:Cyclotomics).E
    end
    total = (big(0)//big(1)) * root(1)
    for t in x.terms
        c = t.coeff.numerator // _rinf_pow2(t.coeff.exponent)
        total += c * root(1 << t.phase.exponent,Int(t.phase.numerator))
    end
    return total
end

"""Small dependency-free smoke check; see julia/test/test_rinf_scalar.jl for regression tests."""
function check()
    @assert DyadicCoefficient(8,2) == DyadicCoefficient(2,0)
    @assert rinf_phase(1,2)^2 == RInfScalar(-1)
    @assert conj(rinf_phase(1,3)) == rinf_phase(-1,3)
    @assert iszero(one(RInfScalar)-one(RInfScalar))
    @assert from_r3(to_r3(from_r3(1,2,3,4))...) == from_r3(1,2,3,4)
    return nothing
end
