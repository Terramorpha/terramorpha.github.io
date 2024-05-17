abstract type Encodable end
function encdecsize(t::Type{A}) where {A <: Encodable}
    # ...
    # ...
    encodefunc, decodefunc, sizeofencoding
end

function encdecsize(::Type{Float64})
	encode(f) = [f]
	decode(v) = v[1]
	encode, decode, 1
end

@show Float64 isa Type{Float64}

@show en, de, s = encdecsize(Float64)
@show encoded = en(1.0)
@show decoded = de(encoded)

function encdecsize(::Type{Missing})
	encode(v) = Float64[]
	decode(v) = missing
	encode, decode, 0
end

function encdecsize(::Type{Bool})
	encode(v) = [1.0*v]
	decode(v) = v[1] > 0.5
	encode, decode, 1
end

function encdecsize(::Type{T}) where {T <: Tuple}
	encs = []
	decs = []
	sizes = Int[]
    
    # We collect encoding functions, decoding functions and encoding
    # sizes for each component type.
	for t in T.types
		enc, dec, s = encdecsize(t)
		push!(encs, enc)
		push!(decs, dec)
		push!(sizes, s)
	end

	function encode(tuple::T)
		out = Float64[]
        # We concatenate the encoded components.
		for (i, elem) in enumerate(tuple)
			out = vcat(out, encs[i](elem))
		end
		out
	end
	function decode(v)::T
		start = 1
		out = []
		for (i, s) in enumerate(sizes)
            # each time we decode a component, we must "consume" the
            # associated part of the vector
			push!(out, decs[i](v[start:start+s-1]))
			start += s
		end
        # we turn back the Vector of Any into a tuple
		(out...,)
	end
	encode, decode, sum(sizes)
end

@show Union{Float32, Bool} isa Union

function pad(v, len)
	vcat(v, zeros(max(0, len - length(v))))
end

function binenc(n, len)
	[1.0 * (n>>i & 1)

     for i in 0:len-1]
end
function bindec(v)
	sum(v[i+1] * 2^i
		for i in 0:length(v)-1)
end

gettypes(u::Type) = [u]
gettypes(u::Union) = [u.a;gettypes(u.b)]

function encdecsize(un::Union)
	encs = []
	decs = []
	sizes = Int[]
	types = gettypes(un)

    # As before, we collect enc, dec and size of each subtype.
	for t in types
		enc, dec, s = encdecsize(t)
		push!(encs, enc)
		push!(decs, dec)
		push!(sizes, s)
	end

	n = length(types)

    # The tag must contain enough "bits" to encode every variant.
	tagsize = Int(ceil(log(2, n)))

    # Apart from the tag, we must be able to encode the biggest
    # variant.
	innersize = maximum(sizes)

	function encode(v)
		for (i, t) in enumerate(types)
			if v isa t
                # We write the tag, then the padded encoded value.
				return vcat(
                    binenc(i-1, tagsize),
                    pad(encs[i](v), innersize),
                )
			end
		end
	end

	function decode(v)
		tag = v[1:tagsize]
        # We calculate the tag, then retrieve the correct decoding
        # function.
		dectag = bindec(tag) |> round |> Int
		d = decs[dectag+1](v[tagsize+1:tagsize+sizes[dectag]])
	end
	encode, decode, tagsize+innersize
end

let
    vec = Tuple{Float64, Bool, Union{Missing, Float64}}[
        (1.0, false, missing),
        (2.0, true, 15.0),
        (2.0, true, 13.0),
    ]

    en, de, _ = encdecsize(eltype(typeof(vec)))
    for v in vec
        @show encoded = en(v)
        @show decoded = de(encoded)
    end
end
