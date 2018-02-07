module FStar.Int.Cast.Full

include FStar.Int.Cast

module U64  = FStar.UInt64
module U128 = FStar.UInt128

val uint64_to_uint128: a:U64.t -> b:U128.t{U128.v b == U64.v a}
let uint64_to_uint128 a = U128.uint64_to_uint128 a

val uint128_to_uint64: a:U128.t -> b:U64.t{U64.v b == U128.v a % pow2 64}
let uint128_to_uint64 a = U128.uint128_to_uint64 a
