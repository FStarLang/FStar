module SInt.Cast

open SInt
open SInt.UInt8
open SInt.UInt32
open SInt.UInt63
open SInt.UInt64

let uint8_to_uint32 (a:uint8) : Tot uint32 = to_usint 32 a
let uint8_to_uint63 (a:uint8) : Tot uint63 = to_usint 63 a
let uint8_to_uint64 (a:uint8) : Tot uint64 = to_usint 64 a

let uint32_to_uint8  (a:uint8) :  Tot uint8 =  to_usint 8 a
let uint32_to_uint63 (a:uint32) : Tot uint63 = to_usint 63 a
let uint32_to_uint64 (a:uint32) : Tot uint64 = to_usint 64 a

let uint63_to_uint8  (a:uint63) : Tot uint8 =  to_usint 8 a
let uint63_to_uint32 (a:uint63) : Tot uint32 = to_usint 32 a
let uint63_to_uint64 (a:uint63) : Tot uint64 = to_usint 64 a

let uint64_to_uint8  (a:uint8)  : Tot uint8 =  to_usint 8 a
let uint64_to_uint32 (a:uint64) : Tot uint32 = to_usint 32 a
let uint64_to_uint63 (a:uint64) : Tot uint63 = to_usint 63 a

let uint128_to_uint64 (a:uint128) : Tot uint64 = to_usint 64 a
let uint64_to_uint128 (a:uint64) : Tot uint128 = to_usint 128 a
