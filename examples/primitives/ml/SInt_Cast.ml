open SInt_UInt8
open SInt_UInt32
open SInt_UInt63
open SInt_UInt64

let uint8_to_uint32  (s:uint8) : uint32 = SInt_UInt32.of_int (SInt_UInt8.to_int s)
let uint8_to_uint63  (s:uint8) : uint63 = SInt_UInt63.of_int (SInt_UInt8.to_int s)
let uint8_to_uint64  (s:uint8) : uint64 = SInt_UInt64.of_int (SInt_UInt8.to_int s)

let uint32_to_uint8  (s:uint32) : uint8  = SInt_UInt8.of_int  (SInt_UInt32.to_int s)
let uint32_to_uint63 (s:uint32) : uint63 = SInt_UInt63.of_int (SInt_UInt32.to_int s)
let uint32_to_uint64 (s:uint32) : uint64 = SInt_UInt64.of_int (SInt_UInt32.to_int s)

let uint63_to_uint8  (s:uint63) : uint8  = SInt_UInt8.of_int  (SInt_UInt63.to_int s)
let uint63_to_uint32 (s:uint63) : uint32 = SInt_UInt32.of_int (SInt_UInt63.to_int s)
let uint63_to_uint64 (s:uint63) : uint64 = SInt_UInt64.of_int (SInt_UInt63.to_int s)

let uint64_to_uint8  (s:uint64) : uint8  = SInt_UInt8.of_int  (SInt_UInt64.to_int s)
let uint64_to_uint32 (s:uint64) : uint32 = SInt_UInt32.of_int (SInt_UInt64.to_int s)
let uint64_to_uint63 (s:uint64) : uint63 = SInt_UInt63.of_int (SInt_UInt64.to_int s)

let uint128_to_uint64 (a:uint128) : uint64 = SInt_UInt64.of_string (SInt_UInt64.uint128_to_string a)
let uint64_to_uint128 (a:uint64) : uint128 = SInt_UInt64.uint128_of_string (SInt_UInt64.to_string a)
