module TestCasts

open FStar.All
open FStar.IO
open FStar.Int.Cast
open FStar.Int.Cast.Full

module I8   = FStar.Int8
module I16  = FStar.Int16
module I32  = FStar.Int32
module I64  = FStar.Int64
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module U128 = FStar.UInt128

let check s (b:bool) =
    if not b then failwith s

let main () =
    check "u128->u64" (U64.to_string (uint128_to_uint64 (U128.uint_to_t (pow2 128 - 1))) = "18446744073709551615");
    check "u64->u32"  (U32.to_string (uint64_to_uint32 (U64.uint_to_t (pow2 64 - 1))) = "4294967295");
    check "u32->u16"  (U16.to_string (uint32_to_uint16 (U32.uint_to_t (pow2 32 - 1))) = "65535");
    check "u16->u8"   (U8.to_string  (uint16_to_uint8  (U16.uint_to_t (pow2 16 - 1))) = "255");

    check "u64->u8"   (U8.to_string  (uint64_to_uint8 (U64.uint_to_t (pow2 64 - 1))) = "255");
    check "u64->u8"   (U8.to_string  (uint64_to_uint8 (U64.uint_to_t (pow2 64 - 255))) = "1");
    check "u64->u8"   (U8.to_string  (uint64_to_uint8 (U64.uint_to_t (pow2 64 - 256))) = "0");

    print_string "correct\n";
    0
