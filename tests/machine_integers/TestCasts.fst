module TestCasts

open FStar.All
open FStar.IO
open FStar.Int.Cast
open FStar.Int.Cast.Full

module I8   = FStar.Int8
module I16  = FStar.Int16
module I32  = FStar.Int32
module I64  = FStar.Int64
module I128 = FStar.Int128
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module U128 = FStar.UInt128

let check s (b:bool) : ML unit =
    if not b then failwith s

let main () : ML int =
    check "u128->u64"
        (U64.to_string (uint128_to_uint64 (U128.uint_to_t (pow2 128 - 1))) = "18446744073709551615");
    check "u64->u32"
        (U32.to_string (uint64_to_uint32 (U64.uint_to_t (pow2 64 - 1))) = "4294967295");
    check "u32->u16"
        (U16.to_string (uint32_to_uint16 (U32.uint_to_t (pow2 32 - 1))) = "65535");
    check "u16->u8"
        (U8.to_string  (uint16_to_uint8  (U16.uint_to_t (pow2 16 - 1))) = "255");
    check "u64->u8"
        (U8.to_string  (uint64_to_uint8 (U64.uint_to_t (pow2 64 - 1))) = "255");
    check "u64->u8'"
        (U8.to_string  (uint64_to_uint8 (U64.uint_to_t (pow2 64 - 255))) = "1");
    check "u64->u8''"
        (U8.to_string  (uint64_to_uint8 (U64.uint_to_t (pow2 64 - 256))) = "0");

    // We don't have this one
    (* check "u128->i64" *)
    (*     (I64.to_string (uint128_to_int64 (U128.uint_to_t (pow2 128 - 1))) = "-1"); *)
    check "u64->i32"
        (I32.to_string (uint64_to_int32 (U64.uint_to_t (pow2 64 - 1))) = "-1");
    check "u32->i16"
        (I16.to_string (uint32_to_int16 (U32.uint_to_t (pow2 32 - 1))) = "-1");
    check "u16->i8"
        (I8.to_string  (uint16_to_int8  (U16.uint_to_t (pow2 16 - 1))) = "-1");
    check "u64->i8"
        (I8.to_string  (uint64_to_int8 (U64.uint_to_t (pow2 64 - 1))) = "-1");
    check "u64->i8'"
        (I8.to_string  (uint64_to_int8 (U64.uint_to_t (pow2 64 - 255))) = "1");
    check "u64->i8''"
        (I8.to_string  (uint64_to_int8 (U64.uint_to_t (pow2 64 - 256))) = "0");
    check "u16->i16"
        (I16.to_string (uint16_to_int16 (U16.uint_to_t (pow2 16 - 1))) = "-1");
    check "u16->i16'"
        (I16.to_string (uint16_to_int16 (U16.uint_to_t (pow2 15 - 1))) = "32767");
    check "u8->i8"
        (I8.to_string  (uint8_to_int8   (U8.uint_to_t (pow2 8 - 1))) = "-1");
    check "u8->i8'"
        (I8.to_string  (uint8_to_int8   (U8.uint_to_t (pow2 7 - 1))) = "127");
    check "u16->i32"
        (I32.to_string (uint16_to_int32 (U16.uint_to_t (pow2 16 - 1))) = "65535");
    check "u16->i32'"
        (I32.to_string (uint16_to_int32 (U16.uint_to_t (pow2 15 - 1))) = "32767");

    // We don't have this one
    (* check "i128->i64" *)
    (*     (I64.to_string (int128_to_int64 (I128.int_to_t (pow2 127 - 1))) = "-1"); *)
    check "i64->i32"
        (I32.to_string (int64_to_int32 (I64.int_to_t (pow2 63 - 1))) = "-1");
    check "i32->i16"
        (I16.to_string (int32_to_int16 (I32.int_to_t (pow2 31 - 1))) = "-1");
    check "i16->i8"
        (I8.to_string  (int16_to_int8  (I16.int_to_t (pow2 15 - 1))) = "-1");
    check "i64->i8"
        (I8.to_string  (int64_to_int8 (I64.int_to_t (pow2 63 - 1))) = "-1");
    check "i64->i8'"
        (I8.to_string  (int64_to_int8 (I64.int_to_t (pow2 63 - 255))) = "1");
    check "i64->i8''"
        (I8.to_string  (int64_to_int8 (I64.int_to_t (pow2 63 - 256))) = "0");

    // We don't have this one
    (* check "i128->u64" *)
    (*     (U64.to_string (int128_to_uint64 (I128.int_to_t (pow2 127 - 1))) = "18446744073709551615"); *)
    check "i64->u32"
        (U32.to_string (int64_to_uint32 (I64.int_to_t (pow2 63 - 1))) = "4294967295");
    check "i32->u16"
        (U16.to_string (int32_to_uint16 (I32.int_to_t (pow2 31 - 1))) = "65535");
    check "i16->u8"
        (U8.to_string  (int16_to_uint8  (I16.int_to_t (pow2 15 - 1))) = "255");
    check "i64->u8"
        (U8.to_string  (int64_to_uint8 (I64.int_to_t (pow2 63 - 1))) = "255");
    check "i64->u8'"
        (U8.to_string  (int64_to_uint8 (I64.int_to_t (pow2 63 - 255))) = "1");
    check "i64->u8''"
        (U8.to_string  (int64_to_uint8 (I64.int_to_t (pow2 63 - 256))) = "0");

    print_string "correct\n";
    0
