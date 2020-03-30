module TestShift

open FStar.All
open FStar.IO
open FStar.Int.Cast
open FStar.Int.Cast.Full
open FStar.Tactics

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

let test_u32 () : ML unit =
    check "u32r0"
        (U32.to_string (U32.uint_to_t (pow2 32 - 1) `U32.shift_right` 0ul)  = "4294967295");
    check "u32r1"
        (U32.to_string (U32.uint_to_t (pow2 32 - 1) `U32.shift_right` 1ul)  = "2147483647");
    check "u32r8"
        (U32.to_string (U32.uint_to_t (pow2 32 - 1) `U32.shift_right` 8ul)  = "16777215");
    check "u32r16"
        (U32.to_string (U32.uint_to_t (pow2 32 - 1) `U32.shift_right` 16ul) = "65535");
    check "u32r24"
        (U32.to_string (U32.uint_to_t (pow2 32 - 1) `U32.shift_right` 24ul) = "255");
    check "u32r31"
        (U32.to_string (U32.uint_to_t (pow2 32 - 1) `U32.shift_right` 31ul) = "1");

    check "u32l0"
        (U32.to_string (U32.uint_to_t 1 `U32.shift_left` 0ul)  = "1");
    check "u32l1"
        (U32.to_string (U32.uint_to_t 1 `U32.shift_left` 1ul)  = "2");
    check "u32l8"
        (U32.to_string (U32.uint_to_t 1 `U32.shift_left` 8ul)  = "256");
    check "u32l16"
        (U32.to_string (U32.uint_to_t 1 `U32.shift_left` 16ul) = "65536");
    check "u32l24"
        (U32.to_string (U32.uint_to_t 1 `U32.shift_left` 24ul) = "16777216");
    check "u32l31"
        (U32.to_string (U32.uint_to_t 1 `U32.shift_left` 31ul) = "2147483648");
    ()

let test_u8 () : ML unit =
    check "u8r0"
        (U8.to_string (U8.uint_to_t (pow2 8 - 1) `U8.shift_right` 0ul)  = "255");
    check "u8r1"
        (U8.to_string (U8.uint_to_t (pow2 8 - 1) `U8.shift_right` 1ul)  = "127");
    check "u8r7"
        (U8.to_string (U8.uint_to_t (pow2 8 - 1) `U8.shift_right` 7ul)  = "1");

    check "u8l0"
        (U8.to_string (U8.uint_to_t 1 `U8.shift_left` 0ul)  = "1");
    check "u8l1"
        (U8.to_string (U8.uint_to_t 1 `U8.shift_left` 1ul)  = "2");
    check "u8l7"
        (U8.to_string (U8.uint_to_t 1 `U8.shift_left` 7ul)  = "128");
    ()

let test_i32_right () : ML unit =
    check "i32r0"
        (I32.to_string (I32.int_to_t (pow2 31 - 1) `I32.shift_right` 0ul)  = "2147483647");
    check "i32r1"
        (I32.to_string (I32.int_to_t (pow2 31 - 1) `I32.shift_right` 1ul)  = "1073741823");
    check "i32r8"
        (I32.to_string (I32.int_to_t (pow2 31 - 1) `I32.shift_right` 8ul)  = "8388607");
    check "i32r16"
        (I32.to_string (I32.int_to_t (pow2 31 - 1) `I32.shift_right` 16ul) = "32767");
    check "i32r24"
        (I32.to_string (I32.int_to_t (pow2 31 - 1) `I32.shift_right` 24ul) = "127");
    check "i32r31"
        (I32.to_string (I32.int_to_t (pow2 31 - 1) `I32.shift_right` 31ul) = "0");
    ()

let test_i32_arith_right () : ML unit =
    check "i32r0"
        (I32.to_string (I32.int_to_t (- pow2 31) `I32.shift_arithmetic_right` 0ul)  = "-2147483648");
    check "i32r1"
        (I32.to_string (I32.int_to_t (- pow2 31) `I32.shift_arithmetic_right` 1ul)  = "-1073741824");
    check "i32r8"
        (I32.to_string (I32.int_to_t (- pow2 31) `I32.shift_arithmetic_right` 8ul)  = "-8388608");
    check "i32r16"
        (I32.to_string (I32.int_to_t (- pow2 31) `I32.shift_arithmetic_right` 16ul) = "-32768");
    check "i32r24"
        (I32.to_string (I32.int_to_t (- pow2 31) `I32.shift_arithmetic_right` 24ul) = "-128");
    check "i32r31"
        (I32.to_string (I32.int_to_t (- pow2 31) `I32.shift_arithmetic_right` 31ul) = "-1");
    ()

#push-options "--lax" // sigh, it's this or a huge rlimit
let test_i32_left () : ML unit =
    check "i32l0"
        (I32.to_string (I32.int_to_t 1 `I32.shift_left` 0ul)  = "1");
    check "i32l1"
        (I32.to_string (I32.int_to_t 1 `I32.shift_left` 1ul)  = "2");
    check "i32l8"
        (I32.to_string (I32.int_to_t 1 `I32.shift_left` 8ul)  = "256");
    check "i32l16"
        (I32.to_string (I32.int_to_t 1 `I32.shift_left` 16ul) = "65536");
    check "i32l24"
        (I32.to_string (I32.int_to_t 1 `I32.shift_left` 24ul) = "16777216");
    check "i32l30"
        (I32.to_string (I32.int_to_t 1 `I32.shift_left` 30ul) = "1073741824");
    ()
#pop-options

let test_i8_right () : ML unit =
    check "i8r0"
        (I8.to_string (I8.int_to_t (pow2 7 - 1) `I8.shift_right` 0ul) = "127");
    check "i8r1"
        (I8.to_string (I8.int_to_t (pow2 7 - 1) `I8.shift_right` 1ul) = "63");
    check "i8r6"
        (I8.to_string (I8.int_to_t (pow2 7 - 1) `I8.shift_right` 6ul) = "1");
    check "i8r7"
        (I8.to_string (I8.int_to_t (pow2 7 - 1) `I8.shift_right` 7ul) = "0");
    ()

let test_i8_arith_right () : ML unit =
    check "i8r0"
        (I8.to_string (I8.int_to_t (- pow2 7) `I8.shift_arithmetic_right` 0ul)  = "-128");
    check "i8r1"
        (I8.to_string (I8.int_to_t (- pow2 7) `I8.shift_arithmetic_right` 1ul)  = "-64");
    check "i8r8"
        (I8.to_string (I8.int_to_t (- pow2 7) `I8.shift_arithmetic_right` 6ul)  = "-2");
    check "i8r16"
        (I8.to_string (I8.int_to_t (- pow2 7) `I8.shift_arithmetic_right` 7ul)  = "-1");
    ()

let test_i8_left () : ML unit =
    check "i8l0"
        (I8.to_string (I8.int_to_t 1 `I8.shift_left` 0ul)  = "1");
    check "i8l1"
        (I8.to_string (I8.int_to_t 1 `I8.shift_left` 1ul)  = "2");
    check "i8l5"
        (I8.to_string (I8.int_to_t 1 `I8.shift_left` 5ul)  = "32");
    check "i8l6"
        (I8.to_string (I8.int_to_t 1 `I8.shift_left` 6ul)  = "64");
    ()

let test_i32 () : ML unit =
    test_i32_right ();
    test_i32_arith_right ();
    test_i32_left ();
    ()

let test_i8 () : ML unit =
    test_i8_right ();
    test_i8_arith_right ();
    test_i8_left ();
    ()

let main () : ML int =
    test_u32 ();
    test_u8 ();
    test_i32 ();
    test_i8 ();
    print_string "correct\n";
    0
