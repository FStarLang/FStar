module Test04

open FStar.All
open FStar.IO
open FStar.Int.Cast
open FStar.Int.Cast.Full

module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64

let check s (b:bool) : ML unit =
    if not b then failwith s

let test_hex () : ML unit =
    check "8-0"
        (U8.to_string_hex (U8.uint_to_t 0) = "0x0");
    check "8-f"
        (U8.to_string_hex (U8.uint_to_t 15) = "0xf");
    check "8-max"
        (U8.to_string_hex (U8.uint_to_t (pow2 8 - 1)) = "0xff");

    check "16-0"
        (U16.to_string_hex (U16.uint_to_t 0) = "0x0");
    check "16-f"
        (U16.to_string_hex (U16.uint_to_t 15) = "0xf");
    check "16-max"
        (U16.to_string_hex (U16.uint_to_t (pow2 16 - 1)) = "0xffff");

    check "32-0"
        (U32.to_string_hex (U32.uint_to_t 0) = "0x0");
    check "32-f"
        (U32.to_string_hex (U32.uint_to_t 15) = "0xf");
    check "32-max"
        (U32.to_string_hex (U32.uint_to_t (pow2 32 - 1)) = "0xffffffff");

    check "64-0"
        (U64.to_string_hex (U64.uint_to_t 0) = "0x0");
    check "64-f"
        (U64.to_string_hex (U64.uint_to_t 15) = "0xf");
    check "64-max"
        (U64.to_string_hex (U64.uint_to_t (pow2 64 - 1)) = "0xffffffffffffffff");

    ()

let test_hex_pad () : ML unit =
    check "8-0-pad"
        (U8.to_string_hex_pad (U8.uint_to_t 0) = "00");
    check "8-f-pad"
        (U8.to_string_hex_pad (U8.uint_to_t 15) = "0f");
    check "8-max-pad"
        (U8.to_string_hex_pad (U8.uint_to_t (pow2 8 - 1)) = "ff");

    check "16-0-pad"
        (U16.to_string_hex_pad (U16.uint_to_t 0) = "0000");
    check "16-f-pad"
        (U16.to_string_hex_pad (U16.uint_to_t 15) = "000f");
    check "16-max-pad"
        (U16.to_string_hex_pad (U16.uint_to_t (pow2 16 - 1)) = "ffff");

    check "32-0-pad"
        (U32.to_string_hex_pad (U32.uint_to_t 0) = "00000000");
    check "32-f-pad"
        (U32.to_string_hex_pad (U32.uint_to_t 15) = "0000000f");
    check "32-max-pad"
        (U32.to_string_hex_pad (U32.uint_to_t (pow2 32 - 1)) = "ffffffff");

    check "64-0-pad"
        (U64.to_string_hex_pad (U64.uint_to_t 0) = "0000000000000000");
    check "64-f-pad"
        (U64.to_string_hex_pad (U64.uint_to_t 15) = "000000000000000f");
    check "64-max-pad"
        (U64.to_string_hex_pad (U64.uint_to_t (pow2 64 - 1)) = "ffffffffffffffff");

    ()

let main () =
    test_hex ();
    test_hex_pad ();
    print_string "correct";
    ()
