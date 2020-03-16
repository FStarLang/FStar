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

let main () : ML unit =
    check "0"
        (U64.to_string_hex (U64.uint_to_t 0) = "0x0");
    check "f"
        (U64.to_string_hex (U64.uint_to_t 15) = "0xf");
    check "1"
        (U64.to_string_hex (U64.uint_to_t (pow2 64 - 1)) = "0xffffffffffffffff");
    print_string "correct"
