module TestPrint

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

let print_line (s:string) =
    print_string s;
    print_newline ()

let test_hex () : ML unit =
    U8.(
      print_line (to_string_hex (uint_to_t 0));
      print_line (to_string_hex (uint_to_t 15));
      print_line (to_string_hex (uint_to_t (pow2 8 - 1)))
    );

    U16.(
      print_line (to_string_hex (uint_to_t 0));
      print_line (to_string_hex (uint_to_t 15));
      print_line (to_string_hex (uint_to_t (pow2 16 - 1)))
    );

    U32.(
      print_line (to_string_hex (uint_to_t 0));
      print_line (to_string_hex (uint_to_t 15));
      print_line (to_string_hex (uint_to_t (pow2 32 - 1)))
    );

    U64.(
      print_line (to_string_hex (uint_to_t 0));
      print_line (to_string_hex (uint_to_t 15));
      print_line (to_string_hex (uint_to_t (pow2 64 - 1)))
    )

let test_dec () : ML unit =
    U8.(
      print_line (to_string (uint_to_t 0));
      print_line (to_string (uint_to_t 15));
      print_line (to_string (uint_to_t (pow2 8 - 1)))
    );

    U16.(
      print_line (to_string (uint_to_t 0));
      print_line (to_string (uint_to_t 15));
      print_line (to_string (uint_to_t (pow2 16 - 1)))
    );

    U32.(
      print_line (to_string (uint_to_t 0));
      print_line (to_string (uint_to_t 15));
      print_line (to_string (uint_to_t (pow2 32 - 1)))
    );

    U64.(
      print_line (to_string (uint_to_t 0));
      print_line (to_string (uint_to_t 15));
      print_line (to_string (uint_to_t (pow2 64 - 1)))
    )

let test_hex_pad () : ML unit =
    U8.(
      print_line (to_string_hex_pad (uint_to_t 0));
      print_line (to_string_hex_pad (uint_to_t 15));
      print_line (to_string_hex_pad (uint_to_t (pow2 8 - 1)))
    );

    U16.(
      print_line (to_string_hex_pad (uint_to_t 0));
      print_line (to_string_hex_pad (uint_to_t 15));
      print_line (to_string_hex_pad (uint_to_t (pow2 16 - 1)))
    );

    U32.(
      print_line (to_string_hex_pad (uint_to_t 0));
      print_line (to_string_hex_pad (uint_to_t 15));
      print_line (to_string_hex_pad (uint_to_t (pow2 32 - 1)))
    );

    U64.(
      print_line (to_string_hex_pad (uint_to_t 0));
      print_line (to_string_hex_pad (uint_to_t 15));
      print_line (to_string_hex_pad (uint_to_t (pow2 64 - 1)))
    )

let main () =
    test_hex ();
    test_dec ();
    test_hex_pad ();
    ()
