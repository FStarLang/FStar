(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.IO

(* The OCaml implementation, over OCaml's channels.  The definitions marked
   [custard_extern] are not compiled, their uses refer to the OCaml symbol
   directly. *)

open FStar.All
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

[@@custard_extern "Stdlib.in_channel"]
private assume new type ocaml_in_channel : Type0

[@@custard_extern "Stdlib.out_channel"]
private assume new type ocaml_out_channel : Type0

type fd_read = ocaml_in_channel

type fd_write = ocaml_out_channel

[@@custard_extern "Stdlib.stdin"]
let stdin = admit ()

[@@custard_extern "Stdlib.stdout"]
let stdout = admit ()

[@@custard_extern "Stdlib.stderr"]
let stderr = admit ()

[@@custard_extern "Stdlib.print_newline"]
let print_newline _ = admit ()

[@@custard_extern "(fun s -> Stdlib.print_string s; Stdlib.flush Stdlib.stdout)"]
let print_string _ = admit ()

let print_uint8 x = print_string (U8.to_string_hex x)
let print_uint16 x = print_string (U16.to_string_hex x)
let print_uint32 x = print_string (U32.to_string_hex x)
let print_uint64 x = print_string (U64.to_string_hex x)

let print_uint8_dec x = print_string (U8.to_string x)
let print_uint16_dec x = print_string (U16.to_string x)
let print_uint32_dec x = print_string (U32.to_string x)
let print_uint64_dec x = print_string (U64.to_string x)

let print_uint8_hex_pad x = print_string (U8.to_string_hex_pad x)
let print_uint16_hex_pad x = print_string (U16.to_string_hex_pad x)
let print_uint32_hex_pad x = print_string (U32.to_string_hex_pad x)
let print_uint64_hex_pad x = print_string (U64.to_string_hex_pad x)

(* [s] padded with zeroes on the left to [n] characters *)
[@@custard_extern "(fun n s -> Stdlib.(^) (String.make (Z.to_int n - String.length s) '0') s)"]
private assume val zeropad : int -> string -> ML string

(* The maximum number of decimal digits of each width: 3 for 255, 5 for
   65535, 10 for 4294967295 and 20 for 18446744073709551615 *)
let print_uint8_dec_pad x = print_string (zeropad 3 (U8.to_string x))
let print_uint16_dec_pad x = print_string (zeropad 5 (U16.to_string x))
let print_uint32_dec_pad x = print_string (zeropad 10 (U32.to_string x))
let print_uint64_dec_pad x = print_string (zeropad 20 (U64.to_string x))

[@@custard_extern "(fun x -> Stdlib.output_value Stdlib.stdout x; Stdlib.flush Stdlib.stdout)"]
let print_any _ = admit ()

[@@custard_extern "Stdlib.read_line"]
let input_line _ = admit ()

[@@custard_extern "(fun () -> Z.of_int (Stdlib.read_int ()))"]
let input_int _ = admit ()

[@@custard_extern "Stdlib.read_float"]
let input_float _ = admit ()

[@@custard_extern "Stdlib.open_in"]
let open_read_file _ = admit ()

[@@custard_extern "Stdlib.open_out"]
let open_write_file _ = admit ()

[@@custard_extern "Stdlib.close_in"]
let close_read_file _ = admit ()

[@@custard_extern "Stdlib.close_out"]
let close_write_file _ = admit ()

[@@custard_extern "(fun fd -> try Some (Stdlib.input_line fd) with End_of_file -> None)"]
private assume val input_line_opt : fd_read -> ML (option string)

let read_line fd =
  match input_line_opt fd with
  | Some l -> l
  | None -> raise EOF

[@@custard_extern "Stdlib.output_string"]
let write_string _ _ = admit ()

[@@custard_extern "(fun s -> Stdlib.print_string s; Stdlib.flush Stdlib.stdout; false)"]
let debug_print_string _ = admit ()
