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
module FStar.Bytes

(* The OCaml implementation: bytes are an OCaml [string], a byte an OCaml
   [int].  The definitions marked [custard_extern] are not compiled, their
   uses refer to the OCaml symbol directly. *)

module S = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Str = FStar.String

type bytes = string

[@@custard_extern "(fun b -> FStar_UInt32.of_native_int (String.length b))"]
let len _ = admit ()

let reveal _ = admit ()

let length_reveal _ = admit ()

let hide _ = admit ()

let hide_reveal _ = admit ()

let reveal_hide _ = admit ()

let empty_bytes = ""

let empty_unique _ = admit ()

[@@custard_extern "(fun b pos -> Char.code (String.get b (FStar_UInt32.to_native_int pos)))"]
let get _ _ = admit ()

let extensionality _ _ = admit ()

[@@custard_extern "(fun len v -> String.make (FStar_UInt32.to_native_int len) (Char.chr v))"]
let create _ _ = admit ()

[@@custard_extern "(fun len f -> String.init (FStar_UInt32.to_native_int len) (fun i -> Char.chr (f (FStar_UInt32.of_native_int i))))"]
let init _ _ = admit ()

let abyte b = create 1ul b

let twobytes b = init 2ul (fun i -> if i = 0ul then fst b else snd b)

[@@custard_extern "Stdlib.(^)"]
let append _ _ = admit ()

[@@custard_extern "(fun b s e -> String.sub b (FStar_UInt32.to_native_int s) (FStar_UInt32.to_native_int e - FStar_UInt32.to_native_int s))"]
let slice _ _ _ = admit ()

[@@custard_extern "(fun b s l -> String.sub b (FStar_UInt32.to_native_int s) (FStar_UInt32.to_native_int l))"]
let sub _ _ _ = admit ()

[@@custard_extern "(fun b k -> let k = FStar_UInt32.to_native_int k in (String.sub b 0 k, String.sub b k (String.length b - k)))"]
let split _ _ = admit ()

[@@custard_extern "(fun n -> let rec go n = if Z.lt n (Z.of_int 256) then Z.one else Z.succ (go (Z.div n (Z.of_int 256))) in go n)"]
let repr_bytes _ = admit ()

let lemma_repr_bytes_values _ = admit ()

let repr_bytes_size _ _ = admit ()

[@@custard_extern "(fun b -> let x = Stdlib.ref Z.zero in String.iter (fun c -> Stdlib.(:=) x (Z.add (Z.mul (Z.of_int 256) (Stdlib.(!) x)) (Z.of_int (Char.code c)))) b; Stdlib.(!) x)"]
let int_of_bytes _ = admit ()

(* Big-endian, in exactly [nb] bytes *)
[@@custard_extern "(fun nb i -> let nb = Z.to_int nb in let i = Z.to_int64 i in if Int64.compare i Int64.zero < 0 then Stdlib.failwith \"Negative 64bit.\"; let rec put_bytes bb lb n = if lb = 0 then Stdlib.failwith \"not enough bytes\" else begin Bytes.set bb (lb-1) (Char.chr (Int64.to_int (Int64.logand n 255L))); let ns = Int64.div n 256L in if Int64.compare ns Int64.zero > 0 then put_bytes bb (lb-1) ns else bb end in Bytes.to_string (put_bytes (Bytes.make nb (Char.chr 0)) nb i))"]
let bytes_of_int _ _ = admit ()

let int_of_bytes_of_int _ = admit ()

let bytes_of_int_of_bytes _ = admit ()
let int32_of_bytes b = U32.uint_to_t (int_of_bytes b)

let int16_of_bytes b = U16.uint_to_t (int_of_bytes b)

let int8_of_bytes b = U8.uint_to_t (int_of_bytes b)

let bytes_of_int32 n = bytes_of_int 4 (U32.v n)

let bytes_of_int16 n = bytes_of_int 2 (U16.v n)

let bytes_of_int8 n = bytes_of_int 1 (U8.v n)

[@@custard_extern "(fun len s1 s2 -> String.init (FStar_UInt32.to_native_int len) (fun i -> Char.chr (Char.code s1.[i] lxor Char.code s2.[i])))"]
let xor _ _ _ = admit ()

let xor_commutative _ _ _ = admit ()

let xor_append _ _ _ _ = admit ()

let xor_idempotent _ _ _ = admit ()

(* TODO: use Camomile *)
[@@custard_extern "(fun x -> x)"]
let utf8_encode _ = admit ()

(* The result must re-encode to the argument, so an ill-formed sequence
   comes back as [None] *)
[@@custard_extern "(fun x -> if String.is_valid_utf_8 x then Some x else None)"]
let iutf8_opt _ = admit ()

(* Some helpers to deal with the conversion from hex literals to bytes and
   conversely. Mostly for tests. *)
[@@custard_extern "(fun s -> let digit c = match c with '0'..'9' -> Char.code c - Char.code '0' | 'a'..'f' -> 10 + Char.code c - Char.code 'a' | _ -> Stdlib.failwith \"hex_to_char: invalid hex digit\" in let n = String.length s in if n mod 2 <> 0 then Stdlib.failwith \"string_of_hex: invalid length\" else String.init (n / 2) (fun i -> Char.chr ((digit s.[2 * i]) lsl 4 + digit s.[2 * i + 1])))"]
let string_of_hex _ = admit ()

let bytes_of_hex s = string_of_hex s

[@@custard_extern "(fun s -> let digits = \"0123456789abcdef\" in let buf = Buffer.create (2 * String.length s) in String.iter (fun c -> let n = Char.code c in Buffer.add_char buf digits.[n lsr 4]; Buffer.add_char buf digits.[n land 0x0f]) s; Buffer.contents buf)"]
let hex_of_string _ = admit ()

let hex_of_bytes b = hex_of_string b

[@@custard_extern "(fun s -> let b = Buffer.create 1024 in String.iter (fun c -> Buffer.add_string b (Printf.sprintf \"%02X\" (Char.code c))) s; Buffer.contents b)"]
let print_bytes _ = admit ()

[@@custard_extern "(fun s -> s)"]
let bytes_of_string _ = admit ()
