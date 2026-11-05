(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.ByteBuffer

(* The OCaml implementation: a [Buffer.t], and a string with a position. *)

open FStarC.Effect
module I = FStarC.SmallInt

[@@custard_extern "Buffer.t"]
private assume new type buf : Type0

type writer = buf

[@@custard_extern "(fun () -> Buffer.create 65536)"]
let writer_create _ = admit ()

[@@custard_extern "(fun b x -> Buffer.add_char b (Char.chr x))"]
let write_byte _ _ = admit ()

[@@custard_extern "(fun b n -> let rec go n = if n land (lnot 127) = 0 then Buffer.add_char b (Char.unsafe_chr n) else (Buffer.add_char b (Char.unsafe_chr ((n land 127) lor 128)); go (n lsr 7)) in go n)"]
let write_uvarint _ _ = admit ()

[@@custard_extern "(fun n -> (n lsl 1) lxor (n asr 62))"]
private assume val zigzag : I.t -> I.t

[@@custard_extern "(fun z -> (z lsr 1) lxor (- (z land 1)))"]
private assume val unzigzag : I.t -> I.t

let write_varint w n = write_uvarint w (zigzag n)

(* Twice the zigzag encoding of [x] if [x] is in [-2^60, 2^60), else -1. *)
[@@custard_extern "(fun x -> if Z.fits_int x then (let n = Z.to_int x in if n >= -0x1000000000000000 && n < 0x1000000000000000 then ((n lsl 1) lxor (n asr 62)) lsl 1 else -1) else -1)"]
private assume val small_code : int -> I.t

(* The integer of an even code. *)
[@@custard_extern "(fun u -> let z = u lsr 1 in Z.of_int ((z lsr 1) lxor (- (z land 1))))"]
private assume val of_small_code : I.t -> int

[@@custard_extern "(fun u -> u land 1 = 0)"]
private assume val is_even : I.t -> bool

[@@custard_extern "(fun b s -> Buffer.add_string b s)"]
let write_raw _ _ = admit ()

let write_string w s =
  write_uvarint w (FStarC.String.byte_length s);
  write_raw w s

let write_int w x =
  let c = small_code x in
  if c <> I.minus_one then write_uvarint w c
  else begin
    write_uvarint w (if x >= 0 then I.one else I.of_int 3);
    write_string w (string_of_int (if x >= 0 then x else - x))
  end

[@@custard_extern "Buffer.length"]
let writer_size _ = admit ()

[@@custard_extern "Buffer.contents"]
let writer_contents _ = admit ()

[@@custard_extern "(string * int ref)"]
private assume new type rd : Type0

type reader = rd

[@@custard_extern "(fun s off -> (s, ref off))"]
let reader_create _ _ = admit ()

[@@custard_extern "(fun (_, p) -> !p)"]
let reader_pos _ = admit ()

[@@custard_extern "(fun (s, _) -> String.length s)"]
private assume val reader_size : reader -> ML I.t

(* The next byte, or -1 at the end of the input. *)
[@@custard_extern "(fun (s, p) -> let i = !p in if i >= String.length s then -1 else (p := i + 1; Char.code (String.unsafe_get s i)))"]
private assume val next_byte : reader -> ML I.t

(* The next unsigned varint, or -1 if it is truncated or does not fit. *)
(* A single byte, by far the most common case, is read without allocating
   the loop's closure. *)
[@@custard_extern "(fun (s, p) -> let n = String.length s in let i0 = !p in if i0 < n && Char.code (String.unsafe_get s i0) < 128 then (p := i0 + 1; Char.code (String.unsafe_get s i0)) else let rec go acc sh = let i = !p in if i >= n || sh > 56 then -1 else (let c = Char.code (String.unsafe_get s i) in p := i + 1; let acc = acc lor ((c land 127) lsl sh) in if c land 128 = 0 then acc else go acc (sh + 7)) in go 0 0)"]
private assume val next_uvarint : reader -> ML I.t

[@@custard_extern "(fun (s, p) n -> let i = !p in p := i + n; String.sub s i n)"]
private assume val take : reader -> I.t -> ML string

private let malformed (#a:Type) (what:string) : ML a = raise (Malformed what)

(* Both are an OCaml [int]. *)
[@@custard_extern "(fun b -> b)"]
private assume val to_u8 : I.t -> FStar.UInt8.t

let read_byte r =
  let b = next_byte r in
  if b = I.minus_one then malformed "unexpected end of input" else to_u8 b

let read_uvarint r =
  let u = next_uvarint r in
  if u = I.minus_one then malformed "bad varint" else u

let read_varint r = unzigzag (read_uvarint r)

let read_raw r len =
  if I.(len < zero) || I.(reader_size r - reader_pos r < len) then
    malformed "unexpected end of input"
  else take r len

let read_string r = read_raw r (read_uvarint r)

let read_int r =
  let u = read_uvarint r in
  if is_even u then of_small_code u
  else
    let s = read_string r in
    match FStarC.Util.safe_int_of_string s with
    | Some n -> if u = I.one then n else - n
    | None -> malformed "bad integer"
