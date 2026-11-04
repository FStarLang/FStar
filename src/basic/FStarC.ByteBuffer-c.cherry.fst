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

(* The Cherry implementation.  A writer is a reference to its contents,
   emptied before each append so that the string is uniquely owned and
   extended in place.  A reader is a string with a position. *)

open FStarC.Effect
module I = FStarC.SmallInt
module U64 = FStar.UInt64
module U32 = FStar.UInt32

(* In ulib/c/cherry.c. *)
[@@custard_extern "cherry_str_push_byte"]
private assume val push_byte : ([@@@cherry_owned] s:string) -> U64.t -> string
[@@custard_extern "cherry_u64_id"]
private assume val u64 : I.t -> U64.t
[@@custard_extern "cherry_u64_id"]
private assume val small : U64.t -> I.t
[@@custard_extern "cherry_str_size64"]
private assume val size64 : string -> U64.t
[@@custard_extern "cherry_str_byte_at64"]
private assume val byte_at64 : string -> U64.t -> U64.t
[@@custard_extern "cherry_str_slice64"]
private assume val slice64 : string -> U64.t -> U64.t -> string

type writer = ref string

let writer_create _ = mk_ref ""

private let push (w:writer) (b:U64.t) : ML unit =
  let cur = !w in
  w := "";
  w := push_byte cur b

let write_byte w b = push w (u64 b)

private let rec uvarint (w:writer) (n:U64.t) : ML unit =
  if U64.lt n 128UL then push w n
  else begin
    push w (U64.logor (U64.logand n 127UL) 128UL);
    uvarint w (U64.shift_right n 7ul)
  end

let write_uvarint w n = uvarint w (u64 n)

private let zigzag (n:U64.t) : U64.t =
  U64.logxor (U64.shift_left n 1ul)
    (if U64.gte n 0x8000000000000000UL then 0xffffffffffffffffUL else 0UL)

private let unzigzag (z:U64.t) : U64.t =
  U64.logxor (U64.shift_right z 1ul) (U64.sub_mod 0UL (U64.logand z 1UL))

let write_varint w n = uvarint w (zigzag (u64 n))

let write_raw w s =
  let cur = !w in
  w := "";
  w := cur ^ s

let write_string w s =
  uvarint w (size64 s);
  write_raw w s

private let lim : int = 0x1000000000000000

let write_int w x =
  if -lim <= x && x < lim then begin
    let n = if x >= 0 then U64.uint_to_t x else U64.sub_mod 0UL (U64.uint_to_t (- x)) in
    uvarint w (U64.shift_left (zigzag n) 1ul)
  end else begin
    uvarint w (if x >= 0 then 1UL else 3UL);
    write_string w (string_of_int (if x >= 0 then x else - x))
  end

let writer_size w = small (size64 !w)

let writer_contents w = !w

noeq type reader = {
  data : string;
  size : U64.t;
  pos  : ref U64.t;
}

let reader_create s off = { data = s; size = size64 s; pos = mk_ref (u64 off) }

let reader_pos r = small !r.pos

private let malformed (#a:Type) (what:string) : ML a = raise (Malformed what)

let read_byte r =
  let i = !r.pos in
  if U64.gte i r.size then malformed "unexpected end of input"
  else begin
    r.pos := U64.add_mod i 1UL;
    small (byte_at64 r.data i)
  end

private let rec uvarint_from (r:reader) (i:U64.t) (acc:U64.t) (sh:U32.t) : ML U64.t =
  if U64.gte i r.size || U32.gt sh 63ul then malformed "bad varint"
  else begin
    let c = byte_at64 r.data i in
    let acc = U64.logor acc (U64.shift_left (U64.logand c 127UL) sh) in
    if U64.lt c 128UL then (r.pos := U64.add_mod i 1UL; acc)
    else uvarint_from r (U64.add_mod i 1UL) acc (U32.add sh 7ul)
  end

let read_uvarint r = small (uvarint_from r !r.pos 0UL 0ul)

let read_varint r = small (unzigzag (uvarint_from r !r.pos 0UL 0ul))

private let raw (r:reader) (len:U64.t) : ML string =
  let i = !r.pos in
  if U64.gte len 0x8000000000000000UL || U64.lt (U64.sub_mod r.size i) len then
    malformed "unexpected end of input"
  else begin
    r.pos := U64.add_mod i len;
    slice64 r.data i (U64.add_mod i len)
  end

let read_raw r len = raw r (u64 len)

let read_string r = raw r (uvarint_from r !r.pos 0UL 0ul)

let read_int r =
  let u = uvarint_from r !r.pos 0UL 0ul in
  if U64.logand u 1UL = 0UL then I.to_int (small (unzigzag (U64.shift_right u 1ul)))
  else
    let s = read_string r in
    match FStarC.Util.safe_int_of_string s with
    | Some n -> if u = 1UL then n else - n
    | None -> malformed "bad integer"
