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
module IntegerParsing

open Slice

open FStar.Ghost
open FStar.Seq
open Parsing
open Serializing

open FStar.HyperStack
open FStar.HyperStack.ST
module B = FStar.Buffer

// kremlib libraries
module C = C
open C.Loops
open FStar.Kremlin.Endianness

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

type u16_array =
  | U16Array : len16:U16.t -> a16:bytes{length a16 == U16.v len16} -> u16_array

type u32_array =
  | U32Array : len32:U32.t -> a32:bytes{length a32 == U32.v len32} -> u32_array

let parse_u8: parser U8.t =
  fun b -> if length b < 1 then None
        else Some (index b 0, 1)

let parse_u16: parser U16.t =
  fun b -> if length b < 2 then None
        else begin
          let b' = slice b 0 2 in
          lemma_be_to_n_is_bounded b';
          Some (U16.uint_to_t (be_to_n b'), 2)
        end

let parse_u32: parser U32.t =
  fun b -> if length b < 4 then None
        else begin
          let b' = slice b 0 4 in
          lemma_be_to_n_is_bounded b';
          Some (U32.uint_to_t (be_to_n b'), 4)
        end

val parse_u16_array: parser u16_array
let parse_u16_array =
  parse_u16 `and_then`
  (fun array_len b' ->
    if length b' < U16.v array_len then None
    else let data = slice b' 0 (U16.v array_len) in
    Some (U16Array array_len data, U16.v array_len))

val parse_u32_array: parser u32_array
let parse_u32_array =
  parse_u32 `and_then`
  (fun array_len b' ->
    if length b' < U32.v array_len then None
    else let data = slice b' 0 (U32.v array_len) in
    Some (U32Array array_len data, U32.v array_len))

noeq type u16_array_st =
  | U16ArraySt : len16_st:U16.t -> a16_st:bslice{U32.v a16_st.len == U16.v len16_st} -> u16_array_st

noeq type u32_array_st =
  | U32ArraySt : len32_st:U32.t -> a32_st:bslice{U32.v a32_st.len == U32.v len32_st} -> u32_array_st

let as_u16_array h (a:u16_array_st) : Ghost u16_array
  (requires (live h a.a16_st))
  (ensures (fun _ -> True)) =
  U16Array a.len16_st (as_seq h a.a16_st)

let as_u32_array h (a:u32_array_st) : Ghost u32_array
  (requires (live h a.a32_st))
  (ensures (fun _ -> True)) =
  U32Array a.len32_st (as_seq h a.a32_st)


let parse_u8_st_nochk :
    parser_st_nochk (hide parse_u8) = fun input ->
    let b0 = B.index input.p 0ul in
    (b0, 1ul)

let parse_u8_st : parser_st (hide parse_u8) = fun input ->
    if U32.lt input.len 1ul then None
    else (Some (parse_u8_st_nochk input))

let parse_u16_st_nochk :
  parser_st_nochk (hide parse_u16) = fun input ->
  let n = C.load16_be (truncated_slice input 2ul).p in
  (n, 2ul)

let parse_u16_st : parser_st (hide parse_u16) = fun input ->
  if U32.lt input.len 2ul
    then None
  else Some (parse_u16_st_nochk input)

let parse_u32_st_nochk :
  parser_st_nochk (hide parse_u32) = fun input ->
  let n = C.load32_be (truncated_slice input 4ul).p in
  (n, 4ul)

let parse_u32_st : parser_st (hide parse_u32) = fun input ->
  if U32.lt input.len 4ul
    then None
    else Some (parse_u32_st_nochk input)

#reset-options "--z3rlimit 15"

// TODO: this isn't a parser_st_nochk because its output isn't exactly the same
// as the parser; the relationship requires converting the return value to bytes
let parse_u16_array_nochk : input:bslice -> Stack (u16_array_st * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_u16_array bs))))
  (ensures (fun h0 r h1 ->
              live h1 input /\
              modifies_none h0 h1 /\
              (let bs = B.as_seq h1 input.p in
                Some? (parse_u16_array bs) /\
                (let (v, n) = Some?.v (parse_u16_array bs) in
                  let (rv, off) = r in
                  // BUG: ommitting this live assertion causes failure in the
                  // precondition to as_u16_array, but the error reported is
                  // simply "ill-kinded type" on as_u16_array
                  live h1 rv.a16_st /\
                  as_u16_array h1 rv == v /\
                  n == U32.v off)))) = fun input ->
  let (len, off) = parse_u16_st_nochk input in
  let input = advance_slice input off in
  let a = U16ArraySt len (truncate_slice input (Cast.uint16_to_uint32 len)) in
  (a, U32.add off (Cast.uint16_to_uint32 len))

let parse_u32_array_nochk : input:bslice -> Stack (u32_array_st * off:U32.t)
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_u32_array bs))))
  (ensures (fun h0 r h1 ->
              live h1 input /\
              modifies_none h0 h1 /\
              (let bs = B.as_seq h1 input.p in
                Some? (parse_u32_array bs) /\
                (let (v, n) = Some?.v (parse_u32_array bs) in
                  let (rv, off) = r in
                  live h1 rv.a32_st /\
                  as_u32_array h1 rv == v /\
                  n == U32.v off)))) = fun input ->
  let (len, off) = parse_u32_st_nochk input in
  let input = advance_slice input off in
  let a = U32ArraySt len (truncate_slice input len) in
  (a, U32.add off len)

let validate_u16_array_st : stateful_validator (hide parse_u16_array) = fun input ->
  match parse_u16_st input with
  | Some (n, off) -> begin
      let n: U32.t = Cast.uint16_to_uint32 n in
      // overflow is not possible here, since n < pow2 16 and off == 2
      // (any encodable length would fit in a U32)
      let total_len = U32.add n off in
      if U32.lt input.len total_len then None
      else Some total_len
    end
  | None -> None

inline_for_extraction
private let u32_array_bound: U32.t = 4294967291ul

private let u32_array_bound_is (_:unit) :
  Lemma (U32.v u32_array_bound = pow2 32 - 4 - 1) = ()

let validate_u32_array_st : stateful_validator (hide parse_u32_array) = fun input ->
  match parse_u32_st input with
  | Some (n, off) -> begin
      // we have to make sure that the total length we compute doesn't overflow
      // a U32.t to correctly check if the input is long enough
      if U32.gte n u32_array_bound then None
      else begin
        assert (U32.v n + U32.v off < pow2 32);
        let total_len = U32.add n off in
        if U32.lt input.len total_len then None
        else Some total_len
      end
    end
  | None -> None

let encode_u8 (v:U8.t) : b:bytes{length b == 1} = Seq.create 1 v
let encode_u16 (v:U16.t) : b:bytes{length b == 2} = n_to_be 2ul (U16.v v)
let encode_u32 (v:U32.t) : b:bytes{length b == 4} = n_to_be 4ul (U32.v v)

let encode_u16_array (len:U16.t) (b:bytes{length b == U16.v len}) : bytes =
  encode_u16 len `append` b

let encode_u32_array (len:U32.t) (b:bytes{length b == U32.v len}) : bytes =
  encode_u32 len `append` b

val upd_len_1 : #a:Type -> s:Seq.seq a{length s == 1} -> v:a ->
  Lemma (Seq.upd s 0 v == Seq.create 1 v)
let upd_len_1 #a s v =
  lemma_eq_intro (Seq.upd s 0 v) (Seq.create 1 v)

val ser_byte: v:byte -> serializer (hide (encode_u8 v))
let ser_byte v = fun buf ->
  if U32.lt buf.len 1ul then None
  else
    let (buf, _) = bslice_split_at buf 1ul in
    let h0 = get() in
    B.upd buf.p 0ul v;
    begin
      let s0 = as_seq h0 buf in
      upd_len_1 s0 v
    end;
    Some 1ul

#reset-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 1"

// TODO: prove this inversion theorem

assume val n_to_be_inv : len:U32.t -> b:bytes{length b == U32.v len} ->
  Lemma (be_to_n b < pow2 (op_Multiply 8 (Seq.length b)) /\ // lemma_be_to_n_is_bounded
         n_to_be len (be_to_n b) == b)
  [SMTPat (n_to_be len (be_to_n b))]

val store_be_inv : len:U32.t -> n:nat{n < pow2 (op_Multiply 8 (U32.v len))} -> bs:bytes{length bs == U32.v len} ->
  Lemma (requires (be_to_n bs == n))
        (ensures (bs == n_to_be len n))
let store_be_inv len n bs =
  n_to_be_inv len bs

val ser_u16: v:U16.t -> serializer (hide (encode_u16 v))
let ser_u16 v = fun buf ->
  if U32.lt buf.len 2ul then None
  else (C.store16_be (truncated_slice buf 2ul).p v;
       (let h = get() in
        store_be_inv 2ul (U16.v v) (as_seq h (truncated_slice buf 2ul)));
      Some 2ul)

val ser_u32: v:U32.t -> serializer (hide (encode_u32 v))
let ser_u32 v = fun buf ->
  if U32.lt buf.len 4ul then None
  else (C.store32_be (truncated_slice buf 4ul).p v;
        (let h = get() in
        store_be_inv 4ul (U32.v v) (as_seq h (truncated_slice buf 4ul)));
        Some 4ul)

let enc_u16_array_st (a: u16_array_st) (h:mem{live h a.a16_st}) : GTot bytes =
    encode_u16 a.len16_st `append` as_seq h a.a16_st

inline_for_extraction [@"substitute"]
val ser_u16_array : a:u16_array_st ->
  serializer_any (hide (TSet.singleton a.a16_st)) (fun h -> enc_u16_array_st a h)
let ser_u16_array a = fun buf ->
  (ser_u16 a.len16_st `ser_append` ser_copy a.a16_st) buf

let enc_u32_array_st (a: u32_array_st) (h:mem{live h a.a32_st}) : GTot bytes =
  encode_u32 a.len32_st `append` as_seq h a.a32_st

val ser_u32_array : a:u32_array_st ->
  serializer_any (hide (TSet.singleton a.a32_st)) (fun h -> enc_u32_array_st a h)
let ser_u32_array a = fun buf ->
  (ser_u32 a.len32_st `ser_append`
  ser_copy a.a32_st) buf
