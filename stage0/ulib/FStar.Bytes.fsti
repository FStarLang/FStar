(*
   Copyright 2008-2017 Microsoft Research

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
(*
A standard library for manipulation of value bytes.

This model is realized by Bytes.bytes in OCaml and by
struct {uintX_t size; char *bytes} (or similar) in C.

This file is essentially a specialized version of FStar.Seq,
with lemmas and refinements taylored for typical operations on
bytes, and with support for machine integers and C-extractible versions
(which Seq does not provide.)

@summary Value bytes standard library
*)
module FStar.Bytes

module S = FStar.Seq
module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Str = FStar.String
module Chr = FStar.Char

unfold let u8 = U8.t
unfold let u16 = U16.t
unfold let u32 = U32.t

(** Realized by uint8_t in C and int in OCaml (char does not have necessary operators...) *)
unfold type byte = u8

(** Realized in C by a pair of a length field and uint8_t* in C
    Realized in OCaml by a string *)
val bytes : t:Type0{hasEq t}
val len : bytes -> u32

unfold let length b = FStar.UInt32.v (len b)

(**  representation for specs that need lemmas not defined here. *)
val reveal:
    bytes
  -> GTot (S.seq byte)

val length_reveal:
    x:bytes
  -> Lemma (ensures (S.length (reveal x) = length x))
          [SMTPatOr [[SMTPat (S.length (reveal x))];
                     [SMTPat (len x)]]]

val hide:
    s:S.seq byte{S.length s < pow2 32}
  -> GTot bytes

val hide_reveal:
    x:bytes
  -> Lemma (ensures (hide (reveal x) = x))
          [SMTPat (reveal x)]

val reveal_hide:
    x:S.seq byte{S.length x < pow2 32}
  -> Lemma (ensures (reveal (hide x) == x))
          [SMTPat (hide x)]

type lbytes (l:nat) = b:bytes{length b = l}
type kbytes (k:nat) = b:bytes{length b < pow2 k}

let lbytes32 (l:UInt32.t) = b:bytes{len b = l}

val empty_bytes : lbytes 0
val empty_unique:
    b:bytes
  -> Lemma (length b = 0 ==> b = empty_bytes)
    [SMTPat (len b)]

(** If you statically know the length, it is OK to read at arbitrary indexes *)
val get:
    b:bytes
  -> pos:u32{U32.v pos < length b}
  -> Pure byte
    (requires True)
    (ensures (fun y -> y == S.index (reveal b) (U32.v pos)))

unfold let op_String_Access = get

unfold let index (b:bytes) (i:nat{i < length b}) = get b (U32.uint_to_t i)

let equal b1 b2 =
  length b1 = length b2 /\
  (forall (i:u32{U32.v i < length b1}).{:pattern (b1.[i]); (b2.[i])} b1.[i] == b2.[i])

val extensionality:
    b1:bytes
  -> b2:bytes
  -> Lemma (requires (equal b1 b2))
          (ensures (b1 = b2))

(** creating byte values **)
val create:
    len:u32
  -> v:byte
  -> b:lbytes (U32.v len){forall (i:u32{U32.(i <^ len)}).{:pattern b.[i]} b.[i] == v}

unfold
let create_ (n:nat{FStar.UInt.size n U32.n}) v = create (U32.uint_to_t n) v

val init:
    len:u32
  -> f:(i:u32{U32.(i <^ len)} -> byte)
  -> b:lbytes (U32.v len){forall (i:u32{U32.(i <^ len)}).{:pattern b.[i]} b.[i] == f i}

// this is a hack JROESCH
val abyte (b:byte) : lbytes 1
    (* admit () create 1ul b *)

val twobytes (b:byte&byte) : lbytes 2
    // init 2ul (fun i -> if i = 0ul then fst b else snd b)

(** appending bytes **)
val append:
    b1:bytes
  -> b2:bytes
  -> Pure bytes
         (requires (UInt.size (length b1 + length b2) U32.n))
         (ensures (fun b -> reveal b == S.append (reveal b1) (reveal b2)))
unfold let op_At_Bar = append

val slice:
    b:bytes
  -> s:u32
  -> e:u32{U32.(s <=^ e) /\ U32.v e <= length b}
  -> r:bytes{reveal r == Seq.slice (reveal b) (U32.v s) (U32.v e)}
let slice_ b (s:nat) (e:nat{s <= e /\ e <= length b}) = slice b (U32.uint_to_t s) (U32.uint_to_t e)

val sub:
    b:bytes
  -> s:u32
  -> l:u32{U32.v s + U32.v l <= length b}
  -> r:bytes{reveal r == Seq.slice (reveal b) (U32.v s) (U32.v s + U32.v l)}

val split:
    b:bytes
  -> k:u32{U32.v k <= length b}
  -> p:(bytes&bytes){
     let x, y = p in
     (reveal x, reveal y) == Seq.split (reveal b) (U32.v k)}

unfold let split_ b (k:nat{FStar.UInt.size k U32.n /\ k < length b}) = split b (U32.uint_to_t k)

(** Interpret a sequence of bytes as a mathematical integer encoded in big endian **)
let fits_in_k_bytes (n:nat) (k:nat) = FStar.UInt.size n (op_Multiply 8 k)
type uint_k (k:nat) = n:nat{fits_in_k_bytes n k}

(** repr_bytes n: The number of bytes needed to represent a nat **)
val repr_bytes:
    n:nat
  -> k:pos{fits_in_k_bytes n k}

val lemma_repr_bytes_values:
    n:nat
  -> Lemma (ensures ( let k = repr_bytes n in
                     if n < 256 then k==1
                     else if n < 65536 then k==2
                     else if n < 16777216 then k==3
                     else if n < 4294967296 then k==4
                     else if n < 1099511627776 then k==5
                     else if n < 281474976710656 then k==6
                     else if n < 72057594037927936 then k==7
                     else if n < 18446744073709551616 then k==8
                     else True ))
          [SMTPat (repr_bytes n)]

val repr_bytes_size:
    k:nat
  -> n:uint_k k
  -> Lemma (ensures (repr_bytes n <= k))
          [SMTPat (fits_in_k_bytes n k)]

val int_of_bytes:
    b:bytes
  -> Tot (uint_k (length b))

val bytes_of_int:
    k:nat
  -> n:nat{repr_bytes n <= k /\ k < pow2 32}
  -> lbytes k

val int_of_bytes_of_int:
  #k:nat{k <= 32}
  -> n:uint_k k
  -> Lemma (ensures (int_of_bytes (bytes_of_int k n) == n))
          [SMTPat (bytes_of_int k n)]

val bytes_of_int_of_bytes:
    b:bytes{length b <= 32}
  -> Lemma (ensures (bytes_of_int (length b) (int_of_bytes b) == b))
          [SMTPat (int_of_bytes b)]

//18-02-25 use [uint32] instead of [int32] etc?
val int32_of_bytes:
    b:bytes{length b <= 4}
  -> n:u32{U32.v n == int_of_bytes b}

val int16_of_bytes:
    b:bytes{length b <= 2}
  -> n:u16{U16.v n == int_of_bytes b}

val int8_of_bytes:
    b:bytes{length b = 1}
  -> n:u8{U8.v n = int_of_bytes b}

val bytes_of_int32:
    n:U32.t
  -> b:lbytes 4{b == bytes_of_int 4 (U32.v n)}

val bytes_of_int16:
    n:U16.t
  -> b:lbytes 2{b == bytes_of_int 2 (U16.v n)}

val bytes_of_int8:
    n:U8.t
  -> b:lbytes 1{b == bytes_of_int 1 (U8.v n)}

////////////////////////////////////////////////////////////////////////////////
type minbytes (n:nat) = b:bytes{length b >= n}

val xor:
    n:u32
  -> b1:minbytes (U32.v n)
  -> b2:minbytes (U32.v n)
  -> b:bytes{len b = n}

unfold let xor_ (#n:nat{FStar.UInt.size n U32.n}) (b1:minbytes n) (b2:minbytes n) = xor (U32.uint_to_t n) b1 b2

val xor_commutative:
    n:u32
  -> b1:minbytes (U32.v n)
  -> b2:minbytes (U32.v n)
  -> Lemma (ensures (xor n b1 b2 == xor n b2 b1))
          [SMTPat (xor n b1 b2)]

val xor_append:
    b1:bytes
  -> b2:bytes{FStar.UInt.size (length b1 + length b2) U32.n}
  -> x1:bytes{len x1 = len b1}
  -> x2:bytes{len x2 = len b2}
  -> Lemma (ensures (xor U32.(len b1 +^ len b2)
                        (b1 @| b2)
                        (x1 @| x2)
                    ==
                    xor (len b1) b1 x1 @| xor (len b2) b2 x2))

val xor_idempotent:
    n:u32
  -> b1:lbytes (U32.v n)
  -> b2:lbytes (U32.v n)
  -> Lemma (ensures (xor n (xor n b1 b2) b2 == b1))

val utf8_encode:
    s:string{Str.maxlen s (pow2 30)}
  -> b:bytes{length b <= op_Multiply 4 (Str.length s)}

val iutf8_opt:
    m:bytes
  -> (option (s:string{Str.maxlen s (pow2 30) /\ utf8_encode s == m}))

val string_of_hex: string -> Tot string

// missing post on the length of the results (exact on constant arguments)
val bytes_of_hex: string -> Tot bytes
val hex_of_string: string -> Tot string
val hex_of_bytes: bytes -> Tot string
val print_bytes: bytes -> Tot string
val bytes_of_string: string -> bytes //abytes

(** A better implementation of BufferBytes, formerly found in miTLS *)

module B = LowStar.Buffer
module M = LowStar.Modifies

open FStar.HyperStack.ST

type lbuffer (l:UInt32.t) = b:B.buffer UInt8.t {B.length b == U32.v l}

val of_buffer (l:UInt32.t) (#p #q:_) (buf:B.mbuffer UInt8.t p q{B.length buf == U32.v l})
  : Stack (b:bytes{length b = UInt32.v l})
  (requires fun h0 ->
    B.live h0 buf)
  (ensures  fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    b = hide (B.as_seq h0 buf))

val store_bytes: src:bytes { length src <> 0 } ->
  dst:lbuffer (len src) ->
  Stack unit
    (requires (fun h0 -> B.live h0 dst))
    (ensures  (fun h0 r h1 ->
      M.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (reveal src) (B.as_seq h1 dst)))

(* JP: let's not add from_bytes here because we want to leave it up to the
caller to allocate on the stack or on the heap *)
