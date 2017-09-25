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
(**
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

(** Realized by uint8_t in C and int in OCaml (char does not have necessary operators...) *)
type byte = U8.t

(** Realized by uint8_t* in C and string in OCaml.
    This is a variant for which length is NOT available at runtime *)
abstract type bytes = S.seq byte

(** Expose the represewntation for specs that need lemmas not defined here. *)
let reveal (b:bytes) : GTot (S.seq byte) = b
let hide (s:S.seq byte) : GTot (b:bytes{reveal b = s}) = s

let length (b:bytes) : GTot (n:nat{n = S.length (reveal b)}) = S.length b
type lbytes (l:nat) = b:bytes{length b = l}
type kbytes (k:nat) = b:bytes{length b < pow2 k}

let empty_bytes : lbytes 0 = S.createEmpty
let lemma_empty (b:bytes)
  : Lemma (length b = 0 ==> b = empty_bytes)
  [SMTPat (length b)] = S.lemma_empty b

(** If you statically know the length, it is OK to read at arbitrary indexes *)
let get (b:bytes) (pos:nat{pos < length b}) : Tot byte = Seq.index b pos
unfold let op_String_Access (b:bytes) (i:nat{i < length b}) = get b i

(** If the length of bytes is not known statically, use on of these variants
    that carry length information inside a machine integer carried with the bytes.
    In C, realized by {uintX_t len; uint8_t *b} - in OCaml, still string *)
type bytes8 = kbytes 8
let length8 (b:bytes8) : n:U8.t{U8.v n = length b} = U8.uint_to_t (S.length b)
type lbytes8 (l:U8.t) = b:bytes8{length8 b = l}
let get8 (b:bytes8) (i:U8.t{U8.(i <^ length8 b)}) = b.[U8.v i]

type bytes16 = kbytes 16
let length16 (b:bytes16) : n:U16.t{U16.v n = length b} = U16.uint_to_t (S.length b)
type lbytes16 (l:U16.t) = b:bytes16{length16 b = l}
let get16 (b:bytes16) (i:U16.t{U16.(i <^ length16 b)}) = b.[U16.v i]

type bytes32 = kbytes 32
let length32 (b:bytes32) : n:U32.t{U32.v n = length b} = U32.uint_to_t (S.length b)
type lbytes32 (l:U32.t) = b:bytes32{length32 b = l}
let get32 (b:bytes32) (i:U32.t{U32.(i <^ length32 b)}) = b.[U32.v i]

let create (len:nat) (v:byte) : b:lbytes len{forall (i:nat{i<len}). b.[i] = v} =
  S.lemma_create_len len v;
  S.create len v

let create8 (len:U8.t) (v:byte) : b:lbytes8 len{forall (i:U8.t{U8.(i <^ len)}). get8 b i = v} =
  create (U8.v len) v
let create16 (len:U16.t) (v:byte) : b:lbytes16 len{forall (i:U16.t{U16.(i <^ len)}). get16 b i = v} =
  create (U16.v len) v
let create32 (len:U32.t) (v:byte) : b:lbytes32 len{forall (i:U32.t{U32.(i <^ len)}). get32 b i = v} =
  create (U32.v len) v

let init (len:nat) (f: i:nat{i<len} -> byte) : b:lbytes len{forall (i:nat{i<len}). get b i = f i} =
  S.lemma_init_len len f;
  S.init len f

let init8 (len:U8.t) (f: i:U8.t{U8.(i <^ len)} -> byte)
  : b:lbytes8 len{forall (i:U8.t{U8.(i <^ len)}). get8 b i = f i} =
  init (U8.v len) (fun (i:nat{i < U8.v len}) -> f (U8.uint_to_t i))
let init16 (len:U16.t) (f: i:U16.t{U16.(i <^ len)} -> byte)
  : b:lbytes16 len{forall (i:U16.t{U16.(i <^ len)}). get16 b i = f i} =
  init (U16.v len) (fun (i:nat{i < U16.v len}) -> f (U16.uint_to_t i))
let init32 (len:U32.t) (f: i:U32.t{U32.(i <^ len)} -> byte)
  : b:lbytes32 len{forall (i:U32.t{U32.(i <^ len)}). get32 b i = f i} =
  init (U32.v len) (fun (i:nat{i < U32.v len}) -> f (U32.uint_to_t i))

let abyte (b:byte) : lbytes 1 = create 1 b
let twobytes (b:byte*byte) : Tot (lbytes 2) =
  Seq.init 2 (fun i -> if i = 0 then fst b else snd b)

let abyte8 (b:byte) : lbytes8 1uy = abyte b
let abyte16 (b:byte) : lbytes16 1us = abyte b
let abyte32 (b:byte) : lbytes32 1ul = abyte b

let twobytes8 (b:byte*byte) : lbytes8 2uy = twobytes b
let twobytes16 (b:byte*byte) : lbytes16 2us = twobytes b
let twobytes32 (b:byte*byte) : lbytes32 2ul = twobytes b

let append (b1:bytes) (b2:bytes)
  : b:bytes{length b = length b1 + length b2} = Seq.append b1 b2
let append8 (b1:bytes8) (b2:bytes8{length b1 + length b2 < pow2 8})
  : b:bytes8{length b = length b1 + length b2} = Seq.append b1 b2
unfold let op_Hat_Hat = append8
let append16 (b1:bytes16) (b2:bytes16{length b1 + length b2 < pow2 16})
  : b:bytes16{length b = length b1 + length b2} = Seq.append b1 b2
unfold let op_Hat_Hat_Hat = append16
let append16_8 (b1:bytes16) (b2:bytes8{length b1 + length b2 < pow2 16})
  : b:bytes16{length b = length b1 + length b2} = Seq.append b1 b2
let append32 (b1:bytes32) (b2:bytes32{length b1 + length b2 < pow2 32})
  : b:bytes32{length b = length b1 + length b2} = Seq.append b1 b2

let lemma_append_empty_r (b:bytes)
  : Lemma (append b empty_bytes = b) [SMTPat (append b empty_bytes)] =
  S.append_empty_r b
let lemma_append_empty_l (b:bytes)
  : Lemma (append empty_bytes b = b) [SMTPat (append empty_bytes b)] =
  S.append_empty_l b

let lemma_equality (b1:bytes) (b2:bytes{length b2 = length b1})
  : Lemma (requires (forall (i:nat{i < length b1}).{:pattern (get b1 i); (get b2 i)} (get b1 i = get b2 i)))
    (ensures b1 = b2)
  =
  assert(forall (i:nat{i < length b1}).{:pattern (get b1 i); (get b2 i)} get b1 i = S.index b1 i /\ get b2 i = S.index b2 i);
  assert(forall (i:nat{i < length b1}).{:pattern (S.index b1 i); (S.index b2 i)} (S.index b1 i == S.index b2 i));
  S.lemma_eq_intro b1 b2

unfold let op_Hat (b1:bytes) (b2:bytes) : b:bytes{length b = length b1 + length b2} = append b1 b2
unfold let op_At_Bar (b1:bytes) (b2:bytes) : b:bytes{length b = length b1 + length b2} = append b1 b2

let lemma_append_inj (a1:bytes) (a2:bytes) (b1:bytes) (b2:bytes)
  : Lemma (requires (length a1 = length b1 \/ length a2 = length b2) /\ a1 ^ a2 = b1 ^ b2)
          (ensures a1 = b1 /\ a2 = b2) [SMTPat (a1 ^ a2 = b1 ^ b2)]
  = S.lemma_append_inj a1 a2 b1 b2

let slice (b:bytes) (s:nat{s <= length b}) (e:nat{e <= length b /\ s <= e})
 : b:bytes{length b = e - s} = Seq.slice b s e
type range = a:nat & b:nat{a <= b}
unfold let op_Amp_Colon (a:nat) (b:nat{a <= b}) : range = (| a, b |)
unfold let op_Array_Access (b:bytes) ((|x, y|):r:range{dsnd r <= length b}) = slice b x y
unfold let op_At (b:bytes) ((|x,y|):range{y <= length b}) = slice b x y

let sub (b:bytes) (s:nat{s <= length b}) (l:nat{s + l <= length b})
  : b:bytes{length b = l} = b @ (s &: (s+l))

let split (b:bytes) (k:nat{k <= length b}): p:(bytes*bytes){
    let b1, b2 = p in length b1 = k /\ length b2 = length b - k /\ b1 ^ b2 = b} =
  S.lemma_split b k; S.split b k

let lemma_split_append (b1:bytes) (b2:bytes)
  : Lemma (split (b1 ^ b2) (length b1) = (b1, b2))
  [SMTPat (split (b1 ^ b2))] =
  let (u, v) = split (b1 ^ b2) (length b1) in
  lemma_append_inj u v b1 b2

type uint_k (k:nat) = U.uint_t (op_Multiply 8 k)

// Interpret a sequence of bytes as a mathematical integer encoded in big endian
let rec int_of_bytes (#k:nat) (b:lbytes k) : Tot (uint_k k) (decreases k) =
  let open FStar.Mul in
  if k = 0 then 0
  else
    let b1, b0 = split b (k - 1) in
    let x = UInt8.v (get b0 0) in
    let y : uint_k (k - 1) = int_of_bytes b1 in
    let z = pow2 8 * y + x in
    FStar.Math.Lemmas.pow2_plus 8 (op_Multiply 8 (k - 1));
    z

#reset-options "--initial_fuel 2 --initial_ifuel 2 --z3rlimit 30"
let rec bytes_of_int (#k:nat) (n:uint_k k)
  : Tot (b:lbytes k{int_of_bytes b = n}) (decreases k) =
  let open FStar.Mul in
  match k with
  | 0 -> empty_bytes
  | 1 -> abyte (U8.uint_to_t n)
  | _ ->
    FStar.Math.Lemmas.pow2_le_compat (8*k) 16;
    FStar.Math.Lemmas.lemma_mod_lt n 256;
    FStar.Math.Lemmas.lemma_div_lt n (8*k) 8;
    let r0:nat = U.mod n 256 in
    let r:nat = U.div n (pow2 8) in
    assert(pow2 8 * r + r0 = n);
    let b0 = abyte (U8.uint_to_t r0) in
    let b = bytes_of_int #(k - 1) r in
    lemma_split_append b b0;
    let result = b ^ b0 in
    assert(
      let n' = int_of_bytes #k result in
      let b', b0' = split (b ^ b0) (length b) in
      b' = b /\ b0' = b0 /\ U8.v (get b0' 0) = r0 /\
      int_of_bytes #(k-1) b' = r /\ n' = pow2 8 * r + r0 /\ n' = n);
    result

let lemma_bytes_of_int_inj (#k:nat) (n:uint_k k)
  : Lemma (int_of_bytes (bytes_of_int n) = n)
  [SMTPat (int_of_bytes (bytes_of_int n))] = ()

private let lemma_div_pow2 (k:nat) (x:nat) (y:nat{y < pow2 k})
  : Lemma ((op_Multiply (pow2 k) x + y) / (pow2 k) = x)
  =
  // a + n * b / b = a / b + n
  FStar.Math.Lemmas.division_addition_lemma y (pow2 k) x;
  assert((op_Multiply (pow2 k) x + y) / (pow2 k) = y / (pow2 k) + x);
  FStar.Math.Lemmas.small_division_lemma_1 y (pow2 k)

#reset-options "--initial_fuel 2 --initial_ifuel 2 --z3rlimit 25"
let rec lemma_int_of_bytes_inj (#k:nat) (b:lbytes k)
  : Lemma (ensures (bytes_of_int (int_of_bytes b) = b))
  (decreases (length b))
  [SMTPat (bytes_of_int (int_of_bytes b))] =
  let n = int_of_bytes b in
  let b' = bytes_of_int n in
  match k with
  | 0 -> lemma_empty b'; lemma_empty b
  | 1 -> assert(b'.[0] = b.[0]); lemma_equality b b'
  | _ ->
    let open FStar.Mul in
    FStar.Math.Lemmas.pow2_le_compat (8*k) 16;
    FStar.Math.Lemmas.lemma_mod_lt n 256;
    FStar.Math.Lemmas.lemma_div_lt n (8*k) 8;
    let r0 : n:nat{n < pow2 8} = U.mod n 256 in
    let r : n:nat{n < pow2 (op_Multiply 8 (k-1))} = U.div n (pow2 8) in
    let r0' = abyte (U8.uint_to_t r0) in
    let r' = bytes_of_int #(k - 1) r in
    let r'', r0'' = split b (k - 1) in
    let x = UInt8.v (get r0'' 0) in
    let y = int_of_bytes #(k - 1) r'' in
    let z = pow2 8 * y + x in
    lemma_div_pow2 8 y x;
    assert(r = int_of_bytes #(k - 1) r'');
    lemma_int_of_bytes_inj #(k - 1) r'';
    U8.v_inj (r0''.[0]) (r0'.[0]);
    lemma_equality r0'' r0';
    assert(r' ^ r0' = r'' ^ r0'')

// Machine integer specializations - these will be realized as typecasts in C
let u8_of_bytes (b:lbytes 1) : Tot (U8.t) = U8.uint_to_t (int_of_bytes b)
let u16_of_bytes (b:lbytes 2) : Tot (U16.t) = U16.uint_to_t (int_of_bytes b)
let u32_of_bytes (b:lbytes 4) : Tot (U32.t) = U32.uint_to_t (int_of_bytes b)

let u8_of_bytes8 (b:lbytes8 1uy) : Tot (U8.t) = U8.uint_to_t (int_of_bytes #1 b)
let u16_of_bytes8 (b:lbytes8 2uy) : Tot (U16.t) = U16.uint_to_t (int_of_bytes #2 b)
let u32_of_bytes8 (b:lbytes8 4uy) : Tot (U32.t) = U32.uint_to_t (int_of_bytes #4 b)
let u8_of_bytes16 (b:lbytes16 1us) : Tot (U8.t) = U8.uint_to_t (int_of_bytes #1 b)
let u16_of_bytes16 (b:lbytes16 2us) : Tot (U16.t) = U16.uint_to_t (int_of_bytes #2 b)
let u32_of_bytes16 (b:lbytes16 4us) : Tot (U32.t) = U32.uint_to_t (int_of_bytes #4 b)
let u8_of_bytes32 (b:lbytes32 1ul) : Tot (U8.t) = U8.uint_to_t (int_of_bytes #1 b)
let u16_of_bytes32 (b:lbytes32 2ul) : Tot (U16.t) = U16.uint_to_t (int_of_bytes #2 b)
let u32_of_bytes32 (b:lbytes32 4ul) : Tot (U32.t) = U32.uint_to_t (int_of_bytes #4 b)

let bytes8_of_u8 (n:U8.t) : b:lbytes8 1uy{u8_of_bytes8 b = n} = bytes_of_int #1 (U8.v n)
let bytes8_of_u16 (n:U16.t) : b:lbytes8 2uy{u16_of_bytes8 b = n} = bytes_of_int #2 (U16.v n)
let bytes8_of_u32 (n:U32.t) : b:lbytes8 4uy{u32_of_bytes8 b = n} = bytes_of_int #4 (U32.v n)
let bytes16_of_u8 (n:U8.t) : b:lbytes16 1us{u8_of_bytes16 b = n} = bytes_of_int #1 (U8.v n)
let bytes16_of_u16 (n:U16.t) : b:lbytes16 2us{u16_of_bytes16 b = n} = bytes_of_int #2 (U16.v n)
let bytes16_of_u32 (n:U32.t) : b:lbytes16 4us{u32_of_bytes16 b = n} = bytes_of_int #4 (U32.v n)
let bytes32_of_u8 (n:U8.t) : b:lbytes32 1ul{u8_of_bytes32 b = n} = bytes_of_int #1 (U8.v n)
let bytes32_of_u16 (n:U16.t) : b:lbytes32 2ul{u16_of_bytes32 b = n} = bytes_of_int #2 (U16.v n)
let bytes32_of_u32 (n:U32.t) : b:lbytes32 4ul{u32_of_bytes32 b = n} = bytes_of_int #4 (U32.v n)

(*)
// Tail recursive version of int_of_bytes that might be extracted
// to avoid unverified realization (would presumably still be too slow)
let rec decode_big_endian (b:bytes) (k:nat) (acc:uint_k k)
  : Tot (uint_k (k + length b)) (decreases (length b)) =
  let open FStar.Mul in
    if length b = 0 then acc
    else
      let b1, b0 = split b (length b - 1) in
      let acc2 = UInt8.v b0.[0] + 256 * acc in
      FStar.Math.Lemmas.pow2_plus 8 (8 * k);
      assert(UInt8.v b0.[0] + 256 * acc < pow2 (8 * (k+1)));
      decode_big_endian b1 (k + 1) acc2

let lemma_decode_big_endion (b:bytes)
  : Lemma (int_of_bytes b = decode_big_endian b 0 0)
  = admit ()
*)

type minbytes (n:nat) = b:bytes{length b >= n}

let rec xor (n:nat) (b1:minbytes n) (b2:minbytes n)
  : Tot (b:lbytes n) (decreases n)
  =
  if n = 0 then empty_bytes
  else
    let u, v = split b1 1 in
    let x, y = split b2 1 in
    let u : U.uint_t 8 = U8.v (u.[0]) in
    let x : U.uint_t 8 = U8.v (x.[0]) in
    (abyte (U8.uint_to_t (U.logxor u x))) ^ (xor (n-1) v y)

let rec lemma_xor_commutative (n:nat) (b1:minbytes n) (b2:minbytes n)
  : Lemma (xor n b1 b2 = xor n b2 b1) [SMTPat (xor n b1 b2)] =
  if n = 0 then ()
  else
    let u, v = split b1 1 in
    let x, y = split b2 1 in
    let u : U.uint_t 8 = U8.v (u.[0]) in
    let x : U.uint_t 8 = U8.v (x.[0]) in
    U.logxor_commutative u x;
    lemma_xor_commutative (n-1) v y

let rec lemma_xor_append (b1:bytes) (b2:bytes) (x1:bytes{length x1 = length b1}) (x2:bytes{length x2 = length b2})
  : Lemma (xor (length b1 + length b2) (b1^b2) (x1^x2) = (xor (length b1) b1 x1) ^ (xor (length b2) b2 x2)) =
  admit()

#reset-options "--z3rlimit 20 --max_ifuel 2 --max_fuel 2"
let rec lemma_xor_idempotent (n:nat) (b1:lbytes n) (b2:lbytes n)
  : Lemma (xor n (xor n b1 b2) b2 = b1) =
  match n with
  | 0 -> lemma_empty b1
  | 1 ->
    let b = xor 1 b1 b2 in
    let b' = xor 1 b b2 in
    let u0 : U.uint_t 8 = U8.v (b1.[0]) in
    let x0 : U.uint_t 8 = U8.v (b2.[0]) in
    assert(U8.v (b.[0]) = U.logxor u0 x0);
    assert(U8.v (b'.[0]) = U.logxor (U.logxor u0 x0) x0);
    U.logxor_inv u0 x0; // (u0 = logxor #n (logxor #n u0 x0) x0)
    assert(U.logxor (U.logxor u0 x0) x0 = u0);
    assert(forall (i:nat{i<1}).b'.[i] = b1.[i]);
    lemma_equality b' b1
  | _ ->
    let u, v = split b1 1 in
    let x, y = split b2 1 in
    let u : lbytes 1 = u in
    let x : lbytes 1 = x in
    lemma_xor_idempotent 1 u x;
    assert(xor 1 (xor 1 u x) x = u);
    let v : lbytes (n-1) = v in
    let y : lbytes (n-1) = y in
    lemma_xor_append u v x y; // xor (u^v) (x^y) = xor u x ^ xor v y
    assert(xor n (xor n b1 b2) b2 = xor n (xor 1 u x ^ xor (n-1) v y) (x^y));
    lemma_xor_append (xor 1 u x) (xor (n-1) v y) x y;
    assert(xor n (xor n b1 b2) b2 = (xor 1 (xor 1 u x) x) ^ (xor (n-1) (xor (n-1) v y) y));
    lemma_xor_idempotent (n-1) v y; // xor (xor v y) y = v
    assert(xor (n-1) (xor (n-1) v y) y = v);
    assert(xor n (xor n b1 b2) b2 = u ^ v)

module IC = FStar.Int.Cast

#reset-options "--z3rlimit 30 --max_ifuel 2 --max_fuel 2"
let utf8_encode (s:string) : b:bytes{length b <= op_Multiply 4 (Str.length s)} =
  let len = Str.length s in
  let rec aux (i:nat{i < len}) (acc:bytes{length acc <= op_Multiply 4 i})
    : Tot (b:bytes{length b <= op_Multiply 4 len}) (decreases (len - i)) =
    if i = len - 1 then acc
    else
      let cur = Str.index s i in
      if U32.(cur <^ 128ul) then
        let c = abyte (IC.uint32_to_uint8 cur) in
        aux (i + 1) (acc ^ c)
      else if U32.(cur <^ 2048ul) then
        let c0 = abyte (IC.uint32_to_uint8 U32.(128ul +^ rem cur 128ul)) in
        let c1 = abyte (IC.uint32_to_uint8 U32.(192ul +^ shift_right cur 6ul)) in
        aux (i + 1) (acc ^ c1 ^ c0)
      else if U32.(cur <^ 65536ul) then
        let c0 = abyte (IC.uint32_to_uint8 U32.(128ul +^ rem cur 128ul)) in
        let c1 = U32.rem (U32.shift_right cur 6ul) 128ul in
        let c1 = abyte (IC.uint32_to_uint8 U32.(128ul +^ c1)) in
        let c2 = U32.rem (U32.shift_right cur 12ul) 16ul in
        let c2 = abyte (IC.uint32_to_uint8 U32.(224ul +^ c2)) in
        aux (i + 1) (acc ^ c2 ^ c1 ^ c0)
      else
        let c0 = abyte (IC.uint32_to_uint8 U32.(128ul +^ rem cur 128ul)) in
        let c1 = U32.rem (U32.shift_right cur 6ul) 128ul in
        let c1 = abyte (IC.uint32_to_uint8 U32.(128ul +^ c1)) in
        let c2 = U32.rem (U32.shift_right cur 12ul) 128ul in
        let c2 = abyte (IC.uint32_to_uint8 U32.(128ul +^ c2)) in
        let c3 = U32.rem (U32.shift_right cur 18ul) 8ul in
        let c3 = abyte (IC.uint32_to_uint8 U32.(480ul +^ c3)) in
        aux (i + 1) (acc ^ c3 ^ c2 ^ c1 ^ c0)
    in
  if len = 0 then empty_bytes
  else aux 0 empty_bytes

let utf8_encode8 (s:string{Str.length s < 64}) : (b:bytes8{U8.v (length8 b) <= op_Multiply 4 (Str.length s)})
  = utf8_encode s
let utf8_encode16 (s:string{Str.length s < 16384}) : (b:bytes16{U16.v (length16 b) <= op_Multiply 4 (Str.length s)})
  = utf8_encode s
let utf8_encode32 (s:string{Str.length s < 536870912}) : (b:bytes32{U32.v (length32 b) <= op_Multiply 4 (Str.length s)})
  = utf8_encode s

(*)
let utf8_decode (b:bytes) : option (s:string{Str.length s <= length b}) =
  let rec
*)
(* Little endian integer value of a sequence of bytes *)
(*)
val decode_little_endian: b:bytes ->
  Tot (uint_t (length b)) (decreases (length b))
let rec decode_little_endian b =
  let open FStar.Mul in
  if length b = 0 then 0
  else UInt8.v (head b) + pow2 8 * decode_little_endian (tail b)

val decode_little_endian_acc: b:bytes -> k:nat -> acc:uint_t k ->
    Tot (uint_t (k + length b)) (decreases (length b))

let rec decode_little_endian_acc b k acc =
  let open FStar.Mul in
    if length b = 0 then acc
    else
      let acc2 = UInt8.v (head b) + 256 * acc in
        FStar.Math.Lemmas.pow2_plus 8 (8 * k);
        assert(UInt8.v (last b) + 256 * acc < pow2 (8 * (k+1)));
        decode_little_endian_acc (tail b) (k + 1) acc2

val eq_lemma_decode_little_endian: b:bytes ->
  Lemma (decode_little_endian b = decode_little_endian_acc b 0 0)
*)
(*
val eq_lemma_decode_big_endion:
  b:bytes ->
  Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)
  (decreases (lengtjh ))

let rec eq_lemma_decode_big_endion b =
  if length b = 0 then ()
  //else eq_lemma_decode_big_endion (tail b)
  else
    let sub = slice b 0 (length b - 1) in
    assert(length sub = length b - 1);
    eq_lemma_decode_big_endion sub
*)
(*
val eq_lemma_decode_big_endion: b:bytes ->
  GTot (u:unit{decode_big_endian b = decode_big_endian_acc b 0 0})
  (decreases (length b))
*)
(*
val eq_lemma_decode_big_endian: b:bytes ->
  Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)

let rec eq_lemma_decode_big_endion b =
  if length b = 0 then ()
  else eq_lemma_decode_big_endion (tail b)
  //else eq_lemma_decode_big_endion (slice b 0 (length b - 1))
*)
(*)
val get_binary: n:nat -> Tot (bytes)
let rec get_binary n =
  match n with
  | 0 -> Seq.createEmpty
  | _ -> Seq.append (get_binary (n / 2)) (of_list [U8.uint_to_t (n % 2)])
*)
(*
//val format: n:nat{n>0 /\ n <=20} -> Tot (bytes)
val format: n:nat -> Tot (bytes)
let format n =
  match n with
  | 1  -> (of_list [U8.uint_to_t 000000]) | 2  -> (of_list [U8.uint_to_t 00000])
  | 3  -> (of_list [U8.uint_to_t 0000])   | 4  -> (of_list [U8.uint_to_t 000])
  | 5  -> (of_list [U8.uint_to_t 00])     | 6  -> (of_list [U8.uint_to_t 0])
  | 7  -> Seq.createEmpty                 | 8  -> (of_list [U8.uint_to_t 000])
  | 9  -> (of_list [U8.uint_to_t 00])     | 10 -> (of_list [U8.uint_to_t 0])
  | 11 -> Seq.createEmpty                 | 12 -> (of_list [U8.uint_to_t 0000])
  | 13 -> (of_list [U8.uint_to_t 000])    | 14 -> (of_list [U8.uint_to_t 00])
  | 15 -> (of_list [U8.uint_to_t 0])      | 16 -> Seq.createEmpty
  | 17 -> (of_list [U8.uint_to_t 000])    | 18 -> (of_list [U8.uint_to_t 00])
  | 19 -> (of_list [U8.uint_to_t 0])      | 20 -> Seq.createEmpty
  | _ -> Seq.createEmpty

val binary_code_point: n:nat -> Tot (bytes)
let binary_code_point n =
  let b = (get_binary n) in
    Seq.append (format(length b)) b

val encode_utf8: n:nat -> Tot (bytes)
let encode_utf8 n =
  let code_point = (binary_code_point n) in
    if n < 127 then Seq.append (of_list [U8.uint_to_t 0]) (code_point)
    else if n < 2047 then
      (of_list [U8.uint_to_t 110])
    else Seq.createEmpty
*)
(*
#reset-options "--initial_fuel 1 --max_fuel 1"

// turns an integer into a bytestream, little-endian
val encode_little_endian: k:nat -> n:uint_t k ->
 Tot (b:lbytes k {n == decode_little_endian b}) (decreases k)
let rec little_bytes len n =
 if len = 0ul then
   Seq.createEmpty
 else
   let len = len -^ 1ul in
   let byte = UInt8.uint_to_t (n % 256) in
   let n' = n / 256 in
//   Math.Lemmas.pow2_plus 8 (8 * v len);
   assert(n' < pow2 (8 * v len ));
   let b' = little_bytes len n' in
   let b = cons byte b' in
   assert(Seq.equal b' (tail b));
   b

#reset-options "--initial_fuel 1 --max_fuel 1"
val little_endian_null: len:nat{len < 16} -> Lemma
 (little_endian (Seq.create len 0uy) == 0)

val little_endian_singleton: n:UInt8.t -> Lemma
 (little_endian (Seq.create 1 n) == UInt8.v n)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

val little_endian_append: w1:bytes -> w2:bytes -> Lemma
 (requires True)
 (ensures
   little_endian (Seq.append w1 w2) ==
   little_endian w1 + pow2 (8 * Seq.length w1) * little_endian w2)
 (decreases (Seq.length w1))
*)
