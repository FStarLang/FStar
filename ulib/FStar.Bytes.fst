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

unfold type u8 = U8.t
unfold type u16 = U16.t
unfold type u32 = U32.t

(** Realized by uint8_t in C and int in OCaml (char does not have necessary operators...) *)
unfold type byte = u8

(** Realized by uint8_t* in C and string in OCaml.
    This is a variant for which length is NOT available at runtime *)
abstract type bytes = s:S.seq byte{S.length s < pow2 32}

(** Expose the represewntation for specs that need lemmas not defined here. *)
let reveal (b:bytes) : GTot (S.seq byte) = b
let hide (s:S.seq byte{S.length s < pow2 32}) : GTot (b:bytes{reveal b = s}) = s

let lengthT (b:bytes) : GTot (n:nat{n = S.length (reveal b)}) = S.length b
let length (b:bytes) : n:u32{U32.v n = lengthT b} = U32.uint_to_t (S.length b)
type lbytes (l:nat) = b:bytes{lengthT b = l}
type kbytes (k:nat) = b:bytes{lengthT b < pow2 k}

let empty_bytes : lbytes 0 = S.createEmpty
let lemma_empty (b:bytes)
  : Lemma (lengthT b = 0 ==> b = empty_bytes)
  [SMTPat (lengthT b)] = S.lemma_empty b

(** If you statically know the length, it is OK to read at arbitrary indexes *)
let get (b:bytes) (pos:nat{pos < lengthT b}) : GTot byte = Seq.index b pos
unfold let op_String_Access (b:bytes) (i:u32{U32.(i <^ length b)})
  : r:byte{r = get b (U32.v i)} = Seq.index b (U32.v i)

let create (len:u32) (v:byte) : b:lbytes (U32.v len){forall (i:u32{U32.(i <^ len)}). b.[i] = v} =
  S.lemma_create_len (U32.v len) v;
  S.create (U32.v len) v

let init (len:u32) (f: i:u32{U32.(i <^ len)} -> byte) : b:lbytes (U32.v len){forall (i:u32{U32.(i <^ len)}). b.[i] = f i} =
  let f' (i:nat{i < U32.v len}) = f (U32.uint_to_t i) in
  S.lemma_init_len (U32.v len) f';
  S.init (U32.v len) f'

let abyte (b:byte) : lbytes 1 = S.create 1 b
let twobytes (b:byte*byte) : lbytes 2 = S.init 2 (fun i -> if i = 0 then fst b else snd b)

let append (b1:bytes) (b2:bytes) : Pure (b:bytes)
  (requires (lengthT b1 + lengthT b2 < pow2 32))
  (ensures (fun b -> lengthT b = lengthT b1 + lengthT b2))
  = Seq.append b1 b2

let lemma_append_empty_r (b:bytes)
  : Lemma (append b empty_bytes = b) [SMTPat (append b empty_bytes)] =
  S.append_empty_r b
let lemma_append_empty_l (b:bytes)
  : Lemma (append empty_bytes b = b) [SMTPat (append empty_bytes b)] =
  S.append_empty_l b

let lemma_equality (b1:bytes) (b2:bytes)
  : Lemma (requires (lengthT b2 = lengthT b1) /\ (forall (i:nat{i < lengthT b1}).{:pattern (get b1 i); (get b2 i)} (get b1 i = get b2 i)))
    (ensures b1 = b2)
  =
  assert(forall (i:nat{i < lengthT b1}).{:pattern (get b1 i); (get b2 i)} get b1 i = S.index b1 i /\ get b2 i = S.index b2 i);
  assert(forall (i:nat{i < lengthT b1}).{:pattern (S.index b1 i); (S.index b2 i)} (S.index b1 i == S.index b2 i));
  S.lemma_eq_intro b1 b2

unfold let op_Hat (b1:bytes) (b2:bytes) : Pure (b:bytes)
  (requires (lengthT b1 + lengthT b2 < pow2 32))
  (ensures (fun b -> lengthT b = lengthT b1 + lengthT b2)) = append b1 b2
unfold let op_At_Bar (b1:bytes) (b2:bytes) : Pure (b:bytes)
  (requires (lengthT b1 + lengthT b2 < pow2 32))
  (ensures (fun b -> lengthT b = lengthT b1 + lengthT b2)) = append b1 b2

let lemma_append_inj (a1:bytes) (a2:bytes) (b1:bytes) (b2:bytes)
  : Lemma (requires ((lengthT a1 + lengthT a2 < pow2 32 /\ lengthT b1 + lengthT b2 < pow2 32)
            /\ (lengthT a1 = lengthT b1 \/ lengthT a2 = lengthT b2) /\ a1 ^ a2 = b1 ^ b2))
          (ensures a1 = b1 /\ a2 = b2) [SMTPat (a1 ^ a2 = b1 ^ b2)]
  = S.lemma_append_inj a1 a2 b1 b2

let sliceT (b:bytes) (s:nat{s <= lengthT b}) (e:nat{e <= lengthT b /\ s <= e})
  : GTot (b:lbytes (e - s)) = Seq.slice b s e
let slice (b:bytes) (s:u32{U32.(s <=^ length b)}) (e:u32{U32.(e <=^ length b /\ s <=^ e)})
  : r:bytes{length r = U32.(e -^ s) /\ r = sliceT b (U32.v s) (U32.v e)}
  = Seq.slice b (U32.v s) (U32.v e)

let subT (b:bytes) (s:nat{s <= lengthT b}) (l:nat{s + l <= lengthT b})
  : GTot (b:bytes{lengthT b = l}) = sliceT b s (s+l)
let sub (b:bytes) (s:u32{U32.(s <=^ length b)}) (l:u32{U32.v s + U32.v l <= lengthT b})
  : r:bytes{length r = l /\ r = subT b (U32.v s) (U32.v l)}
  = Seq.slice b (U32.v s) (U32.v s + U32.v l)

let splitT (b:bytes) (k:nat{k <= lengthT b})
  : GTot (p:(lbytes k * lbytes (lengthT b - k)){(fst p) ^ (snd p) = b}) =
  S.lemma_split b k;
  let (s1, s2) : (S.seq byte * S.seq byte) = S.split b k in
  assert(S.length s1 < pow2 32 /\ S.length s2 < pow2 32);
  assert(S.length s1 = k /\ S.length s2 = S.length b - k);
  (s1, s2)

let split (b:bytes) (k:u32{U32.v k <= lengthT b})
  : p:(bytes*bytes){length (fst p) = k
      /\ length (snd p) = U32.(length b -^ k)
      /\ (fst p) ^ (snd p) = b} =
  S.lemma_split b (U32.v k);
  let (s1, s2) : (S.seq byte * S.seq byte) = S.split b (U32.v k) in
  assert(S.length s1 < pow2 32 /\ S.length s2 < pow2 32);
  assert(S.length s1 = U32.v k /\ S.length s2 = S.length b - U32.v k);
  (s1, s2)

let lemma_split_append (b1:bytes) (b2:bytes{lengthT b1 + lengthT b2 < pow2 32})
  : Lemma (split (b1^b2) (length b1) = (b1, b2))
    [SMTPat (split (b1 ^ b2) (length b1))]
  =
  let (u, v) = split (b1 ^ b2) (length b1) in
  lemma_append_inj u v b1 b2

type uint_k (k:nat) = U.uint_t (op_Multiply 8 k)

// Interpret a sequence of bytes as a mathematical integer encoded in big endian
let rec int_of_bytes (#k:nat) (b:lbytes k) : GTot (uint_k k) (decreases k) =
  let open FStar.Mul in
  if k = 0 then 0
  else
    let b1, b0 = splitT b (k - 1) in
    let x = UInt8.v (get b0 0) in
    let y : uint_k (k - 1) = int_of_bytes b1 in
    let z = pow2 8 * y + x in
    FStar.Math.Lemmas.pow2_plus 8 (op_Multiply 8 (k - 1));
    z

#reset-options "--initial_fuel 2 --initial_ifuel 2 --z3rlimit 30"
let rec bytes_of_int (#k:nat{k <= 32}) (n:uint_k k)
  : GTot (b:lbytes k{int_of_bytes b = n}) (decreases k) =
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

let lemma_int_of_bytes_of_int (#k:nat{k <= 32}) (n:uint_k k)
  : Lemma (int_of_bytes (bytes_of_int n) = n)
  [SMTPat (int_of_bytes (bytes_of_int n))] = ()

private let lemma_div_pow2 (k:nat{k <= 32}) (x:nat) (y:nat{y < pow2 k})
  : Lemma ((op_Multiply (pow2 k) x + y) / (pow2 k) = x) =
  FStar.Math.Lemmas.division_addition_lemma y (pow2 k) x;
  assert((op_Multiply (pow2 k) x + y) / (pow2 k) = y / (pow2 k) + x);
  FStar.Math.Lemmas.small_division_lemma_1 y (pow2 k)

private let lemma_mod_pow2 (k:nat{k <= 32}) (x:nat) (y:nat{y < pow2 k})
  : Lemma ((op_Multiply (pow2 k) x + y) % (pow2 k) = y) =
  FStar.Math.Lemmas.lemma_mod_plus y x (pow2 k);
  FStar.Math.Lemmas.small_modulo_lemma_2 y (pow2 k)

#reset-options "--initial_fuel 2 --initial_ifuel 2 --max_ifuel 2 --max_fuel 2 --z3rlimit 45"
let rec lemma_bytes_of_int_of_bytes (#k:nat{k <= 32}) (b:lbytes k)
  : Lemma (ensures (bytes_of_int (int_of_bytes b) = b)) (decreases k)
  [SMTPat (bytes_of_int (int_of_bytes b))] =
  let n = int_of_bytes b in
  let b' = bytes_of_int n in
  match k with
  | 0 -> lemma_empty b'; lemma_empty b
  | 1 -> assert(get b' 0 = get b 0); lemma_equality b b'
  | _ ->
    let open FStar.Mul in
    assert_norm (pow2 8 = 256);
    FStar.Math.Lemmas.pow2_le_compat (8*k) 16;
    FStar.Math.Lemmas.lemma_mod_lt n 256;
    FStar.Math.Lemmas.lemma_div_lt n (8*k) 8;
    let r0 : n:nat{n < pow2 8} = U.mod n 256 in
    let r : n:nat{n < pow2 (8*(k-1))} = U.div n (pow2 8) in
    let r0' = abyte (U8.uint_to_t r0) in
    let r' = bytes_of_int #(k - 1) r in
    let r'', r0'' = splitT b (k - 1) in
    let x = UInt8.v (get r0'' 0) in
    let y = int_of_bytes #(k - 1) r'' in
    let z = pow2 8 * y + x in
    lemma_div_pow2 8 y x;
    assert(r = int_of_bytes #(k - 1) r'');
    lemma_bytes_of_int_of_bytes #(k - 1) r'';
    lemma_mod_pow2 8 y x;
    assert(x = r0 /\ get r0' 0 = get r0'' 0);
    lemma_equality r0'' r0';
    assert(r' ^ r0' = r'' ^ r0'')

// We assume a correct implementation of the above functions exists
assume val int32_of_bytes: (b:bytes{lengthT b <= 4}) -> n:u32{U32.v n = int_of_bytes #(lengthT b) b}
assume val int16_of_bytes: (b:bytes{lengthT b <= 2}) -> n:u16{U16.v n = int_of_bytes #(lengthT b) b}
assume val int8_of_bytes: (b:bytes{lengthT b = 1}) -> n:u8{U8.v n = int_of_bytes #(lengthT b) b}

assume val bytes_of_int32: n:U32.t -> b:lbytes 4{b = bytes_of_int #4 (U32.v n)}
assume val bytes_of_int16: n:U16.t -> b:lbytes 2{b = bytes_of_int #2 (U16.v n)}
assume val bytes_of_int8: n:U8.t -> b:lbytes 1{b = bytes_of_int #1 (U8.v n)}

type minbytes (n:nat) = b:bytes{lengthT b >= n}
let rec xorT (n:nat) (b1:minbytes n) (b2:minbytes n)
  : GTot (b:lbytes n) (decreases n) =
  if n = 0 then empty_bytes
  else
    let u, v = splitT b1 1 in
    let x, y = splitT b2 1 in
    (abyte (U8.logxor (get u 0) (get x 0))) ^ (xorT (n-1) v y)

let rec lemma_xor_commutative (n:nat) (b1:minbytes n) (b2:minbytes n)
  : Lemma (xorT n b1 b2 = xorT n b2 b1) [SMTPat (xorT n b1 b2)] =
  if n = 0 then ()
  else
    let u, v = splitT b1 1 in
    let x, y = splitT b2 1 in
    let u : U.uint_t 8 = U8.v (get u 0) in
    let x : U.uint_t 8 = U8.v (get x 0) in
    U.logxor_commutative u x;
    lemma_xor_commutative (n-1) v y

let rec lemma_xor_append (b1:bytes) (b2:bytes{lengthT b2 + lengthT b1 < pow2 32})
                         (x1:bytes{lengthT x1 = lengthT b1}) (x2:bytes{lengthT x2 = lengthT b2})
  : Lemma (xorT (lengthT b1 + lengthT b2) (b1 ^ b2) (x1 ^ x2) = (xorT (lengthT b1) b1 x1) ^ (xorT (lengthT b2) b2 x2)) =
  admit()

#reset-options "--z3rlimit 20 --max_ifuel 2 --max_fuel 2"
let rec lemma_xor_idempotent (n:nat) (b1:lbytes n) (b2:lbytes n)
  : Lemma (xorT n (xorT n b1 b2) b2 = b1) =
  match n with
  | 0 -> lemma_empty b1
  | 1 ->
    let b = xorT 1 b1 b2 in
    let b' = xorT 1 b b2 in
    let u0 : U.uint_t 8 = U8.v (get b1 0) in
    let x0 : U.uint_t 8 = U8.v (get b2 0) in
    assert(U8.v (get b 0) = U.logxor u0 x0);
    assert(U8.v (get b' 0) = U.logxor (U.logxor u0 x0) x0);
    U.logxor_inv u0 x0; // (u0 = logxorT #n (logxorT #n u0 x0) x0)
    assert(U.logxor (U.logxor u0 x0) x0 = u0);
    assert(forall (i:nat{i<1}).get b' i = get b1 i);
    lemma_equality b' b1
  | _ ->
    let u, v = splitT b1 1 in
    let x, y = splitT b2 1 in
    let u : lbytes 1 = u in
    let x : lbytes 1 = x in
    lemma_xor_idempotent 1 u x;
    assert(xorT 1 (xorT 1 u x) x = u);
    let v : lbytes (n-1) = v in
    let y : lbytes (n-1) = y in
    lemma_xor_append u v x y; // xorT (u^v) (x^y) = xorT u x ^ xorT v y
    assert(xorT n (xorT n b1 b2) b2 = xorT n (xorT 1 u x ^ xorT (n-1) v y) (x^y));
    lemma_xor_append (xorT 1 u x) (xorT (n-1) v y) x y;
    assert(xorT n (xorT n b1 b2) b2 = (xorT 1 (xorT 1 u x) x) ^ (xorT (n-1) (xorT (n-1) v y) y));
    lemma_xor_idempotent (n-1) v y; // xorT (xorT v y) y = v
    assert(xorT (n-1) (xorT (n-1) v y) y = v);
    assert(xorT n (xorT n b1 b2) b2 = u ^ v)

assume val xor: n:u32 -> b1:minbytes (U32.v n) -> b2:minbytes (U32.v n) -> b:bytes{length b = n /\ b = xorT (U32.v n) b1 b2}

module IC = FStar.Int.Cast

#reset-options "--z3rlimit 30 --initial_ifuel 2 --initial_fuel 2 --max_ifuel 2 --max_fuel 2"
let utf8_encodeT (s:string{Str.length s < pow2 30}) : GTot (b:bytes{lengthT b <= op_Multiply 4 (Str.length s)}) =
  let len : n:nat{n < pow2 30} = Str.length s in
  let rec aux (i:nat{i < len}) (acc:bytes{lengthT acc <= op_Multiply 4 i})
    : GTot (b:bytes{lengthT b <= op_Multiply 4 len}) (decreases (len - i)) =
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

assume val utf8_encode: (s:string{Str.length s < pow2 30}) -> b:bytes{lengthT b <= op_Multiply 4 (Str.length s) /\ b = utf8_encodeT s}

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
