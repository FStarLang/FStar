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
module Crypto.Symmetric.Poly1305.Spec

(** Just the mathematical specification, used in the probabilistic security
  * assumption, aiming for a generic group
  *)

open FStar.Mul
open FStar.Ghost
open FStar.Seq

(** Machine integers *)
open FStar.UInt8
open FStar.UInt64
open FStar.Int.Cast

(** Mathematical definitions *)
open FStar.Math.Lib
open FStar.Math.Lemmas
open Crypto.Symmetric.Bytes 

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(** Poly1305 prime *)
let p_1305: p:nat{pow2 128 < p} =
  assert_norm (pow2 128 < pow2 130 - 5);
  pow2 130 - 5

(** Elements of the field GF(p_1305) *)
type elem = n:nat{n < p_1305}
let zero:elem = 0

(** Words are at most 16 bytes *)
type word = b:bytes{Seq.length b <= 16}

(** Full words (Chacha20-Poly1305 uses only full words) *)
type word_16 = b:bytes{Seq.length b = 16}

(** Tags are 16-byte long *)
let taglen = 16ul 

type tag = word_16

(** A type for messages MACed, used for ideal log *)
type text = seq word // Used to be seq elem

(** Field addition *)
val field_add: elem -> elem -> Tot elem
let field_add a b = (a + b) % p_1305

(** Field product *)
val field_mul: elem -> elem -> Tot elem
let field_mul a b = (a * b) % p_1305

(** Infix field operators for readability *)
let op_Plus_At = field_add
let op_Star_At = field_mul

(** Encoding of words as field elements *)
let encode (w:word) : Tot elem =
  let l = length w in
  pow2_le_compat 128 (8 * l);
  pow2 (8 * l) +@ little_endian w

(** Encoding never maps to the zero element *)
private val lemma_encode_nonzero: v:word -> Lemma (encode v <> 0)
let lemma_encode_nonzero v =
  lemma_little_endian_is_bounded v;
  Math.Lemmas.pow2_double_sum 128;
  Math.Lemmas.pow2_le_compat 128 (8 * length v);
  cut (pow2 (8 * length v) + little_endian v < pow2 129);
  assert_norm(pow2 129 < pow2 130 - 5);
  Math.Lemmas.modulo_lemma (pow2 (8 * length v) + little_endian v) p_1305

(**
   Functional specification of Poly1305.
   Words in the input text are encoded as field elements and interpreted as
   coefficients of the polynomial, which is evaluted on r.
   Note that the because of the way we use this is in ideal logs, the order of
   the input words is reversed, i.e.

   poly (w_q ... w_1) r = encode w_q * r + ... + encode w_1 * r^q

   Accordingly, sequences seen as polynomials are implicitly extended with 0s.
*)
val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))

let rec poly vs r =
  if Seq.length vs = 0 then 0
  else 
    let v = Seq.head vs in
    (encode v +@ poly (Seq.tail vs) r) *@ r


(* REMARK: Currently unused
   The idea was to use it to back up polynomial equality in paper *)
val eq_poly0: p:text -> Tot bool (decreases (length p)) 
let rec eq_poly0 p = 
  Seq.length p = 0 || 
  (encode (Seq.head p) = 0 && eq_poly0 (Seq.tail p))

val eq_poly: p0:text -> p1:text -> Tot bool (decreases (length p0))
let rec eq_poly p0 p1 = 
  if Seq.length p0 = 0 then eq_poly0 p1 
  else if Seq.length p1 = 0 then eq_poly0 p0
  else 
    encode (Seq.head p0) = encode (Seq.head p1) && 
    eq_poly (Seq.tail p0) (Seq.tail p1)

private val eq_poly0_spec: p:text -> r:elem -> Lemma
  (requires (eq_poly0 p))
  (ensures  (poly p r == 0))
  (decreases (Seq.length p))
let eq_poly0_spec p r =
  if Seq.length p = 0 then () 
  else lemma_encode_nonzero (Seq.head p)

private val eq_poly_spec: p0:text -> p1:text -> r:elem -> Lemma
  (requires (eq_poly p0 p1))
  (ensures  (poly p0 r = poly p1 r))
  (decreases (Seq.length p0))
let rec eq_poly_spec p0 p1 r =
  if Seq.length p0 = 0 then eq_poly0_spec p1 r
  else if Seq.length p1 = 0 then eq_poly0_spec p0 r
  else eq_poly_spec (Seq.tail p0) (Seq.tail p1) r


private val fix: word_16 -> i:nat{i < 16} -> m:U8.t -> Tot word_16
let fix r i m = Seq.upd r i (U8.(Seq.index r i &^ m))

(** Abstract spec of clamping for the state invariant.
    For our polynomial-sampling assumption, we rely solely on the number of
    fixed bits (22)
  *)
val clamp: word_16 -> Tot elem
let clamp r =
  let r = fix r  3  15uy in // 0000****
  let r = fix r  7  15uy in
  let r = fix r 11  15uy in
  let r = fix r 15  15uy in
  let r = fix r  4 252uy in // ******00
  let r = fix r  8 252uy in
  let r = fix r 12 252uy in
  little_endian r

(** Final truncation to 128 bits to compute the tag *)
val trunc_1305: elem -> Tot elem
let trunc_1305 e = e % pow2 128

(** Finish: truncate and pad (or pad and truncate) *)
val finish: a:elem -> s:tag -> Tot tag
let finish a s =
  (* REMARK: this is equivalent to n = (a + little_endian s) % pow2 128 *)
  let n = (trunc_1305 a + little_endian s) % pow2 128 in
  little_bytes 16ul n

private val finish_alternative: a:elem -> s:tag -> Lemma
  (finish a s == little_bytes 16ul ((a + little_endian s) % pow2 128))
let finish_alternative a s =
  lemma_mod_plus_distr_l a (little_endian s) (pow2 128)

(** Specification of Poly1305 MAC *)
val mac_1305: vs:text -> r:elem -> s:tag -> Tot tag
let mac_1305 vs r s = finish (poly vs r) s
