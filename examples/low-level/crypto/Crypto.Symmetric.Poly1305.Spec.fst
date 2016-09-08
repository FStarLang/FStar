module Crypto.Symmetric.Poly1305.Spec

(* Just the mathematical specification, 
   used in the probabilistic security assumption,
   aiming for a generic group *)

open FStar.Mul
open FStar.Ghost
open FStar.Seq

(** Machine integers *)
open FStar.UInt8
open FStar.UInt64
open FStar.Int.Cast

(** Mathematical definitions *)
open Math.Axioms
open Math.Lib
open Math.Lemmas

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

// missing overloading...
//inline let op_Array_Access (#a:Type) (s:Seq.seq a) n = Seq.index s n

let p_1305 : nat = pow2 130 - 5  // prime (do we prove it? use it?)

type elem = n:nat{n < p_1305}    // elements of the field Z / p_1305 Z


type word = b: seq byte {Seq.length b <= 16} 
type word_16 = b:seq byte {Seq.length b = 16} 
// we only use full words for AEAD

type text = seq elem // not word_16
type tag = word_16 

(* * *********************************************)
(* *            Field operations                 *)
(* * *********************************************)
val field_add: elem -> elem -> Tot elem
let field_add a b = (a + b) % p_1305 
val field_mul: elem -> elem -> Tot elem
let field_mul a b = (a * b) % p_1305 
(* Infix operators for readability *)
let op_Plus_At = field_add
let op_Star_At = field_mul

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:word) : Tot (n:nat) (decreases (Seq.length b))
  = if Seq.length b = 0 then 0
    else U8.v (Seq.index b 0) +
	 pow2 8 * little_endian (Seq.slice b 1 (Seq.length b))

val lemma_euclidian_division: a:nat -> b:nat -> Lemma
  (requires (a < pow2 8))
  (ensures  (a + pow2 8 * b < pow2 8 * (b+1)))
let lemma_euclidian_division a b = ()

val lemma_factorise: a:nat -> b:nat -> Lemma
  (requires (True))
  (ensures  (a + a * b = a * (b + 1)))
let lemma_factorise a b = ()

//TMP#reset-options "--z3timeout 100"
#set-options "--lax" // OK, but long timeout

val lemma_little_endian_is_bounded: b:word -> Lemma
  (requires (True))
  (ensures  (little_endian b < pow2 (8*(Seq.length b))))
  (decreases (Seq.length b))
let rec lemma_little_endian_is_bounded b =
  if Seq.length b = 0 then ()
  else (
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_little_endian_is_bounded s;
    assert(U8.v (Seq.index b 0) < pow2 8);
    assert(little_endian s < pow2 (8 * Seq.length s));
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidian_division (U8.v (Seq.index b 0)) (little_endian s);
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    assert(little_endian b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_exp_1 8 (pow2 (8 * (Seq.length b - 1)));
    lemma_factorise 8 (Seq.length b - 1)
  )

#reset-options

val lemma_little_endian_lt_2_128: b:word -> Lemma
  (requires (True))
  (ensures  (little_endian b < pow2 128))
  [SMTPat (little_endian b)]
let lemma_little_endian_lt_2_128 b =
  lemma_little_endian_is_bounded b;
  if Seq.length b = 16 then ()
  else Math.Lib.pow2_increases_lemma 128 (8 * Seq.length b)


let encode_16 (w:word_16) : elem = pow2 128  +@  little_endian w 
// not using the lemma below?

let trunc_1305 (e:elem) = e % pow2 128

(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

let lemma_little_endian_is_injective_0 (b:word{Seq.length b > 0}) : Lemma
  (requires (True))
  (ensures  (little_endian b = U8.v (Seq.index b 0) + pow2 8 * little_endian (Seq.slice b 1 (Seq.length b)) ))
  = ()

//TMP#reset-options "--initial_fuel 0 --max_fuel 0"

(* Lemma unknown to F*, should go into core libraries *)
assume val lemma_modulo: a:nat -> b:nat -> c:pos -> Lemma
  (requires (True))
  (ensures   ((a + b * c) % c = a))

let lemma_little_endian_is_injective_1 (b:pos) (q:nat) (r:nat) (q':nat) (r':nat) : Lemma
  (requires (r < b /\ r' < b /\ r + b * q = r' + b * q'))
  (ensures  (r = r' /\ q = q'))
  = lemma_modulo r q b;
    lemma_modulo r' q' b

//TMP#reset-options

val lemma_little_endian_is_injective_2: b:word -> len:pos{len <= Seq.length b} -> Lemma
  (requires (True))
  (ensures  (
    let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
    let s' = Seq.slice s 1 (Seq.length s) in
    let s'' = Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) in
    s'' == s'))
let lemma_little_endian_is_injective_2 b len =
  let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
  let s' = Seq.slice s 1 (Seq.length s) in
  let s'' = Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) in
  Seq.lemma_eq_intro s' s''

//TMP#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val lemma_little_endian_is_injective_3: b:word -> b':word  -> len:pos{len <= Seq.length b /\ len <= Seq.length b'} -> Lemma
  (requires (Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) == Seq.slice b' (Seq.length b' - (len-1)) (Seq.length b')
    /\ Seq.index b (Seq.length b - len) = Seq.index b' (Seq.length b' - len)))
  (ensures  (Seq.slice b (Seq.length b - len) (Seq.length b) == Seq.slice b' (Seq.length b' - len) (Seq.length b')))
let lemma_little_endian_is_injective_3 b b' len =
  Seq.lemma_eq_intro (Seq.slice b' (Seq.length b' - len) (Seq.length b'))
		     (Seq.append (Seq.create 1 (Seq.index b' (Seq.length b' - len))) (Seq.slice b' (Seq.length b' - (len-1)) (Seq.length b')));
  Seq.lemma_eq_intro (Seq.slice b (Seq.length b - len) (Seq.length b))
		     (Seq.append (Seq.create 1 (Seq.index b (Seq.length b - len))) (Seq.slice b (Seq.length b - (len-1)) (Seq.length b)))

#reset-options "--initial_fuel 1 --max_fuel 1 --z3timeout 50"

val lemma_little_endian_is_injective: b:word -> b':word ->
  len:nat{Seq.length b >= len /\ Seq.length b' >= len} -> Lemma
    (requires (little_endian (Seq.slice b (Seq.length b - len) (Seq.length b))
      = little_endian (Seq.slice b' (Seq.length b' - len) (Seq.length b')) ))
    (ensures  (Seq.slice b (Seq.length b - len) (Seq.length b)
	      == Seq.slice b' (Seq.length b' - len) (Seq.length b')))
let rec lemma_little_endian_is_injective b b' len =
  if len = 0 then (
    Seq.lemma_eq_intro (Seq.slice b (Seq.length b - len) (Seq.length b))
		       (Seq.slice b' (Seq.length b' - len) (Seq.length b'))
  )
  else (
    let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
    let s' = Seq.slice b' (Seq.length b' - len) (Seq.length b') in
    assert(Seq.length s = len /\ Seq.length s' = len);
    lemma_little_endian_is_injective_0 s; lemma_little_endian_is_injective_0 s';
    lemma_little_endian_is_injective_1 (pow2 8)
				      (little_endian (Seq.slice s 1 (Seq.length s)))
				      (U8.v (Seq.index s 0))
				      (little_endian (Seq.slice s' 1 (Seq.length s')))
				      (U8.v (Seq.index s' 0));
    lemma_little_endian_is_injective_2 b len;
    lemma_little_endian_is_injective_2 b' len;
    lemma_little_endian_is_injective b b' (len - 1);
    lemma_little_endian_is_injective_3 b b' len
  )


(* * *********************************************)
(* *        Poly1305 functional invariant        *)
(* * *********************************************)

#reset-options "--initial_fuel 4 --max_fuel 4"

let lemma_prime_is_greater_than_2_128 (u:unit) : Lemma
  (requires True)
  (ensures  (p_1305 > pow2 128))
  = cut (pow2 3 = 8);
    Math.Lib.pow2_increases_lemma 130 129;
    Math.Lib.pow2_increases_lemma 129 128;
    Math.Lib.pow2_increases_lemma 128 3

//TMP#reset-options

let seq_head (vs:seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

val poly: vs:seq elem -> r:elem -> GTot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else (poly (seq_head vs) r +@ Seq.index vs (length vs - 1)) *@ r

let fix (r:word_16) (i:nat {i < 16}) m : word_16 = Seq.upd r i (U8 (Seq.index r i &^ m)) 

// an abstract spec of clamping for our state invariant 
// for our polynomial-sampling assumption, 
// we rely solely on the number of fixed bits (22, right?)
val clamp: word_16 -> GTot elem
let clamp r = 
  let r = fix r  3  15uy in // 0000****
  let r = fix r  7  15uy in 
  let r = fix r 11  15uy in 
  let r = fix r 15  15uy in 
  let r = fix r  4 252uy in // ******00
  let r = fix r  8 252uy in 
  let r = fix r 12 252uy in 
  little_endian r


let mac_1305 (vs:seq elem) r s = (trunc_1305 (poly vs r) + little_endian s) % pow2 128
