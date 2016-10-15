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
open FStar.Math.Lib
open FStar.Math.Lemmas

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

#reset-options "--initial_fuel 4 --max_fuel 4"

// prime (do we prove it? use it?)
let p_1305: p:nat{pow2 128 < p} =
  assert_norm (pow2 128 < pow2 130 - 5);
  pow2 130 - 5

#reset-options

type elem = n:nat{n < p_1305} // elements of the field Z / p_1305 Z

type word = b:seq byte {Seq.length b <= 16}
type word_16 = b:seq byte {Seq.length b = 16}
// we only use full words for AEAD

type text = seq elem // not word_16
type tag = word_16
let taglen 'id = 16ul

(* * *********************************************)
(* *            Field operations                 *)
(* * *********************************************)
val field_add: elem -> elem -> Tot elem
let field_add a b = (a + b) % p_1305
val field_mul: elem -> elem -> Tot elem
let field_mul a b = (a * b) % p_1305

(* Infix field operators for readability *)
let op_Plus_At = field_add
let op_Star_At = field_mul

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:word) : Tot (n:nat) (decreases (Seq.length b))
  = if Seq.length b = 0 then 0
    else U8.v (Seq.index b 0) +
	 pow2 8 * little_endian (Seq.slice b 1 (Seq.length b))

val lemma_euclidean_division: a:nat -> b:nat -> Lemma
  (requires (a < pow2 8))
  (ensures  (a + pow2 8 * b < pow2 8 * (b + 1)))
let lemma_euclidean_division a b = ()

val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b = a * (b + 1))
let lemma_factorise a b = ()

#reset-options "--initial_fuel 1 --max_fuel 1"

val little_endian_null: len:nat{len < 16} -> Lemma
  (little_endian (Seq.create len 0uy) == 0)
let rec little_endian_null len =
  if len = 0 then ()
  else
    begin
    Seq.lemma_eq_intro (Seq.slice (Seq.create len 0uy) 1 len)
		       (Seq.create (len - 1) 0uy);
    assert (little_endian (Seq.create len 0uy) ==
      0 + pow2 8 * little_endian (Seq.slice (Seq.create len 0uy) 1 len));
    little_endian_null (len - 1)
    end

val little_endian_singleton: n:U8.t -> Lemma
  (little_endian (Seq.create 1 n) == U8.v n)
let little_endian_singleton n =
  assert (little_endian (Seq.create 1 n) ==
    U8.v (Seq.index (Seq.create 1 n) 0) + pow2 8 *
    little_endian (Seq.slice (Seq.create 1 n) 1 1))

#set-options "--z3timeout 20"

val little_endian_append: w1:word -> w2:word{length w1 + length w2 <= 16} -> Lemma
  (requires True)
  (ensures 
    little_endian (append w1 w2) ==
    little_endian w1 + pow2 (8 * length w1) * little_endian w2)
  (decreases (length w1))
let rec little_endian_append w1 w2 =
  if length w1 = 0 then
    begin
    assert_norm (pow2 (8 * 0) == 1);
    Seq.lemma_eq_intro (append w1 w2) w2
    end
  else 
    begin
    let w1' = slice w1 1 (length w1) in
    assert (length w1' == length w1 - 1);
    little_endian_append w1' w2;
    assert (index (append w1 w2) 0 == index w1 0);
    Seq.lemma_eq_intro
      (append w1' w2) 
      (Seq.slice (append w1 w2) 1 (length (append w1 w2)));
    assert (little_endian (append w1 w2) ==
      U8.v (index w1 0) + pow2 8 * little_endian (append w1' w2));
    assert (little_endian (append w1' w2) ==
      little_endian w1' + pow2 (8 * length w1') * little_endian w2);
    assert (U8.v (index w1 0) + pow2 8 * little_endian (append w1' w2) ==
      U8.v (index w1 0) + 
      pow2 8 * (little_endian w1' + pow2 (8 * length w1') * little_endian w2));
    pow2_plus 8 (8 * (length w1 - 1));
    assert (pow2 8 * pow2 (8 * length w1') == pow2 (8 * length w1));
    assert (U8.v (index w1 0) + pow2 8 * little_endian (append w1' w2) ==
      U8.v (index w1 0) + 
      pow2 8 * little_endian w1' + pow2 (8 * length w1) * little_endian w2);
    assert (U8.v (index w1 0) + pow2 8 * little_endian w1' == little_endian w1)  
    end

val lemma_little_endian_is_bounded: b:word -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
let rec lemma_little_endian_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_little_endian_is_bounded s;
    assert(U8.v (Seq.index b 0) < pow2 8);
    assert(little_endian s < pow2 (8 * Seq.length s));
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (U8.v (Seq.index b 0)) (little_endian s);
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    assert(little_endian b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_little_endian_lt_2_128: b:word -> Lemma
  (requires (True))
  (ensures  (little_endian b < pow2 128))
  [SMTPat (little_endian b)]
let lemma_little_endian_lt_2_128 b =
  lemma_little_endian_is_bounded b;
  if Seq.length b = 16 then ()
  else pow2_lt_compat 128 (8 * Seq.length b)


(* * *********************************************)
(* *            Encoding                         *)
(* * *********************************************)

let encode (w:word) : Tot elem =
  let l = length w in
  pow2_le_compat 128 (8 * l);
  pow2 (8 * l) +@ little_endian w

// a spec for encoding and padding, convenient for injectivity proof
// TODO: Unused now
let pad_0 b l = Seq.append b (Seq.create l 0uy)

val encode_pad: prefix:Seq.seq elem -> txt:Seq.seq UInt8.t -> GTot (Seq.seq elem) 
  (decreases (Seq.length txt))
let rec encode_pad prefix txt =
  let l = Seq.length txt in
  if l = 0 then prefix
  else if l < 16 then
    let w = txt in
    SeqProperties.snoc prefix (encode w)
  else
    begin
    let w, txt = SeqProperties.split txt 16 in
    let prefix = SeqProperties.snoc prefix (encode w) in
    encode_pad prefix txt
    end


//16-09-18 where is it in the libraries??
private let min (a:nat) (b:nat) : nat = if a <= b then a else b

//16-10-15 simpler variant? rediscuss injectivity.
val encode_bytes: txt:Seq.seq UInt8.t -> Tot (Seq.seq elem) (decreases (Seq.length txt))
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then 
    Seq.createEmpty
  else 
    let l0 = min l 16 in
    let txt0, txt = SeqProperties.split txt l0 in
    let w = pad_0 txt0 (16 - l0) in 
    SeqProperties.cons (encode w) (encode_bytes txt)


#reset-options "--z3timeout 200"
let rec lemma_encode_length txt: Lemma
  (ensures (Seq.length(encode_bytes txt) = (Seq.length txt + 15) / 16))
  (decreases (Seq.length txt))
=
  let l = Seq.length txt in 
  if l = 0 then ()
  else if l < 16 then assert(Seq.length(encode_bytes txt) = 1)
  else (
    let txt0, txt' = SeqProperties.split txt 16 in
    lemma_encode_length txt'; 
    assert(Seq.length(encode_bytes txt) = 1 + Seq.length(encode_bytes txt')))

let trunc_1305 (e:elem) : Tot elem = e % pow2 128


(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

val lemma_little_endian_is_injective_0: b:word{Seq.length b > 0} -> Lemma
  (little_endian b =
   U8.v (Seq.index b 0) + pow2 8 * little_endian (Seq.slice b 1 (Seq.length b)))
let lemma_little_endian_is_injective_0 b = ()

val lemma_little_endian_is_injective_1: b:pos -> q:nat -> r:nat -> q':nat -> r':nat -> Lemma
  (requires (r < b /\ r' < b /\ r + b * q = r' + b * q'))
  (ensures  (r = r' /\ q = q'))
let lemma_little_endian_is_injective_1 b q r q' r' =
  lemma_mod_plus r q b;
  lemma_mod_plus r' q' b;
  lemma_mod_injective b r r'

val lemma_little_endian_is_injective_2: b:word -> len:pos{len <= Seq.length b} -> Lemma
  (let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
   let s' = Seq.slice s 1 (Seq.length s) in
   let s'' = Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) in
   s'' == s')
let lemma_little_endian_is_injective_2 b len =
  let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
  let s' = Seq.slice s 1 (Seq.length s) in
  let s'' = Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) in
  Seq.lemma_eq_intro s' s''

val lemma_little_endian_is_injective_3: b:word -> b':word -> len:pos{len <= Seq.length b /\ len <= Seq.length b'} -> Lemma
  (requires (Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) ==
             Seq.slice b' (Seq.length b' - (len-1)) (Seq.length b')
           /\ Seq.index b (Seq.length b - len) = Seq.index b' (Seq.length b' - len)))
  (ensures  (Seq.slice b (Seq.length b - len) (Seq.length b) ==
             Seq.slice b' (Seq.length b' - len) (Seq.length b')))
let lemma_little_endian_is_injective_3 b b' len =
  Seq.lemma_eq_intro (Seq.slice b' (Seq.length b' - len) (Seq.length b'))
		     (Seq.append (Seq.create 1 (Seq.index b' (Seq.length b' - len))) (Seq.slice b' (Seq.length b' - (len-1)) (Seq.length b')));
  Seq.lemma_eq_intro (Seq.slice b (Seq.length b - len) (Seq.length b))
		     (Seq.append (Seq.create 1 (Seq.index b (Seq.length b - len))) (Seq.slice b (Seq.length b - (len-1)) (Seq.length b)))

val lemma_little_endian_is_injective: b:word -> b':word ->
  len:nat{Seq.length b >= len /\ Seq.length b' >= len} -> Lemma
  (requires (little_endian (Seq.slice b (Seq.length b - len) (Seq.length b)) =
             little_endian (Seq.slice b' (Seq.length b' - len) (Seq.length b')) ))
  (ensures  (Seq.slice b (Seq.length b - len) (Seq.length b) ==
             Seq.slice b' (Seq.length b' - len) (Seq.length b')))
let rec lemma_little_endian_is_injective b b' len =
  if len = 0 then
    Seq.lemma_eq_intro (Seq.slice b (Seq.length b - len) (Seq.length b))
		       (Seq.slice b' (Seq.length b' - len) (Seq.length b'))
  else
    begin
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
    end

val lemma_pad_0_injective: b0:Seq.seq UInt8.t -> b1:Seq.seq UInt8.t -> l:nat -> Lemma
  (requires (pad_0 b0 l == pad_0 b1 l))
  (ensures  (b0 == b1))
let lemma_pad_0_injective b0 b1 l =
  SeqProperties.lemma_append_inj b0 (Seq.create l 0uy) b1 (Seq.create l 0uy);
  Seq.lemma_eq_intro b0 b1

val lemma_encode_injective: w0:word -> w1:word -> Lemma
  (requires (length w0 == length w1 /\ encode w0 == encode w1))
  (ensures  (w0 == w1))
let lemma_encode_injective w0 w1 =
  let l = length w0 in
  lemma_little_endian_is_bounded w0;
  lemma_little_endian_is_bounded w1;
  pow2_le_compat 128 (8 * l);
  lemma_mod_plus_injective p_1305 (pow2 (8 * l))
    (little_endian w0) (little_endian w1);
  assert (little_endian w0 == little_endian w1);
  Seq.lemma_eq_intro (Seq.slice w0 0 l) w0;
  Seq.lemma_eq_intro (Seq.slice w1 0 l) w1;
  lemma_little_endian_is_injective w0 w1 l

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

assume val lemma_encode_bytes_injective: t0:Seq.seq UInt8.t -> t1:Seq.seq UInt8.t -> Lemma
  (requires length t0 == length t1 /\ encode_bytes t0 == encode_bytes t1)
  (ensures t0 == t1)
  (decreases (Seq.length t0))
(*
let rec lemma_encode_bytes_injective t0 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else if l < 16 then
    begin
    lemma_index_create 1 (encode t0) 0;
    lemma_index_create 1 (encode t1) 0;
    lemma_encode_injective t0 t1
    end
  else
    begin
    let w0, t0' = SeqProperties.split_eq t0 16 in
    let w1, t1' = SeqProperties.split_eq t1 16 in
    let p0' = Seq.create 1 (encode w0) in
    let p1' = Seq.create 1 (encode w1) in
    assert (encode_pad p0' t0' == encode_pad p1' t1');
    lemma_encode_bytes_injective t0' t1';
    lemma_index_create 1 (encode w0) 0;
    lemma_index_create 1 (encode w1) 0;
    lemma_encode_injective w0 w1
    end
*)

val lemma_encode_pad_injective: p0:Seq.seq elem -> t0:Seq.seq UInt8.t -> p1:Seq.seq elem -> t1:Seq.seq UInt8.t -> Lemma
  (requires length t0 == length t1 /\ encode_pad p0 t0 == encode_pad p1 t1)
  (ensures  p0 == p1 /\ t0 == t1)
  (decreases (Seq.length t0))
let rec lemma_encode_pad_injective p0 t0 p1 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else if l < 16 then
    begin
    SeqProperties.lemma_append_inj
      p0 (Seq.create 1 (encode t0))
      p1 (Seq.create 1 (encode t1));
    lemma_index_create 1 (encode t0) 0;
    lemma_index_create 1 (encode t1) 0;
    lemma_encode_injective t0 t1
    end
  else
    begin
    let w0, t0' = SeqProperties.split_eq t0 16 in
    let w1, t1' = SeqProperties.split_eq t1 16 in
    let p0' = SeqProperties.snoc p0 (encode w0) in
    let p1' = SeqProperties.snoc p1 (encode w1) in
    assert (encode_pad p0' t0' == encode_pad p1' t1');
    lemma_encode_pad_injective p0' t0' p1' t1';
    SeqProperties.lemma_append_inj
      p0 (Seq.create 1 (encode w0))
      p1 (Seq.create 1 (encode w1));
    lemma_index_create 1 (encode w0) 0;
    lemma_index_create 1 (encode w1) 0;
    lemma_encode_injective w0 w1
    end

val encode_pad_empty: prefix:Seq.seq elem -> txt:Seq.seq UInt8.t -> Lemma
  (requires Seq.length txt == 0)
  (ensures  encode_pad prefix txt == prefix)
let encode_pad_empty prefix txt = ()

val encode_pad_snoc: prefix:Seq.seq elem -> txt:Seq.seq UInt8.t -> w:word_16 -> Lemma
  (encode_pad (SeqProperties.snoc prefix (encode w)) txt ==
   encode_pad prefix (append w txt))
let encode_pad_snoc prefix txt w =
  Seq.lemma_len_append w txt;
  assert (16 <= Seq.length (append w txt));
  let w', txt' = SeqProperties.split (append w txt) 16 in
  let prefix' = SeqProperties.snoc prefix (encode w') in
  Seq.lemma_eq_intro w w';
  Seq.lemma_eq_intro txt txt'

(* * *********************************************)
(* *        Poly1305 functional invariant        *)
(* * *********************************************)

let seq_head (vs:seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

val poly: vs:seq elem -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else (poly (seq_head vs) r +@ Seq.index vs (length vs - 1)) *@ r

(* the definition above captures what POLY1305 does, 
   not the usual polynomial computation; 
   it may be more natural to flip the sequence, 
   so that the coefficients are aligned. 
   (i.e. a_0::a_1::a_2 stands for a_0 + a_1 X + a_2 X^2 , is implicitly extended with 0s.) *)

val poly': vs:seq elem -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly' vs r =
  if Seq.length vs = 0 then 0
  else (SeqProperties.head vs +@ poly' (SeqProperties.tail vs) r ) *@ r

val eq_poly0: p:seq elem -> Tot bool (decreases (length p)) 
let rec eq_poly0 p = 
  Seq.length p = 0 || 
  (SeqProperties.head p = 0 && eq_poly0 (SeqProperties.tail p))
  
val eq_poly: p0:seq elem -> p1:seq elem -> Tot bool (decreases (length p0))
let rec eq_poly p0 p1 = 
  if Seq.length p0 = 0 then eq_poly0 p1 
  else if Seq.length p1 = 0 then eq_poly0 p0
  else SeqProperties.head p0 = SeqProperties.head p1 && eq_poly (SeqProperties.tail p0) (SeqProperties.tail p1)

private let rec lemma_sane_eq_poly0 (p:seq elem) (r:elem) : Lemma
  (requires eq_poly0 p)
  (ensures (poly' p r = 0)) (decreases (Seq.length p)) = 
  if Seq.length p = 0 then () 
  else if SeqProperties.head p = 0 then lemma_sane_eq_poly0 (SeqProperties.tail p) r
private let rec lemma_sane_eq_poly (p0:seq elem) (p1:seq elem) (r:elem) : Lemma
  (requires eq_poly p0 p1)
  (ensures (poly' p0 r = poly' p1 r)) (decreases (Seq.length p0)) = 
  if Seq.length p0 = 0 then lemma_sane_eq_poly0 p1 r 
  else if Seq.length p1 = 0 then lemma_sane_eq_poly0 p0 r
  else lemma_sane_eq_poly (SeqProperties.tail p0) (SeqProperties.tail p1) r

//16-10-15 to stay close to the paper, we may apply "encode" in the poly specification.





private let fix (r:word_16) (i:nat {i < 16}) m : Tot word_16 =
  Seq.upd r i (U8 (Seq.index r i &^ m))

// an abstract spec of clamping for our state invariant
// for our polynomial-sampling assumption,
// we rely solely on the number of fixed bits (22, right?)
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

let mac_1305 (vs:seq elem) r s = (trunc_1305 (poly vs r) + little_endian s) % pow2 128
