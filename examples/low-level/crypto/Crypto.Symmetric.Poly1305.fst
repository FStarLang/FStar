(* Implementation of Poly1305 based on the rfc7539 *)
module Crypto.Symmetric.Poly1305

open FStar.Mul
open FStar.Ghost
open FStar.Seq
(** Machine integers *)
open FStar.UInt8
open FStar.UInt64
open FStar.Int.Cast
(** Effects and memory layout *)
open FStar.HyperStack
open FStar.HyperStack.ST
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open FStar.Math.Lemmas
(** Helper functions for buffers *)
open Buffer.Utils
open Crypto.Symmetric.Bytes 

open FStar.Buffer.Quantifiers

open Crypto.Symmetric.Poly1305.Spec
open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint
open Crypto.Symmetric.Poly1305.Bignum
open Flag

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST

(* 2016-11-22: we now forbid opening the current module name as a
namespace, so we need to make the following abbrevs explicit *)
module Spec = Crypto.Symmetric.Poly1305.Spec
module Parameters = Crypto.Symmetric.Poly1305.Parameters

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"

// we may separate field operations, so that we don't
// need to open the bignum modules elsewhere

(* * *********************************************)
(* *            Representation type              *)
(* * *********************************************)

(** Mutable big integer representation (5 64-bit limbs) *)
type elemB = b:Buffer.buffer u64{length b == norm_length}

(** Concrete (mutable) representation of words *)
type wordB = b:bytes{length b <= 16}
type wordB_16 = b:bytes{length b == 16}

(* * *********************************************)
(* *  Mappings from stateful types to pure types *)
(* * *********************************************)

(** From the current memory state, returns the word corresponding to a wordB *)
val sel_word: h:mem -> b:wordB{live h b} -> GTot word
let sel_word h b = as_seq h b

(** Only used when mac_log is true *)
private val _read_word: len:u32 -> b:wordB{length b == w len} 
  -> s:seq byte -> i:u32{w i <= w len} -> ST word
  (requires (fun h -> live h b /\ Seq.slice (sel_word h b) 0 (w i) == s))
  (ensures  (fun h0 s h1 -> h0 == h1 /\ live h1 b /\ s == sel_word h1 b))
let rec _read_word len b s i =
  let h = ST.get () in
  if w i = w len then
    begin
    Seq.lemma_eq_intro s (sel_word h b);
    s
    end
  else
    begin
    let x = b.(i) in
    let s' = FStar.Seq.(s @| Seq.create 1 x) in
    Seq.lemma_eq_intro s' (Seq.slice (sel_word h b) 0 (w i + 1));
    _read_word len b s' (U32.(i +^ 1ul))
    end

val read_word: len:u32 -> b:wordB{length b == w len} -> ST word
  (requires (fun h0 -> live h0 b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 b /\ r == (sel_word h1 b)))
let read_word len b =
  let h = ST.get() in
  let s0 = Seq.empty #byte in
  Seq.lemma_eq_intro s0 (Seq.slice (sel_word h b) 0 0);
  _read_word len b s0 0ul

(** Retrieves the field element corresponding to an elemB *)
val sel_elem: h:mem -> b:elemB{live h b} -> GTot elem
let sel_elem h b = eval h b norm_length % p_1305

(** Retrieves the integer corresponding to an elemB, (before computing the modulo) *)
val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
let sel_int h b = eval h b norm_length


(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

#set-options "--initial_fuel 1 --max_fuel 1"

(* TODO: Move to Crypto.Symmetric.Poly1305.Bignum *)
val lemma_bitweight_templ_values: n:nat -> Lemma (bitweight templ n == 26 * n)
let rec lemma_bitweight_templ_values n =
  if n = 0 then ()
  else lemma_bitweight_templ_values (n-1)

val lemma_eval_norm_is_bounded: ha:mem -> a:elemB -> len:nat{len <= norm_length} -> Lemma
  (requires (norm ha a))
  (ensures  (norm ha a /\ eval ha a len < pow2 (26 * len)))
let rec lemma_eval_norm_is_bounded ha a len =
  if len = 0 then
    eval_def ha a len
  else
    begin
    cut (len >= 1);
    eval_def ha a len;
    lemma_bitweight_templ_values (len-1);
    lemma_eval_norm_is_bounded ha a (len-1);
    assert(eval ha a (len-1) < pow2 (26 * (len-1)));
    assert(pow2 (bitweight templ (len-1)) = pow2 (26 * (len-1)));
    lemma_eucl_div_bound (eval ha a (len-1)) (v (get ha a (len-1))) 
      (pow2 (bitweight templ (len-1)));
    assert(eval ha a len < pow2 (26 * (len-1)) * (v (get ha a (len-1)) + 1));
    lemma_mult_le_left (pow2 (26 * (len-1))) (v (get ha a (len-1))+1) (pow2 26);
    assert(eval ha a len < pow2 (26 * (len-1)) * pow2 26);
    Math.Lemmas.pow2_plus (26 * (len-1)) 26
    end

#set-options "--initial_fuel 0 --max_fuel 0"

val lemma_elemB_equality: ha:mem -> hb:mem -> a:elemB -> b:elemB 
  -> len:pos{len <= norm_length} -> Lemma
  (requires (live ha a /\ live hb b
    /\ Seq.slice (as_seq ha a) 0 (len-1) == Seq.slice (as_seq hb b) 0 (len-1)
    /\ get ha a (len-1) == get hb b (len-1)))
  (ensures  (live ha a /\ live hb b 
    /\ Seq.slice (as_seq ha a) 0 len == Seq.slice (as_seq hb b) 0 len))
let lemma_elemB_equality ha hb a b len =
  Seq.lemma_eq_intro (Seq.slice (as_seq ha a) 0 len)
                     ((Seq.slice (as_seq ha a) 0 (len-1)) @| 
                       Seq.create 1 (get ha a (len-1)));
  Seq.lemma_eq_intro (Seq.slice (as_seq hb b) 0 len)
                     ((Seq.slice (as_seq hb b) 0 (len-1)) @| 
                       Seq.create 1 (get hb b (len-1)))

val lemma_toField_is_injective_0: ha:mem -> hb:mem -> a:elemB -> b:elemB 
  -> len:nat{len <= norm_length} -> Lemma
  (requires (norm ha a /\ norm hb b /\ eval ha a len == eval hb b len))
  (ensures  (norm ha a /\ norm hb b
    /\ Seq.length (as_seq ha a) >= len /\ Seq.length (as_seq hb b) >= len
    /\ Seq.slice (as_seq ha a) 0 len == Seq.slice (as_seq hb b) 0 len))
let rec lemma_toField_is_injective_0 ha hb a b len =
  if len = 0 then
    Seq.lemma_eq_intro 
      (Seq.slice (as_seq ha a) 0 len) (Seq.slice (as_seq hb b) 0 len)
  else
    begin
    eval_def ha a len; eval_def hb b len;
    lemma_eval_norm_is_bounded ha a (len-1);
    lemma_eval_norm_is_bounded hb b (len-1);
    let z = pow2 (26 * (len-1)) in
    let r = eval ha a (len-1) in
    let r' = eval hb b (len-1) in
    let q = v (get ha a (len-1)) in
    let q' = v (get hb b (len-1)) in
    lemma_bitweight_templ_values (len-1);
    lemma_little_endian_is_injective_1 z q r q' r';
    assert(r = r' /\ q = q');
    assert(get ha a (len-1) = get hb b (len-1));
    lemma_toField_is_injective_0 ha hb a b (len-1);
    lemma_elemB_equality ha hb a b len
    end

val lemma_toField_is_injective: ha:mem -> hb:mem -> a:elemB -> b:elemB ->
  Lemma (requires (norm ha a /\ norm hb b /\ sel_int ha a == sel_int hb b))
        (ensures  (norm ha a /\ norm hb b /\ as_seq ha a == as_seq hb b))
let lemma_toField_is_injective ha hb a b =
  lemma_toField_is_injective_0 ha hb a b norm_length;
  assert(Seq.length (as_seq ha a) == norm_length);
  assert(Seq.length (as_seq hb b) == norm_length);
  Seq.lemma_eq_intro (Seq.slice (as_seq ha a) 0 norm_length) (as_seq ha a);
  Seq.lemma_eq_intro (Seq.slice (as_seq hb b) 0 norm_length) (as_seq hb b)


(** Poly1305 Field Operations **)

(* * ******************************************** *)
(* *        Polynomial computation step           *)
(* * ******************************************** *)

val bound27_isSum: h0:mem -> h1:mem -> a:bigint -> b:bigint
  -> Lemma
    (requires (norm h0 a /\ norm h0 b /\ isSum h0 h1 a b))
    (ensures  (bound27 h1 a))
let bound27_isSum h0 h1 a b =
  // The (i+0) is there on purpuose to trigger the pattern in isSum
  cut (forall (i:nat). {:pattern (v (get h1 a i))} i < norm_length ==> v (get h1 a (i+0)) < pow2 26 + pow2 26);
  pow2_double_sum 26

val lemma_sel_elem: h0:mem -> h1:mem -> acc:elemB -> block:elemB -> r:elemB -> Lemma
  (requires (norm h1 acc /\ norm h0 acc /\ norm h0 block /\ norm h0 r
    /\ sel_elem h1 acc == 
      ((eval h0 acc 5 + eval h0 block 5) * eval h0 r 5) % reveal prime))
  (ensures  (norm h1 acc /\ norm h0 acc /\ norm h0 block /\ norm h0 r
    /\ sel_elem h1 acc == 
      (sel_elem h0 acc +@ sel_elem h0 block) *@ sel_elem h0 r))
let lemma_sel_elem h0 h1 acc block r =
  let a = eval h0 acc 5 in
  let b = eval h0 block 5 in
  let c = eval h0 r 5 in
  let d = reveal prime in
  lemma_mod_plus_mul_distr a b c d

(**
    Runs "acc = ((acc + block) * r) % p" 
    on the accumulator, the well formatted block of the message and the 
    clamped part of the key
*)
val add_and_multiply: acc:elemB -> block:elemB{disjoint acc block} 
  -> r:elemB{disjoint acc r /\ disjoint block r} -> Stack unit
  (requires (fun h -> norm h acc /\ norm h block /\ norm h r))
  (ensures (fun h0 _ h1 -> norm h0 acc /\ norm h0 block /\ norm h0 r
    /\ norm h1 acc // the accumulation is back in a workable state
    /\ modifies_1 acc h0 h1 // It was the only thing modified
    /\ sel_elem h1 acc == (sel_elem h0 acc +@ sel_elem h0 block) *@ sel_elem h0 r))

#set-options "--z3rlimit 60"
//NS: hint fails to replay
let add_and_multiply acc block r =
  let h0 = ST.get () in
  fsum' acc block; // acc1 = acc0 + block
  let h1 = ST.get () in
  cut (eval h1 acc 5 == eval h0 acc 5 + eval h0 block 5);
  bound27_isSum h0 h1 acc block;
  push_frame();
  let tmp = create 0UL (U32.(2ul *^ nlength -^ 1ul)) in
  let h2 = ST.get () in
  eval_eq_lemma h1 h2 acc acc norm_length;
  eval_eq_lemma h0 h2 r r norm_length;
  multiplication tmp acc r; // tmp = acc1 * r = (acc0 + block) * r
  let h3 = ST.get () in
  assert (maxValue h3 tmp (2*norm_length-1) <= norm_length * pow2 53);
  lemma_mult_le_right 6 (maxValue h3 tmp (2*norm_length-1)) (norm_length * pow2 53);
  assert_norm ((norm_length * pow2 53) * 6 < pow2 63);
  cut (satisfiesModuloConstraints h3 tmp);
  modulo tmp; // tmp = tmp % p
  let h4 = ST.get() in
  //cut (sel_elem h4 tmp == ((eval h0 acc 5 + eval h0 block 5) * eval h0 r 5) % reveal prime);
  blit tmp 0ul acc 0ul nlength; // acc2 = tmp = (acc0 + block) * r % p
  let h5 = ST.get() in
  //assert(modifies_2 acc tmp h0 h4);
  lemma_blit_quantifiers h4 h5 tmp 0ul acc 0ul nlength;
  assert(forall (i:nat). {:pattern (v (get h5 acc i))} i < 5 ==> v (get h5 acc (0+i)) == v (get h4 tmp (0+i)));
  eval_eq_lemma h4 h5 tmp acc 5;
  lemma_sel_elem h0 h5 acc block r;
  pop_frame ();
  let h6 = ST.get () in
  eval_eq_lemma h5 h6 acc acc norm_length

(** Sets an element buffer to the value '0' *)
val zeroB: a:elemB -> Stack unit
  (requires (fun h -> live h a))
  (ensures  (fun h0 _ h1 -> norm h1 a /\ modifies_1 a h0 h1 /\ sel_elem h1 a == 0))
let zeroB a =
  a.(0ul) <- 0UL;
  a.(1ul) <- 0UL;
  a.(2ul) <- 0UL;
  a.(3ul) <- 0UL;
  a.(4ul) <- 0UL;
  let h = ST.get() in
  Crypto.Symmetric.Poly1305.Bigint.eval_null h a norm_length


(* * *********************************************)
(* *            Encoding functions               *)
(* * *********************************************)

private val mk_mask: nbits:FStar.UInt32.t{FStar.UInt32.v nbits < 64} ->
  Tot (z:U64.t{v z == pow2 (FStar.UInt32.v nbits) - 1})
let mk_mask nbits =
  Math.Lemmas.pow2_lt_compat 64 (FStar.UInt32.v nbits);
  U64.((1uL <<^ nbits) -^ 1uL)

#set-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let lemma_toField_1 (b:elemB) (s:wordB_16{disjoint b s}) h n0 n1 n2 n3 : Lemma
  (requires (let open FStar.UInt8 in
    live h b /\ live h s
    /\ U64.v n0 == v (get h s 0) + pow2 8 * v (get h s 1) + pow2 16 * v (get h s 2) + pow2 24 * v (get h s 3)
    /\ U64.v n1 == v (get h s 4) + pow2 8 * v (get h s 5) + pow2 16 * v (get h s 6) + pow2 24 * v (get h s 7)
    /\ U64.v n2 == v (get h s 8) + pow2 8 * v (get h s 9) + pow2 16 * v (get h s 10) + pow2 24 * v (get h s 11)
    /\ U64.v n3 == v (get h s 12) + pow2 8 * v (get h s 13) + pow2 16 * v (get h s 14) + pow2 24 * v (get h s 15)))
  (ensures  (live h b /\ live h s /\ v n0 + pow2 32 * v n1 + pow2 64 * v n2 + pow2 96 * v n3 == little_endian (sel_word h s)))
  = Crypto.Symmetric.Poly1305.Lemmas.lemma_toField_1 s h n0 n1 n2 n3

#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val upd_elemB: b:elemB{length b == norm_length} -> n0:U64.t -> n1:U64.t -> n2:U64.t -> n3:U64.t -> n4:U64.t -> Stack unit
  (requires (fun h -> live h b
    /\ U64.v n0 < pow2 26 /\ U64.v n1 < pow2 26 /\ U64.v n2 < pow2 26 /\ U64.v n3 < pow2 26
    /\ U64.v n4 < pow2 24))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
    /\ get h1 b 0 == n0 /\ get h1 b 1 == n1 /\ get h1 b 2 == n2 /\ get h1 b 3 == n3 /\  get h1 b 4 == n4
    /\ sel_int h1 b == v n0 + pow2 26 * v n1 + pow2 52 * v n2 + pow2 78 * v n3 + pow2 104 * v n4
    /\ norm h1 b))
let upd_elemB b n0 n1 n2 n3 n4 =
  b.(0ul) <- n0;
  b.(1ul) <- n1;
  b.(2ul) <- n2;
  b.(3ul) <- n3;
  b.(4ul) <- n4;
  let h1 = ST.get() in
  lemma_bitweight_templ_values 4;
  lemma_bitweight_templ_values 3;
  lemma_bitweight_templ_values 2;
  lemma_bitweight_templ_values 1;
  lemma_bitweight_templ_values 0;
  eval_def h1 b 5;
  eval_def h1 b 4;
  eval_def h1 b 3;
  eval_def h1 b 2;
  eval_def h1 b 1;
  eval_def h1 b 0;
  pow2_lt_compat 26 24


#set-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let lemma_toField_2 n0 n1 n2 n3 n0' n1' n2' n3' n4': Lemma
  (requires (let mask_26 = mk_mask 26ul in
    v n0 < pow2 32 /\ v n1 < pow2 32 /\ v n2 < pow2 32 /\ v n3 < pow2 32
    /\ n0' == (n0 &^ mask_26) 
    /\ n1' == ((n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26))
    /\ n2' == ((n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26))
    /\ n3' == ((n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26)) 
    /\ n4' == (n3 >>^ 8ul) ))
  (ensures  (v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4'
    == v n0 + pow2 32 * v n1 + pow2 64 * v n2 + pow2 96 * v n3 ))
  = Crypto.Symmetric.Poly1305.Lemmas.lemma_toField_2 n0 n1 n2 n3 n0' n1' n2' n3' n4'


let lemma_toField_3 n0 n1 n2 n3 n0' n1' n2' n3' n4' : Lemma
  (requires (let mask_26 = mk_mask 26ul in
    v n0 < pow2 32 /\ v n1 < pow2 32 /\ v n2 < pow2 32 /\ v n3 < pow2 32
    /\ n0' == (n0 &^ mask_26)
    /\ n1' == ((n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26))
    /\ n2' == ((n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26))
    /\ n3' == ((n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26))
    /\ n4' == ((n3 >>^ 8ul)) ))
  (ensures  (U64.v n4' < pow2 24
    /\ U64.v n3' < pow2 26 /\ U64.v n2' < pow2 26 /\ U64.v n1' < pow2 26 /\ U64.v n0' < pow2 26))
  = Crypto.Symmetric.Poly1305.Lemmas.lemma_toField_3 n0 n1 n2 n3 n0' n1' n2' n3' n4'

val sel_int_sel_elem: h:mem -> a:elemB{live h a} -> w:word -> Lemma
  (requires (sel_int h a == little_endian w))
  (ensures  (sel_elem h a == little_endian w))
let sel_int_sel_elem h a w =  
  lemma_little_endian_is_bounded w;
  modulo_lemma (little_endian w) p_1305

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

(* Formats a wordB into an elemB *)
val toField: a:elemB{length a == norm_length} -> b:wordB_16{disjoint a b} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures  (fun h0 _ h1 ->
    live h0 b /\         // initial post condition
    modifies_1 a h0 h1 /\ // only a was modified
    norm h1 a /\         // a is in a 'workable' state
    sel_int h1 a == little_endian (sel_word h0 b) /\ // functional correctnes
    //sel_int h1 a == sel_elem h1 a /\
    v (get h1 a 4) < pow2 24 // necessary for adding 2^128 with no overflow
  ))

let toField b s =
  //DEBUG: let _ = print_bytes s 0ul 16ul in
  let h0 = ST.get() in
  let mask_26 = mk_mask 26ul in
  let s0 = sub s 0ul  4ul in
  let s1 = sub s 4ul  4ul in
  let s2 = sub s 8ul  4ul in
  let s3 = sub s 12ul 4ul in
  let n0 = (uint32_of_bytes s0) in
  let n1 = (uint32_of_bytes s1) in
  let n2 = (uint32_of_bytes s2) in
  let n3 = (uint32_of_bytes s3) in
  let n0 = Int.Cast.uint32_to_uint64 n0 in
  let n1 = Int.Cast.uint32_to_uint64 n1 in
  let n2 = Int.Cast.uint32_to_uint64 n2 in
  let n3 = Int.Cast.uint32_to_uint64 n3 in
  lemma_toField_1 b s h0 n0 n1 n2 n3;
  cut (v n0 + pow2 32 * v n1 + pow2 64 * v n2 + pow2 96 * v n3 == little_endian (sel_word h0 s));
  let n0' = n0 &^ mask_26 in
  let n1' = (n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26) in
  let n2' = (n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26) in
  let n3' = (n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26) in
  let n4' = (n3 >>^ 8ul) in
  lemma_toField_2 n0 n1 n2 n3 n0' n1' n2' n3' n4';
  lemma_toField_3 n0 n1 n2 n3 n0' n1' n2' n3' n4';
  cut (v n0' + pow2 26 * v n1' + pow2 52 * v n2' + pow2 78 * v n3' + pow2 104 * v n4'
    == little_endian (sel_word h0 s));
  upd_elemB b n0' n1' n2' n3' n4'


#set-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

val lemma_toField_plus_2_128_0: ha:mem -> a:elemB{live ha a} -> Lemma
  (requires True)
  (ensures  (sel_int ha a =
    v (get ha a 0) + pow2 26 * v (get ha a 1) + pow2 52 * v (get ha a 2) + pow2 78 * v (get ha a 3)
    + pow2 104 * v (get ha a 4)))
let lemma_toField_plus_2_128_0 ha a =
  lemma_bitweight_templ_values 4;
  lemma_bitweight_templ_values 3;
  lemma_bitweight_templ_values 2;
  lemma_bitweight_templ_values 1;
  lemma_bitweight_templ_values 0;
  eval_def ha a 5;
  eval_def ha a 4;
  eval_def ha a 3;
  eval_def ha a 2;
  eval_def ha a 1;
  eval_def ha a 0;
  assert_norm (pow2 0 = 1)

#set-options "--initial_fuel 0 --max_fuel 0"

val lemma_toField_plus_2_128_1: unit -> Lemma (v (1uL <<^ 24ul) == pow2 24)
let lemma_toField_plus_2_128_1 () =
  Math.Lemmas.pow2_lt_compat 64 24

val lemma_toField_plus_2_128: ha:mem -> a:elemB -> hb:mem -> b:elemB -> Lemma
  (requires (norm ha a /\ norm hb b /\ v (get hb b 4) < pow2 24
    /\ v (get ha a 4) == v (get hb b 4) + pow2 24
    /\ v (get ha a 3) == v (get hb b 3) /\ v (get ha a 2) == v (get hb b 2)
    /\ v (get ha a 1) == v (get hb b 1) /\ v (get ha a 0) == v (get hb b 0) ))
  (ensures  (norm ha a /\ norm hb b /\ sel_int ha a == pow2 128 + sel_int hb b))
let lemma_toField_plus_2_128 ha a hb b =
  lemma_toField_plus_2_128_0 ha a;
  lemma_toField_plus_2_128_0 hb b;
  Math.Lemmas.distributivity_add_right (pow2 104) (v (get hb b 4)) (pow2 24);
  Math.Lemmas.pow2_plus 104 24

let add_2_24 (x:t{v x < pow2 24}) : Tot (z:t{v z == v x + pow2 24 /\ v z < pow2 26})
  = lemma_toField_plus_2_128_1 ();
    Math.Lemmas.pow2_double_sum 24;
    Math.Lemmas.pow2_double_sum 25;
    Math.Lemmas.pow2_lt_compat 64 25;
    x +^ (1uL <<^ 24ul)

(* Formats a wordB_16 into an elemB *)
val toField_plus_2_128: a:elemB{length a == norm_length} -> b:wordB_16 -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 ->
    live h0 b /\ // Initial post condition
    norm h1 a /\ // the elemB 'a' is in a 'workable' state
    modifies_1 a h0 h1 /\ // Only a was modified
    sel_int h1 a == pow2 128 + little_endian (sel_word h0 b) ))
let toField_plus_2_128 b s =
  toField b s;
  let h0 = ST.get() in
  let b4 = b.(4ul) in
  let b4' = add_2_24 b4 in
  b.(4ul) <- b4';
  let h1 = ST.get() in
  lemma_upd_quantifiers h0 h1 b 4ul b4';
  lemma_toField_plus_2_128 h1 b h0 b


(* Formats a wordB into an elemB *)
val toField_plus: 
    len:u32 
  -> a:elemB{length a == norm_length} 
  -> b:wordB{length b == w len /\ w len < 16}
  -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 ->
    live h0 b /\ // Initial post condition
    norm h1 a /\ // the elemB 'a' is in a 'workable' state
    modifies_1 a h0 h1 /\ // Only a was modified
    sel_int h1 a == pow2 (8 * w len) + little_endian (sel_word h0 b) ))

#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

let toField_plus len a b =
  let h0 = ST.get() in
  push_frame();
  let n = create 0uy 16ul in
  blit b 0ul n 0ul len;
  let h1 = ST.get() in
  n.(len) <- 1uy;
  let h2 = ST.get() in
  toField a n;
  let h3 = ST.get() in
  pop_frame ();
  let h4 = ST.get() in
  eval_eq_lemma h3 h4 a a norm_length;
  let n1, n2 = Seq.split_eq (sel_word h2 n) (w len) in
  let n3, n4 = Seq.split_eq n2 1 in
  Seq.lemma_eq_intro (sel_word h2 n) (Seq.append n1 (Seq.append n3 n4));
  little_endian_append n1 (Seq.append n3 n4);
  little_endian_append n3 n4;
  cut (little_endian (sel_word h2 n) ==
    little_endian n1 + 
    pow2 (8 * w len) * (little_endian n3 + pow2 (8 * 1) * little_endian n4));
  //assert (sel_int h4 a == little_endian (sel_word h2 n));
  assert (n1 == Seq.slice (sel_word h0 b) 0 (w len));
  Seq.lemma_eq_intro (sel_word h0 b) (Seq.slice (sel_word h0 b) 0 (w len));
  //assert (little_endian n1 == little_endian (sel_word h0 b));
  let _, n2' = Seq.split_eq (sel_word h1 n) (w len) in
  let _, n4' = Seq.split_eq n2' 1 in
  Seq.lemma_eq_intro n4 (Seq.create (Seq.length n4) 0uy);
  little_endian_null (Seq.length n4);
  //assert (little_endian n4 == 0);
  Seq.lemma_eq_intro n3 (Seq.create 1 1uy);
  little_endian_singleton 1uy;
  //assert (little_endian n3 == 1);
  assert_norm ((1 + pow2 (8 * 1) * 0) == 1);
  assert (pow2 (8 * w len) * (1 + pow2 (8 * 1) * 0) == pow2 (8 * w len))


val upd_wordB_16: b:wordB_16 -> 
  s0:U8.t -> s1:U8.t -> s2:U8.t -> s3:U8.t -> s4:U8.t -> 
  s5:U8.t -> s6:U8.t -> s7:U8.t -> s8:U8.t -> s9:U8.t -> 
  s10:U8.t -> s11:U8.t -> s12:U8.t -> s13:U8.t -> s14:U8.t -> s15:U8.t -> Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ get h1 b 0 == s0  /\ get h1 b 1 == s1  /\ get h1 b 2 == s2  /\ get h1 b 3 == s3
      /\ get h1 b 4 == s4  /\ get h1 b 5 == s5  /\ get h1 b 6 == s6  /\ get h1 b 7 == s7
      /\ get h1 b 8 == s8  /\ get h1 b 9 == s9  /\ get h1 b 10 == s10 /\ get h1 b 11 == s11
      /\ get h1 b 12 == s12 /\ get h1 b 13 == s13  /\ get h1 b 14 == s14 /\ get h1 b 15 == s15 ))
let upd_wordB_16 s s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =
  s.(0ul) <- s0;
  s.(1ul) <- s1;
  s.(2ul) <- s2;
  s.(3ul) <- s3;
  s.(4ul) <- s4;
  s.(5ul) <- s5;
  s.(6ul) <- s6;
  s.(7ul) <- s7;
  s.(8ul) <- s8;
  s.(9ul) <- s9;
  s.(10ul) <- s10;
  s.(11ul) <- s11;
  s.(12ul) <- s12;
  s.(13ul) <- s13;
  s.(14ul) <- s14;
  s.(15ul) <- s15


#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val trunc1305: a:elemB -> b:wordB_16{disjoint a b} -> Stack unit
  (requires (fun h -> norm h a /\ live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 -> norm h0 a /\ live h1 a /\ live h1 b
    /\ modifies_2 a b h0 h1
    /\ little_endian (sel_word h1 b) == trunc_1305 (sel_elem h0 a)))
let trunc1305 a b =
  let h0 = ST.get() in
  (* Full reduction of a:
     - before finalization sel_int h a < pow2 130
     - after finalization sel_int h a = sel_elem h a *)
  finalize a;
  let h1 = ST.get() in
  assert (modifies_1 a h0 h1);
  lemma_mod_mod (eval h1 a norm_length) (eval h0 a norm_length) (reveal prime);
  cut (sel_elem h1 a == sel_elem h0 a /\ sel_elem h1 a == sel_int h1 a);
  (* Copy of the 128 first bits of a into b *)
  let a0 = index a 0ul in
  let a1 = index a 1ul in
  let a2 = index a 2ul in
  let a3 = index a 3ul in
  let a4 = index a 4ul in
  (* JK: some bitvector theory would simplify a lot the rest of the proof *)
  let b0 = uint64_to_uint8 a0 in
  let b1 = uint64_to_uint8 (a0 >>^ 8ul) in
  let b2 = uint64_to_uint8 (a0 >>^ 16ul) in
  let b3 = uint64_to_uint8 ((a0 >>^ 24ul) |^ (a1 <<^ 2ul)) in
  let b4 = uint64_to_uint8 (a1 >>^ 6ul) in
  let b5 = uint64_to_uint8 (a1 >>^ 14ul) in
  let b6 = uint64_to_uint8 ((a1 >>^ 22ul) |^ (a2 <<^ 4ul)) in
  let b7 = uint64_to_uint8 (a2 >>^ 4ul) in
  let b8 = uint64_to_uint8 (a2 >>^ 12ul) in
  let b9 = uint64_to_uint8 ((a2 >>^ 20ul) |^ (a3 <<^ 6ul)) in
  let b10 = uint64_to_uint8 (a3 >>^ 2ul) in
  let b11 = uint64_to_uint8 (a3 >>^ 10ul) in
  let b12 = uint64_to_uint8 (a3 >>^ 18ul) in
  let b13 = uint64_to_uint8 a4 in
  let b14 = uint64_to_uint8 (a4 >>^ 8ul) in
  let b15 = uint64_to_uint8 (a4 >>^ 16ul) in
  upd_wordB_16 b b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15;
  let h2 = ST.get() in
  assert (modifies_1 b h1 h2);
  Crypto.Symmetric.Poly1305.Lemmas.lemma_trunc1305 h2 b h1 a;
  cut ((sel_elem h0 a) % pow2 128 = (eval h1 a 5) % pow2 128);
  cut (sel_elem h0 a % pow2 128 == little_endian (sel_word h2 b))


(* Clamps the key, see RFC. Clears 22 bits out of 128
*)
private let fix r i mask = r.(i) <- U8.(r.(i) &^ mask)

val clamp: r:wordB{length r == 16} -> Stack unit
  (requires (fun h -> live h r))
  (ensures  (fun h0 _ h1 -> live h0 r /\ live h1 r 
    /\ modifies_1 r h0 h1
    /\ little_endian (sel_word h1 r) == Spec.clamp (sel_word h0 r)))
let clamp r =
  fix r  3ul  15uy; // 0000****
  fix r  7ul  15uy;
  fix r 11ul  15uy;
  fix r 15ul  15uy;
  fix r  4ul 252uy; // ******00
  fix r  8ul 252uy;
  fix r 12ul 252uy

  
(** Initialization function:
   - clamps the first half of the key
   - stores the well-formatted first half of the key in 'r' 
*)
val poly1305_init:
    r:elemB //out: first half of the key, ready for polynomial evaluation
  -> s:wordB_16{disjoint r s} //out: second half of the key, ready for masking
  -> key:bytes{length key >= 32 /\ disjoint r key /\ disjoint s key} //in: raw key
  -> Stack unit
  (requires (fun h -> live h r /\ live h s /\ live h key /\ length r == norm_length))
  (ensures  (fun h0 log h1 -> live h0 r /\ live h0 s /\ live h0 key 
    /\ norm h1 r /\ live h1 s
    /\ modifies_2 r s h0 h1 
    /\ sel_elem h1 r == Spec.clamp (sel_word h0 (sub key 0ul 16ul))
    /\ sel_word h1 s == sel_word h0 (sub key 16ul 16ul)))
let poly1305_init r s key =
  let h0 = ST.get() in
  push_frame();
  (* Format the keys *)
  (* Make a copy of the first half of the key to clamp it *)
  let r_16 = create 0uy 16ul in
  blit key 0ul r_16 0ul 16ul;
  blit key 16ul s 0ul 16ul;  
  let h1 = ST.get() in
  assert (Seq.equal (sel_word h1 r_16) (sel_word h0 (sub key 0ul 16ul)));
  assert (Seq.equal (sel_word h1 s) (sel_word h0 (sub key 16ul 16ul)));
  (* Clamp r *)
  clamp r_16;
  let h2 = ST.get() in
  assert (little_endian (sel_word h2 r_16) == Spec.clamp (sel_word h1 r_16));
  (* Format r to elemB *)
  toField r r_16;
  let h3 = ST.get() in
  assert (sel_int h3 r == little_endian (sel_word h2 r_16));
  sel_int_sel_elem h3 r (sel_word h2 r_16);
  pop_frame();
  let h4 = ST.get() in
  norm_eq_lemma h3 h4 r r;
  eval_eq_lemma h3 h4 r r norm_length


val poly1305_start: acc:elemB -> Stack unit
  (requires (fun h -> live h acc))
  (ensures  (fun h0 _ h1 -> modifies_1 acc h0 h1 /\ norm h1 acc /\ sel_elem h1 acc == 0))
let poly1305_start a = zeroB a


(* TODO: certainly a more efficient, better implementation of that *)
private val add_word: a:wordB_16 -> b:wordB_16 -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a /\ modifies_1 a h0 h1 /\
     little_endian (sel_word h1 a) ==
     (little_endian (sel_word h0 a) + little_endian (sel_word h0 b)) % pow2 128 ))
let add_word a b =
  let hinit = ST.get() in
  let a04:u64 = let (x:u32) = uint32_of_bytes (sub a 0ul 4ul) in uint32_to_uint64 x  in
  let a48:u64 = let (x:u32) = uint32_of_bytes (sub a 4ul 4ul) in uint32_to_uint64 x in
  let a812:u64 = let (x:u32) = uint32_of_bytes (sub a 8ul 4ul) in uint32_to_uint64 x in
  let a1216:u64 = let (x:u32) = uint32_of_bytes (sub a 12ul 4ul) in uint32_to_uint64 x in
  let b04:u64 = let (x:u32) = uint32_of_bytes (sub b 0ul 4ul) in uint32_to_uint64 x  in
  let b48:u64 = let (x:u32) = uint32_of_bytes (sub b 4ul 4ul) in uint32_to_uint64 x in
  let b812:u64 = let (x:u32) = uint32_of_bytes (sub b 8ul 4ul) in uint32_to_uint64 x in
  let b1216:u64 = let (x:u32) = uint32_of_bytes (sub b 12ul 4ul) in uint32_to_uint64 x in
  let open FStar.UInt64 in
  let z0 = a04 +^ b04 in
  let z1 = a48 +^ b48 +^ (z0 >>^ 32ul) in
  let z2 = a812 +^ b812 +^ (z1 >>^ 32ul) in
  let z3 = a1216 +^ b1216 +^ (z2 >>^ 32ul) in
  let z0' = uint64_to_uint32 z0 in
  let z1' = uint64_to_uint32 z1 in
  let z2' = uint64_to_uint32 z2 in
  let z3' = uint64_to_uint32 z3 in
  let h0 = ST.get() in
  bytes_of_uint32 (Buffer.sub a 0ul 4ul) z0';
  let h1 = ST.get() in
  bytes_of_uint32 (Buffer.sub a 4ul 4ul) z1';
  let h2 = ST.get() in
  bytes_of_uint32 (Buffer.sub a 8ul 4ul) z2';
  let h3 = ST.get() in
  bytes_of_uint32 (Buffer.sub a 12ul 4ul) z3';
  let h4 = ST.get() in
  Crypto.Symmetric.Poly1305.Lemmas.lemma_add_word hinit a hinit b a04 a48 a812 a1216 b04 b48 b812 b1216;
  Crypto.Symmetric.Poly1305.Lemmas.lemma_add_word2 h0 h1 h2 h3 h4 a z0' z1' z2' z3'


(* Finish function, with final accumulator value *)
val poly1305_finish:
  tag:wordB_16 -> acc:elemB -> s:wordB_16 -> Stack unit
  (requires (fun h -> live h tag /\ live h acc /\ live h s
    /\ norm h acc
    /\ disjoint tag acc /\ disjoint tag s /\ disjoint acc s))
  (ensures  (fun h0 _ h1 -> live h0 acc /\ live h0 s
    /\ modifies_2 tag acc h0 h1 /\ live h1 acc /\ live h1 tag
    /\ sel_word h1 tag == finish (sel_elem h0 acc) (sel_word h0 s)))
//    /\ little_endian (sel_word h1 tag) ==
//        (trunc_1305 (sel_elem h0 acc) + little_endian (sel_word h0 s)) % pow2 128))
let poly1305_finish tag acc s =
  let h0 = ST.get () in
  trunc1305 acc tag;
  add_word tag s;
  let h1 = ST.get () in
  let t0 = sel_word h1 tag in
  let t1 = finish (sel_elem h0 acc) (sel_word h0 s) in
  Seq.lemma_eq_intro t0 (Seq.slice t0 0 16);
  Seq.lemma_eq_intro t1 (Seq.slice t1 0 16);
  lemma_little_endian_is_injective t0 t1 16


(**
 *  The rest of the file provides a standalone Poly1305 MAC function proven
 *  functionally correct using an ideal log passed explicitly.
 *  It is not used in the Chacha20-Poly1305 AEAD construction.
 *)

let log_t = if mac_log then text else unit

val ilog: l:log_t{mac_log} -> Tot text
let ilog l = l

#set-options "--initial_fuel 1 --max_fuel 1"

val poly_cons: x:word -> xs:text -> r:elem ->
  Lemma (poly (Seq.cons x xs) r == (encode x +@ poly xs r) *@ r)
let poly_cons x xs r =
  let xxs = Seq.cons x xs in
  Seq.lemma_len_append (Seq.create 1 x) xs;
  Seq.lemma_eq_intro (Seq.tail xxs) xs

val poly_empty: t:text{Seq.length t == 0} -> r:elem ->
  Lemma (poly t r == 0)
let poly_empty t r = ()

#reset-options "--z3rlimit 60 --initial_fuel 0"

(**
   Update function:
   - takes a ghost log
   - takes a message block, appends '1' to it and formats it to bigint format
   - Updates acc = ((acc + block) * r) % p
   *)
val poly1305_update:
  current_log:log_t ->
  msg:wordB_16 ->
  acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} ->
  Stack log_t
  (requires (fun h -> live h msg /\ norm h acc /\ norm h r
    /\ (mac_log ==> sel_elem h acc == poly (ilog current_log) (sel_elem h r)) ))
  (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h0 r
    /\ live h1 msg /\ norm h1 acc /\ norm h1 r
    /\ modifies_1 acc h0 h1
    /\ (mac_log ==>
       ilog updated_log == Seq.cons (sel_word h0 msg) (ilog current_log)
       /\ sel_elem h1 acc == poly (ilog updated_log) (sel_elem h0 r)) ))

#reset-options "--z3rlimit 200 --initial_fuel 2"

let poly1305_update log msgB acc r =
  let h0 = ST.get () in
  push_frame();
  let block = create 0UL nlength in //TODO: pass buffer, don't create one
  toField_plus_2_128 block msgB;
  let h1 = ST.get () in
  eval_eq_lemma h0 h1 acc acc Parameters.norm_length;
  eval_eq_lemma h0 h1 r r Parameters.norm_length;
  add_and_multiply acc block r;
  let h2 = ST.get () in
  assert (sel_elem h2 acc ==
    (encode (sel_word h0 msgB) +@ sel_elem h0 acc) *@ sel_elem h0 r);
  let updated_log:log_t =
    if mac_log then
      let msg = read_word 16ul msgB in
      poly_cons (sel_word h0 msgB) (ilog log) (sel_elem h0 r);
      Seq.cons msg (ilog log)
    else ()
  in
  pop_frame();
  let h3 = ST.get () in
  eval_eq_lemma h2 h3 acc acc Parameters.norm_length;
  updated_log


(** Performs the last step if there is an incomplete block *)
val poly1305_last:
  current_log:log_t ->
  msg:wordB ->
  acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} ->
  len:u32{w len == length msg /\ 0 < w len /\ w len < 16} ->
  Stack log_t
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r
      /\ (mac_log ==> sel_elem h acc == poly (ilog current_log) (sel_elem h r)) ))
    (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h0 r
      /\ live h1 msg /\ norm h1 acc /\ norm h1 r
      /\ modifies_1 acc h0 h1
      /\ (mac_log ==>
         ilog updated_log == Seq.cons (sel_word h0 msg) (ilog current_log)
         /\ sel_elem h1 acc == poly (ilog updated_log) (sel_elem h0 r)) ))
let poly1305_last log msgB acc r len =
  let h0 = ST.get () in
  push_frame ();
  let block = create 0UL nlength in
  toField_plus len block msgB;
  let h1 = ST.get () in
  eval_eq_lemma h0 h1 acc acc Parameters.norm_length;
  eval_eq_lemma h0 h1 r r Parameters.norm_length;
  add_and_multiply acc block r;
  let h2 = ST.get () in
  assert (sel_elem h2 acc ==
    (encode (sel_word h0 msgB) +@ sel_elem h0 acc) *@ sel_elem h0 r);
  let updated_log:log_t =
    if mac_log then
      let msg = read_word len msgB in
      poly_cons (sel_word h0 msgB) (ilog log) (sel_elem h0 r);
      Seq.cons msg (ilog log)
    else ()
  in
  pop_frame ();
  let h3 = ST.get() in
  eval_eq_lemma h2 h3 acc acc Parameters.norm_length;
  updated_log


(* In Crypto.AEAD.Encoding *)
private let min (a:nat) (b:nat) : nat = if a <= b then a else b

val encode_bytes: txt:Seq.seq UInt8.t -> GTot text (decreases (Seq.length txt))
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then
    Seq.empty
  else
    let l0 = min l 16 in
    let w, txt = Seq.split txt l0 in
    Seq.snoc (encode_bytes txt) w // snoc, not cons!
(***)

#set-options "--initial_fuel 1 --max_fuel 1"

(** Auxiliary lemmas *)

val append_empty: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma
  (requires (Seq.length s1 == 0))
  (ensures  (Seq.append s1 s2 == s2))
  [SMTPat (Seq.append s1 s2); SMTPat (Seq.length s1 == 0)]
let append_empty #a s1 s2 =
  Seq.lemma_eq_intro (Seq.append s1 s2) s2
  
val append_cons_snoc: #a:Type -> s1:Seq.seq a -> hd:a -> tl:Seq.seq a -> Lemma
  (Seq.append s1 (Seq.cons hd tl) ==
   Seq.append (Seq.snoc s1 hd) tl)
let append_cons_snoc #a s1 hd tl =
  Seq.lemma_eq_intro
    (Seq.append s1 (Seq.cons hd tl))
    (Seq.append (Seq.snoc s1 hd) tl)

val snoc_cons: #a:Type -> s:Seq.seq a -> x:a -> y:a -> Lemma
  (FStar.Seq.(Seq.equal (snoc (cons x s) y) (cons x (snoc s y))))
let snoc_cons #a s x y = ()

val append_assoc: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> s3:Seq.seq a -> Lemma
  (FStar.Seq.(equal (append s1 (append s2 s3)) (append (append s1 s2) s3)))
let append_assoc #a s1 s2 s3 = ()
#set-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* 2016-11-23: n shadowed by U32.n by local open, so rename into n' *)
val append_as_seq_sub: h:mem -> n':UInt32.t -> m:UInt32.t -> msg:bytes{live h msg /\ w m <= w n' /\ w n' <= length msg} -> Lemma
  (append (as_seq h (Buffer.sub msg 0ul m))
          (as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32.(n' -^ m)))) ==
   as_seq h (Buffer.sub msg 0ul n'))
let append_as_seq_sub h n' m msg =
  Seq.lemma_eq_intro
    (append (as_seq h (Buffer.sub msg 0ul m))
            (as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32.(n' -^ m)))))
     (as_seq h (Buffer.sub msg 0ul n'))

val append_as_seq: h:mem -> m:UInt32.t -> n:UInt32.t ->
  msg:bytes{live h msg /\ w m + w n == length msg} -> Lemma
  (Seq.equal
    (append (as_seq h (Buffer.sub msg 0ul m)) (as_seq h (Buffer.sub msg m n)))
    (as_seq h msg))
let append_as_seq h n m msg = ()

#reset-options "--z3rlimit 60"

val encode_bytes_empty: txt:Seq.seq UInt8.t -> Lemma
    (requires Seq.length txt == 0)
    (ensures  encode_bytes txt == Seq.empty)
    [SMTPat (encode_bytes txt); SMTPat (Seq.length txt == 0)]
let encode_bytes_empty txt = ()

val snoc_encode_bytes: s:Seq.seq UInt8.t -> w:word_16 -> Lemma
  (Seq.equal (Seq.snoc (encode_bytes s) w) (encode_bytes (Seq.append w s)))
let snoc_encode_bytes s w =
  let txt0, txt1 = Seq.split (Seq.append w s) 16 in
  assert (Seq.equal w txt0 /\ Seq.equal s txt1)

val encode_bytes_append: len:U32.t -> s:Seq.seq UInt8.t -> w:word -> Lemma
  (requires (0 < Seq.length w /\ Seq.length s == U32.v len /\ U32.rem len 16ul == 0ul))
  (ensures  (Seq.equal (encode_bytes (Seq.append s w))
                      (Seq.cons w (encode_bytes s))))
  (decreases (Seq.length s))
let rec encode_bytes_append len s w =
  let open FStar.Seq in
  let txt = Seq.append s w in
  lemma_len_append s w;
  let l0 = min (length txt) 16 in
  let w', txt = split_eq txt l0 in
  if length s = 0 then
    begin
    assert (equal w w');
    encode_bytes_empty txt
    end
  else
    begin
    assert (l0 == 16);
    let w0, s' = split_eq s 16 in
    snoc_encode_bytes (append s' w) w0;
    append_assoc w0 s' w;
    snoc_cons (encode_bytes s') w w0;
    encode_bytes_append (U32.(len -^ 16ul)) s' w
    end


#set-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0"

(* Loop over Poly1305_update; could go below MAC *)
val poly1305_loop: log:log_t -> msg:bytes -> acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} -> ctr:u32{length msg >= 16 * w ctr} ->
  Stack log_t
  (requires (fun h -> live h msg /\ norm h acc /\ norm h r /\
      (mac_log ==>
        sel_elem h acc == poly (ilog log) (sel_elem h r)) ))
  (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h1 acc /\ norm h0 r /\
      modifies_1 acc h0 h1 /\
      (mac_log ==>
        ilog updated_log ==
        Seq.append (encode_bytes (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr))))
                   (ilog log) 
        /\ sel_elem h1 acc == poly (ilog updated_log) (sel_elem h0 r)) ))
    (decreases (w ctr))

#set-options "--z3rlimit 300 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let rec poly1305_loop log msg acc r ctr =
  let h0 = ST.get () in
  if U32.lte ctr 0ul then
    begin
    assert (Seq.length (as_seq h0 (Buffer.sub msg 0ul 0ul)) == 0);
    encode_bytes_empty (as_seq h0 (Buffer.sub msg 0ul 0ul));
    log
    end
  else
    begin
    let msg0:wordB_16 = sub msg 0ul 16ul in
    let log1 = poly1305_update log msg0 acc r in
    let h1 = ST.get () in
    let msg1 = offset msg 16ul in
    eval_eq_lemma h0 h1 r r norm_length;
    assert (live h1 msg1 /\ norm h1 acc /\ norm h1 r /\ modifies_1 acc h0 h1);
    let log2 = poly1305_loop log1 msg1 acc r (U32.(ctr -^ 1ul)) in
    if mac_log then
      begin
      assert (sel_elem h1 acc == poly (ilog log1) (sel_elem h0 r));
      assert (ilog log1 == Seq.cons (sel_word h0 msg0) (ilog log));
      let s = as_seq h0 (sub msg1 0ul (UInt32.mul 16ul (U32.(ctr -^ 1ul)))) in
      append_cons_snoc (encode_bytes s) (sel_word h0 msg0) (ilog log);
   //   assert (ilog log2 ==
   //     Seq.append (Seq.snoc (encode_bytes s) 
   //                (sel_word h0 msg0)) (ilog log));
      snoc_encode_bytes 
        (as_seq h0 (sub msg1 0ul (U32.mul 16ul (U32.(ctr -^ 1ul)))))
        (sel_word h0 msg0);
      append_as_seq_sub h0 (U32.mul 16ul ctr) 16ul msg
   //   assert (Seq.equal
   //     (Seq.snoc (encode_bytes s) (sel_word h0 msg0))
   //     (encode_bytes (as_seq h0 (Buffer.sub msg 0ul (UInt32.mul 16ul ctr)))))
      end;
    log2
   end


val div_aux: a:UInt32.t -> b:UInt32.t{w b <> 0} -> Lemma
  (requires True)
  (ensures FStar.UInt32.(UInt.size (v a / v b) n))
  [SMTPat (FStar.UInt32.(UInt.size (v a / v b) n))]
let div_aux a b = ()

#reset-options "--z3rlimit 1000 --initial_fuel 1 --max_fuel 10"

val poly1305_process:
    msg:bytes
  -> len:u32{w len == length msg}
  -> acc:elemB{disjoint msg acc}
  -> r:elemB{disjoint msg r /\ disjoint acc r}
  -> Stack unit
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r /\ sel_elem h acc == 0))
    (ensures (fun h0 log h1 -> live h0 msg /\ norm h1 acc /\ norm h0 r /\
      modifies_1 acc h0 h1 /\
      (mac_log ==>
        sel_elem h1 acc == poly (encode_bytes (as_seq h0 msg)) (sel_elem h0 r))))
let poly1305_process msg len acc r =
  let h0 = ST.get () in
  let ctr, rem = U32.div len 16ul, U32.rem len 16ul in
  let log0:log_t = if mac_log then Seq.empty #word in
  if mac_log then poly_empty (ilog log0) (sel_elem h0 r);
  let log1 = poly1305_loop log0 msg acc r ctr in
  let h1 = ST.get () in
  assert (mac_log ==>
    Seq.equal (ilog log1)
      (encode_bytes (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr))))
    /\ sel_elem h1 acc == poly (ilog log1) (sel_elem h0 r));
  let rem' = rem in (* rem shadowed by U32.rem *)
  if U32.(rem' =^ 0ul) then
    Seq.lemma_eq_intro
      (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr)))
      (as_seq h0 msg)
  else
    begin
    eval_eq_lemma h0 h1 r r norm_length;
    let last = sub msg (U32.mul 16ul ctr) rem in
    let log2 = poly1305_last log1 last acc r rem in
    let h2 = ST.get () in
    if mac_log then
      begin
        Seq.lemma_eq_intro
          (sel_word h1 last)
          (as_seq h0 (sub msg (U32.mul 16ul ctr) rem));
        encode_bytes_append (UInt32.mul 16ul ctr)
          (as_seq h0 (sub msg 0ul (UInt32.mul 16ul ctr)))
          (as_seq h0 (sub msg (U32.mul 16ul ctr) rem));
        append_as_seq h0 (UInt32.mul 16ul ctr) rem msg
      end
    end


private let modifies_mac (#a1:Type) (#a2:Type) (#a3:Type) (#a4:Type)
  (b1:Buffer.buffer a1) (b2:Buffer.buffer a2) (b3:Buffer.buffer a3) (b4:Buffer.buffer a4)
  h0 h1 h2 h3 h4 h5 h6: Lemma
  (requires (  ~(contains h0 b1)
             /\ ~(contains h0 b2)
             /\ ~(contains h0 b3)
             /\ live h0 b4
             /\ fresh_frame h0 h1
             /\ modifies_0 h1 h2
             /\ live h2 b1 /\ live h2 b2 /\ live h2 b3
             /\ modifies_2 b1 b2 h2 h3
             /\ modifies_1 b3 h3 h4
             /\ modifies_2 b4 b3 h4 h5
             /\ popped h5 h6))
  (ensures  (modifies_1 b4 h0 h6))
  = lemma_reveal_modifies_0 h1 h2;
    lemma_reveal_modifies_2 b1 b2 h2 h3;
    lemma_reveal_modifies_1 b3 h3 h4;
    lemma_reveal_modifies_2 b4 b3 h4 h5;
    lemma_intro_modifies_1 b4 h0 h6

#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0"
(** Computes the Poly1305 MAC on a buffer *)
val poly1305_mac:
  tag:wordB{length tag == 16} ->
  msg:bytes{disjoint tag msg} ->
  len:u32{w len == length msg} ->
  key:bytes{length key == 32 /\ disjoint msg key /\ disjoint tag key} ->
  Stack unit
    (requires (fun h -> live h msg /\ live h key /\ live h tag))
    (ensures (fun h0 _ h1 -> live h0 msg /\ live h0 key /\ live h1 tag
      /\ modifies_1 tag h0 h1
      /\ (let r = Spec.clamp (sel_word h0 (sub key 0ul 16ul)) in
         let s = sel_word h0 (sub key 16ul 16ul) in
         mac_log ==>
         Seq.equal 
           (sel_word h1 tag)
           (mac_1305 (encode_bytes (as_seq h0 msg)) r s))))
let poly1305_mac tag msg len key =
  let h0 = ST.get () in
  push_frame();
  let h0' = ST.get () in

  (* Create buffers for the 2 parts of the key and the accumulator *)
  let tmp = create 0UL 10ul in
  let acc = sub tmp 0ul 5ul in
  let r   = sub tmp 5ul 5ul in
  let s   = create 0uy 16ul in
  let h0'' = ST.get () in

  (* Initialize the accumulator and the keys values *)
  poly1305_init r s key;
  let h1 = ST.get () in
  eval_null h1 acc norm_length;
  assert (sel_elem h1 acc == 0);

  (* Process the message bytes, updating the accumulator *)
  poly1305_process msg len acc r;
  let h2 = ST.get () in

  (* Finish *)
  poly1305_finish tag acc s;
  let h3 = ST.get () in
  assert (sel_word h3 tag == finish (sel_elem h2 acc) (sel_word h2 s));
  assert (mac_log ==>
    sel_word h3 tag ==
    mac_1305 (encode_bytes (as_seq h0 msg)) (sel_elem h1 r) (sel_word h1 s));

  pop_frame();
  let h4 = ST.get () in
  assert (Seq.equal (sel_word h4 tag) (sel_word h3 tag));
  modifies_mac r s acc tag h0 h0' h0'' h1 h2 h3 h4
