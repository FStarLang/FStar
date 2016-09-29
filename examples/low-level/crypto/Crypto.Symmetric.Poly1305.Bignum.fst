module Crypto.Symmetric.Poly1305.Bignum

open FStar.Mul
open FStar.Ghost
(** Machine integers *)
open FStar.UInt64
(** Effects and memory layout *)
open FStar.HyperStack
open FStar.HST
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open Math.Axioms
open Math.Lib
open Math.Lemmas

open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

(* open FStar.Buffer.Quantifiers *)

assume val prime: erased pos
assume new type willNotOverflow (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint) (b:bigint)
assume new type isNotModified (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) (a:bigint)
assume new type isSum (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint) (b:bigint)
assume new type satisfiesModuloConstraints (h:heap) (b:bigint)

let w : U32.t -> Tot int = U32.v

(*** Addition ***)

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0 --lax"

val fsum': a:bigint -> b:bigint{disjoint a b} -> STL unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h1 a
      /\ modifies_1 a h0 h1
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
      (* /\ isNotModified h0 h1 0 norm_length 0 a *)
      (* /\ isSum h0 h1 0 0 norm_length 0 a b *)
    ))
let fsum' a b =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let ab0 = a0 +^ b0 in
  let ab1 = a1 +^ b1 in
  let ab2 = a2 +^ b2 in
  let ab3 = a3 +^ b3 in
  let ab4 = a4 +^ b4 in
  a.(0ul) <- ab0;
  a.(1ul) <- ab1;
  a.(2ul) <- ab2;
  a.(3ul) <- ab3;
  a.(4ul) <- ab4

  (* let h0 = HST.get() in *)
  (* cut (pow2 26 + pow2 26 <= pow2 27); *)
  (* pow2_lt_compat 64 27; *)
  (* let h0 = HST.get() in *)
  (* fsum_index a 0ul b 0ul nlength 0ul;  *)
  (* let h1 = HST.get() in *)
  (* cut (forall (i:nat). i < norm_length ==> v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0))); *)
  (* cut (forall (i:nat). (i >= norm_length /\ i < length a) ==> v (get h1 a (i+0)) = v (get h0 a (i+0))); *)
  (* addition_lemma h0 h1 a b norm_length *)

val scalar_multiplication: res:bigint -> a:bigint{disjoint res a} -> s:u64 -> Stack unit
  (requires (fun h -> live h res /\ live h a
    (* /\ (forall (i:nat). {:pattern (v (get h a i))} i < norm_length ==> v (get h a i) * v s < pow2 64)  *)
  ))
  (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1
    (* /\ scalarProduct h0 h1 norm_length a s res *)
    (* /\ equal h0 a h1 a *)
    (* /\ equalSub h0 res norm_length h1 res norm_length (length res - norm_length) *)
    (* /\ eval h1 res norm_length = eval h0 a norm_length * v s *)
  ))
let scalar_multiplication res a s =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  a.(0ul) <- a0 *^ s;
  a.(1ul) <- a1 *^ s;
  a.(2ul) <- a2 *^ s;
  a.(3ul) <- a3 *^ s;
  a.(4ul) <- a4 *^ s

assume new type bound27 (h:mem) (a:bigint)

val multiplication: c:bigint -> a:bigint{disjoint c a} -> b:bigint{disjoint c b} -> Stack unit
     (requires (fun h -> bound27 h a /\ norm h b /\ live h c /\ null h c))
     (ensures (fun h0 u h1 -> bound27 h0 a /\ norm h0 b /\ live h1 c
       /\ modifies_1 c h0 h1
       (* /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) *)
       (* /\ maxValue h1 c (length c) <= norm_length * pow2 53 *)
     ))
let multiplication c a b =
  let a0 = a.(0ul) in let a1 = a.(1ul) in let a2 = a.(2ul) in let a3 = a.(3ul) in let a4 = a.(4ul) in
  let b0 = b.(0ul) in let b1 = b.(1ul) in let b2 = b.(2ul) in let b3 = b.(3ul) in let b4 = b.(4ul) in
  let ab00 = a0 *^ b0 in
  let ab01 = a0 *^ b1 in
  let ab02 = a0 *^ b2 in
  let ab03 = a0 *^ b3 in
  let ab04 = a0 *^ b4 in
  let ab10 = a1 *^ b0 in
  let ab11 = a1 *^ b1 in
  let ab12 = a1 *^ b2 in
  let ab13 = a1 *^ b3 in
  let ab14 = a1 *^ b4 in
  let ab20 = a2 *^ b0 in
  let ab21 = a2 *^ b1 in
  let ab22 = a2 *^ b2 in
  let ab23 = a2 *^ b3 in
  let ab24 = a2 *^ b4 in
  let ab30 = a3 *^ b0 in
  let ab31 = a3 *^ b1 in
  let ab32 = a3 *^ b2 in
  let ab33 = a3 *^ b3 in
  let ab34 = a3 *^ b4 in
  let ab40 = a4 *^ b0 in
  let ab41 = a4 *^ b1 in
  let ab42 = a4 *^ b2 in
  let ab43 = a4 *^ b3 in
  let ab44 = a4 *^ b4 in
  let c0 = ab00 in
  let c1 = ab01 +^ ab10 in
  let c2 = ab02 +^ ab11 +^ ab20 in
  let c3 = ab03 +^ ab12 +^ ab21 +^ ab30 in
  let c4 = ab04 +^ ab13 +^ ab22 +^ ab31 +^ ab40 in
  let c5 = ab14 +^ ab23 +^ ab32 +^ ab41 in
  let c6 = ab24 +^ ab33 +^ ab42 in
  let c7 = ab34 +^ ab43 in
  let c8 = ab44 in
  c.(0ul) <- c0;
  c.(1ul) <- c1;
  c.(2ul) <- c2;
  c.(3ul) <- c3;
  c.(4ul) <- c4;
  c.(5ul) <- c5;
  c.(6ul) <- c6;
  c.(7ul) <- c7;
  c.(8ul) <- c8

val times_5: b:U64.t -> Tot (b':U64.t)
let times_5 b = (b <<^ 2ul) +^ b

val freduce_degree: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\ satisfiesModuloConstraints h b *)
  ))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    (* /\ satisfiesModuloConstraints h0 b *)
    (* /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==> *)
    (* 	v (get h1 b i) < pow2 63) *)
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime *)
  ))
let freduce_degree b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  let b8 = b.(8ul) in
  let b0' = b0 +^ times_5 b5 in
  let b1' = b1 +^ times_5 b6 in
  let b2' = b2 +^ times_5 b7 in
  let b3' = b3 +^ times_5 b8 in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3'

val mod2_26: U64.t -> Tot U64.t
let mod2_26 x = x &^ 0x3ffffffuL

val div2_26: U64.t -> Tot U64.t
let div2_26 x = x >>^ 26ul

val carry_1: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 63) *)
  ))
  (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b /\ modifies_1 b h0 h1
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime *)
  ))
let carry_1 b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b0' = mod2_26 b0 in
  let r0  = div2_26 b0 in
  let b1' = mod2_26 (b1 +^ r0) in
  let r1  = div2_26 (b1 +^ r0) in
  let b2' = mod2_26 (b2 +^ r1) in
  let r2  = div2_26 (b2 +^ r1) in
  let b3' = mod2_26 (b3 +^ r2) in
  let r3  = div2_26 (b3 +^ r2) in
  let b4' = mod2_26 (b4 +^ r3) in
  let b5' = div2_26 (b4 +^ r3) in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3';
  b.(4ul) <- b4';
  b.(5ul) <- b5'


val carry_2: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 63) *)
  ))
  (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b /\ modifies_1 b h0 h1
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime *)
  ))
let carry_2 b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b0' = mod2_26 b0 in
  let r0  = div2_26 b0 in
  let b1' = mod2_26 (b1 +^ r0) in
  let r1  = div2_26 (b1 +^ r0) in
  let b2' = mod2_26 (b2 +^ r1) in
  let r2  = div2_26 (b2 +^ r1) in
  let b3' = mod2_26 (b3 +^ r2) in
  let r3  = div2_26 (b3 +^ r2) in
  let b4' = mod2_26 (b4 +^ r3) in
  let b5' = div2_26 (b4 +^ r3) in
  b.(0ul) <- b0';
  b.(1ul) <- b1';
  b.(2ul) <- b2';
  b.(3ul) <- b3';
  b.(4ul) <- b4';
  b.(5ul) <- b5'

val carry_top: b:bigint -> Stack unit
  (requires (fun h -> live h b /\ length b >= 5))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let carry_top b =
  let b0 = b.(0ul) in
  let b5 = b.(5ul) in
  b.(0ul) <- b0 +^ times_5 b5

val freduce_coefficients: b:bigint -> Stack unit
  (requires (fun h -> live h b
    (* /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 63) *)
  ))
  (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b /\ modifies_1 b h0 h1
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime *)
  ))
let freduce_coefficients b =
  carry_1 b;
  carry_top b;
  carry_2 b;
  carry_top b;
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b0' = mod2_26 b0 in
  let r0  = div2_26 b0 in
  b.(0ul) <- b0;
  b.(1ul) <- b1 +^ r0

val modulo: b:bigint -> Stack unit
  (requires (fun h -> live h b /\ satisfiesModuloConstraints h b))
  (ensures (fun h0 _ h1 -> live h0 b /\ satisfiesModuloConstraints h0 b /\ norm h1 b
    (* /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime  *)
    /\ modifies_1 b h0 h1))
let modulo b =
  freduce_degree b;
  freduce_coefficients b

val finalize: b:bigint -> Stack unit
  (requires (fun h -> norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ norm h1 b
    /\ modifies_1 b h0 h1
    (* /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime *)
  ))
let finalize b =
  let mask_26 = U64 ((1uL <<^ 26ul) -^ 1uL) in
  let mask2_26m5 = U64 (mask_26 -^ (1uL <<^ 2ul)) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let mask = U64.eq_mask b4 mask_26 in
  let mask = U64.eq_mask b3 mask_26 &^ mask in
  let mask = U64.eq_mask b2 mask_26 &^ mask in
  let mask = U64.eq_mask b1 mask_26 &^ mask in
  let mask = U64.gte_mask b0 mask2_26m5 &^ mask in
  b.(0ul) <- (b0 -^ (mask &^ mask2_26m5));
  b.(1ul) <- (b1 -^ (b1 &^ mask));
  b.(2ul) <- (b2 -^ (b2 &^ mask));
  b.(3ul) <- (b3 -^ (b3 &^ mask));
  b.(4ul) <- (b4 -^ (b4 &^ mask))
