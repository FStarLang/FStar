module SPDZ.MPC
open SPDZ.Fp
open Sample
open FStar.Relational
open SPDZ.Sharing
open SPDZ.Triples
open FStar.Comp


(* This module contains the actual arithmetic operations. 
   For each operation we show correctness and we show that the secret inputs
   (the shares of the honest party) do not influence the public output *)

let add_loc s0 s1 = rel_map2T add_fp s0 s1

opaque val add_mpc : h0:double fp -> h1:double fp
              -> s0:shared h0 -> s1:shared h1
              -> Tot (shared(rel_map2T add_fp h0 h1))
let add_mpc _ _ s0 s1 = let r0 = add_loc (fst_rel s0) (fst_rel s1) in
                        let r1 = add_loc (snd_rel s0) (snd_rel s1) in
                        pair_rel r0 r1

let scalar_mul_loc a s = rel_map2T mul_fp a s

opaque val scalar_mul_mpc : h:double fp
                     -> a:eq fp -> s:shared h
                     -> Tot (shared (rel_map2T mul_fp a h))
let scalar_mul_mpc _ a s = let r0 = scalar_mul_loc a (fst_rel s) in
                           let r1 = scalar_mul_loc a (snd_rel s) in
                           pair_rel r0 r1

let add_const_loc a s = rel_map2T add_fp a s

opaque val add_const_mpc : h:double fp
                     -> a:eq fp -> s:shared h
                     -> Tot (shared (rel_map2T add_fp a h))
let add_const_mpc _ a s = let r0 = add_const_loc a (fst_rel s) in
                          let r1 = add_const_loc (twice (mod_p 0)) (snd_rel s) in
                          pair_rel r0 r1

let minus_loc s0 s1 = rel_map2T minus_fp s0 s1

opaque val minus_mpc : h0:double fp -> h1:double fp
              -> s0:shared h0 -> s1:shared h1
              -> Tot (shared(rel_map2T minus_fp h0 h1))
let minus_mpc _ _ s0 s1 = let r0 = minus_loc (fst_rel s0) (fst_rel s1) in
                        let r1 = minus_loc (snd_rel s0) (snd_rel s1) in
                        pair_rel r0 r1

(* Proving this seperately to speed up verfication *)
val mul_lemma : h0:double fp -> h1:double fp -> a:double fp -> b:double fp 
   -> c:double fp{c=rel_map2T mul_fp a b} 
   -> d:double fp{d=rel_map2T minus_fp h1 b}
   -> e:double fp{e=rel_map2T minus_fp h0 a} 
   -> Lemma (requires True)
            (ensures ((rel_map2T add_fp 
                        (rel_map2T add_fp 
                            (rel_map2T mul_fp e b) 
                            (rel_map2T add_fp (rel_map2T mul_fp d a) c)) 
                        (rel_map2T mul_fp d e) 
                       = rel_map2T mul_fp h0 h1)))
let mul_lemma h0 h1 a b c d e= ()

#reset-options
opaque val mul_mpc : h0:double fp -> h1:double fp
              -> s0:shared h0 -> s1:shared h1
              -> St2 (shared(rel_map2T mul_fp h0 h1))
let mul_mpc h0 h1 s0 s1 =
  let (|a, a_s|), (|b, b_s|), (|c, c_s|) = triple (snd_rel s0) (snd_rel s1) in
  let e_s = minus_mpc h0 a s0 a_s in
  let d_s = minus_mpc h1 b s1 b_s in
  let e = reconstruct (rel_map2T minus_fp h0 a) e_s in
  let d = reconstruct (rel_map2T minus_fp h1 b) d_s in
  let tmp1 = scalar_mul_mpc a d a_s in
  let tmp2 = add_mpc (rel_map2T mul_fp d a) c tmp1 c_s in
  let tmp3 = scalar_mul_mpc b e b_s in
  let tmp4 = add_mpc (rel_map2T mul_fp e b) (rel_map2T add_fp (rel_map2T mul_fp d a) c) tmp3 tmp2 in
  let tmp5 = add_const_mpc (rel_map2T add_fp (rel_map2T mul_fp e b) (rel_map2T add_fp (rel_map2T mul_fp d a) c))
                            (rel_map2T mul_fp d e) tmp4 in
  mul_lemma h0 h1 a b c d e;
  tmp5
