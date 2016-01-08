(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 5;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst sample.fst
  --*)

module Fp
open FStar.Relational

(* TODO, actually turn this into Fp
   For now we just use ints because they have better automatic support... *)
assume type prime (p:pos)
type prime_number = p:pos{prime p}
assume val p:prime_number

(* type fp = i:int{0 <= i /\ i < p} *)
type fp = int

val mod_p : int -> Tot fp
let mod_p x = x //% p

val add_fp : fp -> fp -> Tot fp
let add_fp x y = mod_p (x + y)

val mul_fp : fp -> fp -> Tot fp
let mul_fp x y = mod_p (x * y)

val minus_fp : fp -> fp -> Tot fp
let minus_fp x y = add_fp x (mod_p (-y))

assume val div_fp : a:fp -> b:fp -> Tot (r:fp{mul_fp b r = a})

(*
let mod_laws1 = assume(forall a b.((a % p) + b) % p = (a + b) %p)
let mod_laws2 = assume(forall a b.(a + (b % p)) % p = (a + b) %p)
let mod_laws3 = assume(forall a b.((a % p) * b) % p = (a * b) %p)
let mod_laws4 = assume(forall a b.(a * (b % p)) % p = (a * b) %p)
let mod_laws5 = assume(forall a b.((a % p) - b) % p = (a - b) %p)
let mod_laws6 = assume(forall a b.(a - (b % p)) % p = (a - b) %p)
*)

module Sharing
open Fp
open Sample
open Bijection
open FStar.Relational
open FStar.Comp

(* The shares on both sides have to sum up to the respective secret.
   We assume that the first party is dishonest and that the second party is
   honest. Hence, the first shares are always equal in both runs, while the
   second shares are not related (high) *)
type shared (secret:double fp) = s:double (fp*fp)
                                    {fst(R.l s) = fst(R.r s)
                                  /\ add_fp (fst(R.l s)) (snd(R.l s)) = R.l secret
                                  /\ add_fp (fst(R.r s)) (snd(R.r s)) = R.r secret}

(* We show that the identity function used for sampling is a bijection *)
opaque val id_good_sample_fun : unit -> Lemma (good_sample_fun #fp #fp (fun x -> x))
let id_good_sample_fun () =
  cut (bijection #fp #fp (fun x -> x));
  bijection_good_sample_fun #fp #fp(fun x -> x)

(* Simple sharing algorithm *)
opaque val share : h:double fp -> St2 (shared h)
let share h = id_good_sample_fun ();
              let s0 = sample (fun x -> x) in
              let s1 = rel_map2T minus_fp h s0 in
              let p = pair_rel s0 s1 in
              p

(* For reconstruction all  shares have to be of eq type since they are
   published *) opaque val reconstruct : h:double fp -> s:shared h{eq_irel s}
                  -> Tot (r:(eq fp){r=h})
let reconstruct _ s  = rel_map1T (fun (a,b) -> add_fp a b) s


module Triples
open Fp
open Sample
open Bijection
open FStar.Relational
open Sharing
open FStar.Comp

let fst3 = MkTuple3._1
let snd3 = MkTuple3._2
let thd3 = MkTuple3._3

(* We prove that the sample function used is a bijection *)
opaque val triple_a_good_sample_fun : sl:fp -> sr:fp ->
  Lemma (good_sample_fun #fp #fp (fun x -> add_fp (minus_fp x sl) sr))
#reset-options
let triple_a_good_sample_fun sl sr =
  let sample_fun = (fun x -> add_fp (minus_fp x sl) sr) in
  let sample_fun'= (fun x -> add_fp (minus_fp x sr) sl) in
  cut(inverses #fp #fp sample_fun sample_fun');
  lemma_inverses_bij #fp #fp sample_fun sample_fun';
  cut(bijection #fp #fp sample_fun);
  bijection_good_sample_fun #fp #fp sample_fun



(* This function is used to generate the first and the second component of the
   triple. The additional refinement ensures that we can safely publish the
   intermediate shares of the honest party during the multiplication *)
#reset-options
opaque val triple_a : s:double fp
               -> St2 (r:(h:double fp & shared h) {minus_fp (R.l s) (snd(R.l(dsnd r))) =
                                                   minus_fp (R.r s) (snd(R.r(dsnd r)))})

let triple_a s = let sample_fun = (fun x -> add_fp (minus_fp x (R.l s)) (R.r s)) in
                 id_good_sample_fun ();
                 let as0 = sample #fp #fp (fun x -> x) in
                 triple_a_good_sample_fun (R.l s) (R.r s);
                 let as1 = sample  sample_fun in
                 let a = rel_map2T add_fp as0 as1 in
                 (| a, (pair_rel as0 as1) |)
#reset-options

(* This function generates the third component of the triple *)
opaque val triple_c : a:(double fp) -> b:(double fp)
               -> St2 (r:(h:double fp & shared h){dfst r = rel_map2T mul_fp a b})
let triple_c a b  = let c = rel_map2T mul_fp a b in
                    id_good_sample_fun ();
                    let cs0 = sample (fun x -> x) in
                    let cs1 = rel_map2T minus_fp c cs0 in
                    (| c, (pair_rel cs0 cs1) |)
#reset-options

(* Combining the single elements *)
opaque val triple : s01:double fp -> s11:double fp
                    -> St2 (r:((a:double fp & shared a)
                             * (b:double fp & shared b)
                             * (c:double fp & shared c))
                               {dfst (thd3 r) = rel_map2T mul_fp (dfst (fst3 r)) (dfst (snd3 r))
                             /\ minus_fp (R.l s01) (snd(R.l(dsnd (fst3 r)))) =
                                minus_fp (R.r s01) (snd(R.r(dsnd (fst3 r))))
                             /\ minus_fp (R.l s11) (snd(R.l(dsnd (snd3 r)))) =
                                minus_fp (R.r s11) (snd(R.r(dsnd (snd3 r))))})
let triple s01 s11 = let a = triple_a s01 in
                     let b = triple_a s11 in
                     let c = triple_c (dfst a) (dfst b) in
                     a, b, c
#reset-options
module MPC
open Fp
open Sample
open FStar.Relational
open Sharing
open Triples
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
