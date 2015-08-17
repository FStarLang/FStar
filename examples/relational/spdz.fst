(*--build-config
    options:--admit_fsi Set --z3timeout 5 ;
    variables:LIB=../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst $LIB/bytes.fst $LIB/list.fst sample.fst
  --*)
module Fp

open Relational

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

type shared (secret:double fp) = s:double (fp*fp)
                                    {fst(R.l s) = fst(R.r s)
                                  /\ add_fp (fst(R.l s)) (snd(R.l s)) = R.l secret
                                  /\ add_fp (fst(R.r s)) (snd(R.r s)) = R.r secret}

(*
let mod_laws1 = assume(forall a b.((a % p) + b) % p = (a + b) %p)
let mod_laws2 = assume(forall a b.(a + (b % p)) % p = (a + b) %p)
let mod_laws3 = assume(forall a b.((a % p) * b) % p = (a * b) %p)
let mod_laws4 = assume(forall a b.(a * (b % p)) % p = (a * b) %p)
let mod_laws5 = assume(forall a b.((a % p) - b) % p = (a - b) %p)
let mod_laws6 = assume(forall a b.(a - (b % p)) % p = (a - b) %p)
*)
module Triples
open Fp
open Sample
open Bijection
open Relational

let fst3 = MkTuple3._1
let snd3 = MkTuple3._2
let thd3 = MkTuple3._3


opaque val triple_a_good_sample_fun : sl:fp -> sr:fp ->
  Lemma (good_sample_fun #fp #fp (fun x -> add_fp (minus_fp x sl) sr))
let triple_a_good_sample_fun sl sr =
  let sample_fun = (fun x -> add_fp (minus_fp x sl) sr) in
  let sample_fun'= (fun x -> add_fp (minus_fp x sr) sl) in
  cut(inverses #fp #fp sample_fun sample_fun');
  lemma_inverses_bij #fp #fp sample_fun sample_fun';
  cut(bijection #fp #fp sample_fun);
  bijection_good_sample_fun #fp #fp sample_fun


opaque val id_good_sample_fun : unit -> Lemma (good_sample_fun #fp #fp (fun x -> x))
let id_good_sample_fun () =
  cut (bijection #fp #fp (fun x -> x));
  bijection_good_sample_fun #fp #fp(fun x -> x)


#reset-options
opaque val triple_a : s:double fp
               -> Tot (r:(h:double fp & shared h) {minus_fp (R.l s) (snd(R.l(dsnd r))) =
                                                   minus_fp (R.r s) (snd(R.r(dsnd r)))})

let triple_a s = let sample_fun = (fun x -> add_fp (minus_fp x (R.l s)) (R.r s)) in
                 let sample_fun'= (fun x -> add_fp (minus_fp x (R.r s)) (R.l s)) in
                 id_good_sample_fun ();
                 let as0 = sample #fp #fp (fun x -> x) in
                 triple_a_good_sample_fun (R.l s) (R.r s);
                 let as1 = sample  sample_fun in
                 let a = rel_map2 add_fp as0 as1 in
                 (| a, (pair_rel as0 as1) |)
#reset-options

opaque val triple_c : a:(double fp) -> b:(double fp)
               -> Tot (r:(h:double fp & shared h){dfst r = rel_map2 mul_fp a b})
let triple_c a b  = let c = rel_map2 mul_fp a b in
                    id_good_sample_fun ();
                    let cs0 = sample (fun x -> x) in
                    let cs1 = rel_map2 minus_fp c cs0 in
                    (| c, (pair_rel cs0 cs1) |)
#reset-options

opaque val triple : s01:double fp -> s11:double fp
                    -> Tot (r:((a:double fp & shared a)
                             * (b:double fp & shared b)
                             * (c:double fp & shared c))
                               {dfst (thd3 r) = rel_map2 mul_fp (dfst (fst3 r)) (dfst (snd3 r))
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
open Triples
open Relational


val share : h:double fp -> Tot (shared h)
let share h = id_good_sample_fun ();
              let s0 = sample (fun x -> x) in
              let s1 = rel_map2 minus_fp h s0 in
              let p = pair_rel s0 s1 in
              p

opaque val reconstruct : #h:double fp -> s:shared h{eq_rel s}
                  -> Tot (r:(eq fp){r=h})
let reconstruct _ s  = rel_map1 (fun (a,b) -> add_fp a b) s

val add_adv : s0:eq fp -> s1:eq fp -> Tot (eq fp)
let add_adv s0 s1 = rel_map2 add_fp s0 s1

val add_hon : s0:double fp -> s1:double fp -> Tot (double fp)
let add_hon s0 s1 = rel_map2 add_fp s0 s1

opaque val add_mpc : #h0:double fp -> #h1:double fp
              -> s0:shared h0 -> s1:shared h1
              -> Tot (shared(rel_map2 add_fp h0 h1))
let add_mpc _ _ s0 s1 = let r0 = add_adv (fst_rel s0) (fst_rel s1) in
                        let r1 = add_hon (snd_rel s0) (snd_rel s1) in
                        pair_rel r0 r1

val scalar_mul_adv : a:eq fp -> s:eq fp -> Tot (eq fp)
let scalar_mul_adv a s = rel_map2 mul_fp a s

val scalar_mul_hon : a:eq fp -> s:double fp -> Tot (double fp)
let scalar_mul_hon a s = rel_map2 mul_fp a s

opaque val scalar_mul_mpc : #h:double fp
                     -> a:eq fp -> s:shared h
                     -> Tot (shared (rel_map2 mul_fp a h))
let scalar_mul_mpc _ a s = let r0 = scalar_mul_adv a (fst_rel s) in
                           let r1 = scalar_mul_hon a (snd_rel s) in
                           pair_rel r0 r1

val add_const_adv : a:eq fp -> s:eq fp -> Tot (eq fp)
let add_const_adv a s = rel_map2 add_fp a s

val add_const_hon : a:eq fp -> s:double fp -> Tot (double fp)
let add_const_hon a s = rel_map2 add_fp a s

opaque val add_const_mpc : #h:double fp
                     -> a:eq fp -> s:shared h
                     -> Tot (shared (rel_map2 add_fp a h))
let add_const_mpc _ a s = let r0 = add_const_adv a (fst_rel s) in
                          let r1 = add_const_hon (twice (mod_p 0)) (snd_rel s) in
                          pair_rel r0 r1

val minus_adv : s0:eq fp -> s1:eq fp -> Tot (eq fp)
let minus_adv s0 s1 = rel_map2 minus_fp s0 s1

val minus_hon : s0:double fp -> s1:double fp -> Tot (double fp)
let minus_hon s0 s1 = rel_map2 minus_fp s0 s1

opaque val minus_mpc : #h0:double fp -> #h1:double fp
              -> s0:shared h0 -> s1:shared h1
              -> Tot (shared(rel_map2 minus_fp h0 h1))
let minus_mpc _ _ s0 s1 = let r0 = minus_adv (fst_rel s0) (fst_rel s1) in
                        let r1 = minus_hon (snd_rel s0) (snd_rel s1) in
                        pair_rel r0 r1

#reset-options
opaque val mul_mpc : #h0:double fp -> #h1:double fp
              -> s0:shared h0 -> s1:shared h1
              -> Tot (shared(rel_map2 mul_fp h0 h1))
let mul_mpc #h0 #h1 s0 s1 =
  let (|a, a_s|), (|b, b_s|), (|c, c_s|) = triple (rel_map1 snd s0) (rel_map1 snd s1) in
  let e_s = minus_mpc #h0 #a s0 a_s in
  let d_s = minus_mpc #h1 #b s1 b_s in
  let e = reconstruct #(rel_map2 minus_fp h0 a) e_s in
  let d = reconstruct #(rel_map2 minus_fp h1 b) d_s in
  let tmp1 = scalar_mul_mpc #a d a_s in
  let tmp2 = add_mpc #(rel_map2 mul_fp d a) #c tmp1 c_s in
  let tmp3 = scalar_mul_mpc #b e b_s in
  let tmp4 = add_mpc #(rel_map2 mul_fp e b) #(rel_map2 add_fp (rel_map2 mul_fp d a) c) tmp3 tmp2 in
  let tmp5 = add_const_mpc #(rel_map2 add_fp (rel_map2 mul_fp e b) (rel_map2 add_fp (rel_map2 mul_fp d a) c))
                            (rel_map2 mul_fp d e) tmp4 in
  tmp5
