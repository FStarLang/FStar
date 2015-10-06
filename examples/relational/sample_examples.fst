(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst bytes.fst sample.fst xor.fst
  --*)

(* Simple example for Nik's proposal of sequencing (Email from 04/29/2015) *)
module Example1
open FStar.Heap
open FStar.Comp
open Sample
open Bijection
open FStar.Relational

let c0_pfx a = a := 0
let c1_pfx b = b := 1
let equiv_pfx a = compose2 c0_pfx c1_pfx a

let c0_sfx (a, c) = a := !a + c
let c1_sfx (b, d) = b := !b + d
let equiv_sfx a b = compose2 c0_sfx c1_sfx (pair_rel a b)

let dec x = x - 1
let inc x = x + 1

(* We prove that dec is a bijection *)
val dec_good_sample : unit -> Lemma (good_sample_fun dec)
let dec_good_sample () = cut(inverses dec inc);
                         lemma_inverses_bij  dec inc ;
                         bijection_good_sample_fun dec

(* relate the programs
  c0_pfx ; sample ; c0_sfx  and
  c1_pfx ; sample ; c1_sfx
  We first relate the prefixes, then we sample (we have to synchronize on this
  call because we only have a relational specification for it) and use the
  results to relate the suffixes *)
val equiv_seq: a:(double (ref int))
               -> ST2 (double unit)
                  (requires (fun _ -> True))
                  (ensures (fun _ _ h2 -> eq_irel (sel_rel2 h2 a)))
let equiv_seq a = let _ = equiv_pfx a in
                  dec_good_sample ();
                  let r = sample (fun x -> dec x) in
                  equiv_sfx a  r

(* Encryption with xor (Example from RF* paper) *)
module Example2
open FStar.Heap
open FStar.Comp
open Sample
open Bijection
open FStar.Relational
open Xor

let encrypt p k = xor p k
let decrypt c k = xor c k

(* We prove that the sampling function that we use is a bijection *)
val cpa_good_sample_fun: a:block -> b:block ->
  Lemma (good_sample_fun #block #block (fun x -> xor (xor a b) x))
let cpa_good_sample_fun a b =
  let sample_fun = (fun x -> xor (xor a b) x) in
  cut (inverses #block #block sample_fun sample_fun);
  lemma_inverses_bij #block #block sample_fun sample_fun;
  bijection_good_sample_fun #block #block sample_fun

(* Definition of CPA-security: An adversary cannot distinguish between the
   encryption of two plaintexts of his choice *)
val cpa : double block
       -> ST2 (double block)
            (requires (fun _ -> True))
            (ensures (fun _ p _ -> R.l p = R.r p))
let cpa a = let sample_fun = (fun x -> xor (xor (R.l a) (R.r a)) x) in
            cpa_good_sample_fun (R.l a) (R.r a);
            let k = sample sample_fun in
            compose2_self (fun (a,k) -> encrypt a k) (pair_rel a k)
