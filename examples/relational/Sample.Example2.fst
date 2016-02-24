(* Encryption with xor (Example from RF* paper) *)
module Sample.Example2
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
