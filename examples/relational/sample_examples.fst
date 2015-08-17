(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst $LIB/bytes.fst sample.fst xor.fst
  --*)

(* Simple example for Nik's proposal of sequencing (Email from 04/29/2015) *)
module Example1
open Heap
open Comp
open Sample
open Bijection
open Relational

let c0_pfx a = a := 0
let c1_pfx b = b := 1
let equiv_pfx a b = compose2 c0_pfx c1_pfx a b

let c0_sfx (a, c) = a := !a + c
let c1_sfx (b, d) = b := !b + d
let equiv_sfx a b c d = compose2 c0_sfx c1_sfx (a, c) (b, d)

let dec x = x - 1
let inc x = x + 1

val dec_good_sample : unit -> Lemma (good_sample_fun dec)
let dec_good_sample () = cut(inverses dec inc);
                         lemma_inverses_bij  dec inc ;
                         bijection_good_sample_fun dec


(* relate the programs
  c0_pfx ; sample ; c0_sfx  and
  c1_pfx ; sample ; c1_sfx  *)
val equiv_seq: a:ref int
               -> b:ref int
               -> ST2 (double unit)
                  (requires (fun _ -> True))
                  (ensures (fun _ _ h2 -> sel (R.l h2) a = sel (R.r h2) b))
let equiv_seq a b = let _ = equiv_pfx a b in
                    dec_good_sample ();
                    let R c d = sample (fun x -> dec x) in
                    equiv_sfx a b c d

(* Encryption with xor (Example from RF* paper) *)
module Example2
open Heap
open Comp
open Sample
open Bijection
open Relational
open Xor

let encrypt p k = xor p k
let decrypt c k = xor c k

val cpa_good_sample_fun: a:block -> b:block ->
  Lemma (good_sample_fun #block #block (fun x -> xor (xor a b) x))
let cpa_good_sample_fun a b =
  let sample_fun = (fun x -> xor (xor a b) x) in
  cut (inverses #block #block sample_fun sample_fun);
  lemma_inverses_bij #block #block sample_fun sample_fun;
  bijection_good_sample_fun #block #block sample_fun

val cpa : block
       -> block
       -> ST2 (double block)
            (requires (fun _ -> True))
            (ensures (fun _ p _ -> R.l p = R.r p))
let cpa a b = let sample_fun = (fun x -> xor (xor a b) x) in
              cpa_good_sample_fun a b;
              let R k1 k2 = sample sample_fun in
              compose2 (fun k -> encrypt a k) (fun k -> encrypt b k) k1 k2
              (* This does not work with eta reduced versions of the function *)

(* As this example does not use state, we actually don't need the ST2 monad *)
val cpa' : double block
        -> Tot (eq block)
let cpa' b = let sample_fun = (fun x -> xor (xor (R.l b) (R.r b)) x) in
              cpa_good_sample_fun (R.l b) (R.r b);
              let k = sample sample_fun in
              rel_map2 encrypt b k
