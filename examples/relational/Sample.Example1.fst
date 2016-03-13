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

