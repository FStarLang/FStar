module SPDZ.Triples
open SPDZ.Fp
open Sample
open Bijection
open FStar.Relational
open SPDZ.Sharing
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
