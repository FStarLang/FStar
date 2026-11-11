(*
   Copyright 2026 Microsoft Research
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
       http://www.apache.org/licenses/LICENSE-2.0
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Pulse.Extrinsic.HeapLang.Loops
friend PulseCore.IndirectionTheorySep
friend Pulse.Extrinsic.HeapLang.Proof

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module R = Pulse.Extrinsic.Rules
module W = Pulse.Extrinsic.WP
module H = Pulse.Extrinsic.HeapLang.Rules
module E = Pulse.Extrinsic.HeapLang.Semantics
module C = Pulse.Extrinsic.HeapLang.Logic
module K = PulseCore.KnotInstantiation

let clock (n:nat) : S.slprop =
  S.reveal_mem_le ();
  S.mk_slprop (fun h -> K.level_ h < n)

let clock_step (n:nat) (p:S.slprop)
  : Lemma (S.implies (S.star p (clock (n + 1))) (S.later (S.star p (clock n))))
  = S.reveal_slprop_ok ();
    S.later_star p (clock n);
    S.implies_intro (S.star p (clock (n + 1))) (S.later (S.star p (clock n))) (fun h ->
      let a, b = S.star_elim p (clock (n + 1)) h in
      S.star_intro (S.later p) (S.later (clock n)) h a b)

let rec bounded (n:nat) (inv body_pre exit:S.slprop)
  (condition:expr [] TBool) (body:expr [] TUnit)
  : Lemma
      (requires P.hoare inv condition (condition_post body_pre exit) /\
        P.hoare body_pre body (P.constant_post inv))
      (ensures P.hoare (S.star inv (clock n)) (While condition body) (P.constant_post exit))
      (decreases n)
  = S.sep_laws ();
    let loop = While condition body in
    let q = P.constant_post #TUnit exit in
    if n = 0 then (
      S.implies_intro (S.star inv (clock n)) (P.wp loop q) (fun h ->
        let _, bound = S.star_elim inv (clock n) h in ())
    ) else (
      bounded (n - 1) inv body_pre exit condition body;
      let tick = clock (n - 1) in
      let inv' = S.star inv tick in
      let mid = P.framed_post (condition_post body_pre exit) tick in
      P.frame inv condition (condition_post body_pre exit) tick;
      P.frame body_pre body (P.constant_post inv) tick;
      R.entails_refl (S.star body_pre tick);
      introduce forall v. S.implies
        (P.framed_post (P.constant_post #TUnit inv) tick v) (P.constant_post inv' v)
      with R.entails_refl inv';
      P.consequence (S.star body_pre tick) (S.star body_pre tick) body
        (P.framed_post (P.constant_post inv) tick) (P.constant_post inv');
      P.sequence (S.star body_pre tick) inv' body loop q;
      introduce forall b.
        P.hoare (mid b) (If (Val b) (Seq body loop) (Val ())) q
      with (
        if not b then (
          R.entails_emp tick;
          R.entails_refl exit;
          R.entails_star exit exit tick S.emp;
          P.value_rule (S.star exit tick) () q
        );
        P.if_value (mid b) b (Seq body loop) (Val ()) q
      );
      let unrolled = If condition (Seq body loop) (Val ()) in
      P.context_rule (IfCtx Hole (Seq body loop) (Val ())) inv' condition mid q;
      W.later_intro E.language C.physical inv' (E.Pack TUnit unrolled) (P.packed_post q);
      clock_step (n - 1) inv;
      R.entails_trans (S.star inv (clock n)) (S.later inv') (S.later (P.wp unrolled q));
      H.wp_pure_later (S.star inv (clock n)) loop unrolled (P.packed_post q)
        (fun h -> E.while_transition condition body h)
    )

let while_rule inv body_pre exit condition body =
  S.implies_intro inv (P.wp (While condition body) (P.constant_post exit)) (fun h ->
    let n = K.level_ h + 1 in
    bounded n inv body_pre exit condition body;
    S.sep_laws ();
    let owned, empty = S.star_elim inv S.emp h in
    S.star_intro inv (clock n) h owned empty)
