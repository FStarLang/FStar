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
module Pulse.Extrinsic.HeapLang.FancyProof

(** Non-values absorb pre-updates through the existing WP step rule; values
    absorb them by modal transitivity. This case distinction closes the value
    gap without inventing a source step. Context composition applies the same
    argument to each continuation, whose expression may itself be a value. *)
friend Pulse.Extrinsic.HeapLang.Proof

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module S = PulseCore.IndirectionTheorySep
module F = Pulse.Extrinsic.FancyUpdates
module U = Pulse.Extrinsic.Updates
module R = Pulse.Extrinsic.Rules
module E = Pulse.Extrinsic.HeapLang.Semantics
module C = Pulse.Extrinsic.HeapLang.Logic
module GS = Pulse.Lib.GhostSet

let update_intro before after p q = F.intro E.language C.physical before after p q

let embed #t p e q =
  R.entails_refl p;
  introduce forall v. S.implies (q v) (modal_post q v)
  with F.refl E.language C.physical GS.empty (q v);
  P.consequence p p e q (modal_post q)

let value_rule #t p v q =
  update_intro GS.empty GS.empty p (q v);
  P.value_rule p v (modal_post q)

let absorb (#t:ty) (e:expr [] t) (q:P.post t)
  : Lemma (S.implies (fupd GS.empty GS.empty (wp e q)) (wp e q))
  = match to_val e with
    | Some v ->
        P.wp_value e v (modal_post q);
        F.trans E.language C.physical GS.empty GS.empty GS.empty (q v)
    | None ->
        F.elim E.language C.physical GS.empty GS.empty (wp e q);
        R.entails_refl (wp e q);
        P.update_hoare (fupd GS.empty GS.empty (wp e q)) (wp e q) e (modal_post q)

let update_hoare #t p mid e q =
  update_intro GS.empty GS.empty p mid;
  F.mono E.language C.physical GS.empty GS.empty mid (wp e q);
  R.entails_trans p (fupd GS.empty GS.empty mid) (fupd GS.empty GS.empty (wp e q));
  absorb e q;
  R.entails_trans p (fupd GS.empty GS.empty (wp e q)) (wp e q)

let consequence #t p p' e q q' =
  introduce forall v. S.implies (modal_post q v) (modal_post q' v)
  with F.mono E.language C.physical GS.empty GS.empty (q v) (q' v);
  P.consequence p p' e (modal_post q) (modal_post q')

let frame #t p e q f =
  P.frame p e (modal_post q) f;
  R.entails_refl (S.star p f);
  introduce forall v. S.implies (P.framed_post (modal_post q) f v)
    (modal_post (P.framed_post q f) v)
  with F.frame E.language C.physical GS.empty GS.empty (q v) f;
  P.consequence (S.star p f) (S.star p f) e
    (P.framed_post (modal_post q) f) (modal_post (P.framed_post q f))

let post_update #t p e q q' =
  R.entails_refl p;
  introduce forall v. S.implies (modal_post q v) (modal_post q' v) with (
    update_intro GS.empty GS.empty (q v) (q' v);
    F.mono E.language C.physical GS.empty GS.empty (q v) (modal_post q' v);
    F.trans E.language C.physical GS.empty GS.empty GS.empty (q' v);
    R.entails_trans (modal_post q v) (fupd GS.empty GS.empty (modal_post q' v)) (modal_post q' v)
  );
  P.consequence p p e (modal_post q) (modal_post q')

let context_rule #a #b k p e mid q =
  introduce forall v. P.hoare (modal_post mid v) (fill k (Val v)) (modal_post q)
  with (
    F.elim E.language C.physical GS.empty GS.empty (mid v);
    update_hoare (modal_post mid v) (mid v) (fill k (Val v)) q
  );
  P.context_rule k p e (modal_post mid) (modal_post q)

let let_rule #a #b p bound body mid q =
  introduce forall v. P.hoare (modal_post mid v) (substitute v body) (modal_post q)
  with (
    F.elim E.language C.physical GS.empty GS.empty (mid v);
    update_hoare (modal_post mid v) (mid v) (substitute v body) q
  );
  P.let_rule p bound body (modal_post mid) (modal_post q)
