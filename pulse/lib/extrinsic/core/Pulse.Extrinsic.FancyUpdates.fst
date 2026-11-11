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
module Pulse.Extrinsic.FancyUpdates

(** The existential witness is spatial ownership, not mere evidence that an
    update is possible somewhere. Eliminating it uses the witness's framed
    update in the actual caller memory. Every modal law below is a composition
    of proved update rules, then reintroduction of the existential package. *)

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module U = Pulse.Extrinsic.Updates
module S = PulseCore.IndirectionTheorySep
module R = Pulse.Extrinsic.Rules

let intro l physical before after p q =
  S.sep_laws ();
  R.fact_emp (U.hoare l physical before after p q);
  R.exists_intro (witness l physical before after q) p

let elim l physical before after q =
  introduce forall (p:S.slprop).
    U.hoare l physical before after (witness l physical before after q p) q
  with U.pure_pre l physical before after p q (U.hoare l physical before after p q) (fun _ -> ());
  U.exists_pre l physical before after (witness l physical before after q) q

let from_entails l physical before after p q =
  U.entails l physical before p (fupd l physical before after q);
  elim l physical before after q;
  U.trans l physical before before after p (fupd l physical before after q) q

let refl l physical mask p =
  R.entails_refl p;
  U.entails l physical mask p p;
  intro l physical mask mask p p

let trans l physical before middle after p =
  let inner = fupd l physical middle after p in
  let outer = fupd l physical before middle inner in
  elim l physical before middle inner;
  elim l physical middle after p;
  U.trans l physical before middle after outer inner p;
  intro l physical before after outer p

let frame l physical before after p f =
  let pre = fupd l physical before after p in
  elim l physical before after p;
  U.frame l physical before after pre p f;
  intro l physical before after (S.star pre f) (S.star p f)

let mono l physical before after p q =
  let pre = fupd l physical before after p in
  elim l physical before after p;
  U.entails l physical after p q;
  U.trans l physical before after after pre p q;
  intro l physical before after pre q
