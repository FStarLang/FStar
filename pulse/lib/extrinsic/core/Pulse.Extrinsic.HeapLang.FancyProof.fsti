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

(** Update-closed source WP, layered on the strict operational WP.
    wp e q places a closed-mask fancy update at the final postcondition. Values
    therefore satisfy fupd(empty,empty,q v), and ghost updates can precede
    ANY expression, including a value. The original Proof.wp/value equation
    remains available unchanged as the semantic backend.

    Frame, consequence, let/context composition, and post-updates are derived
    here. Existing strict triples embed directly. Adequacy.adequate_fancy
    discharges final updates once for all clients; program proofs need no
    semantic callbacks or per-program soundness argument. *)

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module S = PulseCore.IndirectionTheorySep
module F = Pulse.Extrinsic.FancyUpdates
module E = Pulse.Extrinsic.HeapLang.Semantics
module C = Pulse.Extrinsic.HeapLang.Logic
module GS = Pulse.Lib.GhostSet

let fupd (before after:S.inames) (p:S.slprop) = F.fupd E.language C.physical before after p
let modal_post (#t:ty) (q:P.post t) (v:value t) = fupd GS.empty GS.empty (q v)
let wp (#t:ty) (e:expr [] t) (q:P.post t) = P.wp e (modal_post q)
let hoare (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) = S.implies p (wp e q)

val update_intro (before after:S.inames) (p q:S.slprop)
  : Lemma (requires P.update before after p q) (ensures S.implies p (fupd before after q))
val embed (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t)
  : Lemma (requires P.hoare p e q) (ensures hoare p e q)
val value_rule (#t:ty) (p:S.slprop) (v:value t) (q:P.post t)
  : Lemma (requires P.update GS.empty GS.empty p (q v)) (ensures hoare p (Val v) q)
val update_hoare (#t:ty) (p mid:S.slprop) (e:expr [] t) (q:P.post t)
  : Lemma (requires P.update GS.empty GS.empty p mid /\ hoare mid e q)
      (ensures hoare p e q)
val consequence (#t:ty) (p p':S.slprop) (e:expr [] t) (q q':P.post t)
  : Lemma (requires hoare p e q /\ S.implies p' p /\
      (forall v. S.implies (q v) (q' v))) (ensures hoare p' e q')
val frame (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (f:S.slprop)
  : Lemma (requires hoare p e q) (ensures hoare (S.star p f) e (P.framed_post q f))
val post_update (#t:ty) (p:S.slprop) (e:expr [] t) (q q':P.post t)
  : Lemma (requires hoare p e q /\
      (forall v. P.update GS.empty GS.empty (q v) (q' v)))
      (ensures hoare p e q')
val context_rule (#a #b:ty) (k:context a b) (p:S.slprop) (e:expr [] a)
  (mid:P.post a) (q:P.post b)
  : Lemma (requires hoare p e mid /\ (forall v. hoare (mid v) (fill k (Val v)) q))
      (ensures hoare p (fill k e) q)
val let_rule (#a #b:ty) (p:S.slprop) (bound:expr [] a) (body:expr [a] b)
  (mid:P.post a) (q:P.post b)
  : Lemma (requires hoare p bound mid /\ (forall v. hoare (mid v) (substitute v body) q))
      (ensures hoare p (Let bound body) q)
