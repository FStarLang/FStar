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

(** Assertion-valued mask updates, internalized using impredicative separating
    existential quantification over assertions. A witness owns a resource p
    together with a proved framed update from p to q. Thus fupd can itself be
    framed, transferred, or stored in an invariant.

    intro and elim establish the connection to Updates.hoare. No new
    memory-update axiom is introduced. Composition and frame preserve the
    physical heap and budget exactly as in the underlying update judgment. *)

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module U = Pulse.Extrinsic.Updates
module S = PulseCore.IndirectionTheorySep

let witness (l:L.language) (physical:W.projection l) (before after:S.inames)
  (q p:S.slprop) = S.star p (S.pure (U.hoare l physical before after p q))
let fupd (l:L.language) (physical:W.projection l) (before after:S.inames) (q:S.slprop) =
  S.op_exists_Star (witness l physical before after q)

val intro (l:L.language) (physical:W.projection l) (before after:S.inames) (p q:S.slprop)
  : Lemma (requires U.hoare l physical before after p q)
      (ensures S.implies p (fupd l physical before after q))
val elim (l:L.language) (physical:W.projection l) (before after:S.inames) (q:S.slprop)
  : Lemma (U.hoare l physical before after (fupd l physical before after q) q)
val from_entails (l:L.language) (physical:W.projection l) (before after:S.inames) (p q:S.slprop)
  : Lemma (requires S.implies p (fupd l physical before after q))
      (ensures U.hoare l physical before after p q)
val refl (l:L.language) (physical:W.projection l) (mask:S.inames) (p:S.slprop)
  : Lemma (S.implies p (fupd l physical mask mask p))
val trans (l:L.language) (physical:W.projection l) (before middle after:S.inames) (p:S.slprop)
  : Lemma (S.implies
      (fupd l physical before middle (fupd l physical middle after p))
      (fupd l physical before after p))
val frame (l:L.language) (physical:W.projection l) (before after:S.inames) (p f:S.slprop)
  : Lemma (S.implies (S.star (fupd l physical before after p) f)
      (fupd l physical before after (S.star p f)))
val mono (l:L.language) (physical:W.projection l) (before after:S.inames) (p q:S.slprop)
  : Lemma (requires S.implies p q)
      (ensures S.implies (fupd l physical before after p) (fupd l physical before after q))
