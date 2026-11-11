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
module Pulse.Extrinsic.HeapLang.Invariants

(** Arbitrary, guarded invariant bodies in HeapLang's caller locality.
    Native invariants expose somewhere(later p). Pinning the stored assertion
    to the caller's locality removes the somewhere ambiguity, NOT the later.
    HeapLang has no locality-changing instruction; handles can be duplicated
    and shared by its threads without transporting arbitrary assertions.

    The atomic rule exposes later p and requires its restoration. A transferred
    later postcondition is consumed by Proof.atomic_to_hoare_later at the
    actual source step. Bodies may themselves contain invariants or WPs.
    No timelessness or exposure-elimination premise is imposed on p. *)

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof

let at (i:S.iref) (p:S.slprop) (l:Pulse.Lib.Loc.loc_id) =
  S.star (S.inv i (S.on l p)) (S.loc l)
let inv (i:S.iref) (p:S.slprop) = S.op_exists_Star (at i p)

val duplicate (i:S.iref) (p:S.slprop)
  : Lemma (inv i p == S.star (inv i p) (inv i p))

val atomic (#t:ty) (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p pre:S.slprop) (e:expr [] t) (q:P.post t)
  : Lemma
      (requires P.atomic (S.add_inv mask i) (S.star (S.later p) pre) e
        (P.prepend_post (S.later p) q))
      (ensures P.atomic mask (S.star (inv i p) pre) e (P.prepend_post (inv i p) q))

val allocate (#t:ty) (p pre:S.slprop) (e:expr [] t) (q:P.post t)
  (proof:(i:S.iref -> Lemma (P.hoare (S.star (inv i p) pre) e q)))
  : Lemma (requires to_val e == None)
      (ensures P.hoare (S.star p pre) e q)
