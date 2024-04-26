(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.InvList

val pledge (is:inames) (f:vprop) (v:vprop) : vprop

(* A ghost step to rewrite the context, running under invlist is. *)
// let ustep (is:invlist) (p q : vprop)
//   = unit -> stt_ghost unit (invlist_names is) (invlist_inv is ** p) (fun _ -> invlist_inv is ** q)
// let ustep0 (p q : vprop)
//   = unit -> stt_ghost unit emp_inames p (fun _ -> q)

unfold
let pledge0 (f:vprop) (v:vprop) : vprop = pledge emp_inames f v

val pledge_sub_inv (is1:inames) (is2:inames { inames_subset is1 is2 }) (f v:vprop)
  : stt_ghost unit emp_inames
                   (pledge is1 f v)
                   (fun _ -> pledge is2 f v)

(* Anything that holds now holds in the future too. *)
val return_pledge (f v:vprop)
  : stt_ghost unit emp_inames v (fun _ -> pledge emp_inames f v)

val make_pledge (is:inames) (f:vprop) (v:vprop) (extra:vprop)
  (k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  : stt_ghost unit emp_inames extra (fun _ -> pledge is f v)

val make_pledge_invs (is:invlist) (f v extra:vprop)
  (k:unit -> stt_ghost unit emp_inames (invlist_v is ** f ** extra) (fun _ -> invlist_v is ** f ** v))
  : stt_ghost unit emp_inames (invlist_inv is ** extra) (fun _ -> pledge (invlist_names is) f v)

val redeem_pledge (is:inames) (f v:vprop)
  : stt_ghost unit is (f ** pledge is f v) (fun () -> f ** v)

val squash_pledge (is:inames) (f:vprop) (v1:vprop)
  : stt_ghost unit emp_inames (pledge is f (pledge is f v1)) (fun () -> pledge is f v1)

// Unclear how useful/convenient this is
val bind_pledge (#is:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (#is_k:inames { inames_subset is_k is })
        (k:unit -> stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge is f v2))
  : stt_ghost unit emp_inames (pledge is f v1 ** extra) (fun _ -> pledge is f v2)

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
val bind_pledge' (#is:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (#is_k:inames { inames_subset is_k is })
        (k:unit -> stt_ghost unit is_k (extra ** v1) (fun _ -> pledge is f v2))
  : stt_ghost unit emp_inames (pledge is f v1 ** extra) (fun () -> pledge is f v2)

val rewrite_pledge_full (#is:inames) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** v1) (fun _ -> f ** v2))
  : stt_ghost unit emp_inames
      (pledge is f v1)
      (fun _ -> pledge is f v2)

val rewrite_pledge (#is:inames) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  : stt_ghost unit emp_inames
      (pledge is f v1)
      (fun _ -> pledge is f v2)

val join_pledge (#is:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit emp_inames
      (pledge is f v1 ** pledge is f v2)
      (fun () -> pledge is f (v1 ** v2))

(* Heterogenous variant. Takes the result invlist as an arg since we don't have
a join defined yet. *)
val squash_pledge' (is1 is2 is:inames) (f:vprop) (v1:vprop)
  : stt_ghost unit emp_inames
       (pure (inames_subset is1 is) **
        pure (inames_subset is2 is) **
        pledge is1 f (pledge is2 f v1))
       (fun () -> pledge is f v1)

// // NB: This must be an unobservable step, and not ghost,
// // as it allocates an invariant.
// // val split_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
// //   : stt_ghost (pi:invlist_elem { not (mem_inv (invlist_names is) (snd pi)) })
// //               (invlist_names is)
// //               (pledge is f (v1 ** v2))
// //               (fun pi -> pledge (add_one pi is) f v1 ** pledge (add_one pi is) f v2)
