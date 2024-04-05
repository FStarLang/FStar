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

module Pulse.Lib.Par.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.InvList

val pledge (is:invlist) (f:vprop) (v:vprop) : vprop

(* A ghost step to rewrite the context, running under invlist is. *)
let ustep (is:invlist) (p q : vprop)
  = unit -> stt_ghost unit (invlist_names is) (invlist_inv is ** p) (fun _ -> invlist_inv is ** q)
let ustep0 (p q : vprop)
  = unit -> stt_ghost unit emp_inames p (fun _ -> q)

unfold
let pledge0 (f:vprop) (v:vprop) : vprop = pledge [] f v

val pledge_sub_inv (os1:invlist) (os2:invlist { invlist_sub os1 os2 }) (f:vprop) (v:vprop)
  : stt_ghost unit (invlist_names os1)
                   (invlist_inv os2 ** pledge os1 f v)
                   (fun _ -> invlist_inv os1 ** pledge os2 f v)

(* Anything that holds now holds in the future too. *)
val return_pledge (is:invlist) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (invlist_inv is ** v) (fun _ -> pledge is f v)

val make_pledge (is:invlist) (f:vprop) (v:vprop) (extra:vprop)
  ($k : ustep is (f ** extra) (f ** v))
  : stt_ghost unit emp_inames (invlist_inv is ** extra) (fun _ -> pledge is f v)

val redeem_pledge (is:invlist) (f:vprop) (v:vprop)
  : stt_ghost unit (invlist_names is) (f ** pledge is f v) (fun () -> f ** v ** invlist_inv is)

val pledge_invs (is:invlist) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (pledge is f v) (fun _ -> pledge is f v ** invlist_inv is)

// Unclear how useful/convenient this is
val bind_pledge (#is:invlist) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : ustep is (f ** extra ** v1) (f ** pledge is f v2))
  : stt_ghost unit emp_inames (pledge is f v1 ** extra) (fun () -> pledge is f v2)

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
val bind_pledge' (#is:invlist) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : ustep is (extra ** v1) (pledge is f v2))
  : stt_ghost unit emp_inames (pledge is f v1 ** extra) (fun () -> pledge is f v2)

val rewrite_pledge_full (#is:invlist) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : ustep is (f ** v1) (f ** v2))
  : stt_ghost unit emp_inames
      (pledge is f v1)
      (fun _ -> pledge is f v2)

val rewrite_pledge (#is:invlist) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : ustep is v1 v2)
  : stt_ghost unit emp_inames
      (pledge is f v1)
      (fun _ -> pledge is f v2)

val rewrite_pledge0 (#is:invlist) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : ustep0 v1 v2)
  : stt_ghost unit emp_inames
      (pledge is f v1)
      (fun _ -> pledge is f v2)

val join_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit emp_inames
      (pledge is f v1 ** pledge is f v2)
      (fun () -> pledge is f (v1 ** v2))

val squash_pledge (is:invlist) (f:vprop) (v1:vprop)
  : stt_ghost unit emp_inames (pledge is f (pledge is f v1)) (fun () -> pledge is f v1)

(* Heterogenous variant. Takes the result invlist as an arg since we don't have
a join defined yet. *)
val squash_pledge' (is1 is2 is : invlist) (f:vprop) (v1:vprop)
  : stt_ghost unit emp_inames
       (invlist_inv is **
        pure (invlist_sub is1 is) **
        pure (invlist_sub is2 is) **
        pledge is1 f (pledge is2 f v1))
       (fun () -> pledge is f v1)

// NB: This must be an unobservable step, and not ghost,
// as it allocates an invariant.
// val split_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
//   : stt_ghost (pi:invlist_elem { not (mem_inv (invlist_names is) (snd pi)) })
//               (invlist_names is)
//               (pledge is f (v1 ** v2))
//               (fun pi -> pledge (add_one pi is) f v1 ** pledge (add_one pi is) f v2)
