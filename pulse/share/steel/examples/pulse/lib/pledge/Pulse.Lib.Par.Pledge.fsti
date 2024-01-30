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

let pledge_any (f:vprop) (v:vprop) : vprop =
  exists* is. pledge is f v

(* A ghost step to rewrite the context, running under invlist is. *)
let ustep (is:invlist) (p q : vprop)
  = unit -> stt_ghost unit emp_inames (invlist_v is ** p) (fun _ -> invlist_v is ** q)

unfold
let pledge0 (f:vprop) (v:vprop) : vprop =
  pledge [] f v

val pledge_sub_inv (os1:invlist) (os2:invlist{invlist_sub os1 os2}) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (pledge os1 f v) (fun _ -> pledge os2 f v)

(* Anything that holds now holds in the future too. *)
val return_pledge (is:invlist) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames v (fun _ -> pledge is f v)

val make_pledge (is:invlist) (f:vprop) (v:vprop) (extra:vprop)
  ($k : ustep is (f ** extra) (f ** v))
  : stt_ghost unit emp_inames extra (fun _ -> pledge is f v)

val redeem_pledge_ghost (is:invlist) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (invlist_v is ** f ** pledge is f v) (fun () -> invlist_v is ** f ** v)
  
val redeem_pledge (is:invlist) (f:vprop) (v:vprop)
  : stt_unobservable unit (invlist_names is) (f ** pledge is f v) (fun () -> f ** v)

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

val join_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (pledge is f v1 ** pledge is f v2)
              (fun () -> pledge is f (v1 ** v2))

// NB: This must be an unobservable step, and not ghost,
// as it allocates an invariant.
val split_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_unobservable (pi:(p:vprop & inv p){not (mem_inv (invlist_names is) (dsnd pi))})
              emp_inames
              (pledge is f (v1 ** v2))
              (fun pi -> pledge (pi :: is) f v1 ** pledge (pi :: is) f v2)

// TODO: write a variant that assumes f too
val rewrite_pledge (#is:invlist) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : ustep is v1 v2)
  : stt_ghost unit
              emp_inames
              (pledge is f v1)
              (fun _ -> pledge is f v2)
