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

val pledge (opens:inames) (f:vprop) (v:vprop) : vprop

let pledge_any (f:vprop) (v:vprop) : vprop =
  exists* is. pledge is f v

(* An unobservable step to rewrite the context. *)
let ustep (opens:inames) (p q : vprop)
  = unit -> stt_unobservable unit opens p (fun _ -> q)

unfold
let pledge0 (f:vprop) (v:vprop) : vprop =
  pledge emp_inames f v

val pledge_sub_inv (os1:inames) (os2:inames{inames_subset os1 os2}) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (pledge os1 f v) (fun _ -> pledge os2 f v)

(* Anything that holds now holds in the future too. *)
val return_pledge (os:inames) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames v (fun _ -> pledge os f v)

val make_pledge (opens:inames) (f:vprop) (v:vprop) (extra:vprop)
  ($k : ustep opens (f ** extra) (f ** v))
  : stt_ghost unit emp_inames extra (fun _ -> pledge opens f v)

val redeem_pledge (opens:inames) (f:vprop) (v:vprop)
  : stt_unobservable unit opens (f ** pledge opens f v) (fun () -> f ** v)

// Unclear how useful/convenient this is
val bind_pledge (#os:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : ustep os (f ** extra ** v1) (f ** pledge os f v2))
  : stt_ghost unit emp_inames (pledge os f v1 ** extra) (fun () -> pledge os f v2)

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
val bind_pledge' (#os:inames) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : ustep os (extra ** v1) (pledge os f v2))
  : stt_ghost unit emp_inames (pledge os f v1 ** extra) (fun () -> pledge os f v2)

val join_pledge (#opens:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (pledge opens f v1 ** pledge opens f v2)
              (fun () -> pledge opens f (v1 ** v2))

// NB: This must be an unobservable step, and not ghost,
// as it allocates an invariant.
val split_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_unobservable (erased iname)
              emp_inames
              (pledge os f (v1 ** v2))
              (fun i -> pledge (add_iname os i) f v1 ** pledge (add_iname os i) f v2)

// TODO: write a variant that assumes f too
val rewrite_pledge (#opens:inames) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : ustep opens v1 v2)
  : stt_ghost unit
              emp_inames
              (pledge opens f v1)
              (fun _ -> pledge opens f v2)
