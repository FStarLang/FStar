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

module Pulse.Lib.Par.Pledge.Simple

open Pulse.Lib.Pervasives
open Pulse.Lib.InvList

(* In this this version of the pledge library, pledges
are not indexed by invariants. The actual invariants are existentially
quantified inside the Simple.pledge vprop, and we provide
effectful operations to manipulate them. *)

val pledge (f:vprop) (v:vprop) : vprop

(* An unobservable step to rewrite the context. *)
let ustep (is:invlist) (p q : vprop)
  = unit -> stt_ghost unit (invlist_names is)
                           (invlist_inv is ** p)
                           (fun _ -> invlist_inv is ** q)

(* Anything that holds now holds in the future too. *)
val return_pledge (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames v (fun _ -> pledge f v)

(* The function proving a pledge can use any invariants. *)
val make_pledge (#is:invlist) (f:vprop) (v:vprop) (extra:vprop)
  ($k : ustep is (f ** extra) (f ** v))
  : stt_ghost unit emp_inames (invlist_inv is ** extra) (fun _ -> pledge f v)

(* Redeem is stateful in this simple variant, which is what
allows to ignore the opened invariants. *)
val redeem_pledge (f:vprop) (v:vprop)
  : stt unit (f ** pledge f v) (fun () -> f ** v)

// Unclear how useful/convenient this is
val bind_pledge (#is:invlist) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : ustep is (f ** extra ** v1) (f ** pledge f v2))
  : stt_ghost unit emp_inames (pledge f v1 ** extra) (fun () -> pledge f v2)

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
val bind_pledge' (#is:invlist) (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop)
        (k : ustep is (extra ** v1) (pledge f v2))
  : stt_ghost unit emp_inames (pledge f v1 ** extra) (fun () -> pledge f v2)

val join_pledge (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (pledge f v1 ** pledge f v2)
              (fun () -> pledge f (v1 ** v2))

// See Pulse.Lib.Par.Pledge.fst
// val split_pledge (#f:vprop) (v1:vprop) (v2:vprop)
//   : stt_atomic unit #Unobservable emp_inames
//               (pledge f (v1 ** v2))
//               (fun () -> pledge f v1 ** pledge f v2)

val rewrite_pledge (#is:invlist) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : ustep is v1 v2)
  : stt_ghost unit
              emp_inames
              (pledge f v1)
              (fun _ -> pledge f v2)
