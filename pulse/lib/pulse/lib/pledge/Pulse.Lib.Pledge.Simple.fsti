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

module Pulse.Lib.Pledge.Simple

open Pulse.Lib.Pervasives

(* In this this version of the pledge library, pledges
are not indexed by invariants. The actual invariants are existentially
quantified inside the Simple.pledge slprop, and we provide
effectful operations to manipulate them. *)

val pledge ([@@@mkey] f:slprop) ([@@@mkey] v:slprop) : slprop

(* An unobservable step to rewrite the context. *)
// let ustep (is:invlist) (p q : slprop)
//   = unit -> stt_ghost unit (invlist_names is)
//                            (invlist_inv is ** p)
//                            (fun _ -> invlist_inv is ** q)

(* Anything that holds now holds in the future too. *)
val return_pledge (f v:slprop)
  : stt_ghost unit emp_inames v (fun _ -> pledge f v)

(* The function proving a pledge can use any invariants. *)
val make_pledge (#is:inames) (f v extra:slprop)
  (k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  : stt_ghost unit emp_inames (extra ** inames_live is) (fun _ -> pledge f v)

(* Redeem is stateful in this simple variant, which is what
allows to ignore the opened invariants. *)
val redeem_pledge (f v:slprop)
  : stt unit (f ** pledge f v) (fun _ -> f ** v)

//
// Unclear if we can define this since we
//   would have to know the invariants that second pledge would use,
//   but nothing prevents them from depending on whenever the function
//   is called (i.e. classical order of quantifiers problem.)
// val bind_pledge (#f #v1 #v2:slprop)
//   (extra : slprop)
//   (#is_k:inames)
//   (k:unit -> stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge f v2))
//   : stt_ghost unit emp_inames (pledge f v1 ** extra) (fun _ -> pledge f v2)

val join_pledge (#f v1 v2:slprop)
  : stt_ghost unit emp_inames
      (pledge f v1 ** pledge f v2)
      (fun _ -> pledge f (v1 ** v2))

//
// See Pulse.Lib.Pledge.fst
// This requires pledges to be boxable,
//
// val split_pledge (#f:slprop) (v1:slprop) (v2:slprop)
//   : stt_atomic unit #Unobservable emp_inames
//               (pledge f (v1 ** v2))
//               (fun () -> pledge f v1 ** pledge f v2)

val rewrite_pledge (#f v1 v2:slprop)
  (#is_k:inames)
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  : stt_ghost unit emp_inames
      (pledge f v1 ** inames_live is_k)
      (fun _ -> pledge f v2)
