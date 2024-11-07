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
#lang-pulse

open Pulse.Lib.Pervasives

val pledge (is:inames) (f:slprop) (v:slprop) : slprop

(* A ghost step to rewrite the context, running under invlist is. *)
// let ustep (is:invlist) (p q : slprop)
//   = unit -> stt_ghost unit (invlist_names is) (invlist_inv is ** p) (fun _ -> invlist_inv is ** q)
// let ustep0 (p q : slprop)
//   = unit -> stt_ghost unit emp_inames p (fun _ -> q)

unfold
let pledge0 (f:slprop) (v:slprop) : slprop = pledge emp_inames f v

ghost
fn pledge_sub_inv (is1:inames) (is2:inames { inames_subset is1 is2 }) (f v:slprop)
  requires pledge is1 f v
  ensures pledge is2 f v

(* Anything that holds now holds in the future too. *)
ghost
fn return_pledge (f v:slprop)
  requires v
  ensures pledge emp_inames f v

ghost
fn make_pledge (is:inames) (f:slprop) (v:slprop) (extra:slprop)
  (k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  requires extra
  ensures pledge is f v

ghost
fn redeem_pledge (is:inames) (f v:slprop)
  requires f ** pledge is f v
  ensures  f ** v
  opens is

ghost
fn squash_pledge (is:inames) (f:slprop) (v1:slprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1

// Unclear how useful/convenient this is
ghost
fn bind_pledge (#is:inames) (#f:slprop) (#v1:slprop) (#v2:slprop)
        (extra : slprop)
        (#is_k:inames { inames_subset is_k is })
        (k:unit -> stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
ghost
fn bind_pledge' (#is:inames) (#f:slprop) (#v1:slprop) (#v2:slprop)
        (extra : slprop)
        (#is_k:inames { inames_subset is_k is })
        (k:unit -> stt_ghost unit is_k (extra ** v1) (fun _ -> pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2

ghost
fn rewrite_pledge_full (#is:inames) (#f:slprop) (v1 : slprop) (v2 : slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** v1) (fun _ -> f ** v2))
  requires pledge is f v1
  ensures pledge is f v2

ghost
fn rewrite_pledge (#is:inames) (#f:slprop) (v1 : slprop) (v2 : slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  requires pledge is f v1
  ensures  pledge is f v2

ghost
fn join_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)

(* Heterogenous variant. Takes the result invlist as an arg since we don't have
a join defined yet. *)
ghost
fn squash_pledge' (is1 is2 is:inames) (f:slprop) (v1:slprop)
  requires pure (inames_subset is1 is) ** pure (inames_subset is2 is) **
           pledge is1 f (pledge is2 f v1)
  ensures pledge is f v1

// This is not ghost as it must buy some later credits.
fn split_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  requires pledge is f (v1 ** v2)
  returns i : (i : iname { not (mem_inv is i) })
  ensures pledge (add_inv is i) f v1 ** pledge (add_inv is i) f v2
