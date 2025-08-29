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
open Pulse.Lib.GhostSet {is_finite}
open Pulse.Class.Introducable

module T = FStar.Tactics

val pledge (is:inames) (f:slprop) (v:slprop) : slprop

instance val introducable_pledge (t: Type u#a) is (is': fin_inames)
    f v extra {| introducable is' (extra ** f) (f ** v) t |} :
    introducable is extra (pledge is' f v) t

ghost
fn pledge_inames_finite (is:inames) (f p:slprop)
  preserves pledge is f p
  ensures pure (is_finite is)

unfold
let pledge0 (f:slprop) (v:slprop) : slprop = pledge emp_inames f v

ghost
fn pledge_sub_inv (is1:inames) (is2:fin_inames { inames_subset is1 is2 }) (f v:slprop)
  requires pledge is1 f v
  ensures pledge is2 f v

(* Anything that holds now holds in the future too. *)
ghost
fn return_pledge (f v:slprop)
  requires v
  ensures pledge emp_inames f v

[@@erasable]
let pledge_f (#[T.exact (`emp_inames)] is: inames) (f: slprop) (#[T.exact (`emp)] extra: slprop) (v: slprop) =
  stt_ghost unit is (f ** extra) (fun _ -> f ** v)

ghost
fn make_pledge (is:fin_inames) (f:slprop) (v:slprop) (extra:slprop)
  (k: unit -> pledge_f #is f #extra v)
  requires extra
  ensures pledge is f v

ghost
fn redeem_pledge (is:inames) (f v:slprop)
  preserves f
  requires pledge is f v
  opens is
  ensures v
  ensures pure (is_finite is)

ghost
fn squash_pledge (is:inames) (f:slprop) (v1:slprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1

[@@erasable]
let bind_pledge_f (#[T.exact (`emp_inames)] is) (#[T.exact (`emp_inames)] is_k: inames { inames_subset is_k is })
    f (#[T.exact (`emp)] extra) v1 v2 =
  stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge is f v2)

// Unclear how useful/convenient this is
ghost
fn bind_pledge (#is:inames) (#f:slprop) (#v1:slprop) (#v2:slprop)
        (extra : slprop)
        (#is_k:inames { inames_subset is_k is })
        (k:unit -> bind_pledge_f #is #is_k f #extra v1 v2)
  requires pledge is f v1 ** extra
  ensures pledge is f v2

(* Weaker variant, the proof does not use f. It's implemented
by framing k with f and then using the above combinator. Exposing
only in case it's useful for inference. *)
[@@erasable]
let bind_pledge_f' (#[T.exact (`emp_inames)] is) (#[T.exact (`emp_inames)] is_k: inames { inames_subset is_k is })
    f (#[T.exact (`emp)] extra) v1 v2 =
  stt_ghost unit is_k (extra ** v1) (fun _ -> pledge is f v2)

ghost
fn bind_pledge' (#is:inames) (#f:slprop) (#v1:slprop) (#v2:slprop)
        (extra : slprop)
        (#is_k:inames { inames_subset is_k is })
        (k:unit -> bind_pledge_f' #is #is_k f #extra v1 v2)
  requires pledge is f v1 ** extra
  ensures pledge is f v2

[@@erasable]
let rewrite_pledge_full_f (#[T.exact (`emp_inames)] is_k:inames)
    (f:slprop) (v1 : slprop) (v2 : slprop) =
  stt_ghost unit is_k (f ** v1) (fun _ -> f ** v2)

ghost
fn rewrite_pledge_full (#is:inames) (#f:slprop) (v1 : slprop) (v2 : slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> rewrite_pledge_full_f #is_k f v1 v2)
  requires pledge is f v1
  ensures pledge is f v2

[@@erasable]
let rewrite_pledge_f (#[T.exact (`emp_inames)] is_k:inames)
    (v1 : slprop) (v2 : slprop) =
  stt_ghost unit is_k v1 (fun _ -> v2)

ghost
fn rewrite_pledge (#is:inames) (#f:slprop) (v1 : slprop) (v2 : slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> rewrite_pledge_f #is_k v1 v2)
  requires pledge is f v1
  ensures  pledge is f v2

ghost
fn join_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)

(* Heterogenous variant. Takes the result invlist as an arg since we don't have
a join defined yet. *)
ghost
fn squash_pledge'
  (is1 is2 is:inames)
  (f v1:slprop)
  requires pure (inames_subset is1 is) **
           pure (inames_subset is2 is) **
           pure (is_finite is) **
           pledge is1 f (pledge is2 f v1)
  ensures pledge is f v1

ghost
fn ghost_split_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  requires pledge is f (v1 ** v2) ** later_credit 2
  returns i : iname
  ensures pledge (add_inv is i) f v1 ** pledge (add_inv is i) f v2 ** pure (not (mem_inv is i))

// This is not ghost as it buys the later credits.
fn split_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  requires pledge is f (v1 ** v2)
  returns i : iname
  ensures pledge (add_inv is i) f v1 ** pledge (add_inv is i) f v2 ** pure (not (mem_inv is i))
