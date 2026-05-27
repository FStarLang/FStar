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

module Pulse.Lib.CancellableInvariant
#lang-pulse

open Pulse.Lib.Pervasives

[@@ erasable]
val cinv : Type0

instance val non_informative_cinv
  : NonInformative.non_informative cinv

val cinv_vp ([@@@mkey] c:cinv) (v:slprop) : slprop

instance val is_send_across_cinv_vp_aux #b #g c v {| is_send_across #b g v |} : is_send_across g (cinv_vp c v)
instance placeless_cinv_vp_aux c v {| i: placeless v |} : placeless (cinv_vp c v) = is_send_across_cinv_vp_aux c v #i
instance is_send_cinv_vp_aux c v {| i: is_send v |} : is_send (cinv_vp c v) = is_send_across_cinv_vp_aux c v #i

val active ([@@@mkey] c:cinv) (p:perm) : slprop

instance val placeless_active c p : placeless (active c p)

val active_timeless (c:cinv) (p:perm)
  : Lemma (timeless (active c p))
          [SMTPat (timeless (active c p))]

val iname_of (c:cinv) : GTot iname

ghost
fn new_cancellable_invariant (v:slprop)
  requires v
  returns  c : cinv
  ensures inv (iname_of c) (cinv_vp c v)
  ensures active c 1.0R

val unpacked (c:cinv) (v:slprop) : slprop

ghost
fn unpack_cinv_vp (#p:perm) (#v:slprop) (c:cinv)
  requires cinv_vp c v
  preserves active c p
  ensures v
  ensures unpacked c v

ghost
fn pack_cinv_vp (#v:slprop) (c:cinv)
  requires v
  requires unpacked c v
  ensures  cinv_vp c v

ghost
fn share (#p:perm) (c:cinv)
  requires active c p
  ensures active c (p /. 2.0R)
  ensures active c (p /. 2.0R)

[@@allow_ambiguous]
ghost
fn gather (#p1 #p2 :perm) (c:cinv)
  requires active c p1
  requires active c p2
  ensures  active c (p1 +. p2)

ghost
fn cancel (#v:slprop) (c:cinv)
  requires inv (iname_of c) (cinv_vp c v)
  requires active c 1.0R
  requires later_credit 1
  opens add_inv emp_inames (iname_of c)
  ensures v
