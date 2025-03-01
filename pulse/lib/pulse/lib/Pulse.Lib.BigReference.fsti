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

module Pulse.Lib.BigReference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
open PulseCore.FractionalPermission
open FStar.Ghost
module T = FStar.Tactics
val ref ([@@@unused]a:Type u#2) : Type u#0

val pts_to
  (#a:Type)
  ([@@@mkey] r:ref a)
  (#[T.exact (`1.0R)] p:perm)
  (n:a) : slprop

val pts_to_is_timeless (#a:Type) (r:ref a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

fn alloc (#a:Type) (x:a)
  returns  r : ref a
  ensures  pts_to r x

fn ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  requires pts_to r #p n
  returns  x : a
  ensures  pts_to r #p n ** pure (reveal n == x)

fn ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  requires pts_to r n
  ensures  pts_to r x

fn free (#a:Type) (r:ref a) (#n:erased a)
  requires pts_to r n
  ensures emp

ghost
fn share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures  pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v

val with_local
  (#a:Type u#2)
  (init:a)
  (#pre:slprop)
  (#ret_t:Type)
  (#post:ret_t -> slprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                               (fun v -> post v ** (exists* (x:a). pts_to r x)))
  : stt ret_t pre post

[@@allow_ambiguous]
val pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : stt_ghost unit emp_inames
      (pts_to r #p v0 ** pts_to r #q v1)
      (fun _ -> pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1))

val pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ -> pts_to r #p v ** pure (p <=. 1.0R))
