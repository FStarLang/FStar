(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at


   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.SpinLock
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module T = FStar.Tactics.V2

val lock : Type0

val lock_alive
      ([@@@mkey] l:lock)
      (#[T.exact (`1.0R)] p:perm)
      (v:slprop)
  : slprop

val lock_acquired (l:lock) : slprop

fn new_lock (v:slprop)
  requires v
  returns l:lock
  ensures lock_alive l v

fn rec acquire (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  ensures v ** lock_acquired l

fn release (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  requires lock_acquired l ** v

ghost
fn share (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures lock_alive l #(p /. 2.0R) v ** lock_alive l #(p /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather (#v:slprop) (#p1 #p2 :perm) (l:lock)
  requires lock_alive l #p1 v ** lock_alive l #p2 v
  ensures lock_alive l #(p1 +. p2) v

fn free (#v:slprop) (l:lock)
  requires lock_alive l #1.0R v
  requires lock_acquired l

(* A given lock is associated to a single slprop, roughly.
I'm not sure if we can prove v1 == v2 here. *)
ghost
fn lock_alive_inj
  (l:lock) (#p1 #p2 :perm) (#v1 #v2 :slprop)
  requires lock_alive l #p1 v1 ** lock_alive l #p2 v2
  ensures  lock_alive l #p1 v1 ** lock_alive l #p2 v1

val iname_of (l:lock) : iname
val iname_v_of (l:lock) (v:slprop) : slprop
val lock_active (#[T.exact (`1.0R)] p:perm) (l:lock) : v:slprop { timeless v }

ghost
fn share_lock_active (#p:perm) (l:lock)
  requires lock_active #p l
  ensures lock_active #(p /. 2.0R) l ** lock_active #(p /. 2.0R) l

ghost
fn gather_lock_active (#p1 #p2:perm) (l:lock)
  requires lock_active #p1 l ** lock_active #p2 l
  ensures lock_active #(p1 +. p2) l

ghost
fn elim_inv_and_active_into_alive (l:lock) (v:slprop) (#p:perm)
  ensures (inv (iname_of l) (iname_v_of l v) ** lock_active #p l) @==> lock_alive l #p v

ghost
fn elim_alive_into_inv_and_active (l:lock) (v:slprop) (#p:perm)
  requires emp
  ensures lock_alive l #p v @==> (inv (iname_of l) (iname_v_of l v) ** lock_active #p l)
