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

instance val is_send_lock_alive l p v {| is_send v |} : is_send (lock_alive l #p v)

val lock_acquired (l:lock) : slprop

fn new_lock (v:slprop)
  requires v
  returns l:lock
  ensures lock_alive l v

fn rec acquire (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  ensures v
  ensures lock_acquired l

fn release (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  requires lock_acquired l
  requires v

ghost
fn share (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures lock_alive l #(p /. 2.0R) v
  ensures lock_alive l #(p /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather (#v:slprop) (#p1 #p2 :perm) (l:lock)
  requires lock_alive l #p1 v
  requires lock_alive l #p2 v
  ensures lock_alive l #(p1 +. p2) v

fn free (#v:slprop) (l:lock)
  requires lock_alive l #1.0R v
  requires lock_acquired l

(* A given lock is associated to a single slprop, roughly.
I'm not sure if we can prove v1 == v2 here. *)
ghost
fn lock_alive_inj
  (l:lock) (#p1 #p2 :perm) (#v1 #v2 :slprop)
  preserves lock_alive l #p1 v1
  requires lock_alive l #p2 v2
  ensures lock_alive l #p2 v1
