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

module Pulse.Lib.Mutex
#lang-pulse

open Pulse.Lib.Pervasives

module T = FStar.Tactics.V2

//
// A model of Rust mutex
//

val mutex (a:Type0) : Type0

val mutex_guard (a:Type0) : Type0

val mutex_live
  (#a:Type0)
  ([@@@mkey] m:mutex a)
  (#[T.exact (`1.0R)] p:perm)
  (v:a -> slprop)  : slprop

instance val is_send_mutex_live #a m #p v {| (x:a -> is_send (v x)) |} : is_send (mutex_live #a m #p v)

//
// mutex_guard is a ref-like type
//

val pts_to (#a:Type0) (mg:mutex_guard a) (#[T.exact (`1.0R)] p:perm) (x:a) : slprop

fn ( ! ) (#a:Type0) (mg:mutex_guard a) (#x:erased a) (#p:perm)
  requires pts_to mg #p x
  returns y:a
  ensures pts_to mg #p x ** rewrites_to y (reveal x)

fn ( := ) (#a:Type0) (mg:mutex_guard a) (y:a) (#x:erased a)
  requires mg `pts_to` x
  ensures mg `pts_to` y

fn replace (#a:Type0) (mg:mutex_guard a) (y:a) (#x:erased a)
  requires mg `pts_to` x
  returns r: _
  ensures mg `pts_to` y ** rewrites_to r (reveal x)

fn new_mutex (#a:Type0) (v:a -> slprop) (x:a)
  requires v x
  returns m:mutex a
  ensures mutex_live m v

val belongs_to (#a:Type0) (mg:mutex_guard a) (m:mutex a) : slprop

fn lock (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a)
  preserves mutex_live m #p v
  returns r:mutex_guard a
  ensures r `belongs_to` m ** (exists* x. pts_to r x ** v x)

fn unlock (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a) (mg:mutex_guard a)
  preserves mutex_live m #p v
  requires mg `belongs_to` m
  requires (exists* x. pts_to mg x ** v x)

ghost
fn share (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a)
  requires mutex_live m #p v
  ensures mutex_live m #(p /. 2.0R) v ** mutex_live m #(p /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather (#a:Type0) (#v:a -> slprop) (#p1 #p2:perm) (m:mutex a)
  requires mutex_live m #p1 v
  requires mutex_live m #p2 v
  ensures mutex_live m #(p1 +. p2) v
