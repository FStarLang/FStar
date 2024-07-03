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

module Pulse.Lib.MutexToken

open Pulse.Lib.Pervasives

module T = FStar.Tactics

val mutex (#a:Type0) (p:a -> slprop) : Type u#4

val mutex_guard (a:Type0) : Type0

val pts_to (#a:Type0) (mg:mutex_guard a) (#[T.exact (`1.0R)] p:perm) (x:a) : slprop

val ( ! ) (#a:Type0) (mg:mutex_guard a) (#x:erased a) (#p:perm)
  : stt a
      (requires pts_to mg #p x)
      (ensures fun y -> pts_to mg #p x ** pure (reveal x == y))

val ( := ) (#a:Type0) (mg:mutex_guard a) (y:a) (#x:erased a)
  : stt unit
      (requires mg `pts_to` x)
      (ensures fun _ -> mg `pts_to` y)

val replace (#a:Type0) (mg:mutex_guard a) (y:a) (#x:erased a)
  : stt a
      (requires mg `pts_to` x)
      (ensures fun r -> mg `pts_to` y ** pure (r == reveal x))

val new_mutex (#a:Type0) (v:a -> slprop { forall (x:a). is_slprop2 (v x) }) (x:a)
  : stt (mutex v)
        (requires v x)
        (ensures fun _ -> emp)

val belongs_to (#a:Type0) (#v:a -> slprop) (mg:mutex_guard a) (m:mutex v) : slprop

val lock (#a:Type0) (#v:a -> slprop) (m:mutex v)
  : stt (mutex_guard a)
        (requires emp)
        (ensures fun mg -> mg `belongs_to` m ** (exists* x. pts_to mg x ** v x))

val unlock (#a:Type0) (#v:a -> slprop) (m:mutex v) (mg:mutex_guard a)
  : stt unit
        (requires mg `belongs_to` m ** (exists* x. pts_to mg x ** v x))
        (ensures fun _ -> emp)
