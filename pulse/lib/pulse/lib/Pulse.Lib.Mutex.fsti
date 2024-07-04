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

open Pulse.Lib.Pervasives

module T = FStar.Tactics.V2

//
// A model of Rust mutex
//

val mutex (a:Type0) : Type0

val mutex_guard (a:Type0) : Type0

val mutex_live
  (#a:Type0)
  (m:mutex a)
  (#[T.exact (`1.0R)] p:perm)
  (v:a -> slprop)  : slprop

//
// mutex_guard is a ref-like type
//

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

val new_mutex (#a:Type0) (v:a -> slprop { forall x. is_storable (v x) }) (x:a)
  : stt (mutex a)
      (requires v x)
      (ensures fun m -> mutex_live m v)

val belongs_to (#a:Type0) (mg:mutex_guard a) (m:mutex a) : slprop

val lock (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a)
  : stt (mutex_guard a)
      (requires mutex_live m #p v)
      (ensures fun mg -> mutex_live m #p v ** mg `belongs_to` m ** (exists* x. pts_to mg x ** v x))

val unlock (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a) (mg:mutex_guard a)
  : stt unit
      (requires mutex_live m #p v ** mg `belongs_to` m ** (exists* x. pts_to mg x ** v x))
      (ensures fun _ -> mutex_live m #p v)

val share (#a:Type0) (#v:a -> slprop) (#p:perm) (m:mutex a)
  : stt_ghost unit emp_inames
      (requires mutex_live m #p v)
      (ensures fun _ -> mutex_live m #(p /. 2.0R) v ** mutex_live m #(p /. 2.0R) v)

[@@allow_ambiguous]
val gather (#a:Type0) (#v:a -> slprop) (#p1 #p2:perm) (m:mutex a)
  : stt_ghost unit emp_inames
      (requires mutex_live m #p1 v ** mutex_live m #p2 v)
    (ensures fun _ -> mutex_live m #(p1 +. p2) v)
