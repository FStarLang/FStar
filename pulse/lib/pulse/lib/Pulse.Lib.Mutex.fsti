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

//
// Can we make the specs more precise? E.g., log the values in an append-only log
//   and say that at the time of locking the box value appears later than any (stable) snapshot
//   of the log?
//

val mutex (a:Type0) : Type0

val mutex_live
  (#a:Type0)
  (m:mutex a)
  (#[T.exact (`full_perm)] p:perm)
  (v:a -> vprop)  : vprop

val new_mutex (#a:Type0) (v:a -> vprop { forall x. is_big (v x) }) (x:a)
  : stt (mutex a)
        (requires v x)
        (ensures fun m -> mutex_live m v)

val belongs_to_mutex (#a:Type0) (r:ref a) (m:mutex a) : vprop

val lock (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a)
  : stt (ref a)
        (requires mutex_live m #p v)
        (ensures fun r -> mutex_live m #p v ** r `belongs_to_mutex` m ** (exists* x. pts_to r x ** v x))

val unlock (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a) (r:ref a)
  : stt unit
        (requires mutex_live m #p v ** r `belongs_to_mutex` m ** (exists* x. pts_to r x ** v x))
        (ensures fun _ -> mutex_live m #p v)

val share (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a)
  : stt_ghost unit emp_inames
      (requires mutex_live m #p v)
      (ensures fun _ -> mutex_live m #(half_perm p) v ** mutex_live m #(half_perm p) v)

val gather (#a:Type0) (#v:a -> vprop) (#p:perm) (m:mutex a)
  : stt_ghost unit emp_inames
      (requires mutex_live m #(half_perm p) v ** mutex_live m #(half_perm p) v)
      (ensures fun _ -> mutex_live m #p v)