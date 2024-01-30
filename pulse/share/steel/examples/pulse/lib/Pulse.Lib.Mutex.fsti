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
open Pulse.Lib.Core

open Pulse.Lib.Reference

//
// A model of Rust mutex
//

//
// Can we make the specs more precise? E.g., log the values in an append-only log
//   and say that at the time of locking the box value appears later than any (stable) snapshot
//   of the log?
//

val mutex (#a:Type0) (p:a -> vprop) : Type0

val new_mutex (#a:Type0) (p:a -> vprop) (x:a)
  : stt (mutex p)
        (requires p x)
        (ensures fun _ -> emp)

val belongs_to_mutex (#a:Type0) (#p:a -> vprop) (r:ref a) (m:mutex p) : vprop

val lock (#a:Type0) (#p:a -> vprop) (m:mutex p)
  : stt (ref a)
        (requires emp)
        (ensures fun r -> r `belongs_to_mutex` m ** (exists* v. pts_to r v ** p v))

val unlock (#a:Type0) (#p:a -> vprop) (m:mutex p) (r:ref a)
  : stt unit
        (requires r `belongs_to_mutex` m ** (exists* v. pts_to r v ** p v))
        (ensures fun _ -> emp)
