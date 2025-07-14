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

module Pulse.Lib.Reference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
module H = Pulse.Lib.HigherReference
friend Pulse.Lib.Array.Core
inline_for_extraction
let ref a = H.ref a

inline_for_extraction
let null (#a:Type u#0) : ref a = H.null

inline_for_extraction
let is_null #a (r : ref a)
  : b:bool{b <==> r == null #a}
= H.is_null r

let pts_to r = H.pts_to r

let pts_to_timeless r p x = ()

let is_full_ref r = H.is_full_ref r

inline_for_extraction let alloc v = H.alloc v
inline_for_extraction let read r = H.read r
inline_for_extraction let op_Bang = read
inline_for_extraction let write r = H.write r
inline_for_extraction let op_Colon_Equals = write
inline_for_extraction let free r = H.free r

let share r = H.share r
let gather r = H.gather r


let with_local
    (#a:Type0)
    (init:a)
    (#pre:slprop)
    (#ret_t:Type)
    (#post:ret_t -> slprop)
    (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                                 (fun v -> post v ** (exists* v. pts_to r v)))
: stt ret_t pre post
= H.with_local init #pre #ret_t #post (fun r -> body r)


let pts_to_injective_eq r = H.pts_to_injective_eq r
let pts_to_perm_bound r = H.pts_to_perm_bound r
let pts_to_not_null r = H.pts_to_not_null r

fn replace (#a:Type0) (r:ref a) (x:a) (#v:erased a)
  requires pts_to r v
  returns y:a
  ensures pts_to r x ** pure (y == reveal v)
{
  let y = !r;
  r := x;
  y
}

let to_array_ghost r = H.to_array_ghost r
inline_for_extraction let to_array r = H.to_array r
let return_to_array r = H.return_to_array r

let array_at_ghost arr i = H.array_at_ghost arr i
inline_for_extraction let array_at arr = H.array_at arr
let return_array_at arr = H.return_array_at arr
