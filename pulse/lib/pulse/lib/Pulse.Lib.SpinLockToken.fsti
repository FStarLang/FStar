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

module Pulse.Lib.SpinLockToken

open Pulse.Lib.Pervasives

val lock (v:slprop) : Type u#4

val new_lock (v:slprop { is_storable v })
  : stt (lock v)
        (requires v)
        (ensures fun _ -> emp)

val lock_acquired (#v:slprop) (l:lock v) : slprop

val acquire (#v:slprop) (l:lock v)
  : stt unit
        (requires emp)
        (ensures fun _ -> v ** lock_acquired l)
       
val release (#v:slprop) (l:lock v)
  : stt unit
        (requires v ** lock_acquired l)
        (ensures fun _ -> emp)
