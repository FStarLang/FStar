(*
   Copyright 2020 Microsoft Research

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

module Steel.SpinLock
open Steel.Effect
open Steel.Memory

val lock_t : Type u#0
val protects (l:lock_t) (p:slprop u#1) : prop

let lock (p:slprop u#1) = l:lock_t{l `protects` p}

val new_lock (p:slprop)
  : SteelT (lock p) p (fun _ -> emp)

val acquire (#p:slprop) (l:lock p)
  : SteelT unit emp (fun _ -> p)

val release (#p:slprop) (l:lock p)
  : SteelT unit p (fun _ -> emp)
