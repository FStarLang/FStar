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

module Steel.Closure

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.FractionalPermission

[@@__reduce__]
let repr (r:ref int) (x:int) = pts_to r full_perm (hide x)

let ctr (r:ref int) = prev:erased int  -> SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)

let next (r:ref int) (prev:erased int)
  : SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)
  = let v = read_pt r in
    let (x:int { x == prev + 1 }) = v + 1 in
    write_pt r x;
    x

val new_counter' (u:unit) :
  SteelT ctr_t emp (fun r -> dfst r 0)

let new_counter' () =
  let x = alloc_pt 0 in
  let f : ctr x = next x in
  let res : ctr_t = (| repr x, f |) in
  rewrite_slprop (repr x 0) (dfst res 0) (fun _ -> ());
  return res

let new_counter = new_counter'
