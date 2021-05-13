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
   limitations under the License.o
*)

module Steel.Closure

open Steel.Memory
open Steel.Effect
open FStar.Ghost

let ctr_t = (p:(int -> vprop) & (x:erased int -> SteelT (y:int{y == x + 1}) (p x) p))

val new_counter (u:unit) :
  SteelT ctr_t emp (fun r -> dfst r 0)
