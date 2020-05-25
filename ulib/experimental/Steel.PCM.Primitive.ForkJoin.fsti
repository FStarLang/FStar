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
module Steel.PCM.Primitive.ForkJoin
open Steel.PCM.Effect
open Steel.PCM.Memory

val thread (p:slprop u#1) : Type u#0

val fork (#a:Type) (#p #q #r #s:slprop)
         (f: (unit -> SteelT unit p (fun _ -> q)))
         (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)

val join (#p:slprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
