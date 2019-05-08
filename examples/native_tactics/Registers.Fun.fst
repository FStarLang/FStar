(*
   Copyright 2008-2018 Microsoft Research

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
module Registers.Fun
type reg = int
type regmap a = int -> a

// NB: We cannot handle universe polymorphic plugins in NBE right now.
// To be fixed soon, but that's why we annotate Type0 everywhere.

[@(plugin 2)]
let create (#a:Type0) (x:a) : regmap a = fun _ -> x

[@(plugin 3)]
let sel (#a:Type0) (r:regmap a) (x:reg) : Tot a = r x

let sel' (#a:Type0) (r:regmap a) (x:reg) : Tot a = sel r x

[@(plugin 4)]
let upd (#a:Type0) (r:regmap a) (x:reg) (v:a) : regmap a = fun y -> if x = y then v else r y

[@(plugin 4)]
let const_map_n (#a:Type0) (n:nat) (x:a) (r:regmap a) : regmap a = fun _ -> x

// [@(plugin 2)]
// let identity_map (n:int) (r:regmap int) : regmap int = fun x -> x

let eta_map (#a:Type0) (n:nat) (r:regmap a) : regmap a =
  let rec aux (n:nat) (out:regmap a) : regmap a =
    if n=0 then out
    else aux (n - 1) (upd out n (sel' r n))
  in
  aux n (create (sel' r 0))
