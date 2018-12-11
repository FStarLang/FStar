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
module Registers.IntList
type reg = int
type regmap = list (int * int) * int

[@plugin]
let create (x:int) : regmap = [], x

[@plugin]
let rec sel (r:regmap) (x:reg) : Tot int (decreases (fst r)) =
  match r with
  | [], v -> v
  | (y, v)::tl, u -> if y = x then v else sel (tl, u) x

let sel' (r:regmap) (x:reg) : Tot int = sel r x

[@plugin]
let upd (r:regmap) (x:reg) (v:int) : regmap =
   (x, v)::(match r with | (f, s) -> f), (match r with | (f, s) -> s)

[@plugin]
let rec const_map_n (n:nat) (x:int) (r:regmap) : regmap =
  if n = 0 then r
  else const_map_n (n - 1) x (upd r n x)

let rec identity_map (n:nat) (r:regmap) : regmap =
  if n = 0 then r
  else identity_map (n - 1) (upd r n n)
