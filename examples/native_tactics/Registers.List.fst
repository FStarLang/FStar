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
module Registers.List
type reg = int
type regmap (a:Type0) = list (int * a) * a

[@plugin]
let create #a (x:a) : regmap a = [], x

[@plugin]
let rec sel #a (r:regmap a) (x:reg) : Tot a (decreases (fst r)) =
  match r with
  | [], v -> v
  | (y, v)::tl, u -> if y = x then v else sel (tl, u) x

let sel' #a (r:regmap a) (x:reg) : Tot a = sel r x

[@plugin]
let upd #a (r:regmap a) (x:reg) (v:a) : regmap a =
   (x, v)::(match r with | (f, s) -> f), (match r with | (f, s) -> s)

[@plugin]
let rec const_map_n (n:nat) (x:'a) (r:regmap 'a) : regmap 'a =
  if n = 0 then r
  else const_map_n (n - 1) x (upd r n x)

[@plugin]
let rec identity_map (n:nat) (r:regmap int) : regmap int =
  if n = 0 then r
  else identity_map (n - 1) (upd r n n)

let eta_map (n:nat) (r:regmap 'a) : regmap 'a =
  let rec aux (n:nat) (out:regmap 'a) : regmap 'a =
    if n=0 then out
    else aux (n - 1) (upd out n (sel' r n))
  in
  aux n (create (sel' r 0))
