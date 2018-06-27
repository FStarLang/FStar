module Registers.List
type reg = int
type regmap a = list (int * a) * a

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
let rec identity_map (n:nat) (r:regmap nat) : regmap nat =
  if n = 0 then r
  else identity_map (n - 1) (upd r n n)

let eta_map (n:nat) (r:regmap 'a) : regmap 'a =
  let rec aux (n:nat) (out:regmap 'a) : regmap 'a =
    if n=0 then out
    else aux (n - 1) (upd out n (sel' r n))
  in
  aux n (create (sel' r 0))
