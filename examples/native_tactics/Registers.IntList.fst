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
