module Registers.List
type reg = int
type regmap a = list (int * a) * a

[@plugin]
let create #a (x:a) : regmap a = [], x

[@plugin]
let rec sel #a (r:regmap a) (x:reg) : Tot a (decreases (fst r)) =
  match fst r with
  | [] -> snd r
  | (y, v)::tl -> if y = x then v else sel (tl, snd r) x

[@plugin]
let upd #a (r:regmap a) (x:reg) (v:a) : regmap a =
   (x, v)::fst r, snd r

[@plugin]
let rec const_map_n (n:nat) (x:'a) (r:regmap 'a) : regmap 'a =
  if n = 0 then r
  else const_map_n (n - 1) x (upd r n x)

[@plugin]
let rec identity_map (n:nat) (r:regmap nat) : regmap nat =
  if n = 0 then r
  else identity_map (n - 1) (upd r n n)
