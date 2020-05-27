module Steel.ReshuffleExample
open Steel.Effect
open Steel.Memory
module SB = Steel.SteelT.Basics
module ST = Steel.Memory.Tactics

assume
val pp : int -> hprop u#1

assume
val act (a b:hprop)
  : SteelT int (a `star` b) (fun x -> a `star` pp x)

let test (p q:hprop)
  : SteelT int (p `star` q) (fun x -> pp x `star` q)
  = ST.reshuffle();
    let x = act q p in
    ST.reshuffle #_ #(pp x `star` q) //needs this annotation
  ();
    SB.return x
