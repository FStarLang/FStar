module Steel.PCM.ReshuffleFailure
open FStar.PCM
open Steel.PCM.Effect
open Steel.PCM.Memory
module SB = Steel.PCM.SteelT.Basics
module ST = Steel.PCM.Memory.Tactics

assume
val pp : int -> slprop u#1

assume
val act (a b:slprop)
  : SteelT int (a `star` b) (fun x -> a `star` pp x)

[@@expect_lax_failure]
let test (p q:slprop)
  : SteelT int (p `star` q) (fun x -> pp x `star` q)
  = ST.reshuffle();
    let x = act q p in
    ST.reshuffle #_ #_// (pp x `star` q) //needs this annotation
  ();
    SB.return x
