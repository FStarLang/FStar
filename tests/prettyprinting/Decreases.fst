module Decreases

open FStar.Mul

let rec factorial (n:nat) : Tot nat (decreases n) =
  if n = 0 then 1
  else n * factorial (n - 1)

open FStar.Preorder
open FStar.WellFounded

unfold
let lt : relation nat = fun x y -> x < y

let rec lt_acc (n:nat) : acc_g lt n =
  AccIntro_g (fun m _ -> lt_acc m)

let rec factorial_wf (n:nat)
  : Tot nat (decreases {:well-founded
      (as_well_founded lt_acc)
      n })
  = if n = 0 then 1
    else n * factorial_wf (n - 1)
