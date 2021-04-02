module Dec

let rec f (x y:nat)
  : Tot unit (decreases y)
  = if y = 0 then ()
    else f (x + 1) (y - 1)

let rec f1 (x y :nat)
  : Tot unit (decreases y)
  = if y = 0 then ()
    else f2 (x + 1) (y - 1)

and f2 (x y:nat)
  : Tot unit (decreases y)
  = if y = 0 then ()
    else f1 (x + 1) (y - 1)

let pred (x y:nat) : prop = (x <= y) == true
let rec g (x y : nat)
  : Lemma (requires y >= x)
          (ensures (pred x y))
          (decreases y)
  = if x > 0
    then g (x - 1) (y - 1)
    else ()

[@@expect_failure [19]]
let rec h (x y : nat)
  : Lemma (requires False)
          (ensures (pred x y))
          (decreases y)
  = if x > 0
    then g (x - 1) (y - 1)
    else ()
