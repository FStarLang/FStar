module McCarthy91

let f91_ (x:nat) : nat = if x <= 100 then 91 else x - 10

open FStar.Mul
let rec f91 (x:nat) : Pure nat (requires True)
  (ensures (fun r -> r = f91_ x))
  (decreases (112 - x )) =
if x <= 100 then f91 (f91 (x + 11)) else x - 10
