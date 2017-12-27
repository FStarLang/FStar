module Bug1362
assume val hoo : nat -> Tot nat
let f2 (b:bool) (n:nat) : Tot nat =
  let k =
    let zz = hoo n in
    let rec g (m:nat) : Tot nat =
       if b then m
       else (admit(); g (m - 1))
    in 
    g n
  in
  k + 1
