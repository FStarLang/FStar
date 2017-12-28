module Bug1362
assume val hoo : nat -> Tot nat

let f0 (b:bool) (n:nat) : Tot nat =
  let b, n = b, n in
  let zz = hoo n in
  let k0, k1 =
    let rec g (m:nat) : Tot (nat * nat) =
       if b then m, m
       else (admit(); g (m - 1))
    in
    g n
  in
  k0 + 1

let f1 (n:nat) =
   hoo (let rec g (m:nat) : nat =
         if m=0 then m
         else g (m - 1)
        in g n)

let f2 (b:bool) (n:nat) : Tot nat =
  let k =
    if b then
      let rec g (m:nat) : Tot nat =
        if b then m
        else (admit(); g (m - 1))
      in
      g n
    else 0
  in
  k + 1
