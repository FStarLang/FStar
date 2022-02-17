module Part2.Vec

type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = let Cons hd tl = v in
    if i = 0 then hd
    else get (i - 1) tl

let rec append #a #n #m (v1:vec a n) (v2:vec a m)
  : vec a (n + m)
  = admit()

let split_at #a #n (v:vec a n) (i:nat { i <= n })
  : vec a i & vec a (n - i)
  = admit()
