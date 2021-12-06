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

let rec reverse #a #n (v:vec a n)
  : vec a n
  = match v with
    | Nil -> Nil
    | Cons hd tl -> append (reverse tl) (Cons hd Nil)

let rec foldr #a #n #acc
              (f:a -> acc -> acc)
              (v:vec a n)
              (init:acc)
  : acc
  = match v with
    | Nil -> init
    | Cons hd tl ->
      f hd (foldr f tl init)
