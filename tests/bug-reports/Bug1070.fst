module Bug1070

let rec f (a:Type u#a) (x:a) (n:nat) =
  if n = 0
  then 0
  else f a x (n - 1)

val f' (a:Type u#a) (x:a) (n:nat) : nat
let rec f' a x n =
  if n = 0
  then 0
  else f' a x (n - 1)

let rec f1 (a:Type u#a) = 0
let f2 (a:Type u#a) = 0
let rec f3 (a:Type u#a) : _ = 0
let rec f4 (a:Type u#a) : Tot u#0 _ = 0
