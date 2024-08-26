module VecErased
open FStar.Ghost

noeq
type vec a : nat -> Type = 
  | Nil : vec a 0
  | Cons : #n:erased nat -> hd:a -> tl:vec a n -> vec a (n + 1)

let rec append #a (#n #m:erased nat) (v0:vec a n) (v1:vec a m)
  : vec a (n + m)
  = match v0 with   
    | Nil -> v1
    | Cons hd tl -> Cons hd (append tl v1)
