module VecErasedExplicit
open FStar.Ghost

noeq
type vec a : nat -> Type = 
  | Nil : vec a 0
  | Cons : #n:erased nat -> hd:a -> tl:vec a (reveal n) -> vec a (reveal n + 1)

let rec append #a (#n #m:erased nat) (v0:vec a (reveal n)) (v1:vec a (reveal m))
  : Tot (vec a (reveal n + reveal m))
        (decreases (reveal n))
  = match v0 with   
    | Nil -> v1
    | Cons #_ #n_tl hd tl ->
      Cons #a 
           #(hide (reveal n_tl + reveal m))
           hd 
           (append #a 
                   #n_tl
                   #m
                   tl
                   v1)

