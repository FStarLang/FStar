module Test

type nnat =
| O : nnat
| S : nnat -> nnat

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

(*
type vec : nnat -> Type =
| Nill : vec O
| Conss : n:nnat -> (vec n) -> vec (S n)
*)
