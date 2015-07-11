module Test

type nnat =
| O : nnat
| S : nnat -> nnat

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

type list2 'a  (b:Type) =
  | Nil2  : list2 'a b
  | Cons2 : hd:'a -> hd2:b ->  tl:list2 'a b -> list2 'a b


type vec (a:Type) : nnat -> Type =
| Nill : vec a O
| Conss : n:nnat -> a ->  (vec a n) -> vec a (S n)
