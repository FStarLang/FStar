module Test

type nnat =
| O : nnat
| S : nnat -> nnat

type vec : nnat -> Type =
| Nill : vec O
| Conss : n:nnat -> (vec n) -> vec (S n)
