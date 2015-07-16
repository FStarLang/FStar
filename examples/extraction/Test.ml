type nnat =
| O
| S of nnat

type ('a, 'b) prod =
| Pair of unit * unit * Obj.t * Obj.t

type 'a list =
| Nil of unit
| Cons of unit * Obj.t * Obj.t list

type ('a, 'b) list2 =
| Nil2 of unit * unit
| Cons2 of unit * unit * Obj.t * Obj.t * (Obj.t, Obj.t) list2

type any =
| Any of unit * Obj.t

type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p of unit
| Cons2p of unit * Obj.t * (Obj.t, Obj.t) prod list2p

type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t list3

type 'x poly =
| Poly of unit * nnat * Obj.t

type 'x poly2 =
| Poly2 of unit * unit * Obj.t

type 'x sch =
'x  ->  'x

type sch1 =
Obj.t

type sch3 =
Obj.t

type 'x sch3param =
'x  ->  'x

type idt =
unit  ->  Obj.t  ->  Obj.t

type ('a, 'dummyV1) vec =
| Nill of unit
| Conss of unit * nnat * Obj.t * (Obj.t, 'dummyV1) vec

type vecn1 =
(nnat, unit) vec

type polyvec =
nnat vec poly

type polylist =
list poly2


