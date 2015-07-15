type nnat =
| O
| S of nnat

type 'a list =
| Nil of unit
| Cons of unit * 'a * 'a list

type ('a, 'b) list2 =
| Nil2 of unit * unit
| Cons2 of unit * unit * 'a * 'b * ('a, 'b) list2

type 'x poly =
| Poly of unit * nnat * 'x

type 'x sh =
'x  ->  'x

type sh1 =
Obj.t

type idt =
unit  ->  Obj.t  ->  Obj.t


