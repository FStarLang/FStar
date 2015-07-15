type nnat =
| O
| S of nnat

type 'a list =
| Nil
| Cons of 'a * 'a list

type ('a, 'b) list2 =
| Nil2
| Cons2 of 'a * 'b * ('a, 'b) list2

type 'x poly =
| Poly of nnat * 'x

type 'x sh =
'x  ->  'x

type sh1 =
Obj.t

type idt =
unit  ->  Obj.t  ->  Obj.t


