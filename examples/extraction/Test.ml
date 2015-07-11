type nnat =
| O
| S of nnat

type 'a list =
| Nil
| Cons of 'a * 'a list

type ('a, 'b) list2 =
| Nil2
| Cons2 of 'a * 'b * ('a, 'b) list2

(*
type ('a, 'dummyV1) vec =
| Nill
| Conss of nnat * 'a * ('a, ()) vec *)