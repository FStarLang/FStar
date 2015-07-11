
type nnat =
| O
| S of Test.nnat

type a list =
| Nil
| Cons of a * a Test.list

type ('a, b) list2 =
| Nil2
| Cons2 of 'a * b * ('a, b) Test.list2

type (a, dummyV1) vec =
| Nill
| Conss of Test.nnat * a * (a, ()) Test.vec