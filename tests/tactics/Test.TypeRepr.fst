module Test.TypeRepr

open FStar.Tactics.V2
module TypeRepr = FStar.Tactics.TypeRepr

type test1 (a:Type0) : Type u#123 =
  | A of a
  | B : bool -> int -> test1 a
  | C : int -> string -> list bool -> test1 a
  | D : int -> (int & bool) -> test1 a

%splice[test1_repr; test1_down; test1_up] (TypeRepr.entry (`%test1))

let _ = assert (forall a (x:test1 a). test1_up (test1_down x) == x)

[@@expect_failure] // fuel limitation
let _ = assert (forall a (x:test1_repr a). test1_down (test1_up x) == x)
