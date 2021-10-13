module RevealHide
open FStar.Ghost
open FStar.Tactics

#push-options "--no_smt"

let test1 (a:Type) (x:a) =
  assert (reveal (hide x) == x)
    by   (trefl();
          qed())

//hide (reveal x) is not reducible
[@@expect_failure]
let test2 (a:Type) (x:erased a) =
  assert (hide (reveal x) == x)
    by   (trefl();
          qed())

assume
val t (#a:Type) (x:a) : Type

let test3 (a:Type) (x:a) (y:t (reveal (hide x))) : t x = y

//hide (reveal x) is not reducible
[@@expect_failure]
let test4 (a:Type) (x:erased a) (y:t (hide (reveal x))) : t x = y
