module Superclass

class eq (a:Type) = {
  d1 : a -> a;
}

class ord (a:Type) = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  ord_eq : eq a;

  d2 : a -> a;
}

let test #a {| ord a |} (x : a) : a = d1 x
