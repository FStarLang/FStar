module Unfold

open FStar.Tactics.Typeclasses { solve }

class c (a:Type) = {
  ff : a -> a;
}

unfold
let d a = c (a & a)

let test1
  (#a:Type)
  {| d a |}
  (x : a)
  = ff (x, x)

let test2
  (#a:Type)
  {| c (a & a) |}
  = solve #(d a)
