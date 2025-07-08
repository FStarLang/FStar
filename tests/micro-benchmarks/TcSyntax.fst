module TcSyntax

open FStar.Class.Eq

let foo1
  (#a #b : Type)
  {| deq a |} {| deq b |}
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2

let foo2
  (#a #b : Type)
  {| deq a, deq b |}
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2

let foo3
  (#a #b : Type)
  {| deq a, deq b, |}
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2
