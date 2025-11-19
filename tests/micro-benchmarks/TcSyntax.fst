module TcSyntax

open FStar.Class.Eq.Raw
open FStar.Class.Ord.Raw

let has_eq (a : Type | deq) (x : a) = x = x

let _ = has_eq int 1

let has_eq2 (a b : Type | deq) (x : a) = x = x

let has_ord (a : Type | ord) : unit = ()

let foo1
  (#a #b : Type)
  {| deq a |} {| deq b |}
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2

let foo2
  (#a #b : Type)
  {| _ : deq a, db : deq b |}
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

let foo4
  (#a #b : Type | deq)
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2

let foo5
  (#a #b : Type | deq, ord, )
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2

let foo6
  (a b : Type | deq)
  (a1 a2 : a)
  (b1 b2 : b)
  : Tot bool
  = a1 = a2 && b1 = b2

let _ = foo6 int int #_ #_ 1 2 3 4

let foo7
  (#a : Type | deq)
  (a1 a2 : a)
  : Tot bool
  = (a1 = a2) = (a2 = a1)
