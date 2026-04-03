module Pulse.Lib.TotalOrder
open FStar.Order
let flip_order (o:order) : order =
  match o with
  | Lt -> Gt
  | Eq -> Eq
  | Gt -> Lt

class total_order (a:Type) = {
  compare: a -> a -> order;
  properties : squash (
    (forall (x y:a). {:pattern compare x y} eq (compare x y) <==> x == y) /\
    (forall (x y z:a). {:pattern compare x y; compare y z} lt (compare x y) /\ lt (compare y z) ==> lt (compare x z)) /\
    (forall (x y:a). {:pattern compare x y} compare x y == flip_order (compare y x))
  )
}

let ( <? )  (#t:Type) {| o:total_order t |} (x:t) (y:t) : bool = lt (o.compare x y)
let ( <=? ) (#t:Type) {| o:total_order t |} (x:t) (y:t) : bool = le (o.compare x y)
let ( >? )  (#t:Type) {| o:total_order t |} (x:t) (y:t) : bool = not (x <=? y)
let ( ==? ) (#t:Type) {| o:total_order t |} (x:t) (y:t) : bool = eq (o.compare x y)
let ( >=? )  (#t:Type) {| o:total_order t |} (x:t) (y:t) : bool = not (x <? y)
