module Bug605

(* Polymorphic equality *)
noeq type peq (a:Type0) : a -> a -> Type0 =
| Refl : x:a -> peq a x x

(* Specialized to integer equality *)
let ieq (x:int) (y:int) : Tot Type0 = peq int x y

val steps_preserves_red : e:int -> e':int -> ieq e e' -> Tot unit
let steps_preserves_red e e' heq =
  match heq with
  | Refl _ -> assert(e == e') (* can't prove this obvious thing *)
