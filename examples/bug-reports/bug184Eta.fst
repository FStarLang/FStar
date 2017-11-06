module Bug184Eta
type refl (a:Type) : a -> a -> Type =
  | Refl : x:a -> refl a x x

type refl' (x:int) (y:int) = refl int x y

val foo : e:int -> e':int -> s: refl' e e' -> Tot unit
let foo e e' s =
  match s with
    | Refl _ -> ()
