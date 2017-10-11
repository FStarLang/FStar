module Bug190

noeq type form =
| FForall : (int -> Tot form) -> form

noeq type deduce : form -> Type =
  | DForallElim :
             f:(int->Tot form) ->
             deduce (FForall f) ->
             x:int ->
             deduce (f x)

type pred = int -> Tot form

val hoare_consequence : p:pred -> deduce (FForall (fun (h:int) -> p h)) -> h:int -> Tot unit
let hoare_consequence p vpp' h0 = ignore(DForallElim (fun (h : int) -> p h) vpp' h0)
