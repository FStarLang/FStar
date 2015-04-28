module Bug190

type form =
| FForall : (heap -> Tot form) -> form

type deduce : form -> Type =
  | DForallElim :
             f:(heap->Tot form) ->
             deduce (FForall f) ->
             x:heap ->
             deduce (f x)

type pred = heap -> Tot form

val hoare_consequence : p:pred -> deduce (FForall (fun h -> p h)) -> h:heap -> Tot unit
let hoare_consequence p vpp' h0 =
  ignore(DForallElim (fun (h : heap) -> p h) vpp' h0)
