module Bug3266

assume
val s : Type0
let st (a:Type) : Type = a & s

let functor_laws
  (map : (a:_ -> st a -> unit))
  = unit

noeq
type functor = {
  map : a:Type -> st a -> unit;
  laws : functor_laws map;
}

#set-options "--defensive abort"

let ff : functor = {
    map = (fun a (stf: st a) -> let x, s1 = stf in ()); //if you remove the pattern matching on stf then no error is reported
    laws = admit () //if you remove the admit here, again no error
}
