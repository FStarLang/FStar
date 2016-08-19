module FStar.DM4F.ST

// Note: being in the [FStar] namespace, only [Prims] is automatically opened
// for the current module.

let st (h: Type) (a: Type) =
  h -> M (a * h)

val return_st: h:Type -> a:Type -> x:a -> st h a
let return_st h a x = fun s -> x, s

val bind_st: h:Type -> a:Type -> b:Type -> f:st h a -> g:(a -> st h b) -> st h b
let bind_st h a b f g = fun s0 ->
  let tmp = f s0 in
  let x, s1 = tmp in
  g x s1

let get (h: Type) (_:unit): st h h =
  fun x -> x, x

let put (h: Type) (x: h): st h unit =
  fun _ -> (), x

reifiable reflectable new_effect_for_free {
  STATE (h: Type): a:Type -> Effect
  with repr     = st h
     ; bind     = bind_st h
     ; return   = return_st h
  and effect_actions
       get      = get h
     ; put      = put h
}
