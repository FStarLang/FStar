module FStar.DM4F.ST

(**********************************************************
 * Dijkstra Monads for Free : Simple state
 *
 * A minimal example of defining a state effect along
 * with actions, over a parametrized state type.
 *
 **********************************************************)

(* The underlying representation type *)
let st (h:Type) (a:Type) =
  h -> M (a * h)

(* Monad definition *)
val return_st : (h:Type) -> (a:Type) -> a -> st h a
let return_st h a x = fun s -> x, s

val bind_st: (h:Type) -> (a:Type) -> (b:Type) ->
             st h a -> (a -> st h b) -> st h b
let bind_st h a b f g = fun s0 ->
  let tmp = f s0 in
  let x, s1 = tmp in
  g x s1

(* Actions (get is thunked) *)
let get (h:Type) (_:unit): st h h =
  fun x -> x, x

let put (h: Type) (x: h): st h unit =
  fun _ -> (), x

(*
 * Do the DM4F work. Note that the heap type is a parameter
 * of the resulting effect.
 *)
reifiable reflectable new_effect_for_free {
  STATE (h:Type) : a:Type -> Effect
  with repr     = st h
     ; bind     = bind_st h
     ; return   = return_st h
  and effect_actions
       get      = get h
     ; put      = put h
}
