module FStar.DM4F.BasicIntST

(**********************************************************
 * Dijkstra Monads for Free : Simple state
 *
 * A minimal example of defining a state effect along
 * with actions, over an integer state type.
 *
 **********************************************************)

(* The underlying representation type *)
let st (a:Type) = int -> M (a * int)

(* Monad definition *)
let return_st (a:Type) (x:a) : st a = fun s0 -> x, s0

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun (s0:int) -> let (x,s) = f s0 in g x s

(* Actions *)
let get () : st int = fun s0 -> s0, s0

let put (x:int) : st unit = fun _ -> (), x

(*
 * Do the DM4F work. Note that the heap type is a parameter
 * of the resulting effect.
 *)
total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get
     ; put      = put
}


open FStar.Tactics


unfold let bind_elab
  (#a #b: Type)
  (#f_w: STATE?.wp a)
  ($f: (s0: Prims.int -> Prims.PURE (a * Prims.int) (f_w s0)))
  (#g_w: (y: a -> STATE?.wp b))
  ($g: (y: a -> s0: Prims.int -> Prims.PURE (b * Prims.int) (g_w y s0))) =
  STATE?.bind_elab a b f_w f g_w g

let test1 (s0:int) (v:int) =
  assert ((reify (let _ = STATE?.put v in
                   STATE?.put v) s0 ==
           bind_elab (reify (STATE?.put v))
                     (fun _ -> reify (STATE?.put v)) s0))

let test2 (s0:int) (v:int) =
  assert ((reify (let _ = STATE?.put v in
                   STATE?.put v) s0 ==
                   bind_elab (reify (STATE?.put v))
                             (fun _ -> reify (STATE?.put v)) s0))
      by (dump "start"; norm [reify_; delta_only [`%bind_elab; `%STATE?.bind_elab]]; trefl())
