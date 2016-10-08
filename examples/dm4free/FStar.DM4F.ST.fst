module FStar.DM4F.ST

(**********************************************************
 * Dijkstra Monads for Free : Simple state
 *
 * A minimal example of defining a state effect along
 * with actions, over a parametrized state type.
 *
 **********************************************************)

(* The underlying representation type *)
let st (s:Type) (a:Type) = s -> M (a * s)

(* Monad definition *)
let return_st (s:Type) (a:Type) (x:a) : st s a = fun s0 -> x, s0

let bind_st (s:Type) (a:Type) (b:Type) (f:st s a) (g:a -> st s b) : st s b =
  fun s0 -> let x, s1 = f s0 in g x s1

(* TODO: Check the monad laws, now at least the first assert fails
   - I remember these kind of things working at submission time though
   MAYBE: In the paper types are treated as implicit,
          but new_effect_for_free fails if I try to do that *)
(* let right_unit_st (f:st 's 'a) = assert (feq (bind_st f return_st) f) *)

open FStar.FunctionalExtensionality

(* let right_unit_st (s:Type) (a:Type) (f:st s a) = *)
(*   assert (feq (bind_st s a a f (return_st s a)) f) *)

(* let left_unit_st (x:'a) (f:('a -> st 'b)) = *)
(*      assert (feq (bind (return x) f) (f x)) *)

(* let assoc_st (f:st 'a) (g:('a -> st 'b)) (h:('b -> st 'c)) *)
(*    = assert (feq (bind f (fun x -> bind (g x) h)) (bind (bind f g) h)) *)

(* Actions *)
let get (s:Type) () : st s s = fun s0 -> s0, s0

let put (s:Type) (x:s) : st s unit = fun _ -> (), x

(*
 * Do the DM4F work. Note that the heap type is a parameter
 * of the resulting effect.
 *)
reifiable reflectable new_effect_for_free {
  STATE (s:Type) : a:Type -> Effect
  with repr     = st s
     ; bind     = bind_st s
     ; return   = return_st s
  and effect_actions
       get      = get s
     ; put      = put s
}
