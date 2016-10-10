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

let bind_st (s:Type) (a:Type) (b:Type) (f:st s a) (g:a -> st s b) : st s b
  (* = fun s0 -> let tmp = f s0 in g (fst tmp) (snd tmp) *)
  = fun s0 -> let x, s1 = f s0 in g x s1

(* MAYBE: In the paper types are treated as implicit,
          but new_effect_for_free fails if I try to do use implicit arguments *)

open FStar.FunctionalExtensionality

(* TODO: This monad law don't work because of #710 (works for Tot) *)
(* let right_unit_st (s:Type) (a:Type) (f:st s a) = *)
(*   assert (feq (bind_st s a a f (return_st s a)) f) *)

let left_unit_st (s:Type) (a:Type) (b:Type) (x:a) (f:(a -> st s b)) =
  assert (feq (bind_st s a b (return_st s a x) f) (f x))

let assoc_st (s:Type) (a:Type) (b:Type) (c:Type)
             (f:st s a) (g:(a -> st s b)) (h:(b -> st s c))
   = assert (feq (bind_st s a c f (fun x -> bind_st s b c (g x) h))
                 (bind_st s b c (bind_st s a b f g) h))

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

(* Trying to do incr here, but running into universe problem when
   trying to instantiate STATE to int; unsure whether this is related
   to Guido's latest bug reports, but at least conceptually it seems
   related to #706:

Expected expression of type "Type(n515252)";
got expression "Prims.int" of type "Type(0)"

val incr : unit -> STATE int unit
  (fun s0 post -> forall (s1:int). (s1 > s0) ==> post ((), s1))
let incr u =
  let n = STATE.get () in
  STATE.put (n + 1)
*)
