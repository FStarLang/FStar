module FStar.DM4F.Test

// Note: being in the [FStar] namespace, only [Prims] is automatically opened
// for the current module.

let st (a: Type) =
  int -> M (a * int)

let exnst (a: Type) =
  int -> M (option (a * int))

val return_st : a:Type -> x:a -> st a
let return_st a x = fun s -> x, s

val bind_st : a:Type -> b:Type -> f:st a -> g:(a -> st b) -> st b
let bind_st a b f g = fun s0 ->
  let tmp = f s0 in
  let x, s1 = tmp in
  g x s1

(* TODO: at this stage, not elaborating and generating the following two
 * combinators; so, the user has to write them in the "old style", by
 * _anticipating_ what the ouput of the *-translation and the _-elaboration will
 * be. *)

let post (a:Type) = (a * int) -> Type0
let pre = int -> Type0
let wp (a:Type) = int -> post a -> Type0

inline let ite_wp (a:Type) (wp:wp a) (h0:int) (q:post a) =
  forall (k:post a).
    (forall (x:a) (h:int).{:pattern (guard_free (k (x, h)))} k (x, h) <==> q (x, h))
    ==> wp h0 k

inline let null_wp (a:Type) (h:int) (p:post a) =
  (forall (x:a) (h:int). p (x,h))

reifiable reflectable new_effect_for_free {
  STINT: a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     // The two combinators below are meant to be automatically generated, eventually.
     ; ite_wp   = ite_wp
     ; null_wp  = null_wp
  (* and effect_actions
       get      = get
     ; put      = put *)
}

inline let lift_pure_stint (a:Type) (wp:pure_wp a) (n:int) (p:post a) = wp (fun a -> p (a, n))
sub_effect PURE ~> STINT = lift_pure_stint

effect StInt (a:Type) (pre: pre) (post: (int -> a -> int -> GTot Type0)) =
       STINT a (fun n0 p -> pre n0 /\ (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

// From the definition language to the effectful world with WPs
val action_get: input:int -> PURE (int * int) (fun post -> post (input, input))
let action_get i = (i, i)

val action_put: x:int -> input:int -> PURE (unit * int) (fun post -> post ((), x))
let action_put x i = ((), x)

reifiable val get : unit -> STINT int (fun z post -> post (z, z))
let get () = STINT.reflect action_get

reifiable val put: x:int -> STINT unit (fun z post -> post ((), x))
let put x = STINT.reflect (action_put x)
