module FStar.DM4F.Test

// Note: being in the [FStar] namespace, only [Prims] is automatically opened
// for the current module. In particular, this means the default effect is [Tot]
// and we don't need to annotate our function types.

let st (a:Type) =
  int -> M (a * int)

val return_st : a:Type -> x:a -> st a
let return_st a x = fun s -> x, s

val bind_st : a:Type -> b:Type -> f:st a -> g:(a -> st b) -> st b
let bind_st a b f g = fun s0 ->
  let x, s1 = f s0 in
  g x s1

val get: unit -> st int
let get u = fun s ->
  s, s

val put: int -> st unit
let put s = fun _ -> (), s

(* TODO: at this stage, not elaborating and generating the following three
 * combinators; so, the user has to write them in the "old style", by
 * _anticipating_ what the ouput of the *-translation and the _-elaboration will
 * be. *)

let post (a:Type) = (a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0

inline let ite_wp (a:Type) (wp:wp a) (h0:int) (q:post a) =
  forall (k:post a).
    (forall (x:a) (h:int).{:pattern (guard_free (k (x, h)))} k (x, h) <==> q (x, h))
    ==> wp h0 k

inline let stronger (a:Type) (wp1:wp a) (wp2:wp a) =
  (forall (p:post a) (h:int). wp1 h p ==> wp2 h p)

inline let null_wp (a:Type) (h:int) (p:post a) =
  (forall (x:a) (h:int). p (x,h))

reifiable reflectable new_effect_for_free {
  STInt: a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     // The three combinators below are meant to be automatically generated.
     ; ite_wp   = ite_wp
     ; stronger = stronger
     ; null_wp  = null_wp
  and effect_actions
       get      = get
     ; put      = put
}
