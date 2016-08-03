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

val get: unit -> st int
let get u = fun s ->
  s, s

val put: int -> st unit
let put s = fun _ -> (), s

(* TODO: at this stage, not elaborating and generating the following two
 * combinators; so, the user has to write them in the "old style", by
 * _anticipating_ what the ouput of the *-translation and the _-elaboration will
 * be. *)

let post (a:Type) = (a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0

inline let ite_wp (a:Type) (wp:wp a) (h0:int) (q:post a) =
  forall (k:post a).
    (forall (x:a) (h:int).{:pattern (guard_free (k (x, h)))} k (x, h) <==> q (x, h))
    ==> wp h0 k

inline let null_wp (a:Type) (h:int) (p:post a) =
  (forall (x:a) (h:int). p (x,h))

(* #set-options "--debug FStar.DM4F.Test --debug_level Extreme --print_implicits --debug_level SMTEncoding --debug_level Simplification --print_effect_args" *)
reifiable reflectable new_effect_for_free {
  STInt: a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     // The two combinators below are meant to be automatically generated.
     ; ite_wp   = ite_wp
     ; null_wp  = null_wp
  (* and effect_actions
       get      = get
     ; put      = put *)
}

// From the definition language to the effectful world with WPs
reifiable let get' (): Pure int (fun z post -> post (z, z)) =
  STInt.reflect (get ())

// From the effectful world with WPs back to the functional monadic semantics
let get'' (): st int =
  reify (get' ())

let sanity =
  assert (forall (s: nat). get () s = get'' () s)

(* reifiable val incr2 : unit -> St unit *)
(* let incr2 u = *)
(*     let n = STATE.get() in *)
(*     STATE.put (n + 1) *)
