module FStar.Tactics.Effect

open FStar.Reflection

type goal    = (env * term) * term
type goals   = list goal
type state   = goals  //active goals
             * goals  //goals that have to be dispatched to SMT: maybe change this part of the state to be opaque to a user program

noeq type __result (a:Type) =
  | Success: a -> state -> __result a
  | Failed: string -> state -> __result a

let __tac (a:Type) = state -> M (__result a)

(* monadic return *)
val __ret : a:Type -> x:a -> __tac a
let __ret a x = fun (s:state) -> Success x s

(* monadic bind *)
let __bind (a:Type) (b:Type) (t1:__tac a) (t2:a -> __tac b) : __tac b =
    fun p -> let r = t1 p in
             match r with
             | Success a q  -> t2 a q
             | Failed msg q -> Failed msg q

(* Actions *)
let __get () : __tac state = fun s0 -> Success s0 s0

let __tac_wp a = state -> (__result a -> Tot Type0) -> Tot Type0

(*
 * The DMFF-generated `bind_wp` doesn't the contain the "don't duplicate the post-condition"
 * optimization, which causes VCs (for well-formedness of tactics) to blow up.
 *
 * Work around that by overriding `bind_wp` for the effect with an efficient one.
 *)
unfold let g_bind (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success a q -> f a q post
                     | Failed msg q -> post (Failed msg q))

unfold let g_compact (a:Type) (wp:__tac_wp a) : __tac_wp a =
    fun ps post -> forall post'. (forall (r:__result a). post r <==> post' r) ==> wp ps post'

unfold let __TAC_eff_override_bind_wp (r:range) (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) =
    g_compact b (g_bind a b wp f)

(* total  *) //disable the termination check, although it remains reifiable
reifiable reflectable new_effect {
  TAC : a:Type -> Effect
  with repr     = __tac
     ; bind     = __bind
     ; return   = __ret
     ; __get    = __get
}
effect Tac (a:Type) = TAC a (fun i post -> forall j. post j)


let tactic (a:Type) = unit -> Tac a

let return (#a:Type) (x:a) : tactic a =
    fun () -> x

let bind (#a:Type) (#b:Type) (t : tactic a) (f : a -> tactic b) : tactic b =
    fun () -> let r = t () in f r ()

(* Cannot eta reduce this... *)
let get : tactic state = fun () -> TAC?.__get ()

let reify_tactic (t:tactic 'a) : __tac 'a =
  fun s -> reify (t ()) s

abstract
let by_tactic (t:__tac 'a) (p:Type) : Type = p

// Must run with tactics off, as it will otherwise try to run `by_tactic
// (reify_tactic t)`, which fails as `t` is not a concrete tactic
#reset-options "--no_tactics"
let assert_by_tactic (t:tactic 'a) (p:Type)
  : Pure unit
         (requires (by_tactic (reify_tactic t) p))
         (ensures (fun _ -> p))
  = ()
#reset-options
