module FStar.Tactics.Effect

open FStar.Tactics.Types
open FStar.Tactics.Result

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

let __tac (a:Type) = proofstate -> M (__result a)

(* monadic return *)
val __ret : a:Type -> x:a -> __tac a
let __ret a x = fun (s:proofstate) -> Success(x, s)

(* monadic bind *)
let __bind (a:Type) (b:Type) (t1:__tac a) (t2:a -> __tac b) : __tac b =
    fun p -> let r = t1 (incr_depth p) in
             match r with
             | Success(a, q)  ->
                 (* We want range_of t2, but it does not work until we make range_of a constant *)
                 let r = range_of q in
                 let q = set_proofstate_range q (FStar.Range.prims_to_fstar_range r) in
                 // Force evaluation of __tracepoint q
                 begin match tracepoint q with
                 | () -> t2 a (decr_depth q)
                 end
             | Failed(msg, q) -> Failed(msg, q)

(* Actions *)
let __get () : __tac proofstate = fun s0 -> Success(s0, s0)

let __tac_wp a = proofstate -> (__result a -> Tot Type0) -> Tot Type0

(*
 * The DMFF-generated `bind_wp` doesn't the contain the "don't duplicate the post-condition"
 * optimization, which causes VCs (for well-formedness of tactics) to blow up.
 *
 * Work around that by overriding `bind_wp` for the effect with an efficient one.
 *)
unfold let g_bind (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success(a, q) -> f a q post
                     | Failed(msg, q) -> post (Failed(msg, q)))

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

let lift_div_tac (a:Type) (wp:pure_wp a) : __tac_wp a =
    fun ps p -> wp (fun x -> p (Success(x, ps)))

sub_effect DIV ~> TAC = lift_div_tac

let tactic (a:Type) = unit -> Tac a

let return (#a:Type) (x:a) : tactic a =
    fun () -> x

let bind (#a:Type) (#b:Type) (t : tactic a) (f : a -> tactic b) : tactic b =
    fun () -> let r = t () in f r ()

(* Cannot eta reduce this... *)
let get : tactic proofstate = fun () -> TAC?.__get ()

let reify_tactic (t:tactic 'a) : __tac 'a =
  fun s -> reify (t ()) s

abstract
let __by_tactic (t:__tac 'a) (p:Type) : Type = p

unfold let by_tactic (t : tactic 'a) (p:Type) : Type = __by_tactic (reify_tactic t) p

// This will run the tactic in order to (try to) produce a term of type t
// It should not lead to any inconsistency, as any time this term appears
// during typechecking, it is forced to be fully applied and the tactic
// is run. A failure of the tactic is a typechecking failure.
// TODO: `a` is really fixed to unit for now. Make it consistent
assume val synth_by_tactic : (#t:Type) -> (#a:Type) -> tactic a -> Tot t

private let trace_wrap (t : tactic 'a) : tactic 'a =
    return ();;
    r <-- t;
    return r

// Must run with tactics off, as it will otherwise try to run `by_tactic
// (reify_tactic t)`, which fails as `t` is not a concrete tactic
#reset-options "--no_tactics"
let assert_by_tactic (p:Type) (t:tactic unit)
  : Pure unit
         (requires (by_tactic (trace_wrap t) (squash p)))
         (ensures (fun _ -> p))
  = ()
#reset-options

(* We don't peel off all `by_tactic`s in negative positions, so give the SMT a way to reason about them *)
val by_tactic_seman : a:Type -> tau:(tactic a) -> phi:Type -> Lemma (by_tactic tau phi ==> phi) [SMTPat (by_tactic tau phi)]
let by_tactic_seman a tau phi = ()
