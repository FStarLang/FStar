module FStar.Tactics.Effect

open FStar.Tactics.Types
open FStar.Tactics.Result

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

let __tac (a:Type) = proofstate -> M (__result a)

(* monadic return *)
val __ret : a:Type -> x:a -> __tac a
let __ret a x = fun (s:proofstate) -> Success x s

(* monadic bind *)
let __bind (a:Type) (b:Type) (r1 r2:range) (t1:__tac a) (t2:a -> __tac b) : __tac b =
    fun ps ->
        let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
        let ps = incr_depth ps in
        let r = t1 ps in
        match r with
        | Success a ps' ->
            let ps' = set_proofstate_range ps' (FStar.Range.prims_to_fstar_range r2) in
            // Force evaluation of __tracepoint q even on the interpreter
            begin match tracepoint ps' with
            | () -> t2 a (decr_depth ps')
            end
        | Failed e ps' -> Failed e ps'

(* Actions *)
let __get () : __tac proofstate = fun s0 -> Success s0 s0

let __raise (a:Type0) (e:exn) : __tac a = fun (ps:proofstate) -> Failed #a e ps

let __tac_wp a = proofstate -> (__result a -> Tot Type0) -> Tot Type0

(*
 * The DMFF-generated `bind_wp` doesn't the contain the "don't duplicate the post-condition"
 * optimization, which causes VCs (for well-formedness of tactics) to blow up.
 *
 * Plus, we don't need to model the ranges and depths: they make no difference since the
 * proofstate type is abstract and the SMT never sees a concrete one.
 *
 * So, override `bind_wp` for the effect with an efficient one.
 *)
unfold let g_bind (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success a q -> f a q post
                     | Failed e q -> post (Failed e q))

unfold let g_compact (a:Type) (wp:__tac_wp a) : __tac_wp a =
    fun ps post -> forall k. (forall (r:__result a).{:pattern (guard_free (k r))} post r ==> k r) ==> wp ps k

unfold let __TAC_eff_override_bind_wp (r:range) (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) =
    g_compact b (g_bind a b wp f)

[@ dm4f_bind_range ]
new_effect {
  TAC : a:Type -> Effect
  with repr     = __tac
     ; bind     = __bind
     ; return   = __ret
     ; __raise  = __raise
     ; __get    = __get
}

(* Hoare variant *)
effect TacH (a:Type) (pre : proofstate -> Tot Type0) (post : proofstate -> __result a -> Tot Type0) =
    TAC a (fun ps post' -> pre ps /\ (forall r. post ps r ==> post' r))

(* "Total" variant *)
effect Tac (a:Type) = TacH a (requires (fun _ -> True)) (ensures (fun _ _ -> True))

(* Metaprograms that succeed *)
effect TacS (a:Type) = TacH a (requires (fun _ -> True)) (ensures (fun _ps r -> Success? r))

(* A variant that doesn't prove totality (nor type safety!) *)
effect TacF (a:Type) = TacH a (requires (fun _ -> False)) (ensures (fun _ _ -> True))

unfold
let lift_div_tac (a:Type) (wp:pure_wp a) : __tac_wp a =
    fun ps p -> wp (fun x -> p (Success x ps))

sub_effect DIV ~> TAC = lift_div_tac

let get = TAC?.__get
let raise (#a:Type) (e:exn) = TAC?.__raise a e

abstract
let with_tactic (t : unit -> Tac 'a) (p:Type) : Type = p

// This will run the tactic in order to (try to) produce a term of type t
// It should not lead to any inconsistency, as any time this term appears
// during typechecking, it is forced to be fully applied and the tactic
// is run. A failure of the tactic is a typechecking failure.
assume val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t

let assert_by_tactic (p:Type) (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic t (squash p)) (range_of t)))
         (ensures (fun _ -> p))
  = ()

(* We don't peel off all `with_tactic`s in negative positions, so give the SMT a way to reason about them *)
val by_tactic_seman : a:Type -> tau:(unit -> Tac a) -> phi:Type -> Lemma (with_tactic tau phi ==> phi)
                                                                         [SMTPat (with_tactic tau phi)]
let by_tactic_seman a tau phi = ()

(* One can always bypass the well-formedness of metaprograms. It does not matter
 * as they are only run at typechecking time, and if they get stuck, the compiler
 * will simply raise an error. *)
val assume_safe : (#a:Type) -> (unit -> TacF a) -> Tac a
let assume_safe #a tau = admit (); tau ()

private let tactic a = unit -> Tac a

(* A hook to postprocess a definition, after typechecking, and rewrite it
 * into a (provably equal) shape chosen by the user. This can be used to implement
 * custom transformations previous to extraction, such as selective inlining.
 * When ran added to a definition [let x = E], the [tau] metaprogram
 * is presented with a goal of the shape [E = ?u] for a fresh uvar [?u].
 * The metaprogram should then both instantiate [?u] and prove the equivalence
 * to [E]. *)
irreducible
let postprocess_with (tau : unit -> Tac unit) = ()

(* Similar semantics to [postprocess_with], but the metaprogram only runs before
 * extraction, and hence typechecking and the logical environment should not be
 * affected at all. *)
irreducible
let postprocess_for_extraction_with (tau : unit -> Tac unit) = ()
