(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Tactics.Effect

open FStar.Monotonic.Pure

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Tactics.Types
open FStar.Stubs.Tactics.Result

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

type tac_wp_t0 (a:Type) =
  proofstate -> (__result a -> Type0) -> Type0

unfold
let tac_wp_monotonic (#a:Type) (wp:tac_wp_t0 a) =
  forall (ps:proofstate) (p q:__result a -> Type0).
    (forall x. p x ==> q x) ==> (wp ps p ==> wp ps q)

type tac_wp_t (a:Type) = wp:tac_wp_t0 a{tac_wp_monotonic wp}

let tac_repr (a:Type) (wp:tac_wp_t a) =
  ps0:proofstate -> DIV (__result a) (as_pure_wp (wp ps0))

unfold
let tac_return_wp (#a:Type) (x:a) : tac_wp_t a =
  fun ps post -> post (Success x ps)

(* monadic return *)
let tac_return (a:Type) (x:a) : tac_repr a (tac_return_wp x) =
  fun (s:proofstate) -> Success x s

unfold
let tac_bind_wp (#a #b:Type) (wp_f:tac_wp_t a) (wp_g:a -> tac_wp_t b) : tac_wp_t b =
  fun ps post ->
  wp_f ps (fun r ->
           match r with
           | Success x ps -> wp_g x ps post
           | Failed ex ps -> post (Failed ex ps))

/// An optimization to name the continuation

unfold
let tac_wp_compact (a:Type) (wp:tac_wp_t a) : tac_wp_t a =
  fun ps post ->
  forall (k:__result a -> Type0). (forall (r:__result a).{:pattern (guard_free (k r))} post r ==> k r) ==> wp ps k


/// tac_bind_interleave_begin is an ugly hack to get interface interleaving
/// work with admit_smt_queries true for the bind combinator

val tac_bind_interleave_begin : unit


/// We cannot verify the bind combinator, since the body of bind
///   does some operations on the proof state, with which we cannot prove
///   that the proofstate is sequenced. Two ways to fix it:
///
/// 1. We separate the "meta" proofstate s.t. range, depth, etc. from the main
///    proofstate, and then sequencing only applies to the main proofstate
///
/// 2. The pre and post of the TAC effect are just exception pre and post,
///    since we can't prove much about the proofstate anyway, as it is
///    mostly abstract

(* monadic bind *)
#push-options "--admit_smt_queries true"
let tac_bind (a:Type) (b:Type)
  (wp_f:tac_wp_t a)
  (wp_g:a -> tac_wp_t b)
  (r1 r2:range)
  (t1:tac_repr a wp_f)
  (t2:(x:a -> tac_repr b (wp_g x))) : tac_repr b (tac_wp_compact b (tac_bind_wp wp_f wp_g)) =
  fun ps ->
  let ps = set_proofstate_range ps r1 in
  let ps = incr_depth ps in
  let r = t1 ps in
  match r with
  | Success a ps' ->
    let ps' = set_proofstate_range ps' r2 in
    // Force evaluation of __tracepoint q even on the interpreter
    begin match tracepoint ps' with
          | true -> t2 a (decr_depth ps')
    end
  | Failed e ps' -> Failed e ps'
#pop-options


/// tac_bind_interleave_end is an ugly hack to get interface interleaving
/// work with admit_smt_queries true for the bind combinator

val tac_bind_interleave_end : unit

unfold
let tac_if_then_else_wp (#a:Type) (wp_then:tac_wp_t a) (wp_else:tac_wp_t a) (b:bool)
  : tac_wp_t a
  = fun ps post -> (b ==> wp_then ps post) /\
                ((~ b) ==> wp_else ps post)

let tac_if_then_else (a:Type)
  (wp_then:tac_wp_t a)
  (wp_else:tac_wp_t a)
  (f:tac_repr a wp_then)
  (g:tac_repr a wp_else)
  (b:bool)
  : Type
  = tac_repr a (tac_wp_compact a (tac_if_then_else_wp wp_then wp_else b))

let tac_subcomp (a:Type)
  (wp_f:tac_wp_t a)
  (wp_g:tac_wp_t a)
  (f:tac_repr a wp_f)
  : Pure (tac_repr a wp_g)
         (requires forall ps p. wp_g ps p ==> wp_f ps p)
         (ensures fun _ -> True)
  = f

let tac_close (a b:Type)
  (wp_f:b -> tac_wp_t a)
  (f:(x:b -> tac_repr a (wp_f x))) =

  tac_repr a (fun ps post -> forall (x:b). wp_f x ps post)

/// default effect is Tac : meaning, unannotated TAC functions will be
///                         typed as Tac a
///
/// And the bind combinator has range arguments
///   that will be provided when the effect is reified

[@@ default_effect "FStar.Tactics.Effect.Tac"; bind_has_range_args]
reflectable
effect {
  TAC (a:Type) (wp:tac_wp_t a)
  with { repr=tac_repr;
         return=tac_return;
         bind=tac_bind;
         if_then_else=tac_if_then_else;
         subcomp=tac_subcomp;
         close = tac_close }
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
let lift_div_tac_wp (#a:Type) (wp:pure_wp a) : tac_wp_t a =
  elim_pure_wp_monotonicity wp;  
  fun ps p -> wp (fun x -> p (Success x ps))

let lift_div_tac (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> DIV a wp)
  : tac_repr a (lift_div_tac_wp wp)
  = elim_pure_wp_monotonicity wp;
    fun ps -> Success (f ()) ps

sub_effect DIV ~> TAC = lift_div_tac

let get ()
  : TAC proofstate (fun ps post -> post (Success ps ps))
  = TAC?.reflect (fun ps -> Success ps ps)

let raise (#a:Type) (e:exn)
  : TAC a (fun ps post -> post (Failed e ps))
  = TAC?.reflect (fun ps -> Failed #a e ps)


/// assert p by t

val with_tactic (t : unit -> Tac unit) (p:Type u#a) : Type u#a

(* This syntactic marker will generate a goal of the shape x == ?u for
 * a new unification variable ?u, and run tactic [t] to solve this goal.
 * If after running [t], the uvar was solved and only trivial goals remain
 * in the proofstate, then `rewrite_with_tactic t x` will be replaced
 * by the solution of ?u *)
val rewrite_with_tactic (t:unit -> Tac unit) (#a:Type) (x:a) : a

(* This will run the tactic in order to (try to) produce a term of type
 * t. Note that the type looks dangerous from a logical perspective. It
 * should not lead to any inconsistency, however, as any time this term
 * appears during typechecking, it is forced to be fully applied and the
 * tactic is run. A failure of the tactic is a typechecking failure. It
 * can be thought as a language construct, and not a real function. *)
val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t

val assert_by_tactic (p:Type) (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic t (squash p)) (range_of t)))
         (ensures (fun _ -> p))

val by_tactic_seman (tau:unit -> Tac unit) (phi:Type)
  : Lemma (with_tactic tau phi ==> phi)

(* One can always bypass the well-formedness of metaprograms. It does
 * not matter as they are only run at typechecking time, and if they get
 * stuck, the compiler will simply raise an error. *)
let assume_safe (#a:Type) (tau:unit -> TacF a) : Tac a = admit (); tau ()

private let tac a b = a -> Tac b
private let tactic a = tac unit a

(* A hook to preprocess a definition before it is typechecked and
 * elaborated. This attribute should be used for top-level lets. The
 * tactic [tau] will be called on a quoting of the definition of the let
 * (if many, once for each) and the result of the tactic will replace
 * the definition. There are no goals involved, nor any proof obligation
 * to be done by the tactic. *)
val preprocess_with (tau : term -> Tac term) : Tot unit

(* A hook to postprocess a definition, after typechecking, and rewrite
 * it into a (provably equal) shape chosen by the user. This can be used
 * to implement custom transformations previous to extraction, such as
 * selective inlining. When ran added to a definition [let x = E], the
 * [tau] metaprogram is presented with a goal of the shape [E == ?u] for
 * a fresh uvar [?u]. The metaprogram should then both instantiate [?u]
 * and prove the equality. *)
val postprocess_with (tau : unit -> Tac unit) : Tot unit

(* Similar semantics to [postprocess_with], but the metaprogram only
 * runs before extraction, and hence typechecking and the logical
 * environment should not be affected at all. *)
val postprocess_for_extraction_with (tau : unit -> Tac unit) : Tot unit

#set-options "--no_tactics"

val unfold_with_tactic (t:unit -> Tac unit) (p:Type)
  : Lemma (requires p)
          (ensures (with_tactic t p))

val unfold_rewrite_with_tactic (t:unit -> Tac unit) (#a:Type) (p:a)
  : Lemma (rewrite_with_tactic t p == p)
