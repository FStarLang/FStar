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

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

type tac_wp_t0 (a:Type) =
  (a -> Type0) -> Type0

unfold
let tac_wp_monotonic (#a:Type) (wp:tac_wp_t0 a) =
  forall (p q:a -> Type0).
    (forall x. p x ==> q x) ==> (wp p ==> wp q)

type tac_wp_t (a:Type) = wp:tac_wp_t0 a{tac_wp_monotonic wp}

let tac_repr (a:Type) (wp:tac_wp_t a) =
  ref_proofstate -> Dv a

unfold
let tac_return_wp (#a:Type) (x:a) : tac_wp_t a =
  fun post -> post x

(* monadic return *)
let tac_return (a:Type) (x:a) : tac_repr a (tac_return_wp x) =
  fun _ -> x

unfold
let tac_bind_wp (#a #b:Type) (wp_f:tac_wp_t a) (wp_g:a -> tac_wp_t b) : tac_wp_t b =
  fun post -> wp_f (fun r -> wp_g r post)

/// An optimization to name the continuation

unfold
let tac_wp_compact (a:Type) (wp:tac_wp_t a) : tac_wp_t a =
  fun post ->
  forall (k:a -> Type0). (forall (r:a).{:pattern (guard_free (k r))} post r ==> k r) ==> wp k


(* monadic bind *)
let tac_bind (a:Type) (b:Type)
  (wp_f:tac_wp_t a)
  (wp_g:a -> tac_wp_t b)
  (t1:tac_repr a wp_f)
  (t2:(x:a -> tac_repr b (wp_g x))) : tac_repr b (tac_wp_compact b (tac_bind_wp wp_f wp_g)) =
  fun ps ->
  let x = t1 ps in
  t2 x ps


unfold
let tac_if_then_else_wp (#a:Type) (wp_then:tac_wp_t a) (wp_else:tac_wp_t a) (b:bool)
  : tac_wp_t a
  = fun post -> (b ==> wp_then post) /\
                ((~ b) ==> wp_else post)

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
         (requires forall p. wp_g p ==> wp_f p)
         (ensures fun _ -> True)
  = f

let tac_close (a b:Type)
  (wp_f:b -> tac_wp_t a)
  (f:(x:b -> tac_repr a (wp_f x))) =

  tac_repr a (fun post -> forall (x:b). wp_f x post)

/// default effect is Tac : meaning, unannotated TAC functions will be
///                         typed as Tac a

[@@ default_effect "FStar.Tactics.Effect.Tac"]
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
effect TacH (a:Type) (pre : Type0) (post : a -> Tot Type0) =
    TAC a (fun post' -> pre /\ (forall r. post r ==> post' r))

(* "Total" variant *)
effect Tac (a:Type) = TacH a (requires True) (ensures fun _ -> True)

(* Metaprograms that succeed *)
effect TacS (a:Type) = Tac a

(* Always succeed, no effect *)
effect TacRO (a:Type) = Tac a

(* A variant that doesn't prove totality (nor type safety!) *)
effect TacF (a:Type) = TacH a (requires False) (ensures fun _ -> True)

unfold
let lift_div_tac_wp (#a:Type) (wp:pure_wp a) : tac_wp_t a =
  elim_pure_wp_monotonicity wp;  
  fun p -> wp (fun x -> p x)

val lift_div_tac_interleave_begin : unit
#push-options "--admit_smt_queries true"
let lift_div_tac (a:Type) (wp:pure_wp a) (f:unit -> DIV a wp)
  : tac_repr a (lift_div_tac_wp wp)
  = fun _ -> f ()
#pop-options
val lift_div_tac_interleave_end : unit

sub_effect DIV ~> TAC = lift_div_tac

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

(* When using [postprocess_with] or [postprocess_for_extraction_with]
 * this flag indicates that the type of the definition should also be
 * processed with the same tactic. *)
val postprocess_type : unit

#set-options "--no_tactics"

val unfold_with_tactic (t:unit -> Tac unit) (p:Type)
  : Lemma (requires p)
          (ensures (with_tactic t p))

val unfold_rewrite_with_tactic (t:unit -> Tac unit) (#a:Type) (p:a)
  : Lemma (rewrite_with_tactic t p == p)
