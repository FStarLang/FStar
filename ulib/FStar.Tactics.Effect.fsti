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

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Tactics.Types

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

(* The representation of a tactic: a function from a proofstate to a
   (possibly divergent) result.  This plays no role in typechecking;
   it is only used for extraction and reification. *)
inline_for_extraction
let tac_repr (a:Type) : Type = ref_proofstate -> Dv a

(* monadic return *)
inline_for_extraction
let tac_return (a:Type) (x:a) : tac_repr a =
  fun _ -> x

(* monadic bind *)
inline_for_extraction
let tac_bind (a:Type) (b:Type) (t1:tac_repr a) (t2:(a -> tac_repr b)) : tac_repr b =
  fun ps ->
  let x = t1 ps in
  t2 x ps

/// default effect is Tac : meaning, unannotated TAC functions will be
///                         typed as Tac a

[@@ default_effect "FStar.Tactics.Effect.Tac"]
reflectable
effect { TAC with { repr = tac_repr; return = tac_return; bind = tac_bind } }

(* Hoare variant *)
effect TacH (a:Type) = TAC a

(* "Total" variant *)
effect Tac (a:Type) = TAC a

(* Metaprograms that succeed *)
effect TacS (a:Type) = TAC a

(* Always succeed, no effect *)
effect TacRO (a:Type) = TAC a

(* A variant that doesn't prove totality (nor type safety!) *)
effect TacF (a:Type) = TAC a (requires False)

val lift_div_tac_interleave_begin : unit
#push-options "--admit_smt_queries true"
inline_for_extraction
let lift_div_tac (a:Type) (f:unit -> Dv a) : tac_repr a
  = fun _ -> f ()
#pop-options
val lift_div_tac_interleave_end : unit

sub_effect DIV ~> TAC = lift_div_tac

/// assert p by t

val with_tactic (t : unit -> Tac unit) (p:prop) : prop

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

val assert_by_tactic (p:prop) (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic t p) (range_of t)))
         (ensures (fun _ -> p))

val by_tactic_seman (tau:unit -> Tac unit) (phi:prop)
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

val unfold_with_tactic (t:unit -> Tac unit) (p:prop)
  : Lemma (requires p)
          (ensures (with_tactic t p))

val unfold_rewrite_with_tactic (t:unit -> Tac unit) (#a:Type) (p:a)
  : Lemma (rewrite_with_tactic t p == p)
