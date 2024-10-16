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
module FStar.Tactics.V2.Logic

open FStar.Tactics.Effect
open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Tactics.NamedView
open FStar.Tactics.V1.Logic.Lemmas {} (* bring lemmas into TC scope *)

(* Repeated to avoid importing FStar.Tactics.V1.Derived. *)
private let cur_goal () : Tac typ =
  let open FStar.Stubs.Tactics.Types in
  let open FStar.Stubs.Tactics.V2.Builtins in
  match goals_of (get ()) with
  | g::_ -> goal_type g
  | _ -> raise (TacticFailure (mkmsg "no more goals", None))

(** Returns the current goal as a [formula]. *)
let cur_formula () : Tac formula = term_as_formula (cur_goal ())

(** Revert an introduced binder as a forall. *)
[@@plugin]
val l_revert () : Tac unit

(** Repeated [l_revert]. *)
[@@plugin]
val l_revert_all (bs:list binding) : Tac unit

(** Introduce a forall. *)
[@@plugin]
val forall_intro () : Tac binding

(** Introduce a forall, with some given name. *)
[@@plugin]
val forall_intro_as (s:string) : Tac binding

(** Repeated [forall_intro]. *)
[@@plugin]
val forall_intros () : Tac (list binding)

(** Split a conjunction into two goals. *)
[@@plugin]
val split () : Tac unit

(** Introduce an implication. *)
[@@plugin]
val implies_intro () : Tac binding

[@@plugin]
val implies_intro_as (s:string) : Tac binding

(** Repeated [implies_intro]. *)
[@@plugin]
val implies_intros () : Tac (list binding)

(** "Logical" intro: introduce a forall or an implication. *)
[@@plugin]
val l_intro () : Tac binding

(** Repeated [l]. *)
[@@plugin]
val l_intros () : Tac (list binding)

[@@plugin]
val squash_intro () : Tac unit

[@@plugin]
val l_exact (t:term) : Tac unit

// FIXME: should this take a binding? It's less general...
// but usually what we want. Coercions could help.
[@@plugin]
val hyp (x:namedv) : Tac unit

[@@plugin]
val pose_lemma (t : term) : Tac binding

[@@plugin]
val explode () : Tac unit

[@@plugin]
val simplify_eq_implication () : Tac unit

[@@plugin]
val rewrite_all_equalities () : Tac unit

[@@plugin]
val unfold_definition_and_simplify_eq (tm:term) : Tac unit

(** A tactic to unsquash a hypothesis. Perhaps you are looking
for [unsquash_term].

Pre:
  goal =
    G |- e : squash s
    t : squash r

Post:
    G, x:r |- e : squash s
    `x` is returned as a term
*)
[@@plugin]
val unsquash (t : term) : Tac term

[@@plugin]
val cases_or (o:term) : Tac unit

[@@plugin]
val cases_bool (b:term) : Tac unit

[@@plugin]
val left () : Tac unit

[@@plugin]
val right () : Tac unit

[@@plugin]
val and_elim (t : term) : Tac unit

[@@plugin]
val destruct_and (t : term) : Tac (binding & binding)

[@@plugin]
val witness (t : term) : Tac unit

(* returns witness and proof as binders *)
[@@plugin]
val elim_exists (t : term) : Tac (binding & binding)

[@@plugin]
val instantiate (fa : term) (x : term) : Tac binding

[@@plugin]
val instantiate_as (fa : term) (x : term) (s : string) : Tac binding

[@@plugin]
val skolem () : Tac (list (list binding & binding))

[@@plugin]
val easy_fill () : Tac unit

(* We mark this as a plugin so it can reduce. Some kind of 'transparent' attribute
would be better. `inline_for_extraction` is almost that? *)
[@@plugin]
val easy : #a:Type -> (#[easy_fill ()] _ : a) -> a

(** Add a lemma into the local context, quantified for all arguments.
Only works for lemmas with up to 3 arguments for now. It is expected
that `t` is a top-level name, this has not been battle-tested for other
kinds of terms. *)
[@@plugin]
val using_lemma (t : term) : Tac binding
