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
module FStar.Tactics.V1.Logic

open FStar.Tactics.Effect
open FStar.Reflection.V1
open FStar.Reflection.V1.Formula
open FStar.Tactics.V1.Logic.Lemmas {} (* bring lemmas into TC scope *)

(* Repeated to avoid importing FStar.Tactics.V1.Derived. *)
private let cur_goal () : Tac typ =
  let open FStar.Stubs.Tactics.Types in
  let open FStar.Stubs.Tactics.V1.Builtins in
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
val l_revert_all (bs:binders) : Tac unit

(** Introduce a forall. *)
[@@plugin]
val forall_intro () : Tac binder

(** Introduce a forall, with some given name. *)
[@@plugin]
val forall_intro_as (s:string) : Tac binder

(** Repeated [forall_intro]. *)
[@@plugin]
val forall_intros () : Tac binders

(** Split a conjunction into two goals. *)
[@@plugin]
val split () : Tac unit

(** Introduce an implication. *)
[@@plugin]
val implies_intro () : Tac binder

[@@plugin]
val implies_intro_as (s:string) : Tac binder

(** Repeated [implies_intro]. *)
[@@plugin]
val implies_intros () : Tac binders

(** "Logical" intro: introduce a forall or an implication. *)
[@@plugin]
val l_intro () : Tac binder

(** Repeated [l]. *)
[@@plugin]
val l_intros () : Tac (list binder)

[@@plugin]
val squash_intro () : Tac unit

[@@plugin]
val l_exact (t:term) : Tac unit

[@@plugin]
val hyp (b:binder) : Tac unit

[@@plugin]
val pose_lemma (t : term) : Tac binder

[@@plugin]
val explode () : Tac unit

[@@plugin]
val simplify_eq_implication () : Tac unit

[@@plugin]
val rewrite_all_equalities () : Tac unit

[@@plugin]
val unfold_definition_and_simplify_eq (tm:term) : Tac unit

(** A tactic to unsquash a hypothesis. Perhaps you are looking
for [unsquash_term]. *)
[@@plugin]
val unsquash (t:term) : Tac term

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
val destruct_and (t : term) : Tac (binder & binder)

[@@plugin]
val witness (t : term) : Tac unit

(* returns witness and proof as binders *)
[@@plugin]
val elim_exists (t : term) : Tac (binder & binder)

[@@plugin]
val instantiate (fa : term) (x : term) : Tac binder

[@@plugin]
val instantiate_as (fa : term) (x : term) (s : string) : Tac binder

[@@plugin]
val skolem () : Tac (list (binders & binder))

[@@plugin]
val easy_fill () : Tac unit

[@@plugin]
val easy : #a:Type -> (#[easy_fill ()] _ : a) -> a

(** Add a lemma into the local context, quantified for all arguments.
Only works for lemmas with up to 3 arguments for now. It is expected
that `t` is a top-level name, this has not been battle-tested for other
kinds of terms. *)
[@@plugin]
val using_lemma (t : term) : Tac binder