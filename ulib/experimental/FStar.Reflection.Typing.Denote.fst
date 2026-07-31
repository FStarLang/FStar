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
module FStar.Reflection.Typing.Denote

(* This module connects the concrete (range-carrying) builtin substitution
   [FStar.Stubs.Reflection.V2.Builtins.subst_term] on [term] with the ghost,
   structural substitution [FStar.Reflection.TermSpec.subst_term_spec] on the
   erasable model type [term_spec]. The central fact is [denote_subst_term]:

     denote_term (subst_term ss t) ==
       subst_term_spec (denote_term t) (denote_subst ss)

   i.e. [denote_term] is a homomorphism from the concrete substitution
   calculus to the spec one. [subst_term_spec] replaces the old ghost
   [Reflection.Typing.subst_term], whose only purpose was to specify the
   behavior of the real (builtin) substitution; we therefore take
   [denote_subst_term] as an axiom. Its soundness was validated by an
   explicit proof against a ghost [subst_term] model (see git history).

   TODO(universe-substs): the builtin [subst_t] admits universe
   substitutions [UN]/[UD], which the type theory formalized here does not
   (yet) model. We therefore restrict [denote_subst]/[denote_subst_term] to
   the *term-level* fragment [DB]/[DT]/[NM]/[NT] via the [term_level_subst]
   precondition. All current callers of the builtin (NamedView, Derived,
   MkProjectors, Pulse.Syntax.Naming) stay within this fragment; universe
   substitutions only appear inside [shift_subst], never applied to a term.
   If universe substitution on terms is ever needed, extend [term_spec]/
   [subst_term_spec] with universe substitution and drop the precondition. *)

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Reflection.TermSpec
module L = FStar.List.Tot
module SS = FStar.Stubs.Syntax.Syntax

let namedv_uniq (x:namedv) : nat = (inspect_namedv x).uniq

(* The term-level fragment of the builtin substitution: no universe
   substitutions, and non-negative de Bruijn indices. *)
let term_level_subst_elt (se:SS.subst_elt) : bool =
  match se with
  | SS.DB i _
  | SS.DT i _ -> i >= 0
  | SS.NM _ i -> i >= 0
  | SS.NT _ _ -> true
  | SS.UN _ _
  | SS.UD _ _ -> false

let term_level_subst (ss:SS.subst_t) : bool =
  L.for_all term_level_subst_elt ss

(* -------------------------------------------------------------------- *)
(* Denotation of a substitution: map each builtin term-level substitution
   element to its [subst_spec] counterpart. *)

let denote_subst_elt (se:SS.subst_elt { term_level_subst_elt se })
  : GTot subst_spec_elt =
  match se with
  | SS.DB i x -> DTs i (Ts_Var (namedv_uniq x))
  | SS.DT i t -> DTs i (denote_term t)
  | SS.NM x i -> NDs (namedv_uniq x) i
  | SS.NT x t -> NTs (namedv_uniq x) (denote_term t)

let rec denote_subst (ss:SS.subst_t { term_level_subst ss })
  : GTot subst_spec (decreases ss) =
  match ss with
  | [] -> []
  | se::ss -> denote_subst_elt se :: denote_subst ss

(* -------------------------------------------------------------------- *)
(* The central homomorphism, taken as an axiom (see module comment). *)

assume
val denote_subst_term (ss:SS.subst_t { term_level_subst ss }) (t:term)
  : Lemma (denote_term (subst_term ss t)
           == subst_term_spec (denote_term t) (denote_subst ss))
