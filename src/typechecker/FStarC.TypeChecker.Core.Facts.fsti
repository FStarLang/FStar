(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core.Facts

(* Facts (see [Core.Base.facts]): what the typing of a term says about the
   term and its subterms, beyond its type. [do_check] computes the facts of
   a term from those of its subterms (its [sub_facts]) with [mk_facts], in
   the same pass as its type; they are assumed in the guards of subtypings
   of which the term is the witness (see [Core.Guard.witness_guard]), or
   that are in the scope of a [let] binding it. They are computed lazily,
   since most are never needed. *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad

(* [fs] without repetitions. Facts gathered from the types of subterms
   repeat themselves, e.g. the refinement of a variable used several
   times; stating each once keeps the VC small. *)
val dedup_facts (fs:list term) : ML (list term)

val no_facts_l (_:unit) : ML (Thunk.t (list term))

val no_facts (_:unit) : ML facts

val facts_concat (fs:list (Thunk.t (list term))) : ML (Thunk.t (list term))

(* What the type [t_a] of the pure term [a] says about it: its refinement,
   or the proposition it squashes, looking through definitions if
   [unfold_ok]. *)
val type_facts (g:env) (unfold_ok:bool) (a:term) (t_a:typ) : ML (list term)

(* The facts that [do_check] gathers from the subterms of a term, from
   which [mk_facts] makes the term's [facts]: [s_sub] is its [f_sub], and
   [s_tail] its [f_tail], if not its [f_term]. *)
type sub_facts = {
  s_sub : Thunk.t (list term);
  s_tail: option (Thunk.t (list term));
}

val no_sub_facts (_:unit) : ML sub_facts

(* For a term with no [let]s to end with, e.g. a function or a [match]. *)
val no_tail_facts (_:unit) : ML sub_facts

(* Those of a term wrapped (e.g. ascribed) in another, of the same value. *)
val inner_facts (f:facts) : sub_facts

(* The facts of [e], of effect [eff] and type [t], whose subterms have the
   facts [s]. *)
val mk_facts (g:env) (e:term) (eff:eff) (t:typ) (s:sub_facts) : ML facts

(* Those of [let x = def in body], from the facts of [def] and [body]: a
   pure [def] is substituted for [x], whose facts are those of [def];
   otherwise, those of [body] are closed over [x], of universe [u]. *)
val let_facts (pure_def:bool) (def:term) (x:bv) (u:universe) (fdef fbody:facts) : ML sub_facts

(* Those of [let rec xs = ... in body], of universes [us]: the facts of the
   body are closed over the recursive names. *)
val letrec_facts (xs:binders) (us:list universe) (fbody:facts) : ML sub_facts

(* For a term none of whose subterms has facts. *)
val no_sub (r:result (eff & typ)) : ML (result (eff & typ & sub_facts))
