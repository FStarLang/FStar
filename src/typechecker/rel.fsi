(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module FStar.TypeChecker.Rel

open FStar
open FStar.Util
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax

(* relations on types, kinds, etc. *)
type rel =
  | EQ
  | SUB
  | SUBINV  (* sub-typing/sub-kinding, inverted *)

type problem<'a,'b> = {               //Try to prove: lhs rel rhs ~> guard
    lhs:'a;
    relation:rel;
    rhs:'a;
    element:option<'b>;               //where, guard is a predicate on this term (which appears free in/is a subterm of the guard)
    logical_guard:(term * term);      //the condition under which this problem is solveable; (uv x1 ... xn, uv)
    scope:binders;                    //the set of names permissible in the guard of this formula
    reason: list<string>;             //why we generated this problem, for error reporting
    loc: Range.range;                 //and the source location where this arose
    rank: option<int>;
}

type prob =
  | TProb of problem<typ,term>
  | CProb of problem<comp,unit>

type probs = list<prob>

type guard_formula =
  | Trivial
  | NonTrivial of formula

type deferred = list<(string * prob)>

type implicits = list<(uvar * Range.range)>

type guard_t = {
  guard_f:  guard_formula;
  deferred: deferred;
  implicits: implicits;
}

val new_uvar: Range.range -> binders -> typ -> typ * typ

val close_guard               : binders -> guard_t -> guard_t
val apply_guard               : guard_t -> term -> guard_t
val trivial_guard             : guard_t
val is_trivial                : guard_t -> bool
val conj_guard                : guard_t -> guard_t -> guard_t
val imp_guard                 : guard_t -> guard_t -> guard_t
val guard_of_guard_formula    : guard_formula -> guard_t
val guard_form                : guard_t -> guard_formula
val guard_to_string           : env -> guard_t -> string
val simplify_guard            : env -> guard_t -> guard_t
val solve_deferred_constraints: env -> guard_t -> guard_t
val try_discharge_guard       : env -> guard_t -> unit 

val unrefine   : env -> typ -> typ
val try_teq    : env -> typ -> typ -> option<guard_t>
val teq        : env -> typ -> typ -> guard_t
val try_subtype: env -> typ -> typ -> option<guard_t>
val subtype    : env -> typ -> typ -> guard_t
val sub_comp   : env -> comp -> comp -> option<guard_t>

val universe_inequality : universe -> universe -> guard_t

val subtype_fail: env -> typ -> typ -> 'a
