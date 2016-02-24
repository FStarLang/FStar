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
module FStar.TypeChecker.Common

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax

(* relations on types, kinds, etc. *)
type rel =
  | EQ
  | SUB
  | SUBINV  (* sub-typing/sub-kinding, inverted *)

type problem<'a,'b> = {               //Try to prove: lhs rel rhs ~> guard
    pid:int;
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
type univ_ineq = universe * universe


