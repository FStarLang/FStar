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
open FStar.Ident

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


module C = FStar.Syntax.Const

let tconst l = mk (Tm_fvar(Syntax.lid_as_fv l Delta_constant None)) (Some Util.ktype0.n) Range.dummyRange
let tabbrev l = mk (Tm_fvar(Syntax.lid_as_fv l (Delta_defined_at_level 1) None)) (Some Util.ktype0.n) Range.dummyRange
let t_unit   = tconst C.unit_lid
let t_bool   = tconst C.bool_lid
let t_int    = tconst C.int_lid
let t_string = tconst C.string_lid
let t_float  = tconst C.float_lid
let t_char   = tabbrev C.char_lid
let t_range  = tconst C.range_lid

let rec delta_depth_greater_than l m = match l, m with 
    | Delta_constant, _ -> false
    | Delta_equational, _ -> true
    | _, Delta_equational -> false
    | Delta_defined_at_level i, Delta_defined_at_level j -> i > j
    | Delta_defined_at_level _, Delta_constant -> true 
    | Delta_abstract d, _ -> delta_depth_greater_than d m
    | _, Delta_abstract d -> delta_depth_greater_than l d

let rec decr_delta_depth = function
    | Delta_constant
    | Delta_equational -> None
    | Delta_defined_at_level 1 -> Some Delta_constant 
    | Delta_defined_at_level i -> Some (Delta_defined_at_level (i - 1))
    | Delta_abstract d -> decr_delta_depth d
