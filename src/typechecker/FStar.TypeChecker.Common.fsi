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
open Prims
open FStar.ST
open FStar.All

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Ident
module S = FStar.Syntax.Syntax

module BU = FStar.Util

(* relations on types, kinds, etc. *)
type rel =
  | EQ
  | SUB
  | SUBINV  (* sub-typing/sub-kinding, inverted *)

type rank_t =
    | Rigid_rigid
    | Flex_rigid_eq
    | Flex_flex_pattern_eq
    | Flex_rigid
    | Rigid_flex
    | Flex_flex

type problem<'a> = {                  //Try to prove: lhs rel rhs ~> guard
    pid:int;
    lhs:'a;
    relation:rel;
    rhs:'a;
    element:option<bv>;               //where, guard is a predicate on this term (which appears free in/is a subterm of the guard)
    logical_guard:term;               //the condition under which this problem is solveable; (?u v1..vn)
    logical_guard_uvar:ctx_uvar;
    reason: list<string>;             //why we generated this problem, for error reporting
    loc: Range.range;                 //and the source location where this arose
    rank: option<rank_t>;
}

type prob =
  | TProb of problem<typ>
  | CProb of problem<comp>

val as_tprob : prob -> problem<typ>

type probs = list<prob>

type guard_formula =
  | Trivial
  | NonTrivial of formula

val check_uvar_ctx_invariant : string -> Range.range -> bool -> gamma -> binders -> unit

type deferred = list<(string * prob)>
type univ_ineq = universe * universe

val mk_by_tactic : term -> term -> term

val delta_depth_greater_than : delta_depth -> delta_depth -> bool
val decr_delta_depth : delta_depth -> option<delta_depth>

(***********************************************************************************)
(* A table of file -> starting row -> starting col -> identifier info              *)
(* Used to support querying information about an identifier in interactive mode    *)
(*    The table provides:                                                          *)
(*          -- the full name of the identifier                                     *)
(*          -- the source range of its use                                         *)
(*          -- the source range of its defining occurrence                         *)
(*          -- its type                                                            *)
(***********************************************************************************)

type identifier_info = {
    identifier:either<bv, fv>;
    identifier_ty:typ;
    identifier_range:Range.range;
}

val insert_col_info : int -> identifier_info -> list<(int * identifier_info)> -> list<(int * identifier_info)>
val find_nearest_preceding_col_info : int -> list<(int * identifier_info)> -> option<identifier_info>

type id_info_by_col = //sorted in ascending order of columns
    list<(int * identifier_info)>

type col_info_by_row =
    BU.pimap<id_info_by_col>

type row_info_by_file =
    BU.psmap<col_info_by_row>

type id_info_table = {
    id_info_enabled: bool;
    id_info_db: row_info_by_file;
    id_info_buffer: list<identifier_info>;
}
val id_info_table_empty : id_info_table

val id_info_insert_bv : id_info_table -> bv -> typ -> id_info_table
val id_info_insert_fv : id_info_table -> fv -> typ -> id_info_table
val id_info_toggle    : id_info_table -> bool -> id_info_table
val id_info_promote   : id_info_table -> (typ -> typ) -> id_info_table
val id_info_at_pos    : id_info_table -> string -> int -> int -> option<identifier_info>

// Reason, term and uvar, and (rough) position where it is introduced
// The term is just a Tm_uvar of the ctx_uvar
type implicit = {
    imp_reason : string;                  // Reason (in text) why the implicit was introduced
    imp_uvar   : ctx_uvar;                // The ctx_uvar representing it
    imp_tm     : term;                    // The term, made up of the ctx_uvar
    imp_range  : Range.range;             // Position where it was introduced
}
type implicits = list<implicit>

type guard_t = {
  guard_f:    guard_formula;
  deferred:   deferred;
  univ_ineqs: list<universe> * list<univ_ineq>;
  implicits:  implicits;
}

val trivial_guard : guard_t

val conj_guard    : guard_t -> guard_t -> guard_t
val check_trivial : term -> guard_formula
val imp_guard     : guard_t -> guard_t -> guard_t
val conj_guards   : list<guard_t> -> guard_t


type lcomp = { //a lazy computation
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflag>;
    comp_thunk: ref<(either<(unit -> (comp * guard_t)), comp>)>
}

val mk_lcomp:
    eff_name: lident ->
    res_typ: typ ->
    cflags: list<cflag> ->
    comp_thunk: (unit -> (comp * guard_t)) -> lcomp

val lcomp_comp: lcomp -> (comp * guard_t)
val apply_lcomp : (comp -> comp) -> (guard_t -> guard_t) -> lcomp -> lcomp
val lcomp_to_string : lcomp -> string
val lcomp_set_flags : lcomp -> list<S.cflag> -> lcomp
val is_total_lcomp : lcomp -> bool
val is_tot_or_gtot_lcomp : lcomp -> bool
val is_lcomp_partial_return : lcomp -> bool
val is_pure_lcomp : lcomp -> bool
val is_pure_or_ghost_lcomp : lcomp -> bool
val set_result_typ_lc : lcomp -> typ -> lcomp
val residual_comp_of_lcomp : lcomp -> residual_comp
val lcomp_of_comp : comp -> lcomp
