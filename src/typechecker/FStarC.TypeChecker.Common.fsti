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
module FStarC.TypeChecker.Common

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Class.Show
open FStarC.Class.Monoid
open FStarC.CList
open FStarC.Range.Type

module S = FStarC.Syntax.Syntax


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

type problem 'a = {                  //Try to prove: lhs rel rhs ~ guard
    pid:int;
    lhs:'a;
    relation:rel;
    rhs:'a;
    element:option bv;               //where, guard is a predicate on this term (which appears free in/is a subterm of the guard)
    logical_guard:term;               //the condition under which this problem is solveable; (?u v1..vn)
    logical_guard_uvar:ctx_uvar;
    reason: list string;             //why we generated this problem, for error reporting
    loc: range;                 //and the source location where this arose
    rank: option rank_t;
    logical : bool;                             //logical problems cannot unfold connectives
}

type prob =
  | TProb of problem typ
  | CProb of problem comp
type prob_t = prob

val as_tprob : prob -> problem typ

type probs = list prob

type guard_formula =
  | Trivial
  | NonTrivial of formula

instance val showable_guard_formula : showable guard_formula

type deferred_reason =
  | Deferred_univ_constraint
  | Deferred_occur_check_failed
  | Deferred_first_order_heuristic_failed
  | Deferred_flex
  | Deferred_free_names_check_failed
  | Deferred_not_a_pattern
  | Deferred_flex_flex_nonpattern
  | Deferred_delay_match_heuristic
  | Deferred_to_user_tac

instance val showable_deferred_reason : showable deferred_reason

type deferred = clist (deferred_reason & string & prob)

type univ_ineq = universe & universe

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
    identifier:either bv fv;
    identifier_ty:typ;
    identifier_range:range;
}

type id_info_by_col = //sorted in ascending order of columns
    list (int & identifier_info)

type col_info_by_row =
    PIMap.t id_info_by_col

type row_info_by_file =
    PSMap.t col_info_by_row

type id_info_table = {
    id_info_enabled: bool;
    id_info_db: row_info_by_file;
    id_info_buffer: list identifier_info;
}

val check_uvar_ctx_invariant : string -> range -> bool -> gamma -> binders -> unit

val mk_by_tactic : term -> term -> term

val delta_depth_greater_than : delta_depth -> delta_depth -> bool
val decr_delta_depth : delta_depth -> option delta_depth

val insert_col_info : int -> identifier_info -> list (int & identifier_info) -> list (int & identifier_info)
val find_nearest_preceding_col_info : int -> list (int & identifier_info) -> option identifier_info

val id_info_table_empty : id_info_table

val id_info_insert_bv : id_info_table -> bv -> typ -> id_info_table
val id_info_insert_fv : id_info_table -> fv -> typ -> id_info_table
val id_info_toggle    : id_info_table -> bool -> id_info_table
val id_info_promote   : id_info_table -> (typ -> option typ) -> id_info_table
val id_info_at_pos    : id_info_table -> string -> int -> int -> option identifier_info

// Reason, term and uvar, and (rough) position where it is introduced
// The term is just a Tm_uvar of the ctx_uvar
type implicit = {
    imp_reason : string;                  // Reason (in text) why the implicit was introduced
    imp_uvar   : ctx_uvar;                // The ctx_uvar representing it
    imp_tm     : term;                    // The term, made up of the ctx_uvar
    imp_range  : range;                   // Position where it was introduced
}

instance val showable_implicit : showable implicit

(* Bad naming here *)
type implicits = list implicit
val implicits_to_string : implicits -> string
type implicits_t = CList.t implicit

type guard_t = {
  guard_f:    guard_formula;
  deferred_to_tac: deferred; //This field maintains problems that are to be dispatched to a tactic
                             //They are never attempted by the unification engine in Rel
  deferred:   deferred;
  univ_ineqs: clist universe & clist univ_ineq;
  implicits:  implicits_t;
}

val trivial_guard : guard_t
val conj_guard    : guard_t -> guard_t -> guard_t

instance val monoid_guard_t : monoid guard_t (* conj_guard, trivial_guard *)

val check_trivial : term -> guard_formula
val imp_guard     : guard_t -> guard_t -> guard_t
val conj_guards   : list guard_t -> guard_t

// splits the guard into the logical component (snd in the returned tuple)
//   and the rest (fst in the returned tuple)
val split_guard   : guard_t -> guard_t & guard_t

val weaken_guard_formula: guard_t -> typ -> guard_t
type lcomp = { //a lazy computation
    eff_name: lident;
    res_typ: typ;
    cflags: list cflag;
    comp_thunk: ref (either (unit -> (comp & guard_t)) comp)
}

val mk_lcomp:
    eff_name: lident ->
    res_typ: typ ->
    cflags: list cflag ->
    comp_thunk: (unit -> (comp & guard_t)) -> lcomp

val lcomp_comp: lcomp -> (comp & guard_t)
val apply_lcomp : (comp -> comp) -> (guard_t -> guard_t) -> lcomp -> lcomp
val lcomp_to_string : lcomp -> string (* CAUTION! can have side effects of forcing the lcomp *)
val lcomp_set_flags : lcomp -> list S.cflag -> lcomp
val is_total_lcomp : lcomp -> bool
val is_tot_or_gtot_lcomp : lcomp -> bool
val is_lcomp_partial_return : lcomp -> bool
val is_pure_lcomp : lcomp -> bool
val is_pure_or_ghost_lcomp : lcomp -> bool
val set_result_typ_lc : lcomp -> typ -> lcomp
val residual_comp_of_lcomp : lcomp -> residual_comp
val lcomp_of_comp_guard : comp -> guard_t -> lcomp
//lcomp_of_comp_guard with trivial guard
val lcomp_of_comp : comp -> lcomp

val check_positivity_qual (subtyping:bool) (p0 p1:option positivity_qualifier)
  : bool
