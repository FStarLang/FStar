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

let as_tprob = function
   | TProb p -> p
   | _ -> failwith "Expected a TProb"

type probs = list<prob>

type guard_formula =
  | Trivial
  | NonTrivial of formula

type deferred = list<(string * prob)>
type univ_ineq = universe * universe


module C = FStar.Parser.Const

let mk_by_tactic tac f =
    let t_by_tactic = S.mk_Tm_uinst (tabbrev C.by_tactic_lid) [U_zero] in
    let t_reify_tactic = S.mk_Tm_uinst (tabbrev C.reify_tactic_lid) [U_zero] in
    let tac = S.mk_Tm_app t_reify_tactic [S.iarg t_unit; S.as_arg tac]
                           None Range.dummyRange in
    S.mk_Tm_app t_by_tactic [S.iarg t_unit; S.as_arg tac; S.as_arg f] None Range.dummyRange

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

let insert_col_info col info col_infos =
    // Tail recursive helper
    let rec __insert aux rest =
        match rest with
        | [] -> (aux, [col, info])
        | (c,i)::rest' ->
          if col < c
          then (aux, (col, info)::rest)
          else __insert ((c,i)::aux) rest'
     in
     let l, r = __insert [] col_infos
     in (List.rev l) @ r

let find_nearest_preceding_col_info col col_infos =
    let rec aux out = function
        | [] -> out
        | (c, i)::rest ->
          if c > col then out
          else aux (Some i) rest
    in
    aux None col_infos

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

let id_info_table_empty =
    { id_info_enabled = false;
      id_info_db = BU.psmap_empty ();
      id_info_buffer = [] }

open FStar.Range

let id_info__insert ty_map db info =
    let range = info.identifier_range in
    let use_range = { range with def_range = range.use_range } in
    let info = { info with identifier_range = use_range;
                           identifier_ty = ty_map info.identifier_ty } in

    let fn = file_of_range use_range in
    let start = start_of_range use_range in
    let row, col = line_of_pos start, col_of_pos start in

    let rows = BU.psmap_find_default db fn (BU.pimap_empty ()) in
    let cols = BU.pimap_find_default rows row [] in

    insert_col_info col info cols
    |> BU.pimap_add rows row
    |> BU.psmap_add db fn

let id_info_insert table id ty range =
    let info = { identifier = id; identifier_ty = ty; identifier_range = range} in
    { table with id_info_buffer = info :: table.id_info_buffer }

let id_info_insert_bv table bv ty =
    if table.id_info_enabled then id_info_insert table (Inl bv) ty (range_of_bv bv)
    else table

let id_info_insert_fv table fv ty =
    if table.id_info_enabled then id_info_insert table (Inr fv) ty (range_of_fv fv)
    else table

let id_info_toggle table enabled =
    { table with id_info_enabled = enabled && FStar.Options.ide () }

let id_info_promote table ty_map =
    { table with
      id_info_buffer = [];
      id_info_db = List.fold_left (id_info__insert ty_map)
                     table.id_info_db table.id_info_buffer }

let id_info_at_pos (table: id_info_table) (fn:string) (row:int) (col:int) : option<identifier_info> =
    let rows = BU.psmap_find_default table.id_info_db fn (BU.pimap_empty ()) in
    let cols = BU.pimap_find_default rows row [] in

    match find_nearest_preceding_col_info col cols with
    | None -> None
    | Some info ->
      let last_col = col_of_pos (end_of_range info.identifier_range) in
      if col <= last_col then Some info else None
