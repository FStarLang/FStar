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

type probs = list<prob>

type guard_formula =
  | Trivial
  | NonTrivial of formula

type deferred = list<(string * prob)>
type univ_ineq = universe * universe


module C = FStar.Parser.Const

let tconst l = mk (Tm_fvar(S.lid_as_fv l Delta_constant None)) None Range.dummyRange
let tabbrev l = mk (Tm_fvar(S.lid_as_fv l (Delta_defined_at_level 1) None)) None Range.dummyRange
let t_unit   = tconst C.unit_lid
let t_bool   = tconst C.bool_lid
let t_int    = tconst C.int_lid
let t_string = tconst C.string_lid
let t_float  = tconst C.float_lid
let t_char   = tabbrev C.char_lid
let t_range  = tconst C.range_lid
let t_tactic_unit = S.mk_Tm_app (S.mk_Tm_uinst (tabbrev C.tactic_lid) [U_zero]) [S.as_arg t_unit] None Range.dummyRange


let t_list_of t = S.mk_Tm_app (S.mk_Tm_uinst (tabbrev C.list_lid) [U_zero]) [S.as_arg t] None Range.dummyRange
let t_option_of t = S.mk_Tm_app (S.mk_Tm_uinst (tabbrev C.option_lid) [U_zero]) [S.as_arg t] None Range.dummyRange

let unit_const = S.mk (S.Tm_constant FStar.Const.Const_unit) None Range.dummyRange
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
type col_info = //sorted in ascending order of columns
    list<(int * identifier_info)>
type row_info =
    BU.imap<ref<col_info>>
type file_info =
    BU.smap<row_info>
let mk_info id ty range = {
    identifier=id;
    identifier_ty=ty;
    identifier_range=range
}
let file_info_table : file_info = BU.smap_create 50 //50 files
open FStar.Range
let insert_identifier_info id ty range =
    let use_range = {range with def_range=range.use_range} in //key the lookup table from the use range
    let info = mk_info id ty use_range in
    let fn = Range.file_of_range use_range in
    let start = Range.start_of_range use_range in
    let row, col = Range.line_of_pos start, Range.col_of_pos start in
    begin match BU.smap_try_find file_info_table fn with
    | None ->
      let col_info = BU.mk_ref (insert_col_info col info []) in
      let rows = BU.imap_create 1000 in //1000 rows per file
      BU.imap_add rows row col_info;
      BU.smap_add file_info_table fn rows
    | Some file_rows -> begin
      match BU.imap_try_find file_rows row with
      | None ->
        let col_info = BU.mk_ref (insert_col_info col info []) in
        BU.imap_add file_rows row col_info
      | Some col_infos ->
        col_infos := insert_col_info col info !col_infos
      end
    end;
    fn, row, col
let info_at_pos (fn:string) (row:int) (col:int) : option<identifier_info> =
    match BU.smap_try_find file_info_table fn with
    | None -> None
    | Some rows ->
      match BU.imap_try_find rows row with
      | None -> None
      | Some cols ->
        match find_nearest_preceding_col_info col !cols with
        | None -> None
        | Some ci ->
          // Check that `col` is in `ci.identifier_range`
          let last_col = Range.col_of_pos (Range.end_of_range ci.identifier_range) in
          if col <= last_col then Some ci else None
type insert_id_info_ops = {
    enable:bool -> unit;
    bv:bv -> typ -> unit;
    fv:fv -> typ -> unit;
    promote:(typ -> typ) -> unit;
}
let insert_id_info =
    let enabled = BU.mk_ref false in
    let id_info_buffer : ref<(list<(either<bv,fv>*typ*Range.range)>)> = BU.mk_ref [] in
    let enable b = enabled := FStar.Options.ide() && b in
    let bv x t = if !enabled then id_info_buffer := (Inl x, t, range_of_bv x)::!id_info_buffer in
    let fv x t = if !enabled then id_info_buffer := (Inr x, t, range_of_fv x)::!id_info_buffer in
    let promote cb =
        !id_info_buffer |> List.iter (fun (i, t, r) -> ignore <| insert_identifier_info i (cb t) r);
        id_info_buffer := [] in
    {enable=enable;
     bv=bv;
     fv=fv;
     promote=promote}
