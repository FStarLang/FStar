﻿(*
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
open FStar.All

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Ident

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
    identifier_ty:typ
}
let rec insert_col_info col info col_infos =
    match col_infos with 
    | [] -> [col, info]
    | (c,i)::rest -> 
      if col < c 
      then (col, info)::col_infos
      else (c, i)::insert_col_info col info rest
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
let mk_info id ty = {
    identifier=id;
    identifier_ty=ty;
}
let file_info_table : file_info = BU.smap_create 50 //50 files
open FStar.Range
let insert_identifier_info id ty range =
    let info = mk_info id ty in
    let use_range = {range with def_range=range.use_range} in //key the lookup table from the use range
    let fn = Range.file_of_range use_range in
    let start = Range.start_of_range use_range in 
    let row, col = Range.line_of_pos start, Range.col_of_pos start in
    match BU.smap_try_find file_info_table fn with
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
let info_at_pos (fn:string) (row:int) (col:int) : option<identifier_info> =
    match BU.smap_try_find file_info_table fn with
    | None -> None
    | Some rows -> 
      match BU.imap_try_find rows row with 
      | None -> None
      | Some cols -> 
        match find_nearest_preceding_col_info col !cols with
        | None -> None
        | Some ci -> Some ci//(info_as_string ci)
let insert_bv bv ty = insert_identifier_info (Inl bv) ty (FStar.Syntax.Syntax.range_of_bv bv)
let insert_fv fv ty = insert_identifier_info (Inr fv) ty (FStar.Syntax.Syntax.range_of_fv fv)


