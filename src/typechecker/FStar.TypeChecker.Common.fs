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
module Print = FStar.Syntax.Print
module U = FStar.Syntax.Util

module BU = FStar.Util
module PC = FStar.Parser.Const

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
    S.mk_Tm_app t_by_tactic [S.as_arg tac; S.as_arg f] None Range.dummyRange

let rec delta_depth_greater_than l m = match l, m with
    | Delta_equational_at_level i, Delta_equational_at_level j -> i > j
    | Delta_constant_at_level i,   Delta_constant_at_level j   -> i > j
    | Delta_abstract d, _                                      -> delta_depth_greater_than d m
    | _, Delta_abstract d                                      -> delta_depth_greater_than l d
    | Delta_equational_at_level _, _                           -> true
    | _, Delta_equational_at_level _                           -> false

let rec decr_delta_depth = function
    | Delta_constant_at_level 0
    | Delta_equational_at_level 0 -> None
    | Delta_constant_at_level i   -> Some (Delta_constant_at_level (i - 1))
    | Delta_equational_at_level i -> Some (Delta_equational_at_level (i - 1))
    | Delta_abstract d            -> decr_delta_depth d

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

let insert_col_info (col:int) (info:identifier_info) (col_infos:list<(int * identifier_info)>) =
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

let find_nearest_preceding_col_info (col:int) (col_infos:list<(int * identifier_info)>) =
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
    let use_range = Range.set_def_range range (Range.use_range range) in
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
    { table with id_info_enabled = enabled }

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

let check_uvar_ctx_invariant (reason:string) (r:range) (should_check:bool) (g:gamma) (bs:binders) =
    let print_gamma gamma =
        (gamma |> List.map (function
          | Binding_var x -> "Binding_var " ^ (Print.bv_to_string x)
          | Binding_univ u -> "Binding_univ " ^ u.idText
          | Binding_lid (l, _) -> "Binding_lid " ^ (Ident.string_of_lid l)))//  @
    // (env.gamma_sig |> List.map (fun (ls, _) ->
    //     "Binding_sig " ^ (ls |> List.map Ident.string_of_lid |> String.concat ", ")
    // ))
      |> String.concat "::\n"
     in
     let fail () =
         failwith (BU.format5
                   "Invariant violation: gamma and binders are out of sync\n\t\
                               reason=%s, range=%s, should_check=%s\n\t
                               gamma=%s\n\t\
                               binders=%s\n"
                               reason
                               (Range.string_of_range r)
                               (if should_check then "true" else "false")
                               (print_gamma g)
                               (FStar.Syntax.Print.binders_to_string ", " bs))
     in
     if not should_check then ()
     else match BU.prefix_until (function Binding_var _ -> true | _ -> false) g, bs with
     | None, [] -> ()
     | Some (_, hd, gamma_tail), _::_ ->
       let _, (x, _) = BU.prefix bs in
       begin
       match hd with
       | Binding_var x' when S.bv_eq x x' ->
         ()
       | _ -> fail()
        end
     | _ -> fail()

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

let trivial_guard = {guard_f=Trivial; deferred=[]; univ_ineqs=([], []); implicits=[]}

let conj_guard_f g1 g2 = match g1, g2 with
  | Trivial, g
  | g, Trivial -> g
  | NonTrivial f1, NonTrivial f2 -> NonTrivial (U.mk_conj f1 f2)

let check_trivial t = match (U.unmeta t).n with
    | Tm_fvar tc when S.fv_eq_lid tc PC.true_lid -> Trivial
    | _ -> NonTrivial t

let imp_guard_f g1 g2 = match g1, g2 with
  | Trivial, g -> g
  | g, Trivial -> Trivial
  | NonTrivial f1, NonTrivial f2 ->
    let imp = U.mk_imp f1 f2 in check_trivial imp

let binop_guard f g1 g2 = {guard_f=f g1.guard_f g2.guard_f;
                           deferred=g1.deferred@g2.deferred;
                           univ_ineqs=(fst g1.univ_ineqs@fst g2.univ_ineqs,
                                       snd g1.univ_ineqs@snd g2.univ_ineqs);
                           implicits=g1.implicits@g2.implicits}
let conj_guard g1 g2 = binop_guard conj_guard_f g1 g2
let imp_guard g1 g2 = binop_guard imp_guard_f g1 g2
let conj_guards gs = List.fold_left conj_guard trivial_guard gs


type lcomp = { //a lazy computation
    eff_name: lident;
    res_typ: typ;
    cflags: list<cflag>;
    comp_thunk: ref<(either<(unit -> (comp * guard_t)), comp>)>
}

let mk_lcomp eff_name res_typ cflags comp_thunk =
    { eff_name = eff_name;
      res_typ = res_typ;
      cflags = cflags;
      comp_thunk = FStar.Util.mk_ref (Inl comp_thunk) }

let lcomp_comp lc =
    match !(lc.comp_thunk) with
    | Inl thunk ->
      let c, g = thunk () in
      lc.comp_thunk := Inr c;
      c, g
    | Inr c -> c, trivial_guard

let apply_lcomp fc fg lc =
  mk_lcomp
    lc.eff_name lc.res_typ lc.cflags
    (fun () ->
     let (c, g) = lcomp_comp lc in
     fc c, fg g)

let lcomp_to_string lc =
    if Options.print_effect_args () then
        Print.comp_to_string (lc |> lcomp_comp |> fst)
    else
        BU.format2 "%s %s" (Print.lid_to_string lc.eff_name) (Print.term_to_string lc.res_typ)

let lcomp_set_flags lc fs =
    let comp_typ_set_flags (c:comp) =
        match c.n with
        | Total _
        | GTotal _ -> c
        | Comp ct ->
          let ct = {ct with flags=fs} in
          {c with n=Comp ct}
    in
    mk_lcomp lc.eff_name
             lc.res_typ
             fs
             (fun () -> lc |> lcomp_comp |> (fun (c, g) -> comp_typ_set_flags c, g))

let is_total_lcomp c = lid_equals c.eff_name PC.effect_Tot_lid || c.cflags |> BU.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_tot_or_gtot_lcomp c = lid_equals c.eff_name PC.effect_Tot_lid
                             || lid_equals c.eff_name PC.effect_GTot_lid
                             || c.cflags |> BU.for_some (function TOTAL | RETURN -> true | _ -> false)

let is_lcomp_partial_return c = c.cflags |> BU.for_some (function RETURN | PARTIAL_RETURN -> true | _ -> false)

let is_pure_lcomp lc =
    is_total_lcomp lc
    || U.is_pure_effect lc.eff_name
    || lc.cflags |> BU.for_some (function LEMMA -> true | _ -> false)

let is_pure_or_ghost_lcomp lc =
    is_pure_lcomp lc || U.is_ghost_effect lc.eff_name

let set_result_typ_lc lc t =
  mk_lcomp lc.eff_name t lc.cflags (fun () -> lc |> lcomp_comp |> (fun (c, g) -> U.set_result_typ c t, g))

let residual_comp_of_lcomp lc = {
    residual_effect=lc.eff_name;
    residual_typ=Some (lc.res_typ);
    residual_flags=lc.cflags
  }

let lcomp_of_comp c0 =
    let eff_name, flags =
        match c0.n with
        | Total _ -> PC.effect_Tot_lid, [TOTAL]
        | GTotal _ -> PC.effect_GTot_lid, [SOMETRIVIAL]
        | Comp c -> c.effect_name, c.flags in
    mk_lcomp eff_name (U.comp_result c0) flags (fun () -> c0, trivial_guard)
