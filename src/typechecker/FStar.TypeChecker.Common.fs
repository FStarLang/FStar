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
    S.mk_Tm_app t_by_tactic [S.as_arg tac; S.as_arg f] Range.dummyRange

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
          | Binding_univ u -> "Binding_univ " ^ (string_of_id u)
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
       let _, x = BU.prefix bs in
       begin
       match hd with
       | Binding_var x' when S.bv_eq x.binder_bv x' ->
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

let implicits_to_string imps =
    let imp_to_string i =
        Print.uvar_to_string i.imp_uvar.ctx_uvar_head
    in
    FStar.Common.string_of_list imp_to_string imps

type guard_t = {
  guard_f:    guard_formula;
  deferred_to_tac: deferred; //This field maintains problems that are to be dispatched to a tactic
                             //They are never attempted by the unification engine in Rel
  deferred:   deferred;
  univ_ineqs: list<universe> * list<univ_ineq>;
  implicits:  implicits;
}

let trivial_guard = {
  guard_f=Trivial;
  deferred_to_tac=[];
  deferred=[];
  univ_ineqs=([], []);
  implicits=[]
}

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

let binop_guard f g1 g2 = {
  guard_f=f g1.guard_f g2.guard_f;
  deferred_to_tac=g1.deferred_to_tac@g2.deferred_to_tac;
  deferred=g1.deferred@g2.deferred;
  univ_ineqs=(fst g1.univ_ineqs@fst g2.univ_ineqs,
              snd g1.univ_ineqs@snd g2.univ_ineqs);
  implicits=g1.implicits@g2.implicits
}
let conj_guard g1 g2 = binop_guard conj_guard_f g1 g2
let imp_guard g1 g2 = binop_guard imp_guard_f g1 g2
let conj_guards gs = List.fold_left conj_guard trivial_guard gs

let weaken_guard_formula g fml =
  match g.guard_f with
  | Trivial -> g
  | NonTrivial f ->
    { g with guard_f = check_trivial (U.mk_imp fml f) }


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

let lcomp_of_comp_guard c0 g =
    let eff_name, flags =
        match c0.n with
        | Total _ -> PC.effect_Tot_lid, [TOTAL]
        | GTotal _ -> PC.effect_GTot_lid, [SOMETRIVIAL]
        | Comp c -> c.effect_name, c.flags in
    mk_lcomp eff_name (U.comp_result c0) flags (fun () -> c0, g)

let lcomp_of_comp c0 = lcomp_of_comp_guard c0 trivial_guard

////////////////////////////////////////////////////////////////////////////////
// Core logical simplification of terms
////////////////////////////////////////////////////////////////////////////////
module SS = FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
let simplify (debug:bool) (tm:term) : term =
    let w t = {t with pos=tm.pos} in
    let simp_t t =
        // catch annotated subformulae too
        match (U.unmeta t).n with
        | Tm_fvar fv when S.fv_eq_lid fv PC.true_lid ->  Some true
        | Tm_fvar fv when S.fv_eq_lid fv PC.false_lid -> Some false
        | _ -> None
    in
    let rec args_are_binders args bs =
        match args, bs with
        | (t, _)::args, b::bs ->
            begin match (SS.compress t).n with
            | Tm_name bv' -> S.bv_eq b.binder_bv bv' && args_are_binders args bs
            | _ -> false
            end
        | [], [] -> true
        | _, _ -> false
    in
    let is_applied (bs:binders) (t : term) : option<bv> =
        if debug then
            BU.print2 "WPE> is_applied %s -- %s\n"  (Print.term_to_string t) (Print.tag_of_term t);
        let hd, args = U.head_and_args_full t in
        match (SS.compress hd).n with
        | Tm_name bv when args_are_binders args bs ->
            if debug then
                BU.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                            (Print.term_to_string t)
                            (Print.bv_to_string bv)
                            (Print.term_to_string hd);
            Some bv
        | _ -> None
    in
    let is_applied_maybe_squashed (bs : binders) (t : term) : option<bv> =
        if debug then
            BU.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"  (Print.term_to_string t) (Print.tag_of_term t);
        match is_squash t with
        | Some (_, t') -> is_applied bs t'
        | _ -> begin match is_auto_squash t with
               | Some (_, t') -> is_applied bs t'
               | _ -> is_applied bs t
               end
    in
    let is_const_match (phi : term) : option<bool> =
        match (SS.compress phi).n with
        (* Trying to be efficient, but just checking if they all agree *)
        (* Note, if we wanted to do this for any term instead of just True/False
         * we need to open the terms *)
        | Tm_match (_, br::brs) ->
            let (_, _, e) = br in
            let r = begin match simp_t e with
            | None -> None
            | Some b -> if List.for_all (fun (_, _, e') -> simp_t e' = Some b) brs
                        then Some b
                        else None
            end
            in
            r
        | _ -> None
    in
    let maybe_auto_squash t =
        if U.is_sub_singleton t
        then t
        else U.mk_auto_squash U_zero t
    in
    let squashed_head_un_auto_squash_args t =
        //The head of t is already a squashed operator, e.g. /\ etc.
        //no point also squashing its arguments if they're already in U_zero
        let maybe_un_auto_squash_arg (t,q) =
            match U.is_auto_squash t with
            | Some (U_zero, t) ->
             //if we're squashing from U_zero to U_zero
             // then just remove it
              t, q
            | _ ->
              t,q
        in
        let head, args = U.head_and_args t in
        let args = List.map maybe_un_auto_squash_arg args in
        S.mk_Tm_app head args t.pos
    in
    let rec clearly_inhabited (ty : typ) : bool =
        match (U.unmeta ty).n with
        | Tm_uinst (t, _) -> clearly_inhabited t
        | Tm_arrow (_, c) -> clearly_inhabited (U.comp_result c)
        | Tm_fvar fv ->
            let l = S.lid_of_fv fv in
               (Ident.lid_equals l PC.int_lid)
            || (Ident.lid_equals l PC.bool_lid)
            || (Ident.lid_equals l PC.string_lid)
            || (Ident.lid_equals l PC.exn_lid)
        | _ -> false
    in
    let simplify arg = (simp_t (fst arg), arg) in
    match (SS.compress tm).n with
    | Tm_app({n=Tm_uinst({n=Tm_fvar fv}, _)}, args)
    | Tm_app({n=Tm_fvar fv}, args) ->
      if S.fv_eq_lid fv PC.and_lid
      then match args |> List.map simplify with
           | [(Some true, _); (_, (arg, _))]
           | [(_, (arg, _)); (Some true, _)] -> maybe_auto_squash arg
           | [(Some false, _); _]
           | [_; (Some false, _)] -> w U.t_false
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.or_lid
      then match args |> List.map simplify with
           | [(Some true, _); _]
           | [_; (Some true, _)] -> w U.t_true
           | [(Some false, _); (_, (arg, _))]
           | [(_, (arg, _)); (Some false, _)] -> maybe_auto_squash arg
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.imp_lid
      then match args |> List.map simplify with
           | [_; (Some true, _)]
           | [(Some false, _); _] -> w U.t_true
           | [(Some true, _); (_, (arg, _))] -> maybe_auto_squash arg
           | [(_, (p, _)); (_, (q, _))] ->
             if U.term_eq p q
             then w U.t_true
             else squashed_head_un_auto_squash_args tm
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.iff_lid
      then match args |> List.map simplify with
           | [(Some true, _)  ; (Some true, _)]
           | [(Some false, _) ; (Some false, _)] -> w U.t_true
           | [(Some true, _)  ; (Some false, _)]
           | [(Some false, _) ; (Some true, _)]  -> w U.t_false
           | [(_, (arg, _))   ; (Some true, _)]
           | [(Some true, _)  ; (_, (arg, _))]   -> maybe_auto_squash arg
           | [(_, (arg, _))   ; (Some false, _)]
           | [(Some false, _) ; (_, (arg, _))]   -> maybe_auto_squash (U.mk_neg arg)
           | [(_, (p, _)); (_, (q, _))] ->
             if U.term_eq p q
             then w U.t_true
             else squashed_head_un_auto_squash_args tm
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.not_lid
      then match args |> List.map simplify with
           | [(Some true, _)] ->  w U.t_false
           | [(Some false, _)] -> w U.t_true
           | _ -> squashed_head_un_auto_squash_args tm
      else if S.fv_eq_lid fv PC.forall_lid
      then match args with
           (* Simplify ∀x. True to True *)
           | [(t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some true -> w U.t_true
                     | _ -> tm)
                   | _ -> tm
             end
           (* Simplify ∀x. True to True, and ∀x. False to False, if the domain is not empty *)
           | [(ty, Some (Implicit _)); (t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some true -> w U.t_true
                     | Some false when clearly_inhabited ty -> w U.t_false
                     | _ -> tm)
                   | _ -> tm
             end
           | _ -> tm
      else if S.fv_eq_lid fv PC.exists_lid
      then match args with
           (* Simplify ∃x. False to False *)
           | [(t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some false -> w U.t_false
                     | _ -> tm)
                   | _ -> tm
             end
           (* Simplify ∃x. False to False and ∃x. True to True, if the domain is not empty *)
           | [(ty, Some (Implicit _)); (t, _)] ->
             begin match (SS.compress t).n with
                   | Tm_abs([_], body, _) ->
                     (match simp_t body with
                     | Some false -> w U.t_false
                     | Some true when clearly_inhabited ty -> w U.t_true
                     | _ -> tm)
                   | _ -> tm
             end
           | _ -> tm
      else if S.fv_eq_lid fv PC.b2t_lid
      then match args with
           | [{n=Tm_constant (Const_bool true)}, _] -> w U.t_true
           | [{n=Tm_constant (Const_bool false)}, _] -> w U.t_false
           | _ -> tm //its arg is a bool, can't unsquash
      else if S.fv_eq_lid fv PC.haseq_lid
      then begin
        (*
         * AR: We try to mimic the hasEq related axioms in Prims
         *       and the axiom related to refinements
         *     For other types, such as lists, whose hasEq is derived by the typechecker,
         *       we leave them as is
         *)
        let t_has_eq_for_sure (t:S.term) :bool =
          //Axioms from prims
          let haseq_lids = [PC.int_lid; PC.bool_lid; PC.unit_lid; PC.string_lid] in
          match (SS.compress t).n with
          | Tm_fvar fv when haseq_lids |> List.existsb (fun l -> S.fv_eq_lid fv l) -> true
          | _ -> false
        in
        if List.length args = 1 then
          let t = args |> List.hd |> fst in
          if t |> t_has_eq_for_sure then w U.t_true
          else
            match (SS.compress t).n with
            | Tm_refine _ ->
              let t = U.unrefine t in
              if t |> t_has_eq_for_sure then w U.t_true
              else
                //get the hasEq term itself
                let haseq_tm =
                  match (SS.compress tm).n with
                  | Tm_app (hd, _) -> hd
                  | _ -> failwith "Impossible! We have already checked that this is a Tm_app"
                in
                //and apply it to the unrefined type
                mk_app (haseq_tm) [t |> as_arg]
            | _ -> tm
        else tm
      end
      else if S.fv_eq_lid fv PC.eq2_lid
      then match args with
           | [(_typ, _); (a1, _); (a2, _)]  ->         //eq2
             (match U.eq_tm a1 a2 with
              | U.Equal -> w U.t_true
              | U.NotEqual -> w U.t_false
              | _ -> tm)
           | _ -> tm
      else if S.fv_eq_lid fv PC.eq3_lid
      then match args with
           | [(t1, _); (t2, _); (a1, _); (a2, _)] ->    //eq3
            (match U.eq_inj (U.eq_tm t1 t2) (U.eq_tm a1 a2) with
            | U.Equal -> w U.t_true
            | U.NotEqual -> w U.t_false
            | _ -> tm)
           | _ -> tm
      else
      begin
        match U.is_auto_squash tm with
        | Some (U_zero, t)
             when U.is_sub_singleton t ->
             //remove redundant auto_squashes
             t
        | _ ->
             tm
      end
    | Tm_refine (bv, t) ->
        begin match simp_t t with
        | Some true -> bv.sort
        | Some false -> tm
        | None -> tm
        end
    | Tm_match _ ->
        begin match is_const_match tm with
        | Some true -> w U.t_true
        | Some false -> w U.t_false
        | None -> tm
        end
    | _ -> tm
