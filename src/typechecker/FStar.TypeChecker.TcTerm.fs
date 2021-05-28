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
module FStar.TypeChecker.TcTerm
open FStar.Pervasives
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Errors
open FStar.TypeChecker
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.Dyn
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module TcComm = FStar.TypeChecker.Common
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module Gen = FStar.TypeChecker.Generalize
module BU = FStar.Util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
module UF = FStar.Syntax.Unionfind
module Const = FStar.Parser.Const

(* Some local utilities *)
let instantiate_both env = {env with Env.instantiate_imp=true}
let no_inst env = {env with Env.instantiate_imp=false}

let is_eq = function
    | Some Equality -> true
    | _ -> false
let steps env = [Env.Beta; Env.Eager_unfolding; Env.NoFullNorm]
let norm   env t = N.normalize (steps env) env t
let norm_c env c = N.normalize_comp (steps env) env c
let check_no_escape head_opt env (fvs:list<bv>) kt : term * guard_t =
    let rec aux try_norm t = match fvs with
        | [] -> t, Env.trivial_guard
        | _ ->
          let t = if try_norm then norm env t else t in
          let fvs' = Free.names t in
          begin match List.tryFind (fun x -> BU.set_mem x fvs') fvs with
            | None -> t, Env.trivial_guard
            | Some x ->
              if not try_norm
              then aux true t
              else let fail () =
                       let msg = match head_opt with
                        | None -> BU.format1 "Bound variables '%s' escapes; add a type annotation" (Print.bv_to_string x)
                        | Some head -> BU.format2 "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                        (Print.bv_to_string x) (N.term_to_string env head) in
                       raise_error (Errors.Fatal_EscapedBoundVar, msg) (Env.get_range env) in
                   let s, _, g0 = TcUtil.new_implicit_var "no escape" (Env.get_range env) env (fst <| U.type_u()) in
                   match Rel.try_teq true env t s with
                    | Some g ->
                      let g = Rel.solve_deferred_constraints env (Env.conj_guard g g0) in
                      s, g
                    | _ -> fail ()
         end in
    aux false kt

let push_binding env b =
  Env.push_bv env b.binder_bv

let maybe_extend_subst s b v : subst_t =
    if is_null_binder b then s
    else NT(b.binder_bv, v)::s

let set_lcomp_result lc t =
  TcComm.apply_lcomp
    (fun c -> U.set_result_typ c t) (fun g -> g) ({ lc with res_typ = t })

let memo_tk (e:term) (t:typ) = e

let maybe_warn_on_use env fv : unit =
    match Env.lookup_attrs_of_lid env fv.fv_name.v with
    | None -> ()
    | Some attrs ->
      attrs |>
      List.iter
        (fun a ->
          let head, args = U.head_and_args a in
          let msg_arg m =
              match args with
              | [{n=Tm_constant (Const_string (s, _))}, _] ->
                m ^ ": " ^ s
              | _ ->
                m
          in
          match head.n with
          | Tm_fvar attr_fv
              when lid_equals attr_fv.fv_name.v Const.warn_on_use_attr ->
            let m =
              BU.format1 "Every use of %s triggers a warning"
                         (Ident.string_of_lid fv.fv_name.v)
            in
            log_issue (range_of_lid fv.fv_name.v)
                      (Warning_WarnOnUse,
                       msg_arg m)

          | Tm_fvar attr_fv
              when lid_equals attr_fv.fv_name.v Const.deprecated_attr ->
            let m =
              BU.format1
                "%s is deprecated"
                (Ident.string_of_lid fv.fv_name.v)
            in
            log_issue (range_of_lid fv.fv_name.v)
                      (Warning_DeprecatedDefinition,
                        msg_arg m)

          | _ -> ())

//Interface to FStar.TypeChecker.Rel:

(************************************************************************************************************)
(* value_check_expected_type env e tlc g                                                                    *)
(*     e is computed to have type or computation type, tlc                                                  *)
(*          subject to the guard g                                                                          *)
(* This function compares tlc to the expected type from the context, augmenting the guard if needed         *)
(************************************************************************************************************)
let value_check_expected_typ env (e:term) (tlc:either<term,lcomp>) (guard:guard_t)
    : term * lcomp * guard_t =
  Env.def_check_guard_wf e.pos "value_check_expected_typ" env guard;
  let lc = match tlc with
    | Inl t -> TcComm.lcomp_of_comp <| mk_Total t
    | Inr lc -> lc in
  let t = lc.res_typ in
  let e, lc, g =
   match Env.expected_typ env with
   | None -> memo_tk e t, lc, guard
   | Some t' ->
     let e, lc, g = TcUtil.check_has_type_maybe_coerce env e lc t' in
     if debug env Options.Medium
     then BU.print4 "value_check_expected_typ: type is %s<:%s \tguard is %s, %s\n"
                (TcComm.lcomp_to_string lc) (Print.term_to_string t')
                (Rel.guard_to_string env g) (Rel.guard_to_string env guard);
     let t = lc.res_typ in
     let g = Env.conj_guard g guard in
     (* adding a guard for confirming that the computed type t is a subtype of the expected type t' *)
     let msg = if Env.is_trivial_guard_formula g then None else Some <| Err.subtyping_failed env t t' in
     let lc, g = TcUtil.strengthen_precondition msg env e lc g in
     memo_tk e t', set_lcomp_result lc t', g
  in
  e, lc, g

(************************************************************************************************************)
(* comp_check_expected_type env e lc g                                                                      *)
(*    similar to value_check_expected_typ, except this time e is a non-value                                *)
(************************************************************************************************************)
let comp_check_expected_typ env e lc : term * lcomp * guard_t =
  match Env.expected_typ env with
   | None -> e, lc, Env.trivial_guard
   | Some t ->
     let e, lc, g_c = TcUtil.maybe_coerce_lc env e lc t in
     let e, lc, g = TcUtil.weaken_result_typ env e lc t in
     e, lc, Env.conj_guard g g_c

(************************************************************************************************************)
(* check_expected_effect: triggers a sub-effecting, WP implication, etc. if needed                          *)
(************************************************************************************************************)
let check_expected_effect env (copt:option<comp>) (ec : term * comp) : term * comp * guard_t =
  let e, c = ec in
  let tot_or_gtot c = //expects U.is_pure_or_ghost_comp c
     if U.is_pure_comp c
     then mk_Total (U.comp_result c)
     else if U.is_pure_or_ghost_comp c
     then mk_GTotal (U.comp_result c)
     else failwith "Impossible: Expected pure_or_ghost comp"
  in

  let expected_c_opt, c, gopt =
    let ct = U.comp_result c in
    match copt with
    | Some _ -> copt, c, None  //setting gopt to None since expected comp is already set, so we will do sub_comp below
    | None  ->
        if (Options.ml_ish()
            && Ident.lid_equals Const.effect_ALL_lid (U.comp_effect_name c))
        || (Options.ml_ish ()
            && env.lax
            && not (U.is_pure_or_ghost_comp c))
        then Some (U.ml_comp ct e.pos), c, None
        else if U.is_tot_or_gtot_comp c //these are already the defaults for their particular effects
        then None, tot_or_gtot c, None //but, force c to be exactly ((G)Tot t), since otherwise it may actually contain a return
        else if U.is_pure_or_ghost_comp c
        then Some (tot_or_gtot c), c, None
        else if U.comp_effect_name c |> Env.norm_eff_name env |> Env.is_layered_effect env
        then raise_error (Errors.Error_LayeredMissingAnnot,  //hard error if layered effects are used without annotations
               BU.format2 "Missing annotation for a layered effect (%s) computation at %s"
                 (c |> U.comp_effect_name |> Ident.string_of_lid) (Range.string_of_range e.pos)) e.pos
        else if Options.trivial_pre_for_unannotated_effectful_fns ()
        then None, c, (
               let _, _, g = TcUtil.check_trivial_precondition env c in
               Some g)
        else None, c, None
  in
  let c = norm_c env c in
  match expected_c_opt with
    | None ->
      e, c, (match gopt with | None -> Env.trivial_guard | Some g -> g)
    | Some expected_c -> //expected effects should already be normalized
       let _ = match gopt with
         | None -> ()
         | Some _ -> failwith "Impossible! check_expected_effect, gopt should have been None"
       in

       let c = TcUtil.maybe_assume_result_eq_pure_term env e (TcComm.lcomp_of_comp c) in
       let c, g_c = TcComm.lcomp_comp c in
       if debug env <| Options.Medium then
       BU.print3 "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                 (Print.term_to_string e) (Print.comp_to_string c) (Print.comp_to_string expected_c);
       let e, _, g = TcUtil.check_comp env e c expected_c in
       let g = TcUtil.label_guard (Env.get_range env) "could not prove post-condition" g in
       if debug env Options.Medium
       then BU.print2 "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                         (Range.string_of_range e.pos)
                         (guard_to_string env g);
       let e = TcUtil.maybe_lift env e (U.comp_effect_name c) (U.comp_effect_name expected_c) (U.comp_result c) in
       e, expected_c, Env.conj_guard g_c g

let no_logical_guard env (te, kt, f) =
  match guard_form f with
    | Trivial -> te, kt, f
    | NonTrivial f -> raise_error (Err.unexpected_non_trivial_precondition_on_term env f) (Env.get_range env)

let print_expected_ty env = match Env.expected_typ env with
    | None -> BU.print_string "Expected type is None\n"
    | Some t -> BU.print1 "Expected type is %s" (Print.term_to_string t)

(************************************************************************************************************)
(* check the patterns in an SMT lemma to make sure all bound vars are mentiond *)
(************************************************************************************************************)

(* andlist: whether we're inside an SMTPatOr and we should take the
 * intersection of the sub-variables instead of the union. *)
let rec get_pat_vars' all (andlist : bool) (pats:term) :set<bv> =
  let pats = unmeta pats in
  let head, args = head_and_args pats in
  match (un_uinst head).n, args with
  | Tm_fvar fv, _ when fv_eq_lid fv Const.nil_lid ->
      if andlist
      then BU.as_set all Syntax.order_bv
      else BU.new_set Syntax.order_bv

  | Tm_fvar fv, [(_, Some (Implicit _)); (hd, None); (tl, None)] when fv_eq_lid fv Const.cons_lid ->
      (* The head is not under the scope of the SMTPatOr, consider
        * SMTPatOr [ [SMTPat p1; SMTPat p2] ; ... ]
        * we should take the union of fv(p1) and fv(p2) *)
      let hdvs = get_pat_vars' all false   hd in
      let tlvs = get_pat_vars' all andlist tl in

      if andlist
      then BU.set_intersect hdvs tlvs
      else BU.set_union     hdvs tlvs

  | Tm_fvar fv, [(_, Some (Implicit _)); (pat, None)] when fv_eq_lid fv Const.smtpat_lid ->
      Free.names pat

  | Tm_fvar fv, [(subpats, None)] when fv_eq_lid fv Const.smtpatOr_lid ->
      get_pat_vars' all true subpats

  | _ ->
      BU.new_set Syntax.order_bv

let get_pat_vars all pats = get_pat_vars' all false pats

let check_pat_fvs rng env pats bs =
    let pat_vars = get_pat_vars (List.map (fun b -> b.binder_bv) bs) (N.normalize [Env.Beta] env pats) in
    begin match bs |> BU.find_opt (fun ({binder_bv=b}) -> not(BU.set_mem b pat_vars)) with
        | None -> ()
        | Some ({binder_bv=x}) ->
          Errors.log_issue rng
            (Errors.Warning_SMTPatternIllFormed,
             (BU.format1 "Pattern misses at least one bound variable: %s" (Print.bv_to_string x)))
    end

(*
 * Check that term t (an smt pattern) does not contain theory symbols
 * These symbols are fvs with attribute smt_theory_symbol from Prims
 *   and other terms such as abs, arrows etc.
 *)
let check_no_smt_theory_symbols (en:env) (t:term) :unit =
  let rec pat_terms (t:term) :list<term> =
    let t = unmeta t in
    let head, args = head_and_args t in
    match (un_uinst head).n, args with
    | Tm_fvar fv, _ when fv_eq_lid fv Const.nil_lid -> []
    | Tm_fvar fv, [_; (hd, _); (tl, _)] when fv_eq_lid fv Const.cons_lid ->
      pat_terms hd @ pat_terms tl
    | Tm_fvar fv, [_; (pat, _)] when fv_eq_lid fv Const.smtpat_lid -> [pat]
    | Tm_fvar fv, [(subpats, None)] when fv_eq_lid fv Const.smtpatOr_lid ->
      pat_terms subpats
    | _ -> []  //TODO: should this be a hard error?
  in
  let rec aux (t:term) :list<term> =
    match (SS.compress t).n with
    //these cases are fine
    | Tm_bvar _ | Tm_name _ | Tm_constant _ | Tm_type _ | Tm_uvar _
    | Tm_lazy _ | Tm_unknown -> []

    //these should not be allowed in patterns
    | Tm_abs _ | Tm_arrow _ | Tm_refine _
    | Tm_match _ | Tm_let _ | Tm_delayed _ | Tm_quoted _ -> [t]

    //these descend more in the term
    | Tm_fvar fv ->
      if Env.fv_has_attr en fv Const.smt_theory_symbol_attr_lid then [t]
      else []

    | Tm_app (t, args) ->
      List.fold_left (fun acc (t, _) ->
        acc @ aux t) (aux t) args

    | Tm_ascribed (t, _, _)
    | Tm_uinst (t, _)
    | Tm_meta (t, _) -> aux t
  in
  let tlist = t |> pat_terms |> List.collect aux in
  if List.length tlist = 0 then ()  //did not find any offending term
  else
    //string to be displayed in the warning
    let msg = List.fold_left (fun s t -> s ^ " " ^ (Print.term_to_string t)) "" tlist in
    Errors.log_issue t.pos (Errors.Warning_SMTPatternIllFormed,
      BU.format1 "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
                 msg)

let check_smt_pat env t bs c =
    if U.is_smt_lemma t //check patterns cover the bound vars
    then match c.n with
        | Comp ({effect_args=[_pre; _post; (pats, _)]}) ->
            check_pat_fvs t.pos env pats bs;
            check_no_smt_theory_symbols env pats
        | _ -> failwith "Impossible"

(************************************************************************************************************)
(* Building the environment for the body of a let rec;                                                      *)
(* guards the recursively bound names with a termination check                                              *)
(************************************************************************************************************)
let guard_letrecs env actuals expected_c : list<(lbname*typ*univ_names)> =
    match env.letrecs with
    | [] -> []
    | letrecs ->
      let r = Env.get_range env in
      let env = {env with letrecs=[]} in

      let decreases_clause bs c =
          if debug env Options.Low
          then BU.print2 "Building a decreases clause over (%s) and %s\n"
                (Print.binders_to_string ", " bs) (Print.comp_to_string c);

          //exclude types and function-typed arguments from the decreases clause
          let filter_types_and_functions (bs:binders)  =
            bs |> List.collect (fun ({binder_bv=b}) ->
                    let t = N.unfold_whnf env (U.unrefine b.sort) in
                    match t.n with
                        | Tm_type _
                        | Tm_arrow _ -> []
                        | _ -> [S.bv_to_name b]) in
          let cflags = U.comp_flags c in
          match cflags |> List.tryFind (function DECREASES _ -> true | _ -> false) with
                | Some (DECREASES d) -> d
                | _ -> bs |> filter_types_and_functions |> Decreases_lex in

      let precedes_t = TcUtil.fvar_const env Const.precedes_lid in
      let rec mk_precedes_lex env l l_prev : term =
        (*
         * AR: aux assumes that l and l_prev have the same lengths
         *     Given l = [a; b; c], l_prev = [d; e; f], it builds:
         *       a << d \/ (eq3 a d /\ b << e) \/ (eq3 a d /\ eq3 b e /\ c << f
         *     We build an "untyped" term here, the caller will typecheck it properly
         *)
        let rec aux l l_prev : term =
         let type_of (e1:term) (e2:term) : typ * typ =
           (*
            * AR: we compute the types of e1 and e2 to provide type
            *     arguments to eq3 (otherwise F* may infer something that Z3 is unable
            *       to prove equal later on)
            *     as a check, if the types are not equal, we emit a warning so that
            *       the programmer may annotate explicitly if needed
            *)
           //AR: 03/30: WARNING: dropping the guard in computing t1 and t2 below
           let t1 = env.typeof_well_typed_tot_or_gtot_term env e1 false |> fst |> U.unrefine in
           let t2 = env.typeof_well_typed_tot_or_gtot_term env e2 false |> fst |> U.unrefine in
           let rec warn t1 t2 =
             if U.eq_tm t1 t2 = Equal
             then false
             else match (SS.compress t1).n, (SS.compress t2).n with
                  | Tm_uinst (t1, _), Tm_uinst (t2, _) -> warn t1 t2
                  | Tm_name _, Tm_name _ -> false  //do not warn for names, e.g. in polymorphic functions, the names may be instantiated at the call sites
                  | Tm_app (h1, args1), Tm_app (h2, args2) ->
                    warn h1 h2 || List.length args1 <> List.length args2 ||
                    (List.zip args1 args2 |> List.existsML (fun ((a1, _), (a2, _)) -> warn a1 a2))
                  | Tm_refine (t1, phi1), Tm_refine (t2, phi2) ->
                    warn t1.sort t2.sort || warn phi1 phi2
                  | Tm_uvar _, _
                  | _, Tm_uvar _ -> false
                  | _, _ -> true in

           (if warn t1 t2
            then match (SS.compress t1).n, (SS.compress t2).n with
                 | Tm_name _, Tm_name _ -> ()
                 | _, _ ->
                   Errors.log_issue e1.pos (Errors.Warning_Defensive,
                     BU.format6 "SMT may not be able to prove the types of %s at %s (%s) and %s at %s (%s) to be equal, if the proof fails, try annotating these with the same type\n"
                       (Print.term_to_string e1)
                       (Range.string_of_range e1.pos)
                       (Print.term_to_string t1)
                       (Print.term_to_string e2)
                       (Range.string_of_range e2.pos)
                       (Print.term_to_string t2)));
           t1, t2 in

          match l, l_prev with
          | [], [] ->
            mk_Tm_app precedes_t [as_arg S.unit_const; as_arg S.unit_const] r
          | [x], [x_prev] -> mk_Tm_app precedes_t [as_arg x; as_arg x_prev] r
          | x::tl, x_prev::tl_prev ->
            let t_x, t_x_prev = type_of x x_prev in
            let tm_precedes = mk_Tm_app precedes_t [
              iarg t_x;
              iarg t_x_prev;
              as_arg x;
              as_arg x_prev ] r in
            let eq3_x_x_prev = mk_eq3_no_univ t_x t_x_prev x x_prev in

            mk_disj tm_precedes
                    (mk_conj eq3_x_x_prev (aux tl tl_prev)) in

        (* Call aux with equal sized prefixes of l and l_prev *)
        let l, l_prev =
          let n, n_prev = List.length l, List.length l_prev in
          if n = n_prev then l, l_prev
          else if n < n_prev then l, l_prev |> List.splitAt n |> fst
          else l |> List.splitAt n_prev |> fst, l_prev in
        aux l l_prev in

      let mk_precedes env d d_prev =
        match d, d_prev with
        | Decreases_lex l, Decreases_lex l_prev ->
          mk_precedes_lex env l l_prev
        | Decreases_wf (rel, e), Decreases_wf (rel_prev, e_prev) ->
          if not (U.eq_tm rel rel_prev = U.Equal)
          then Errors.raise_error (Errors.Fatal_UnexpectedTerm,
                 BU.format2 "Cannot build termination VC with two different well-founded \
                   relations %s and %s"
                   (Print.term_to_string rel)
                   (Print.term_to_string rel_prev)) r;
          (*
           * For well-founded relations based termination checking,
           *   just prove that (rel e e_prev)
           *)
          mk_Tm_app rel [as_arg e; as_arg e_prev] r
        | _, _ ->
          Errors.raise_error (Errors.Fatal_UnexpectedTerm,
            "Cannot build termination VC with a well-founded relation and lex ordering") r in

      let previous_dec = decreases_clause actuals expected_c in

      let guard_one_letrec (l, arity, t, u_names) =
        let formals, c = N.get_n_binders env arity t in

        (* This should never happen since `termination_check_enabled`
         * takes care to not return an arity bigger than the one in
         * the lbtyp. *)
        if arity > List.length formals then
          failwith "impossible: bad formals arity, guard_one_letrec";

        //make sure they all have non-null names
        let formals = formals |> List.map (fun b ->
          if S.is_null_bv b.binder_bv
          then ({b with binder_bv=S.new_bv (Some (S.range_of_bv b.binder_bv)) b.binder_bv.sort})
          else b) in
        let dec = decreases_clause formals c in
        let precedes =
          let env = Env.push_binders env formals in
          mk_precedes env dec previous_dec in
        let precedes = TcUtil.label "Could not prove termination of this recursive call" r precedes in
        let bs, ({binder_bv=last; binder_qual=imp}) = BU.prefix formals in
        let last = {last with sort=U.refine last precedes} in
        let refined_formals = bs@[S.mk_binder_with_attrs last imp []] in
        let t' = U.arrow refined_formals c in
        if debug env Options.Medium
        then BU.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
              (Print.lbname_to_string l) (Print.term_to_string t) (Print.term_to_string t');
        l, t', u_names
      in
      letrecs |> List.map guard_one_letrec
      
let wrap_guard_with_tactic_opt topt g =
   match topt with
   | None -> g
   | Some tactic ->
     (* We use always_map_guard so the annotation is there even for trivial
      * guards. If the user writes (a <: b by fail ""), we should fail. *)
     Env.always_map_guard g (fun g ->
     Common.mk_by_tactic tactic (U.mk_squash U_zero g)) //guards are in U_zero


(*
 * This is pattern matching an `(M.reflect e) <: C`
 *
 * As we special case typechecking of such terms (as a subcase of `Tm_ascribed` in the main `tc_term` loop
 *
 * Returns the (e, arg_qualifier) and the lident of M
 *)
let is_comp_ascribed_reflect (e:term) : option<(lident * term * aqual)> =
  match (SS.compress e).n with
  | Tm_ascribed (e, (Inr _, _), _) ->
    (match (SS.compress e).n with
     | Tm_app (head, args) when List.length args = 1 ->
       (match (SS.compress head).n with
        | Tm_constant (Const_reflect l) -> args |> List.hd |> (fun (e, aqual) -> (l, e, aqual)) |> Some
        | _ -> None)
     | _ -> None)
   | _ -> None



(************************************************************************************************************)
(* Main type-checker begins here                                                                            *)
(************************************************************************************************************)
let rec tc_term env e =
    if Env.debug env Options.Medium then
        BU.print5 "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
          (Range.string_of_range <| Env.get_range env)
          (string_of_bool env.phase1)
          (Print.term_to_string e)
          (Print.tag_of_term (SS.compress e))
          (match Env.expected_typ env with | None -> "None" | Some t -> Print.term_to_string t);

    let r, ms = BU.record_time (fun () ->
                    tc_maybe_toplevel_term ({env with top_level=false}) e) in
    if Env.debug env Options.Medium then begin
        BU.print4 "(%s) } tc_term of %s (%s) took %sms\n" (Range.string_of_range <| Env.get_range env)
                                                        (Print.term_to_string e)
                                                        (Print.tag_of_term (SS.compress e))
                                                        (string_of_int ms);
        let e, lc , _ = r in
        BU.print4 "(%s) Result is: (%s:%s) (%s)\n" (Range.string_of_range <| Env.get_range env)
                                                   (Print.term_to_string e)
                                                   (TcComm.lcomp_to_string lc)
                                                   (Print.tag_of_term (SS.compress e))
    end;
    r

and tc_maybe_toplevel_term env (e:term) : term                  (* type-checked and elaborated version of e            *)
                                        * lcomp                 (* computation type where the WPs are lazily evaluated *)
                                        * guard_t =             (* well-formedness condition                           *)
  let env = if e.pos=Range.dummyRange then env else Env.set_range env e.pos in
  let top = SS.compress e in
  if debug env Options.Medium then
    BU.print3 "Typechecking %s (%s): %s\n" (Range.string_of_range <| Env.get_range env) (Print.tag_of_term top) (Print.term_to_string top);
  match top.n with
  | Tm_delayed _ -> failwith "Impossible"

  | Tm_uinst _
  | Tm_uvar _
  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _
  | Tm_constant _
  | Tm_abs _
  | Tm_arrow _
  | Tm_refine _
  | Tm_type _
  | Tm_unknown -> tc_value env e

  | Tm_quoted (qt, qi)  ->
    let projl = function
      | Inl x -> x
      | Inr _ -> failwith "projl fail"
    in
    let non_trivial_antiquotes qi =
        let is_name t =
            match (SS.compress t).n with
            | Tm_name _ -> true
            | _ -> false
        in
        BU.for_some (fun (_, t) -> not (is_name t)) qi.antiquotes
    in
    begin match qi.qkind with
    (* In this case, let-bind all antiquotations so we're sure that effects
     * are properly handled. *)
    | Quote_static when non_trivial_antiquotes qi ->
        let e0 = e in
        let newbvs = List.map (fun _ -> S.new_bv None S.t_term) qi.antiquotes in

        let z = List.zip qi.antiquotes newbvs in

        let lbs = List.map (fun ((bv, t), bv') ->
                                U.close_univs_and_mk_letbinding None (Inl bv') []
                                                                S.t_term Const.effect_Tot_lid
                                                                t [] t.pos)
                           z in
        let qi = { qi with antiquotes = List.map (fun ((bv, _), bv') ->
                                            (bv, S.bv_to_name bv')) z } in
        let nq = mk (Tm_quoted (qt, qi)) top.pos in
        let e = List.fold_left (fun t lb -> mk (Tm_let ((false, [lb]),
                                                        SS.close [S.mk_binder (projl lb.lbname)] t)) top.pos) nq lbs in
        tc_maybe_toplevel_term env e

    (* A static quote is of type `term`, as long as its antiquotations are too *)
    | Quote_static ->
        (* Typecheck the antiquotes expecting a term *)
        let aqs = qi.antiquotes in
        let env_tm = Env.set_expected_typ env t_term in
        let (aqs_rev, guard) =
            List.fold_right (fun (bv, tm) (aqs_rev, guard) ->
                                    let tm, _, g = tc_term env_tm tm in
                                    ((bv, tm)::aqs_rev, Env.conj_guard g guard)) aqs ([], Env.trivial_guard) in
        let qi = { qi with antiquotes = List.rev aqs_rev } in

        let tm = mk (Tm_quoted (qt, qi)) top.pos in
        value_check_expected_typ env tm (Inl S.t_term) guard

    | Quote_dynamic ->
        let c = mk_Tac S.t_term in

        (* Typechecked the quoted term just to elaborate it *)
        let env', _ = Env.clear_expected_typ env in
        let qt, _, _ = tc_term ({ env' with lax = true }) qt in
        let t = mk (Tm_quoted (qt, qi)) top.pos in

        let t, lc, g = value_check_expected_typ env top (Inr (TcComm.lcomp_of_comp c)) Env.trivial_guard in
        let t = mk (Tm_meta(t, Meta_monadic_lift (Const.effect_PURE_lid, Const.effect_TAC_lid, S.t_term)))
                   t.pos in
        t, lc, g
    end

  | Tm_lazy ({lkind=Lazy_embedding _ }) ->
    tc_term env (U.unlazy top)

  // lazy terms have whichever type they're annotated with
  | Tm_lazy i ->
    value_check_expected_typ env top (Inl i.ltyp) Env.trivial_guard

  | Tm_meta(e, Meta_desugared Meta_smt_pat) ->
    let e, c, g = tc_tot_or_gtot_term env e in
    let g = {g with guard_f=Trivial} in //VC's in SMT patterns are irrelevant
    mk (Tm_meta (e, Meta_desugared Meta_smt_pat)) top.pos, c, g  //AR: keeping the pats as meta for the second phase. smtencoding does an unmeta.

  | Tm_meta(e, Meta_pattern(names, pats)) ->
    let t, u = U.type_u () in
    let e, c, g = tc_check_tot_or_gtot_term env e t "" in
    //NS: PATTERN INFERENCE
    //if `pats` is empty (that means the user did not annotate a pattern).
    //In that case try to infer a pattern by
    //analyzing `e` for the smallest terms that contain all the variables
    //in `names`.
    //If not pattern can be inferred, raise a warning
    let pats, g' =
        let env, _ = Env.clear_expected_typ env in
        tc_smt_pats env pats in
    let g' = {g' with guard_f=Trivial} in //The pattern may have some VCs associated with it, but these are irrelevant.
    mk (Tm_meta(e, Meta_pattern(names, pats))) top.pos,
    c,
    Env.conj_guard g g' //but don't drop g' altogether, since it also contains unification constraints

  | Tm_meta(e, Meta_desugared Sequence) ->
    begin match (SS.compress e).n with
        | Tm_let((_,[{lbname=x; lbdef=e1}]), e2) -> //NS: Why not handle this specially in the deugaring phase, adding a unit annotation on x?
          let e1, c1, g1 = tc_term (Env.set_expected_typ env t_unit) e1 in
          let e2, c2, g2 = tc_term env e2 in
          let c = TcUtil.maybe_return_e2_and_bind e1.pos env (Some e1) c1 e2 (None, c2) in
          let e1 = TcUtil.maybe_lift env e1 c1.eff_name c.eff_name c1.res_typ in
          let e2 = TcUtil.maybe_lift env e2 c2.eff_name c.eff_name c2.res_typ in
          let attrs =
            if TcUtil.is_pure_or_ghost_effect env c1.eff_name
            then [U.inline_let_attr]
            else []
          in
          let e = mk (Tm_let((false, [mk_lb (x, [], c.eff_name, t_unit, e1, attrs, e1.pos)]), e2)) e.pos in
          let e = TcUtil.maybe_monadic env e c.eff_name c.res_typ in
          let e = mk (Tm_meta(e, Meta_desugared Sequence)) top.pos in
          e, c, Env.conj_guard g1 g2
        | _ ->
          let e, c, g = tc_term env e in
          let e = mk (Tm_meta(e, Meta_desugared Sequence)) top.pos in
          e, c, g
    end

  | Tm_meta(e, Meta_monadic _)
  | Tm_meta(e, Meta_monadic_lift _) ->
    (* KM : This case should not happen when typechecking once but is it really *)
    (* okay to just drop the annotation ? *)
    tc_term env e

  | Tm_meta(e, m) ->
    let e, c, g = tc_term env e in
    let e = mk (Tm_meta(e, m)) top.pos in
    e, c, g

  | Tm_ascribed (e, (asc, Some tac), labopt) ->
    (* Ascription with an associated tactic for its guard. We typecheck
     * the ascribed term without the tactic by recursively calling tc_term,
     * and then we wrap the returned guard with the tactic. We must also return
     * the guard for the well-typing of the tactic itself. *)

    let tac, _, g_tac = tc_tactic t_unit t_unit env tac in

    let t' = mk (Tm_ascribed (e, (asc, None), labopt)) top.pos in
    let t', c, g = tc_term env t' in

    (* Set the tac ascription on the elaborated term *)
    let t' =
      match (SS.compress t').n with
      | Tm_ascribed (e, (asc, None), labopt) ->
        mk (Tm_ascribed (e, (asc, Some tac), labopt)) t'.pos
      | _ ->
        failwith "impossible"
    in
    let g = wrap_guard_with_tactic_opt (Some tac) g in
    t', c, Env.conj_guard g g_tac

  (*
   * AR: Special case for the typechecking of (M.reflect e) <: M a is
   *
   *     As part of it, we typecheck (e <: Tot (repr a is)), this keeps the bidirectional
   *       typechecking for e, which is most cases is a lambda
   *
   *     Also the `Tot` annotation is important since for lambdas, we fold the guard
   *       into the returned comp (making it something like PURE (arrow_t) wp, see the end of tc_abs)
   *     If we did not put `Tot` we would have to separately check that the wp has
   *       a trivial precondition
   *)

  | Tm_ascribed (_, (Inr expected_c, None), _)
    when top |> is_comp_ascribed_reflect |> is_some ->

    let (effect_lid, e, aqual) = top |> is_comp_ascribed_reflect |> must in

    let env0, _ = Env.clear_expected_typ env in

    let expected_c, _, g_c = tc_comp env0 expected_c in
    let expected_ct = Env.unfold_effect_abbrev env0 expected_c in

    if not (lid_equals effect_lid expected_ct.effect_name)
    then raise_error (Errors.Fatal_UnexpectedEffect,
           BU.format2 "The effect on reflect %s does not match with the annotation %s\n"
             (Ident.string_of_lid effect_lid) (Ident.string_of_lid expected_ct.effect_name)) top.pos;

    if not (is_user_reflectable_effect env effect_lid)
    then raise_error (Errors.Fatal_EffectCannotBeReified,
           BU.format1 "Effect %s cannot be reflected" (Ident.string_of_lid effect_lid)) top.pos;

    let u_c = expected_ct.comp_univs |> List.hd in
    let repr = Env.effect_repr env0 (expected_ct |> S.mk_Comp) u_c |> must in

    // e <: Tot repr
    let e = S.mk (Tm_ascribed (e, (Inr (S.mk_Total' repr (Some u_c)), None), None)) e.pos in

    if Env.debug env0 <| Options.Extreme
    then BU.print1 "Typechecking ascribed reflect, inner ascribed term: %s\n"
           (Print.term_to_string e);

    let e, _, g_e = tc_tot_or_gtot_term env0 e in
    let e = U.unascribe e in

    if Env.debug env0 <| Options.Extreme
    then BU.print2 "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
           (Print.term_to_string e) (Rel.guard_to_string env0 g_e);

    //reconstruct (M.reflect e) < M a is
    let top =
      let r = top.pos in
      let tm = mk (Tm_constant (Const_reflect effect_lid)) r in
      let tm = mk (Tm_app (tm, [e, aqual])) r in
      mk (Tm_ascribed (tm, (Inr expected_c, None), expected_c |> U.comp_effect_name |> Some)) r in

    //check the expected type in the env, if present
    let top, c, g_env = comp_check_expected_typ env top (expected_c |> TcComm.lcomp_of_comp) in

    top, c, Env.conj_guards [g_c; g_e; g_env]

  | Tm_ascribed (e, (Inr expected_c, None), _) ->
    let env0, _ = Env.clear_expected_typ env in
    let expected_c, _, g = tc_comp env0 expected_c in
    let e, c', g' = tc_term (U.comp_result expected_c |> Env.set_expected_typ env0) e in
    let e, expected_c, g'' =
      let c', g_c' = TcComm.lcomp_comp c' in
      let e, expected_c, g'' = check_expected_effect env0 (Some expected_c) (e, c') in
      e, expected_c, Env.conj_guard g_c' g'' in
    let e = mk (Tm_ascribed(e, (Inr expected_c, None), Some (U.comp_effect_name expected_c))) top.pos in  //AR: this used to be Inr t_res, which meant it lost annotation for the second phase
    let lc = TcComm.lcomp_of_comp expected_c in
    let f = Env.conj_guard g (Env.conj_guard g' g'') in
    let e, c, f2 = comp_check_expected_typ env e lc in
    e, c, Env.conj_guard f f2

  | Tm_ascribed (e, (Inl t, None), _) ->
    let k, u = U.type_u () in
    let t, _, f = tc_check_tot_or_gtot_term env t k "" in
    let e, c, g = tc_term (Env.set_expected_typ env t) e in
    //NS: Maybe redundant strengthen
    let c, f = TcUtil.strengthen_precondition (Some (fun () -> return_all Err.ill_kinded_type)) (Env.set_range env t.pos) e c f in
    let e, c, f2 = comp_check_expected_typ env (mk (Tm_ascribed(e, (Inl t, None), Some c.eff_name)) top.pos) c in
    e, c, Env.conj_guard f (Env.conj_guard g f2)

  (* Unary operators. Explicitly curry extra arguments *)
  | Tm_app({n=Tm_constant Const_range_of}, a::hd::rest)
  | Tm_app({n=Tm_constant Const_reify}, a::hd::rest)
  | Tm_app({n=Tm_constant (Const_reflect _)}, a::hd::rest) ->
    let rest = hd::rest in //no 'as' clauses in F* yet, so we need to do this ugliness
    let unary_op, _ = U.head_and_args top in
    let head = mk (Tm_app(unary_op, [a])) (Range.union_ranges unary_op.pos (fst a).pos) in
    let t = mk (Tm_app(head, rest)) top.pos in
    tc_term env t

  (* Binary operators *)
  | Tm_app({n=Tm_constant Const_set_range_of}, a1::a2::hd::rest) ->
    let rest = hd::rest in //no 'as' clauses in F* yet, so we need to do this ugliness
    let unary_op, _ = U.head_and_args top in
    let head = mk (Tm_app(unary_op, [a1; a2])) (Range.union_ranges unary_op.pos (fst a1).pos) in
    let t = mk (Tm_app(head, rest)) top.pos in
    tc_term env t

  | Tm_app({n=Tm_constant Const_range_of}, [(e, None)]) ->
    let e, c, g = tc_term (fst <| Env.clear_expected_typ env) e in
    let head, _ = U.head_and_args top in
    mk (Tm_app (head, [(e, None)])) top.pos, (TcComm.lcomp_of_comp <| mk_Total (tabbrev Const.range_lid)), g

  | Tm_app({n=Tm_constant Const_set_range_of}, (t, None)::(r, None)::[]) ->
    let head, _ = U.head_and_args top in
    let env' = Env.set_expected_typ env (tabbrev Const.range_lid) in
    let er, _, gr = tc_term env' r in
    let t, tt, gt = tc_term env t in
    let g = Env.conj_guard gr gt in
    mk_Tm_app head [S.as_arg t; S.as_arg r] top.pos, tt, g

  | Tm_app({n=Tm_constant Const_range_of}, _)
  | Tm_app({n=Tm_constant Const_set_range_of}, _) ->
    raise_error (Errors.Fatal_IllAppliedConstant, BU.format1 "Ill-applied constant %s" (Print.term_to_string top)) e.pos

  | Tm_app({n=Tm_constant Const_reify}, [(e, aqual)]) ->
    if Option.isSome aqual
    then Errors.log_issue e.pos (Errors.Warning_IrrelevantQualifierOnArgumentToReify, "Qualifier on argument to reify is irrelevant and will be ignored");
    let env0, _ = Env.clear_expected_typ env in
    let e, c, g = tc_term env0 e in
    let reify_op, _ = U.head_and_args top in
    let u_c = env.universe_of env c.res_typ in
    let c, g_c = TcComm.lcomp_comp c in
    let ef = U.comp_effect_name c in
    if not (is_user_reifiable_effect env ef) then
        raise_error (Errors.Fatal_EffectCannotBeReified, (BU.format1 "Effect %s cannot be reified" (string_of_lid ef))) e.pos;
    let repr = Env.reify_comp env c u_c in
    let e = mk (Tm_app(reify_op, [(e, aqual)])) top.pos in
    let c =
        if is_total_effect env ef
        then S.mk_Total repr |> TcComm.lcomp_of_comp
        else let ct = { comp_univs = [u_c]
                      ; effect_name = Const.effect_Dv_lid
                      ; result_typ = repr
                      ; effect_args = []
                      ; flags = []
                      }
             in S.mk_Comp ct |> TcComm.lcomp_of_comp
    in
    let e, c, g' = comp_check_expected_typ env e c in
    e, c, Env.conj_guard g (Env.conj_guard g_c g')

  | Tm_app({n=Tm_constant (Const_reflect l)}, [(e, aqual)])->
    if Option.isSome aqual then
      Errors.log_issue e.pos
        (Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
         "Qualifier on argument to reflect is irrelevant and will be ignored");

    if not (is_user_reflectable_effect env l) then
      raise_error (Errors.Fatal_EffectCannotBeReified,
        BU.format1 "Effect %s cannot be reflected" (string_of_lid l)) e.pos;

    let reflect_op, _ = U.head_and_args top in

    begin match Env.effect_decl_opt env l with
    | None ->
      raise_error (Errors.Fatal_EffectNotFound,
        BU.format1 "Effect %s not found (for reflect)" (Ident.string_of_lid l)) e.pos

    | Some (ed, qualifiers) ->
      let env_no_ex, _ = Env.clear_expected_typ env in

      let e, c_e, g_e =
        let e, c, g = tc_tot_or_gtot_term env_no_ex e in
        if not <| TcComm.is_total_lcomp c then
          Errors.log_issue e.pos (Errors.Error_UnexpectedGTotComputation, "Expected Tot, got a GTot computation");
        e, c, g
      in

      let (expected_repr_typ, g_repr), u_a, a, g_a =
        let a, u_a = U.type_u () in
        let a_uvar, _, g_a = TcUtil.new_implicit_var "" e.pos env_no_ex a in
        TcUtil.fresh_effect_repr_en env_no_ex e.pos l u_a a_uvar, u_a, a_uvar, g_a in

      let g_eq = Rel.teq env_no_ex c_e.res_typ expected_repr_typ in

      let eff_args =
        match (SS.compress expected_repr_typ).n with
        | Tm_app (_, _::args) -> args
        | _ ->
          raise_error (Errors.Fatal_UnexpectedEffect,
            BU.format3 "Expected repr type for %s is not an application node (%s:%s)"
              (Ident.string_of_lid l) (Print.tag_of_term expected_repr_typ)
              (Print.term_to_string expected_repr_typ)) top.pos in

      let c = S.mk_Comp ({
        comp_univs=[u_a];
        effect_name = ed.mname;
        result_typ=a;
        effect_args=eff_args;
        flags=[]
      }) |> TcComm.lcomp_of_comp in

      let e = mk (Tm_app(reflect_op, [(e, aqual)])) top.pos in

      let e, c, g' = comp_check_expected_typ env e c in

      let e = S.mk (Tm_meta(e, Meta_monadic(c.eff_name, c.res_typ))) e.pos in

      e, c, Env.conj_guards [g_e; g_repr; g_a; g_eq; g']
    end

  // If we're on the first phase, we don't synth, and just wait for the next phase
  | Tm_app (head, [(tau, None)])
  | Tm_app (head, [(_, Some (Implicit _)); (tau, None)])
        when U.is_synth_by_tactic head && not env.phase1 ->
    (* Got an application of synth_by_tactic, process it *)

    // no "as" clause
    let head, args = U.head_and_args top in
    tc_synth head env args top.pos

  | Tm_app (head, args)
        when U.is_synth_by_tactic head && not env.phase1 ->
    (* We have some extra args, move them out of the way *)
    let args1, args2 =
        match args with
        | (tau, None)::rest ->
            [(tau, None)], rest
        | (a, Some (Implicit b)) :: (tau, None) :: rest ->
            [(a, Some (Implicit b)); (tau, None)], rest
        | _ ->
            raise_error (Errors.Fatal_SynthByTacticError, "synth_by_tactic: bad application") top.pos
    in
    let t1 = mk_app head args1 in
    let t2 = mk_app t1 args2 in
    tc_term env t2

  (* An ordinary application *)
  | Tm_app(head, args) ->
    let env0 = env in
    let env = Env.clear_expected_typ env |> fst |> instantiate_both in
    if debug env Options.High
    then BU.print3 "(%s) Checking app %s, expected type is %s\n"
                    (Range.string_of_range top.pos)
                    (Print.term_to_string top)
                    (Env.expected_typ env0 |> (function None -> "none" | Some t -> Print.term_to_string t));

    //Don't instantiate head; instantiations will be computed below, accounting for implicits/explicits
    let head, chead, g_head = tc_term (no_inst env) head in
    let chead, g_head = TcComm.lcomp_comp chead |> (fun (c, g) -> c, Env.conj_guard g_head g) in
    let e, c, g = if not env.lax && not (Options.lax()) && TcUtil.short_circuit_head head
                  then let e, c, g = check_short_circuit_args env head chead g_head args (Env.expected_typ env0) in
                       // //TODO: this is not efficient:
                       // //      It is quadratic in the size of boolean terms
                       // //      e.g., a && b && c && d ... & zzzz will be huge
                       // let c = if Env.should_verify env &&
                       //         not (U.is_lcomp_partial_return c) &&
                       //         U.is_pure_or_ghost_lcomp c
                       //         then TcUtil.maybe_assume_result_eq_pure_term env e c
                       //         else c in
                       e, c, g
                  else check_application_args env head chead g_head args (Env.expected_typ env0) in
    let e, c, implicits =
        if TcComm.is_tot_or_gtot_lcomp c
        then let e, res_typ, implicits = TcUtil.maybe_instantiate env0 e c.res_typ in
             e, TcComm.set_result_typ_lc c res_typ, implicits
        else e, c, Env.trivial_guard
    in
    if Env.debug env Options.Extreme
    then BU.print1 "Introduced {%s} implicits in application\n" (Rel.print_pending_implicits g);
    let e, c, g' = comp_check_expected_typ env0 e c in
    let gres = Env.conj_guard g g' in
    let gres = Env.conj_guard gres implicits in
    if Env.debug env Options.Extreme
    then BU.print2 "Guard from application node %s is %s\n"
                (Print.term_to_string e)
                (Rel.guard_to_string env gres);
    e, c, gres

  | Tm_match _ ->
    tc_match env top

  | Tm_let ((false, [{lbname=Inr _}]), _) ->
    check_top_level_let env top

  | Tm_let ((false, _), _) ->
    check_inner_let env top

  | Tm_let ((true, {lbname=Inr _}::_), _) ->
    check_top_level_let_rec env top

  | Tm_let ((true, _), _) ->
    check_inner_let_rec env top

and tc_match (env : Env.env) (top : term) : term * lcomp * guard_t =

  (*
   * AR: Typechecking of match expression:
   *
   * match expressions may be optionally annotated with a `return` annotation
   *   for dependent pattern matching
   *
   * When the return annotation is not supplied, we:
   *   -- typecheck the scrutinee
   *   -- typecheck the branches with
   *      -- if the expected type is not set in the env, then create a new uvar for it
   *      -- a new bv, guard_x below, as the scrutinee expression
   *   -- combine the computation types of the branches (TcUtil.bind_cases)
   *      -- with the if_the_else combinator, also adding pattern exhaustiveness checks
   *   -- bind the scrutinee computation type with the combined branches (using guard_x as the bv in bind)
   *
   * When the return annotation is supplied:
   *   -- typecheck the scrutinee
   *   -- typecheck the return annotation
   *   -- typecheck the branches with
   *      -- env with expected type unset
   *      -- a new bv, guard_x, as the scrutinee expression
   *      -- substituting scrutinee bv by guard_x in the return annotation
   *      -- in tc_eqn: substituting guard_x with the pattern expression, and ascribing it on the branch exp
   *   -- if the return annotation was a type:
   *      -- TcUtil.bind_cases as before
   *   -- if the return annotation was a computation type:
   *      -- no need to bind cases, take the comp annotation as is
   *      -- but add the pattern exhaustiveness check in the guard
   *      -- need to substitute guard_x by scrutinee bv back
   *   -- bind the scrutinee computation type with the combined branches (using guard_x as the bv in bind)
   *)

  match (SS.compress top).n with
  | Tm_match(e1, ret_opt, eqns) ->  //ret_opt is the return annotation
    let e1, c1, g1 = tc_term
      (env |> Env.clear_expected_typ |> fst |> instantiate_both)
      e1 in

    let e1, c1 =
        match TcUtil.coerce_views env e1 c1 with
        | Some (e1, c1) -> e1, c1
        | None -> e1, c1 in

    //ret_or_res_typ has type either<either<typ, comp>, typ>
    let env_branches, ret_or_res_typ, ret_opt, g1 =
      match ret_opt with
      | None ->  //no return annotation, set an expected type either from env or a new uvar
        (match Env.expected_typ env with
         | Some t -> env, Inr t, None, g1
         | None ->
           let k, _ = U.type_u() in
           let res_t, _, g = TcUtil.new_implicit_var "match result" e1.pos env k in
           Env.set_expected_typ env res_t, Inr res_t, None, Env.conj_guard g1 g)
      | Some (t_or_c, None) ->
        //typecheck the return annotation and unset expected type in the env if exists,
        //  (we will check the expected type at the end)
        //the branch typechecking (tc_eqn) will typecheck the branch with an ascription
        let env, _ = Env.clear_expected_typ env in
        let t_or_c, g =
          match t_or_c with
           | Inl t -> let k, _ = U.type_u () in
                     let t, _, g = tc_check_tot_or_gtot_term env t k "" in
                     Inl t, g
           | Inr c -> let c, _, g = tc_comp env c in
                     Inr c, g in
        env, Inl t_or_c, Some (t_or_c, None), Env.conj_guard g1 g
      | _ ->
        raise_error (Errors.Fatal_UnexpectedTerm,
          "Tactic is not yet supported with match return") (Env.get_range env) in

    let guard_x, t_eqns =
      let guard_x =
        match ret_opt with
        | None -> S.new_bv (Some e1.pos) c1.res_typ
        | Some _ ->
          (match (e1 |> U.unascribe |> SS.compress).n with
           | Tm_name scrutinee_bv -> scrutinee_bv
           | _ ->
             raise_error (Errors.Fatal_UnexpectedTerm,
               "The scrutinee must be a variable when a return annotation is supplied with a match") e1.pos) in
      guard_x,
      eqns |> List.map (tc_eqn guard_x env_branches ret_opt) in

    let c_branches, g_branches, erasable =
      let cases, g, erasable =
          List.fold_right
                (fun (branch, f, eff_label, cflags, c, g, erasable_branch) (caccum, gaccum, erasable) ->
                     (f, eff_label, cflags, c)::caccum,
                     Env.conj_guard g gaccum,
                     erasable || erasable_branch)
                t_eqns
                ([], Env.trivial_guard, false) in
      
      (* note that bind_cases adds an exhaustiveness check *)
      match ret_or_res_typ with
      | Inr res_t ->
        //no return annotation, just bind_cases
        TcUtil.bind_cases env res_t cases guard_x, g, erasable

      | Inl (Inl t) ->  //a return annotation, with type
        //set the type in the lcomp of the branches, and then bind_cases

        let cases = List.map
          (fun (f, eff_label, cflags, c) ->
             (f, eff_label, cflags, (fun b -> TcComm.set_result_typ_lc (c b) t))) cases in
        
        TcUtil.bind_cases env t cases guard_x, g, erasable

      | Inl (Inr c) ->  //a return annotation, with computation type
        //we don't need to bind the cases
        //but we still need to weaken the guards for the branches with the
        //negation of the branch conditions that come before this branch
        let fmls, gs =  //branch conditions, branch guards
          t_eqns
          |> List.map (fun (_, f, _, _, _, g, _) -> (f, g))
          |> List.unzip in
        let neg_conds, exhaustiveness_cond = TcUtil.get_neg_branch_conds fmls in
        let g =
          List.map2 TcComm.weaken_guard_formula gs neg_conds
          |> List.fold_left Env.conj_guard Env.trivial_guard in
        let g_exhaustiveness =
          U.mk_imp exhaustiveness_cond U.t_false
          |> TcUtil.label Err.exhaustiveness_check (Env.get_range env)  //label
          |> NonTrivial
          |> Env.guard_of_guard_formula in
        TcComm.lcomp_of_comp c, Env.conj_guard g g_exhaustiveness, erasable in

    //combine with e1's computation type
    let cres = TcUtil.bind e1.pos env (Some e1) c1 (Some guard_x, c_branches) in

    let cres =
      if erasable
      then (* promote cres to ghost *)
           let e = U.exp_true_bool in
           let c = mk_GTotal' U.t_bool (Some U_zero) in
           TcUtil.bind e.pos env (Some e) (TcComm.lcomp_of_comp c) (None, cres)
      else cres
    in

    let e =
      let mk_match scrutinee =
        (* TODO (KM) : I have the impression that lifting here is useless/wrong : the scrutinee should always be pure... *)
        (* let scrutinee = TypeChecker.Util.maybe_lift env scrutinee c1.eff_name cres.eff_name c1.res_typ in *)
        let branches = t_eqns |> List.map (fun ((pat, wopt, br), _, eff_label, _, _, _, _) ->
          pat, wopt, TcUtil.maybe_lift env br eff_label cres.eff_name cres.res_typ
        ) in
        let e = mk (Tm_match(scrutinee, ret_opt, branches)) top.pos in
        let e = TcUtil.maybe_monadic env e cres.eff_name cres.res_typ in
        //The ascription with the result type is useful for re-checking a term, translating it to Lean etc.
        //AR: revisit, for now doing only if return annotation is not provided
        match ret_or_res_typ with
        | Inr _ -> mk (Tm_ascribed(e, (Inl cres.res_typ, None), Some cres.eff_name)) e.pos
        | Inl _ -> e
      in

      //see issue #594: if the scrutinee is impure, then explicitly sequence it with an impure let binding
      //                to protect it from the normalizer optimizing it away
      if TcUtil.is_pure_or_ghost_effect env c1.eff_name
      then mk_match e1
      else
        (* generate a let binding for e1 *)
        let e_match = mk_match (S.bv_to_name guard_x) in
        let lb = U.mk_letbinding (Inl guard_x) [] c1.res_typ (Env.norm_eff_name env c1.eff_name) e1 [] e1.pos in
        let e = mk (Tm_let((false, [lb]), SS.close [S.mk_binder guard_x] e_match)) top.pos in
        TcUtil.maybe_monadic env e cres.eff_name cres.res_typ
    in

    //AR: finally, if we typechecked with the return annotation,
    //    we need to make sure that we check the expected type in the env
    let e, cres, g_expected_type =
      match ret_opt with
      | None -> e, cres, Env.trivial_guard
      | Some _ -> comp_check_expected_typ env e cres in

    if debug env Options.Extreme
    then BU.print2 "(%s) Typechecked Tm_match, comp type = %s\n"
                      (Range.string_of_range top.pos) (TcComm.lcomp_to_string cres);

    e, cres, Env.conj_guards [g1; g_branches; g_expected_type]

  | _ ->
    failwith (BU.format1 "tc_match called on %s\n" (Print.tag_of_term top))

and tc_synth head env args rng =
    let tau, atyp =
    match args with
    | (tau, None)::[] ->
        tau, None
    | (a, Some (Implicit _)) :: (tau, None) :: [] ->
        tau, Some a
    | _ ->
        raise_error (Errors.Fatal_SynthByTacticError, "synth_by_tactic: bad application") rng
    in

    let typ =
        match atyp with
        | Some t -> t
        | None -> begin match Env.expected_typ env with
                  | Some t -> t
                  | None -> raise_error (Errors.Fatal_SynthByTacticError, "synth_by_tactic: need a type annotation when no expected type is present") (Env.get_range env)
                  end
    in

    // Check the result type
    let typ, _, g1 = tc_term (Env.set_expected_typ env (fst <| U.type_u ())) typ in
    Rel.force_trivial_guard env g1;

    // Check the tactic
    let tau, _, g2 = tc_tactic t_unit t_unit env tau in
    Rel.force_trivial_guard env g2;

    let t = env.synth_hook env typ ({ tau with pos = rng }) in
    if Env.debug env <| Options.Other "Tac" then
        BU.print1 "Got %s\n" (Print.term_to_string t);

    // Should never trigger, meta-F* will check it before.
    TcUtil.check_uvars tau.pos t;

    t, TcComm.lcomp_of_comp <| mk_Total typ, Env.trivial_guard

and tc_tactic (a:typ) (b:typ) (env:Env.env) (tau:term) : term * lcomp * guard_t =
    let env = { env with failhard = true } in
    tc_check_tot_or_gtot_term env tau (t_tac_of a b) ""

and check_instantiated_fvar (env:Env.env) (v:S.var) (q:option<S.fv_qual>) (e:term) (t0:typ)
  : term * lcomp * guard_t
  =
  let is_data_ctor = function
      | Some Data_ctor
      | Some (Record_ctor _) -> true
      | _ -> false
  in
  if is_data_ctor q && not (Env.is_datacon env v.v) then
    raise_error (Errors.Fatal_MissingDataConstructor,
                 BU.format1 "Expected a data constructor; got %s" (string_of_lid v.v))
                (Env.get_range env);

  (* remove inaccesible pattern implicits, make them regular implicits *)
  let t = U.remove_inacc t0 in

  let e, t, implicits = TcUtil.maybe_instantiate env e t in
//  BU.print3 "Instantiated type of %s from %s to %s\n" (Print.term_to_string e) (Print.term_to_string t0) (Print.term_to_string t);
  let tc =
    if Env.should_verify env
    then Inl t
    else Inr (TcComm.lcomp_of_comp <| mk_Total t)
  in

  value_check_expected_typ env e tc implicits

(************************************************************************************************************)
(* Type-checking values:                                                                                    *)
(*   Values have no special status, except that we structure the code to promote a value type t to a Tot t  *)
(************************************************************************************************************)
and tc_value env (e:term) : term
                          * lcomp
                          * guard_t =

  //As a general naming convention, we use e for the term being analyzed and its subterms as e1, e2, etc.
  //We use t and its variants for the type of the term being analyzed
  let env = Env.set_range env e.pos in
  let top = SS.compress e in
  match top.n with
  | Tm_bvar x ->
    (* This can happen if user tactics build an ill-scoped term *)
    raise_error (Errors.Error_IllScopedTerm,
                 BU.format1 "Violation of locally nameless convention: %s" (Print.term_to_string top))
                top.pos

  | Tm_uvar (u, s) -> //the type of a uvar is given directly with it; we do not recheck the type
    //FIXME: Check context inclusion?
    value_check_expected_typ env e (Inl (SS.subst' s u.ctx_uvar_typ)) Env.trivial_guard

  //only occurs where type annotations are missing in source programs
  //or the program has explicit _ for missing terms
  | Tm_unknown ->
    let r = Env.get_range env in
    let t, _, g0 =
        match Env.expected_typ env with
        | None ->
          let k, u = U.type_u () in
          TcUtil.new_implicit_var "type of user-provided implicit term" r env k
        | Some t -> t, [], Env.trivial_guard in
    
    let e, _, g1 = TcUtil.new_implicit_var
          ("user-provided implicit term at " ^ (Range.string_of_range r))
          r env t in
    e, S.mk_Total t |> TcComm.lcomp_of_comp, (Env.conj_guard g0 g1)

  | Tm_name x ->
    let t, rng =
        if env.use_bv_sorts
        then x.sort, S.range_of_bv x
        else Env.lookup_bv env x in
    let x = S.set_range_of_bv ({x with sort=t}) rng in
    Env.insert_bv_info env x t;
    let e = S.bv_to_name x in
    let e, t, implicits = TcUtil.maybe_instantiate env e t in
    let tc = if Env.should_verify env then Inl t else Inr (TcComm.lcomp_of_comp <| mk_Total t) in
    value_check_expected_typ env e tc implicits

  | Tm_uinst({n=Tm_fvar fv}, _)
  | Tm_fvar fv when S.fv_eq_lid fv Const.synth_lid && not env.phase1 ->
    raise_error (Errors.Fatal_BadlyInstantiatedSynthByTactic, "Badly instantiated synth_by_tactic") (Env.get_range env)

  | Tm_uinst({n=Tm_fvar fv}, us) ->
    let us = List.map (tc_universe env) us in
    let (us', t), range = Env.lookup_lid env fv.fv_name.v in
    let fv = S.set_range_of_fv fv range in
    maybe_warn_on_use env fv;
    if List.length us <> List.length us' then
      raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
                   BU.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                                  (Print.fv_to_string fv)
                                  (string_of_int (List.length us))
                                  (string_of_int (List.length us')))
                    (Env.get_range env);

    (* Make sure the instantiated universes match with the ones
     * provided by the Tm_uinst. The universes in us' will usually
     * be U_unif with unresolved uvars, but they could be U_names
     * when the definition is recursive. *)
    List.iter2
      (fun ul ur -> match ul, ur with
        | U_unif u'', _ -> UF.univ_change u'' ur
        // TODO: more cases? we cannot get U_succ or U_max here I believe...
        | U_name n1, U_name n2 when Ident.ident_equals n1 n2 -> ()
        | _ ->
          raise_error (Errors.Fatal_IncompatibleUniverse,
                       BU.format3 "Incompatible universe application for %s, expected %s got %s\n"
                                  (Print.fv_to_string fv)
                                  (Print.univ_to_string ul)
                                  (Print.univ_to_string ur))
                      (Env.get_range env))
      us' us;

    Env.insert_fv_info env fv t;
    let e = S.mk_Tm_uinst (mk (Tm_fvar fv) e.pos) us in
    check_instantiated_fvar env fv.fv_name fv.fv_qual e t

  (* not an fvar, fail *)
  | Tm_uinst(_, us) ->
    raise_error (Errors.Fatal_UnexpectedNumberOfUniverse,
                 "Universe applications are only allowed on top-level identifiers")
                (Env.get_range env)

  | Tm_fvar fv ->
    let (us, t), range = Env.lookup_lid env fv.fv_name.v in
    let fv = S.set_range_of_fv fv range in
    maybe_warn_on_use env fv;
    if Env.debug env <| Options.Other "Range"
    then BU.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s\n"
            (Print.lid_to_string (lid_of_fv fv))
            (Range.string_of_range e.pos)
            (Range.string_of_range range)
            (Range.string_of_use_range range)
            (Print.term_to_string t);
    Env.insert_fv_info env fv t;
    let e = S.mk_Tm_uinst (mk (Tm_fvar fv) e.pos) us in
    check_instantiated_fvar env fv.fv_name fv.fv_qual e t

  | Tm_constant c ->
    let t = tc_constant env top.pos c in
    let e = mk (Tm_constant c) e.pos in
    value_check_expected_typ env e (Inl t) Env.trivial_guard

  | Tm_arrow(bs, c) ->
    let bs, c = SS.open_comp bs c in
    let env0 = env in
    let env, _ = Env.clear_expected_typ env in
    (* type checking the binders *)
    let bs, env, g, us = tc_binders env bs in
    (* type checking the computation *)
    let c, uc, f = tc_comp env c in
    let e = {U.arrow bs c with pos=top.pos} in
    (* checks the SMT pattern associated with this function is properly defined with regard to context *)
    check_smt_pat env e bs c;
    (* taking the maximum of the universes of the computation and of all binders *)
    let u = S.U_max (uc::us) in
    (* create a universe of level u *)
    let t = mk (Tm_type u) top.pos in
    let g = Env.conj_guard g (Env.close_guard_univs us bs f) in
    let g = TcUtil.close_guard_implicits env false bs g in
    value_check_expected_typ env0 e (Inl t) g

  | Tm_type u ->
    let u = tc_universe env u in
    let t = mk (Tm_type(S.U_succ u)) top.pos in
    let e = mk (Tm_type u) top.pos in
    value_check_expected_typ env e (Inl t) Env.trivial_guard

  | Tm_refine(x, phi) ->
    let x, phi = SS.open_term [S.mk_binder x] phi in
    let env0 = env in
    let env, _ = Env.clear_expected_typ env in
    let x, env, f1, u = tc_binder env (List.hd x) in
    if debug env Options.High
    then BU.print3 "(%s) Checking refinement formula %s; binder is %s\n"
        (Range.string_of_range top.pos) (Print.term_to_string phi) (Print.bv_to_string x.binder_bv);
    let t_phi, _ = U.type_u () in
    let phi, _, f2 = tc_check_tot_or_gtot_term env phi t_phi
      "refinement formula must be pure or ghost" in
    let e = {U.refine x.binder_bv phi with pos=top.pos} in
    let t = mk (Tm_type u) top.pos in
    let g = Env.conj_guard f1 (Env.close_guard_univs [u] [x] f2) in
    let g = TcUtil.close_guard_implicits env false [x] g in
    value_check_expected_typ env0 e (Inl t) g

  | Tm_abs(bs, body, _) ->
    (* in case we use type variables which are implicitly quantified, we add quantifiers here *)
    let bs = TcUtil.maybe_add_implicit_binders env bs in
    if Env.debug env Options.Medium
    then BU.print1 "Abstraction is: %s\n" (Print.term_to_string ({top with n=Tm_abs(bs, body, None)}));
    let bs, body = SS.open_term bs body in
    tc_abs env top bs body

  | _ ->
    failwith (BU.format2 "Unexpected value: %s (%s)" (Print.term_to_string top) (Print.tag_of_term top))

and tc_constant (env:env_t) r (c:sconst) : typ =
  let res =
     match c with
      | Const_unit -> t_unit
      | Const_bool _ -> t_bool
      | Const_int (_, None) -> t_int
      | Const_int (_, Some msize) ->
        tconst (match msize with
          | Signed, Int8 -> Const.int8_lid
          | Signed, Int16 -> Const.int16_lid
          | Signed, Int32 -> Const.int32_lid
          | Signed, Int64 -> Const.int64_lid
          | Unsigned, Int8 -> Const.uint8_lid
          | Unsigned, Int16 -> Const.uint16_lid
          | Unsigned, Int32 -> Const.uint32_lid
          | Unsigned, Int64 -> Const.uint64_lid)
      | Const_string _ -> t_string
      | Const_real _ -> t_real
      | Const_float _ -> t_float
      | Const_char _ ->
        FStar.Syntax.DsEnv.try_lookup_lid env.dsenv FStar.Parser.Const.char_lid
        |> BU.must

      (* TODO (KM) : Try to change this to U.ktype1 *)
      (* (because that's the minimal universe level of the WP) *)
      (* and see how much code breaks *)
      | Const_effect -> U.ktype0 //NS: really?
      | Const_range _ -> t_range
      | Const_range_of
      | Const_set_range_of
      | Const_reify
      | Const_reflect _ ->
        raise_error (Errors.Fatal_IllTyped, BU.format1 "Ill-typed %s: this constant must be fully applied"
                                 (Const.const_to_string c)) r

      | _ -> raise_error (Errors.Fatal_UnsupportedConstant, "Unsupported constant") r
  in
  SS.set_use_range r res


(************************************************************************************************************)
(* Type-checking computation types                                                                          *)
(************************************************************************************************************)
and tc_comp env c : comp                                      (* checked version of c                       *)
                  * universe                                  (* universe of c                              *)
                  * guard_t =                                 (* logical guard for the well-formedness of c *)
  let c0 = c in
  match c.n with
    | Total (t, _) ->
      let k, u = U.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k "" in
      mk_Total' t (Some u), u, g

    | GTotal (t, _) ->
      let k, u = U.type_u () in
      let t, _, g = tc_check_tot_or_gtot_term env t k "" in
      mk_GTotal' t (Some u), u, g

    | Comp c ->
      let head = S.fvar c.effect_name delta_constant None in
      let head = match c.comp_univs with
         | [] -> head
         | us -> S.mk (Tm_uinst(head, us)) c0.pos in
      let tc = mk_Tm_app head ((as_arg c.result_typ)::c.effect_args) c.result_typ.pos in
      let tc, _, f =
        (*
         * AR: 11/18: TcUtil.weaken_result_typ by default logs a typing error and continues
         *            Failing hard when typechecking computation types, since errors
         *              like missing effect args can result in broken invariants in
         *              the unifier or the normalizer
         *)
        tc_check_tot_or_gtot_term ({ env with failhard = true }) tc S.teff "" in
      let head, args = U.head_and_args tc in
      let comp_univs = match (SS.compress head).n with
        | Tm_uinst(_, us) -> us
        | _ -> [] in
      let _, args = U.head_and_args tc in
      let res, args = List.hd args, List.tl args in
      let flags, guards = c.flags |> List.map (function
        | DECREASES (Decreases_lex l) ->
          let env, _ = Env.clear_expected_typ env in
          let l, g = l |> List.fold_left (fun (l, g) e ->
            let e, _, g_e = tc_tot_or_gtot_term env e in
            l@[e], Env.conj_guard g g_e) ([], Env.trivial_guard) in
          DECREASES (Decreases_lex l), g
        | DECREASES (Decreases_wf (rel, e)) ->
          (*
           * We will check that for a fresh uvar (?u:Type),
           *   rel:well_founded_relation ?u  and
           *   e:?u
           *)
          let env, _ = Env.clear_expected_typ env in
          let t, u_t = U.type_u () in
          let a, _, g_a = TcUtil.new_implicit_var
            "implicit for type of the well-founded relation in decreases clause"
            rel.pos
            env
            t in
          let wf_t = mk_Tm_app
            (Env.fvar_of_nonqual_lid env Const.well_founded_relation_lid)
            [as_arg a] rel.pos in
          let rel, _, g_rel = tc_tot_or_gtot_term (Env.set_expected_typ env wf_t) rel in
          let e, _, g_e = tc_tot_or_gtot_term (Env.set_expected_typ env a) e in
          DECREASES (Decreases_wf (rel, e)),
          Env.conj_guards [g_a; g_rel; g_e]
        | f -> f, Env.trivial_guard) |> List.unzip in
      let u = env.universe_of env (fst res) in
      let c = mk_Comp ({c with
          comp_univs=comp_univs;
          result_typ=fst res;
          flags = flags;
          effect_args=args}) in
      let u_c = c |> TcUtil.universe_of_comp env u in
      c, u_c, List.fold_left Env.conj_guard f guards

and tc_universe env u : universe =
   let rec aux u =
       let u = SS.compress_univ u in
       match u with
        | U_bvar _  -> failwith "Impossible: locally nameless"
        | U_unknown -> failwith "Unknown universe"
        | U_unif _
        | U_zero    -> u
        | U_succ u  -> U_succ (aux u)
        | U_max us  -> U_max (List.map aux us)
        | U_name x  ->
          if env.use_bv_sorts || Env.lookup_univ env x
          then u
          else failwith ("Universe variable " ^ (Print.univ_to_string u) ^ " not found")
   in if env.lax_universes then U_zero
      else (match u with
            | U_unknown -> U.type_u () |> snd
            | _ -> aux u)

(* Several complex cases from the main type-checker are factored in to separate functions below *)


(*
 * Called when typechecking a Tm_abs node
 * 
 * t0 is the expected type in the environment for the Tm_abs node
 *)
and tc_abs_expected_function_typ env (bs:binders) t0 (body:term)
: (option<typ>        (* any remaining expected type to check against *)
* binders             (* binders from the abstraction checked against the binders in the corresponding Typ_fun, if any *)
* binders             (* let rec binders, suitably guarded with termination check, if any *)
* option<comp>        (* the expected comp type for the body *)
* Env.env             (* environment for the body *)
* term                (* the body itself *)
* guard_t)            (* accumulated guard from checking the binders, well-formed in the initial env *)

= match t0 with
  | None -> (* no expected type; just build a function type from the binders in the term *)
    (* env.letrecs are the current letrecs we are checking *)
    let _ = match env.letrecs with
      | [] -> ()
      | _ -> failwith "Impossible: Can't have a let rec annotation but no expected type" in
    let bs, envbody, g_env, _ = tc_binders env bs in
    None, bs, [], None, envbody, body, g_env

  | Some t ->
    let t = SS.compress t in
    let rec as_function_typ norm t =
      match (SS.compress t).n with
      (* we are type checking abs so all cases except arrow are required for definitional equality *)
      | Tm_uvar _
      | Tm_app({n=Tm_uvar _}, _) ->
        (* expected a uvar; build a function type from the term and unify with it *)
        let _ = match env.letrecs with | [] -> () | _ -> failwith "Impossible" in
        let bs, envbody, g_env, _ = tc_binders env bs in
        let envbody, _ = Env.clear_expected_typ envbody in
        Some t, bs, [], None, envbody, body, g_env

      (* CK: add this case since the type may be f:(a -> M b wp){φ}, in which case I drop the refinement *)
      (* NS: 07/21 dropping the refinement is not sound; we need to check that f validates phi. See Bug #284 *)
      | Tm_refine (b, _) ->
        let _, bs, bs', copt, env_body, body, g_env = as_function_typ norm b.sort in
        //we pass type `t` out to check afterwards the full refinement type is respected
        Some t, bs, bs', copt, env_body, body, g_env

      | Tm_arrow(bs_expected, c_expected) ->
        let bs_expected, c_expected = SS.open_comp bs_expected c_expected in
        (* Two main interesting bits here;
           1. The expected type may have
              a. more immediate binders, whereas the function may itself return a function
              b. fewer immediate binders, meaning that the function type is explicitly curried
           2. If the function is a let-rec and it is to be total, then we need to add termination checks.
         *)
        let check_actuals_against_formals env bs bs_expected body
          : Env.env
          * binders
          * guard_t
          * comp
          * term
          = let rec handle_more (env_bs, bs, more, guard_env, subst) c_expected body =
              match more with
              | None -> //number of binders match up
                env_bs, bs, guard_env, SS.subst_comp subst c_expected, body

              | Some (Inr more_bs_expected) -> //more formal parameters; expect the body to return a total function
                let c = S.mk_Total (U.arrow more_bs_expected c_expected) in
                env_bs, bs, guard_env, SS.subst_comp subst c, body

              | Some (Inl more_bs) ->  //more actual args
                let c = SS.subst_comp subst c_expected in
                (* the expected type is explicitly curried *)
                if Options.ml_ish () || U.is_named_tot c then
                  let t = N.unfold_whnf env_bs (U.comp_result c) in
                  match t.n with
                  | Tm_arrow(bs_expected, c_expected) ->
                    let bs_expected, c_expected = SS.open_comp bs_expected c_expected in
                    let (env_bs_bs', bs', more, guard'_env_bs, subst) = tc_abs_check_binders env_bs more_bs bs_expected in
                    let guard'_env = Env.close_guard env_bs bs guard'_env_bs in
                    handle_more (env_bs_bs', bs@bs', more, Env.conj_guard guard_env guard'_env, subst) c_expected body
                  | _ ->
                    let body = U.abs more_bs body None in
                    env_bs, bs, guard_env, c, body
                else let body = U.abs more_bs body None in
                     env_bs, bs, guard_env, c, body
            in  //end let rec handle_more

            handle_more (tc_abs_check_binders env bs bs_expected) c_expected body
        in  //end let rec check_actuals_against_formals

        let mk_letrec_env envbody bs c =
          let letrecs = guard_letrecs envbody bs c in
          let envbody = {envbody with letrecs=[]} in
          let envbody, letrec_binders, g =
            letrecs |> List.fold_left (fun (env, letrec_binders, g) (l,t,u_names) ->
              //let t = N.normalize [Env.EraseUniverses; Env.Beta] env t in
              //printfn "Checking let rec annot: %s\n" (Print.term_to_string t);
              let t, _, g' = tc_term (Env.clear_expected_typ env |> fst) t in
              let env = Env.push_let_binding env l (u_names, t) in
              let lb = match l with
                | Inl x -> S.mk_binder ({x with sort=t})::letrec_binders
                | _ -> letrec_binders in
              env, lb, Env.conj_guard g g') (envbody, [], Env.trivial_guard) in
          (envbody, letrec_binders, Env.close_guard envbody bs g)
        in

        (* Set letrecs to [] before calling check_actuals_against_formals,
         * then restore. That function will typecheck the types of the binders
         * and having letrecs set will make a mess. *)
        let envbody = { env with letrecs = [] } in
        let envbody, bs, g_env, c, body = check_actuals_against_formals envbody bs bs_expected body in
        let envbody = { envbody with letrecs = env.letrecs } in
        let envbody, letrecs, g_annots = mk_letrec_env envbody bs c in
        let envbody = Env.set_expected_typ envbody (U.comp_result c) in
        Some t, bs, letrecs, Some c, envbody, body, Env.conj_guard g_env g_annots

      | _ -> (* expected type is not a function;
               try normalizing it first;
               otherwise synthesize a type and check it against the given type *)
        if not norm
        then as_function_typ true (t |> N.unfold_whnf env |> U.unascribe)  //AR: without the unascribe we lose out on some arrows
        else let _, bs, _, c_opt, envbody, body, g_env = tc_abs_expected_function_typ env bs None body in
            Some t, bs, [], c_opt, envbody, body, g_env
    in
    as_function_typ false t

(***************************************************************************************************************)
    (* check_binders checks that the binders bs of top                                                             *)
    (*               are compatible with the binders of the function typ expected by the context                   *)
    (*               If there are more bs than bs_expected, we only check a prefix and the suffix is returned Inl  *)
    (*               If there are more bs_expected than bs, the suffix of bs_expected is returned Inr              *)
(***************************************************************************************************************)
and tc_abs_check_binders env bs bs_expected  : Env.env                         (* env extended with a prefix of bs  *)
                                             * binders                         (* the type-checked prefix of bs     *)
                                             * option<either<binders,binders>> (* suffix of either bs or bs_expected*)
                                             * guard_t                         (* accumulated logical guard
                                                                                  well-formed in argument env *)
                                             * subst_t =                       (* alpha conv. of bs_expected to bs  *)
  let rec aux (env, subst) (bs:binders) (bs_expected:binders)
    : Env.env
    * binders
    * option<either<binders,binders>>
    * guard_t    //guard is well-formed in the input environment
    * subst_t =
    match bs, bs_expected with
    | [], [] -> env, [], None, Env.trivial_guard, subst

    | ({binder_qual=None})::_, ({binder_bv=hd_e;binder_qual=q;binder_attrs=attrs})::_
      when S.is_implicit_or_meta q ->
      (* When an implicit is expected, but the user provided an
       * explicit binder, insert a nameless implicit binder. *)
      let bv = S.new_bv (Some (Ident.range_of_id hd_e.ppname)) (SS.subst subst hd_e.sort) in
      aux (env, subst) ((S.mk_binder_with_attrs bv q attrs) :: bs) bs_expected

    | ({binder_bv=hd;binder_qual=imp;binder_attrs=attrs})::bs,
      ({binder_bv=hd_expected;binder_qual=imp';binder_attrs=attrs'})::bs_expected -> begin
        (* These are the discrepancies in qualifiers that we allow *)
        let special q1 q2 = match q1, q2 with
        | Some (Meta _), Some (Meta _) -> true (* don't compare the metaprograms *)
        | None, Some Equality -> true
        | Some (Implicit _), Some (Meta _) -> true
        | _ -> false in
  
        if not (special imp imp') && U.eq_aqual imp imp' <> U.Equal
        then raise_error (Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                          BU.format1 "Inconsistent implicit argument annotation on argument %s" (Print.bv_to_string hd))
                         (S.range_of_bv hd)
        end;
        
        (* since binders depend on previous ones, we accumulate a substitution *)
        let expected_t = SS.subst subst hd_expected.sort in
        let t, g_env =
          match (U.unmeta hd.sort).n with
          | Tm_unknown -> expected_t, Env.trivial_guard
            (* in case we have an annotation on both implementation and declaration, we:
             * 1) type check the implementation type
             * 2) add an extra guard that the two types must be equal (use_eq will be used in Rel.teq
             *)
          | _ ->
            if Env.debug env Options.High then BU.print1 "Checking binder %s\n" (Print.bv_to_string hd);
            let t, _, g1_env = tc_tot_or_gtot_term env hd.sort in
            let g2_env =
              //cf issue #57 (the discussion at the end about subtyping vs. equality in check_binders)
              //check that the context is more demanding of the argument type
              match Rel.teq_nosmt env t expected_t with
              | Some g -> g |> Rel.resolve_implicits env
              | None ->
                match Rel.get_subtyping_prop env expected_t t with
                | None -> raise_error (Err.basic_type_error env None expected_t t) (Env.get_range env)
                | Some g_env ->
                  TcUtil.label_guard
                    hd.sort.pos
                    "Type annotation on parameter incompatible with the expected type"
                    g_env in
            t, Env.conj_guard g1_env g2_env in
        
        let hd = {hd with sort=t} in
        let b = {binder_bv=hd;binder_qual=imp;binder_attrs=attrs} in
        let b_expected = ({binder_bv=hd_expected;binder_qual=imp';binder_attrs=attrs'}) in
        let env_b = push_binding env b in
        let subst = maybe_extend_subst subst b_expected (S.bv_to_name hd) in
        let env_bs, bs, rest, g'_env_b, subst = aux (env_b, subst) bs bs_expected in
        let g'_env = Env.close_guard env_bs [b] g'_env_b in
        env_bs, b::bs, rest, Env.conj_guard g_env g'_env, subst

    | rest, [] ->
      env, [], Some (Inl rest), Env.trivial_guard, subst

    | [], rest ->
      env, [], Some (Inr rest), Env.trivial_guard, subst in

      aux (env, []) bs bs_expected

(*******************************************************************************************************************)
(* Type-checking abstractions, aka lambdas                                                                         *)
(*    top = fun bs -> body, although bs and body must already be opened                                            *)
(*******************************************************************************************************************)
and tc_abs env (top:term) (bs:binders) (body:term) : term * lcomp * guard_t =
    let fail :string -> typ -> 'a = fun msg t ->
        raise_error (Err.expected_a_term_of_type_t_got_a_function env msg t top) (top.pos) in

    (* whether to try first to use unification for solving sub-typing constraints or only propagate to the SMT solver *)
    let use_eq = env.use_eq in
    (* topt is the expected type of the expression obtained from the env *)
    let env, topt = Env.clear_expected_typ env in

    if Env.debug env Options.High
    then BU.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
          (match topt with | None -> "None" | Some t -> Print.term_to_string t)
          (if env.top_level then "true" else "false");

    let tfun_opt, bs, letrec_binders, c_opt, envbody, body, g_env =
      tc_abs_expected_function_typ env bs topt body in

    if Env.debug env Options.Extreme
    then BU.print3 "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
           (match tfun_opt with
            | None -> "None"
            | Some t -> Print.term_to_string t)
           (match c_opt with
            | None -> "None"
            | Some t -> Print.comp_to_string t)
           (match Env.expected_typ envbody with
            | None -> "None"
            | Some t -> Print.term_to_string t);

    if Env.debug env <| Options.Other "NYC"
    then BU.print2 "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
          (Print.binders_to_string ", " bs)
          (guard_to_string env g_env);

    let envbody = Env.set_range envbody body.pos in
    let body, cbody, guard_body =
      (*
       * AR: Special casing the typechecking of the body when it is a M.reflect e
       *     If so, and c_opt is not None, i.e. we have an expected type in the env,
       *       we make the body as (M.reflect e) <: c_opt
       *     Basically, typechecking a reflect can be made better by the effect indices
       *     See also special casing of M.reflect <: C in the same file
       *)
      let envbody, body, should_check_expected_effect =
        if c_opt |> is_some &&
           (match (SS.compress body).n with  //body is an M.reflect
            | Tm_app (head, args) when List.length args = 1 ->
              (match (SS.compress head).n with
               | Tm_constant (Const_reflect _) -> true
               | _ -> false)
            | _ -> false)
        then
          Env.clear_expected_typ envbody |> fst,
          S.mk
            (Tm_ascribed (body, (Inr (c_opt |> must), None), None))
            Range.dummyRange,
          false
        else 
          envbody,
          body,
          (match c_opt, (SS.compress body).n with
           | None, Tm_ascribed (_, (Inr expected_c, _), _) ->
             //body is already ascribed a computation type;
             //don't check it again
             //Not only is it redundant and inefficient, it also sometimes leads to bizarre errors
             //e.g., Issue #1208
             false
           | _ -> true)
      in
      let body, cbody, guard_body =
        tc_term ({envbody with top_level=false; use_eq=use_eq}) body in

      //we don't abstract over subtyping constraints; so solve them now
      //but leave out the tactics constraints for later so that the tactic
      //can have a more global view of all the constraints
      let guard_body = Rel.solve_non_tactic_deferred_constraints envbody guard_body in

      if should_check_expected_effect
      then let cbody, g_lc = TcComm.lcomp_comp cbody in
           let body, cbody, guard = check_expected_effect
             ({envbody with use_eq=use_eq})
             c_opt (body, cbody) in
           body, cbody, Env.conj_guard guard_body (Env.conj_guard g_lc guard)
      else let cbody, g_lc = TcComm.lcomp_comp cbody in
           body, cbody, Env.conj_guard guard_body g_lc
    in

    let guard = if env.top_level || not(Env.should_verify env)
                then Env.conj_guard (Rel.discharge_guard env g_env)
                                    (Rel.discharge_guard envbody guard_body)
                else let guard = Env.conj_guard g_env (Env.close_guard env (bs@letrec_binders) guard_body) in
                     guard in

    let guard = TcUtil.close_guard_implicits env false bs guard in //TODO: this is a noop w.r.t scoping; remove it and the eager_subtyping flag
    let tfun_computed = U.arrow bs cbody in
    let e = U.abs bs body (Some (U.residual_comp_of_comp (dflt cbody c_opt))) in
    (*
     * AR: there are three types in the code above now:
     *     topt : option<term> -- the original annotation
     *     tfun_opt : option<term> -- a definitionally equal type to topt (e.g. when topt is not an arrow but can be reduced to one)
     *     tfun_computed : term -- computed type of the abstraction
     *
     *     the following code has the logic for which type to package the input expression with
     *     if tfun_opt is Some we are guaranteed that topt is also Some, and in that case, we use Some?.v topt
     *       in this case earlier we were returning Some?.v tfun_opt but that means we lost out on the user annotation
     *     if tfun_opt is None, then so is topt and we just return tfun_computed
     *)
    let e, tfun, guard = match tfun_opt with
        | Some t ->
           let t = SS.compress t in
           let t_annot =
             match topt with
             | Some t -> t
             | None -> failwith "Impossible! tc_abs: if tfun_computed is Some, expected topt to also be Some" in
           begin match t.n with
                | Tm_arrow _ ->
                    //we already checked the body to have the expected type; so, no need to check again
                    //just repackage the expression with this type; t is guaranteed to be alpha equivalent to tfun_computed
                    e, t_annot, guard
                | _ ->
                    let lc = S.mk_Total tfun_computed |> TcComm.lcomp_of_comp in
                    let e, _, guard' = TcUtil.check_has_type_maybe_coerce env e lc t in  //QUESTION: t should also probably be t_annot here
                    e, t_annot, Env.conj_guard guard guard'
           end

        | None -> e, tfun_computed, guard in

    let c = mk_Total tfun in
    let c, g = TcUtil.strengthen_precondition None env e (TcComm.lcomp_of_comp c) guard in

    e, c, g

(******************************************************************************)
(* Type-checking applications: Tm_app head args                               *)
(*      head is already type-checked has comp type chead, with guard ghead    *)
(******************************************************************************)
and check_application_args env head (chead:comp) ghead args expected_topt : term * lcomp * guard_t=
    let n_args = List.length args in
    let r = Env.get_range env in
    let thead = U.comp_result chead in
    if debug env Options.High then BU.print2 "(%s) Type of head is %s\n" (Range.string_of_range head.pos) (Print.term_to_string thead);

    (* given |- head : chead | ghead
           where head is a computation returning a function of type (bs0@bs -> cres)
           and the paramters bs0 have been applied to the arguments in arg_comps_rev (in reverse order)
        and args_comps_rev = [(argn, _, cn), ..., (arg0, _, c0)]


        This function builds
            head arg0 ... argn : M (bs -> cres) wp
        where in the case where
            bs = [], i.e., a full application
                M, wp is built using
                         bind chead (bind c0 (bind c1 ... (bind cn cres)))
            bs = _::_, i.e., a partial application
                M, wp is built using
                         bind chead (bind c0 (bind c1 ... (bind cn (Tot (bs -> cres))))
    *)
    let monadic_application
      (head, chead, ghead, cres)                        (* the head of the application, its lcomp chead, and guard ghead, returning a bs -> cres *)
      subst                                             (* substituting actuals for formals seen so far, when actual is pure *)
      (arg_comps_rev:list<(arg * option<bv> * lcomp)>)  (* type-checked actual arguments, so far; in reverse order *)
      arg_rets_rev                                      (* The results of each argument at the logic level, in reverse order *)
      guard                                             (* conjoined guard formula for all the actuals *)
      fvs                                               (* unsubstituted formals, to check that they do not occur free elsewhere in the type of f *)
      bs                                                (* formal parameters *)
        : term   //application of head to args
        * lcomp  //its computation type
        * guard_t //and whatever guard remains
    =
      let rt, g0 = check_no_escape (Some head) env fvs (U.comp_result cres) in
      let cres = U.set_result_typ cres rt in
      let cres, guard =
          match bs with
          | [] -> (* full app *)
//              let cres = TcUtil.subst_lcomp subst cres in
              //NS 12/22 ... this comment looks stale
              (* If we have f e1 e2
                  where e1 or e2 is impure but f is a pure function,
                  then refine the result to be equal to f x1 x2,
                  where xi is the result of ei. (See the last two tests in examples/unit-tests/unit1.fst)
              *)
              let g = Env.conj_guard g0 <| Env.conj_guard ghead guard in
              cres, g

          | _ ->  (* partial app *)
              let g = Env.conj_guard g0 (Env.conj_guard ghead guard |> Rel.solve_deferred_constraints env) in
              mk_Total (U.arrow bs cres), g
      in
      if debug env Options.Medium then BU.print1 "\t Type of result cres is %s\n" (Print.comp_to_string cres);

      let chead, cres = SS.subst_comp subst chead |> TcComm.lcomp_of_comp, SS.subst_comp subst cres |> TcComm.lcomp_of_comp in

      (* Note: The arg_comps_rev are in reverse order. e.g., f e1 e2 e3, we have *)
      (* arg_comps_rev = [(e3, _, c3); (e2; _; c2); (e1; _; c1)] *)
      (* We build comp = bind chead (bind c1 (bind c2 (bind c3 cres))) *)
      (* The typing rule for monadic application should be something like *)

      (* G |- head : chead      G |- ei :ci                *)
      (* ------------------------------------------------- *)
      (*  G |- let xhead = lift_{chead}^{comp} head in     *)
      (*       let x1 = lift_{ci}^{comp} e1 in             *)
      (*       ...                                         *)
      (*       lift_{cres}^{comp} (xhead x1 ... xn) : cres *)

      (* where chead = b1 -> ... bn -> cres *)

      (* if cres is pure or ghost, we augment it with a return
           i.e., in the case where the head f is a pure or ghost function,
                 treat the application as (e e1 e2 .. en) as
                    f <-- e;
                    x1 <-- e1; ...
                    xn <-- en;
                    return (f x1 ... xn)
           1. The return at the end enhances f's result type with an equality
                e.g., if (f : xs -> Tot t)
                the type of the application becomes
                      Pure t (ensures (fun y -> y = f x1 ...xn))
           2. It's VERY important that the return is inserted using the bound names x1...xn.
              Previously, in case e1..en were pure, we were inserting
                      Pure t (ensures (fun y -> y = f e1 ...en))
              But this leads to a massive blow up in the size of generated VCs (cf issue #971)
              arg_rets below are those xn...x1 bound variables
       *)
      let cres =
        let head_is_pure_and_some_arg_is_effectful =
            TcComm.is_pure_or_ghost_lcomp chead
            && (BU.for_some (fun (_, _, lc) -> not (TcComm.is_pure_or_ghost_lcomp lc)
                                           || TcUtil.should_not_inline_lc lc)
                            arg_comps_rev)
        in
        let term = S.mk_Tm_app head (List.rev arg_rets_rev) head.pos in
        if TcComm.is_pure_or_ghost_lcomp cres
        && (head_is_pure_and_some_arg_is_effectful)
            // || Option.isSome (Env.expected_typ env))
        then let _ = if Env.debug env Options.Extreme then BU.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" (Print.term_to_string term) in
             TcUtil.maybe_assume_result_eq_pure_term env term cres
        else let _ = if Env.debug env Options.Extreme then BU.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" (Print.term_to_string term) in
             cres
      in

      (* 1. We compute the final computation type comp  *)
      let comp =
        List.fold_left
          (fun out_c ((e, q), x, c) ->
              if Env.debug env Options.Extreme then
                  BU.print3 "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                        (match x with None -> "_" | Some x -> Print.bv_to_string x)
                        (Print.term_to_string e)
                        (TcComm.lcomp_to_string c);
              if TcComm.is_pure_or_ghost_lcomp c
              then TcUtil.bind e.pos env (Some e) c (x, out_c)
              else TcUtil.bind e.pos env None c (x, out_c))
          cres
          arg_comps_rev
      in
      let comp =
          if Env.debug env Options.Extreme then BU.print1 "(c) Monadic app: Binding head %s\n" (Print.term_to_string head);
          if TcComm.is_pure_or_ghost_lcomp chead
          then TcUtil.bind head.pos env (Some head) chead (None, comp)
          else TcUtil.bind head.pos env None chead (None, comp) in

      (* TODO : This is a really syntactic criterion to check if we can evaluate *)
      (* applications left-to-right, can we do better ? *)
      let shortcuts_evaluation_order =
        match (SS.compress head).n with
        | Tm_fvar fv ->
          S.fv_eq_lid fv Parser.Const.op_And ||
          S.fv_eq_lid fv Parser.Const.op_Or
        | _ -> false
      in

      let app =
       if shortcuts_evaluation_order then
         (* Note: this case is only reachable in --lax mode.
                  In non-lax code, shortcut evaluation order is handled by
                  check_short_circuit_args. See, roughly, line 511, case Tm_app
         *)
         (* If the head is shortcutting we cannot hoist its arguments *)
         (* Leaving it `as is` is a little dubious, it would fail whenever we try to reify it *)
         let args = List.fold_left (fun args (arg, _, _) -> arg::args) [] arg_comps_rev in
         let app = mk_Tm_app head args r in
         let app = TcUtil.maybe_lift env app cres.eff_name comp.eff_name comp.res_typ in
         TcUtil.maybe_monadic env app comp.eff_name comp.res_typ

       else
          (* 2. For each monadic argument (including the head of the application) we introduce *)
          (*    a fresh variable and lift the actual argument to comp.       *)
          let lifted_args, head, args =
            let map_fun ((e, q), _ , c) =
               if Env.debug env Options.Extreme then
                 BU.print2 "For arg e=(%s) c=(%s)... " (Print.term_to_string e) (TcComm.lcomp_to_string c);
               if TcComm.is_pure_or_ghost_lcomp c
               then begin
                   if Env.debug env Options.Extreme then
                      BU.print_string "... not lifting\n";
                   None, (e, q)
               end else begin
                   //this argument is effectful, warn if the function would be erased
                   //special casing for ignore, may be use an attribute instead?
                   let warn_effectful_args  =
                     (TcUtil.must_erase_for_extraction env chead.res_typ) &&
                     (not (match (U.un_uinst head).n with
                           | Tm_fvar fv -> S.fv_eq_lid fv (Parser.Const.psconst "ignore")
                           | _ -> true))
                   in
                   if warn_effectful_args then
                     Errors.log_issue e.pos (Errors.Warning_EffectfulArgumentToErasedFunction,
                                             (format3 "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                      (Print.term_to_string e) (string_of_lid c.eff_name) (Print.term_to_string head)));
                   if Env.debug env Options.Extreme then
                       BU.print_string "... lifting!\n";
                   let x = S.new_bv None c.res_typ in
                   let e = TcUtil.maybe_lift env e c.eff_name comp.eff_name c.res_typ in
                   Some (x, c.eff_name, c.res_typ, e), (S.bv_to_name x, q)
               end
            in
            let lifted_args, reverse_args =
                List.split <| List.map map_fun ((as_arg head, None, chead)::arg_comps_rev)
            in
            lifted_args, fst (List.hd reverse_args), List.rev (List.tl reverse_args)
          in

          (* 3. We apply the (non-monadic) head to the non-monadic arguments, lift the *)
          (*    result to comp and then bind each monadic arguments to close over the *)
          (*    variables introduces at step 2. *)
          let app = mk_Tm_app head args r in
          let app = TcUtil.maybe_lift env app cres.eff_name comp.eff_name comp.res_typ in
          let app = TcUtil.maybe_monadic env app comp.eff_name comp.res_typ in
          let bind_lifted_args e = function
            | None -> e
            | Some (x, m, t, e1) ->
              let lb = U.mk_letbinding (Inl x) [] t m e1 [] e1.pos in
              let letbinding = mk (Tm_let ((false, [lb]), SS.close [S.mk_binder x] e)) e.pos in
              mk (Tm_meta(letbinding, Meta_monadic(m, comp.res_typ))) e.pos
          in
          List.fold_left bind_lifted_args app lifted_args
      in

      (* Each conjunct in g is already labeled *)
      //NS: Maybe redundant strengthen
      // let comp, g = comp, guard in
      let comp, g = TcUtil.strengthen_precondition None env app comp guard in
      if Env.debug env Options.Extreme then BU.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
        (Print.term_to_string app)
        (TcComm.lcomp_to_string comp);
      app, comp, g
    in

    let rec tc_args (head_info:(term * comp * guard_t * comp)) //the head of the application, its comp and guard, returning a bs -> cres
                    (subst,   (* substituting actuals for formals seen so far, when actual is pure *)
                     outargs, (* type-checked actual arguments, so far; in reverse order *)
                     arg_rets,(* The results of each argument at the logic level, in reverse order *)
                     g,       (* conjoined guard formula for all the actuals *)
                     fvs)     (* unsubstituted formals, to check that they do not occur free elsewhere in the type of f *)
                     bs       (* formal parameters *)
                     args     (* remaining actual arguments *) : (term * lcomp * guard_t) =
        match bs, args with
        | ({binder_bv=x;binder_qual=Some (Implicit _);binder_attrs=[]})::rest,
          (_, None)::_ -> (* instantiate an implicit arg that's not associated with a tactic, i.e. no Meta or attrs *)
            let t = SS.subst subst x.sort in
            let t, g_ex = check_no_escape (Some head) env fvs t in
            (* We compute a range by combining the range of the head
             * and the last argument we checked (if any). This is such that
             * if we instantiate an implicit for `f ()` (of type `#x:a -> ...),
             * we give it the range of `f ()` instead of just the range for `f`.
             * See issue #2021. This is only for the use range, we take
             * the def range from the head, so the 'see also' should still
             * point to the definition of the head. *)
            let r = match outargs with
                    | [] -> head.pos
                    | ((t, _), _, _)::_ ->
                        Range.range_of_rng (Range.def_range head.pos)
                                           (Range.union_rng (Range.use_range head.pos)
                                                            (Range.use_range t.pos))
            in
            let varg, _, implicits = TcUtil.new_implicit_var "Instantiating implicit argument in application" r env t in //new_uvar env t in
            let subst = NT(x, varg)::subst in
            let arg = varg, as_implicit true in
            let guard = List.fold_right Env.conj_guard [g_ex; g] implicits in
            tc_args head_info (subst, (arg, None, S.mk_Total t |> TcComm.lcomp_of_comp)::outargs, arg::arg_rets, guard, fvs) rest args

        | ({binder_bv=x;binder_qual=qual;binder_attrs=attrs})::rest,
          (_, None)::_
          when (TcUtil.maybe_implicit_with_meta_or_attr qual attrs) -> (* instantiate a meta arg *)
            (* We follow the exact same procedure as for instantiating an implicit,
             * except that we keep track of the (uvar, env, metaprogram) pair in the environment
             * so we can later come back to the implicit and, if it wasn't solved by unification,
             * run the metaprogram on it.
             *
             * Why don't we run the metaprogram here? At this stage, it's very likely that `t`
             * is full of unresolved uvars, and it wouldn't be a whole lot useful to try
             * to find an instance for it. We might not even be able to, since instances
             * are for concrete types.
             *)
            let ctx_uvar_meta, g_tau_or_attr = 
                match qual, attrs with
                | Some (Meta tau), _ ->
                  let tau = SS.subst subst tau in
                  let tau, _, g_tau = tc_tactic t_unit t_unit env tau in
                  Ctx_uvar_meta_tac (mkdyn env, tau), g_tau
                | Some (Implicit _), attr::_ ->
                  let attr = SS.subst subst attr in
                  let attr, _, g_attr = tc_tot_or_gtot_term env attr in
                  Ctx_uvar_meta_attr attr, g_attr
                | _ -> failwith "Impossible, match is under a guard"
            in
            let t = SS.subst subst x.sort in
            let t, g_ex = check_no_escape (Some head) env fvs t in
            let r = match outargs with
                    | [] -> head.pos
                    | ((t, _), _, _)::_ ->
                        Range.range_of_rng (Range.def_range head.pos)
                                           (Range.union_rng (Range.use_range head.pos)
                                                            (Range.use_range t.pos))
            in
            let varg, _, implicits = 
              new_implicit_var_aux "Instantiating meta argument in application" r env t Strict (Some ctx_uvar_meta)
            in
            let subst = NT(x, varg)::subst in
            let arg = varg, as_implicit true in
            let guard = List.fold_right Env.conj_guard [g_ex; g; g_tau_or_attr] implicits in
            tc_args head_info (subst, (arg, None, S.mk_Total t |> TcComm.lcomp_of_comp)::outargs, arg::arg_rets, guard, fvs) rest args

        | ({binder_bv=x;binder_qual=aqual})::rest, (e, aq)::rest' -> (* a concrete argument *)
            let _ =
                match aqual, aq with
                | _, Some (Meta _) ->
                    raise_error (Errors.Fatal_InconsistentImplicitQualifier,
                                  "Inconsistent implicit qualifier; cannot apply meta arguments, just use #") e.pos

                | Some (Meta _), Some (Implicit _)
                | Some (Implicit _), Some (Implicit _)
                | None, None
                | Some Equality, None -> ()
                | _ -> raise_error (Errors.Fatal_InconsistentImplicitQualifier,
                                     (BU.format4 "Inconsistent implicit qualifier; expected `%s` got `%s` for bvar %s and term %s"
                                               (Print.aqual_to_string aqual)
                                               (Print.aqual_to_string aq)
                                               (Print.bv_to_string x)
                                               (Print.term_to_string e))) e.pos in
            let targ = SS.subst subst x.sort in
            let aqual = SS.subst_imp subst aqual in
            let x = {x with sort=targ} in
            if debug env Options.Extreme
            then BU.print5 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                           (Print.bv_to_string x)
                           (Print.term_to_string x.sort)
                           (Print.term_to_string e)
                           (Print.subst_to_string subst)
                           (Print.term_to_string targ);
            let targ, g_ex = check_no_escape (Some head) env fvs targ in
            let env = Env.set_expected_typ env targ in
            let env = {env with use_eq=is_eq aqual} in
            if debug env Options.High
            then BU.print4 "Checking arg (%s) %s at type %s with use_eq:%s\n"
                   (Print.tag_of_term e) (Print.term_to_string e) (Print.term_to_string targ) (string_of_bool env.use_eq);
            let e, c, g_e = tc_term env e in
            let g = Env.conj_guard g_ex <| Env.conj_guard g g_e in
//                if debug env Options.High then BU.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" (guard_to_string env g_e) (guard_to_string env g);
            let arg = e, aq in
            let xterm = (fst (S.as_arg (S.bv_to_name x)), aq) in  //AR: fix for #1123, we were dropping the qualifiers
            if TcComm.is_tot_or_gtot_lcomp c //early in prims, Tot and GTot are primitive, not defined in terms of Pure/Ghost yet
            || TcUtil.is_pure_or_ghost_effect env c.eff_name
            then let subst = maybe_extend_subst subst (List.hd bs) e in
                 tc_args head_info (subst, (arg, Some x, c)::outargs, xterm::arg_rets, g, fvs) rest rest'
            else tc_args head_info (subst, (arg, Some x, c)::outargs, xterm::arg_rets, g, x::fvs) rest rest'

        | _, [] -> (* no more args; full or partial application *)
            monadic_application head_info subst outargs arg_rets g fvs bs

        | [], arg::_ -> (* too many args, except maybe c returns a function *)
            let head, chead, ghead = monadic_application head_info subst outargs arg_rets g fvs [] in
            let chead, ghead = TcComm.lcomp_comp chead |> (fun (c, g) -> c, Env.conj_guard ghead g) in
            let rec aux norm solve ghead tres =
                let tres = SS.compress tres |> U.unrefine in
                match tres.n with
                | Tm_arrow(bs, cres') ->
                        let bs, cres' = SS.open_comp bs cres' in
                        let head_info = (head, chead, ghead, cres') in
                        if debug env Options.Low
                        then FStar.Errors.log_issue tres.pos
                               (Errors.Warning_RedundantExplicitCurrying, "Potentially redundant explicit currying of a function type");
                        tc_args head_info ([], [], [], Env.trivial_guard, []) bs args
                | _ when not norm ->
                      let rec norm_tres (tres:term) :term =
                        let tres = tres |> N.unfold_whnf env |> U.unascribe in
                        match (SS.compress tres).n with
                        | Tm_refine ( { sort = tres }, _) -> norm_tres tres
                        | _                               -> tres
                      in
                      aux true solve ghead (norm_tres tres)

                | _ when not solve ->
                    let ghead = Rel.solve_deferred_constraints env ghead in
                    aux norm true ghead tres

                | _ ->
                    raise_error (Errors.Fatal_ToManyArgumentToFunction,
                                        BU.format3 "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                      (N.term_to_string env thead)
                                                      (BU.string_of_int n_args)
                                                      (Print.term_to_string tres))
                                       (argpos arg) in
            aux false false ghead (U.comp_result chead)
    in //end tc_args

    let rec check_function_app tf guard =
       match (N.unfold_whnf env tf).n with
        | Tm_uvar _
        | Tm_app({n=Tm_uvar _}, _) ->
            let bs, guard =
                List.fold_right
                    (fun _ (bs, guard) ->
                         let t, _, g = TcUtil.new_implicit_var "formal parameter" tf.pos env (U.type_u () |> fst) in
                         null_binder t::bs, Env.conj_guard g guard)
                    args
                    ([], guard)
            in
            let cres, guard =
                let t, _, g = TcUtil.new_implicit_var "result type" tf.pos env (U.type_u() |> fst) in
                if Options.ml_ish ()
                then U.ml_comp t r, Env.conj_guard guard g
                else S.mk_Total t, Env.conj_guard guard g
            in
            let bs_cres = U.arrow bs cres in
            if Env.debug env <| Options.Extreme
            then BU.print3 "Forcing the type of %s from %s to %s\n"
                            (Print.term_to_string head)
                            (Print.term_to_string tf)
                            (Print.term_to_string bs_cres);
            //Yes, force only the guard for this equation; the other uvars will not be solved yet
            let g = Rel.solve_deferred_constraints env (Rel.teq env tf bs_cres) in
            check_function_app bs_cres (Env.conj_guard g guard)

        | Tm_arrow(bs, c) ->
            let bs, c = SS.open_comp bs c in
            let head_info = head, chead, ghead, c in
            if Env.debug env Options.Extreme
            then BU.print4 "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                  (Print.term_to_string head)
                                  (Print.term_to_string tf)
                                  (Print.binders_to_string ", " bs)
                                  (Print.comp_to_string c);
            tc_args head_info ([], [], [], guard, []) bs args

        | Tm_refine (bv,_) ->
            check_function_app bv.sort guard

        | Tm_ascribed (t, _, _) ->
            check_function_app t guard

        | _ ->
            raise_error (Err.expected_function_typ env tf) head.pos in

    check_function_app thead Env.trivial_guard

(******************************************************************************)
(* SPECIAL CASE OF CHECKING APPLICATIONS:                                     *)
(*        head symbol is one of &&, ||, /\, \/, ==>                           *)
(*   ALL OF THEM HAVE A LOGICAL SPEC THAT IS BIASED L-to-R,                   *)
(*  aka they are short-circuiting                                             *)
(******************************************************************************)
and check_short_circuit_args env head chead g_head args expected_topt : term * lcomp * guard_t =
    let r = Env.get_range env in
    let tf = SS.compress (U.comp_result chead) in
    match tf.n with
        | Tm_arrow(bs, c) when (U.is_total_comp c && List.length bs=List.length args) ->
          let res_t = U.comp_result c in
          let args, guard, ghost = List.fold_left2 (fun (seen, guard, ghost) (e, aq) ({binder_bv=b;binder_qual=aq'}) ->
                if eq_aqual aq aq' <> Equal
                then raise_error (Errors.Fatal_InconsistentImplicitQualifier, "Inconsistent implicit qualifiers") e.pos;
                let e, c, g = tc_check_tot_or_gtot_term env e b.sort
                  "arguments to short circuiting operators must be pure or ghost" in //NS: this forbids stuff like !x && y, maybe that's ok
                let short = TcUtil.short_circuit head seen in
                let g = Env.imp_guard (Env.guard_of_guard_formula short) g in
                let ghost = ghost
                          || (not (TcComm.is_total_lcomp c)
                              && not (TcUtil.is_pure_effect env c.eff_name)) in
                seen@[as_arg e], Env.conj_guard guard g, ghost) ([], g_head, false) args bs in
          let e = mk_Tm_app head args r  in
          let c = if ghost then S.mk_GTotal res_t |> TcComm.lcomp_of_comp else TcComm.lcomp_of_comp c in
          //NS: maybe redundant strengthen
          // let c, g = c, guard in
          let c, g = TcUtil.strengthen_precondition None env e c guard in
          e, c, g

        | _ -> //fallback
          check_application_args env head chead g_head args expected_topt

and tc_pat env (pat_t:typ) (p0:pat) :
        pat                          (* the type-checked, fully decorated pattern                                   *)
      * list<bv>                     (* all its bound variables, used for closing the type of the branch term       *)
      * list<term>                   (* for each bv in the returned bv list, this list contains a Tm_abs,
                                        that when applied to the scrutinee, returns an expression for bv in terms of
                                        projectors. for example, say scrutinee is of type list (option int), and the
                                        pattern is (Some hd)::_, then hd will be returned in the bv list, and the
                                        list<term> would contain syntax for:
                                          fun (x:list (option int)) -> Some?.v (Cons?.hd x)
                                        in the case of layered effects, we close over the pattern variables in the
                                        branch VC by substituting them with these expressions                       *)
      * Env.env                      (* the environment extended with all the binders                               *)
      * term                         (* terms corresponding to the pattern                                          *)
      * term                         (* the same term in normal form                                                *)
      * guard_t                      (* unresolved implicits *)
      * bool                         (* true if the pattern matches an erasable type *)
      =
    let fail : string -> 'a = fun msg ->
        raise_error (Errors.Fatal_MismatchedPatternType, msg) p0.p
    in
    let expected_pat_typ env pos scrutinee_t : typ  =
        let rec aux norm t =
            let t = U.unrefine t in
            let head, args = U.head_and_args t in
            match (SS.compress head).n with
            | Tm_uinst ({n=Tm_fvar f}, us) -> unfold_once t f us args
            | Tm_fvar f -> unfold_once t f [] args
            | _ ->
              if norm then t
              else aux true (N.normalize [Env.HNF; Env.Unmeta; Env.Unascribe; Env.UnfoldUntil delta_constant] env t)
        and unfold_once t f us args =
            if Env.is_type_constructor env f.fv_name.v
            then t
            else match Env.lookup_definition [Env.Unfold delta_constant] env f.fv_name.v with
                 | None -> t
                 | Some head_def_ts ->
                   let _, head_def = Env.inst_tscheme_with head_def_ts us in
                   let t' = S.mk_Tm_app head_def args t.pos in
                   let t' = N.normalize [Env.Beta; Env.Iota] env t' in
                   aux false t'
        in
        aux false (N.normalize [Env.Beta;Env.Iota] env scrutinee_t)
    in
    let pat_typ_ok env pat_t scrutinee_t : guard_t =
       if Env.debug env <| Options.Other "Patterns"
       then BU.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               (Print.term_to_string pat_t)
               (Print.term_to_string scrutinee_t);
       let fail : string -> 'a = fun msg ->
         let msg = BU.format3 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                                        (Print.term_to_string pat_t)
                                        (Print.term_to_string scrutinee_t)
                                        msg in
         raise_error (Errors.Fatal_MismatchedPatternType, msg) p0.p
       in
       let head_s, args_s = U.head_and_args scrutinee_t in
       let pat_t = N.normalize [Env.Beta] env pat_t in
       match U.un_uinst head_s with
       | {n=Tm_fvar _} ->
           let head_p, args_p = U.head_and_args pat_t in
           if Rel.teq_nosmt_force env head_p head_s
           then match (U.un_uinst head_p).n with
                | Tm_fvar f ->
                  if not <| Env.is_type_constructor env (S.lid_of_fv f)
                  then fail "Pattern matching a non-inductive type";

                  if List.length args_p <> List.length args_s
                  then fail "";

                  let params_p, params_s =
                        match Env.num_inductive_ty_params env (S.lid_of_fv f) with
                        | None ->
                          args_p, args_s
                        | Some n ->
                          let params_p, _ = BU.first_N n args_p in
                          let params_s, _ = BU.first_N n args_s in
                          params_p, params_s
                  in

                  List.fold_left2
                        (fun out (p, _) (s, _) ->
                            match Rel.teq_nosmt env p s with
                            | None ->
                              fail (BU.format2 "; parameter %s <> parameter %s"
                                            (Print.term_to_string p)
                                            (Print.term_to_string s))
                            | Some g ->
                              let g = Rel.discharge_guard_no_smt env g in
                              Env.conj_guard g out)
                        Env.trivial_guard
                        params_p
                        params_s

                | _ -> fail "Pattern matching a non-inductive type"
            else fail (BU.format2 "; head mismatch %s vs %s"
                                    (Print.term_to_string head_p)
                                    (Print.term_to_string head_s))

       | _ ->
         match Rel.teq_nosmt env pat_t scrutinee_t with
         | None -> fail ""
         | Some g ->
           let g = Rel.discharge_guard_no_smt env g in
           g
    in
    let type_of_simple_pat env (e:term) : term * typ * list<bv> * guard_t * bool =
        let head, args = U.head_and_args e in
        match head.n with
        | Tm_fvar f ->
          let us, t_f = Env.lookup_datacon env f.fv_name.v in
          let formals, t = U.arrow_formals t_f in
          //Data constructors are marked with the "erasable" attribute
          //if their types are; matching on this constructor incurs
          //a ghost effect
          let erasable = Env.non_informative env t in
          if List.length formals <> List.length args
          then fail "Pattern is not a fully-applied data constructor";
          let rec aux (subst, args_out, bvs, guard) formals args =
            match formals, args with
            | [], [] ->
              let head = S.mk_Tm_uinst head us in
              let pat_e = S.mk_Tm_app head args_out e.pos in
              pat_e, SS.subst subst t, bvs, guard, erasable
            | ({binder_bv=f})::formals, (a, imp_a)::args ->
              let t_f = SS.subst subst f.sort in
              let a, subst, bvs, g =
                match (SS.compress a).n with
                | Tm_name x ->
                  let x = {x with sort=t_f} in
                  let a = S.bv_to_name x in
                  let subst = NT(f, a)::subst in
                  (a, imp_a), subst, bvs@[x], Env.trivial_guard

                | Tm_uvar _ ->
                  let env = Env.set_expected_typ env t_f in
                  let a, _, g = tc_tot_or_gtot_term env a in
                  let g = Rel.discharge_guard_no_smt env g in
                  let subst = NT(f, a)::subst in
                  (a, imp_a), subst, bvs, g

                | _ ->
                  fail "Not a simple pattern"
              in
              aux (subst, args_out@[a], bvs, Env.conj_guard g guard) formals args
            | _ -> fail "Not a fully applued pattern"
           in
           aux ([], [], [], Env.trivial_guard) formals args
        | _ ->
          fail "Not a simple pattern"
    in
    (*
     * This function checks the nested pattern and
     *   builds the list<bv> and corresponding list<term> (see the comment at the signature of tc_pat)
     *   by checking the pattern "inside out"
     *
     * For example, taking the scrutinee of type list (option int), and the pattern as Cons (Some hd) _,
     *   the recursive call first typechecks hd, and returns the term as t1 = Prims.id
     * Then we come to Some hd, and the term becomes t2 = (fun (x:option int). t1 (Some?.v x))
     * Then we come to Cons (Some hd), and the term becomes t3 = (fun (x:list (option int)). t2 (Cons?.hd x))
     * After a bit of normalization, this is same as (fun (x:list (option int)). Some?.v (Cons?.hd x))
     *)
    let rec check_nested_pattern env (p:pat) (t:typ)
        : list<bv>
        * list<term>
        * term
        * pat
        * guard_t
        * bool =
        if Env.debug env <| Options.Other "Patterns"
        then BU.print2 "Checking pattern %s at type %s\n" (Print.pat_to_string p) (Print.term_to_string t);

        let id = S.fvar Const.id_lid (S.Delta_constant_at_level 1) None in

        (*
         * Taking the example of scrutinee of type list (option int), and pattern as Cons (Some hd), _,
         * this function will be called twice:
         * (a) disc as Some?.v and inner_t as Prims.id (say it returns t1)
         * (b) disc as Cons?.hd and inner_t as t1
         * It builds the term as mentioned above in the comment at check_nested_pattern
         *)
        let mk_disc_t (disc:term) (inner_t:term) : term =
          let x_b = S.gen_bv "x" None t |> S.mk_binder in
          let tm = S.mk_Tm_app
            disc
            [x_b.binder_bv |> S.bv_to_name |> S.as_arg] Range.dummyRange in
          let tm = S.mk_Tm_app
            inner_t
            [tm |> S.as_arg] Range.dummyRange in
          U.abs [x_b] tm None in

        match p.v with
        | Pat_dot_term _ ->
          failwith (BU.format1 "Impossible: Expected an undecorated pattern, got %s" (Print.pat_to_string p))

        | Pat_wild x ->
          let x = {x with sort=t} in
          [x],
          [id],
          S.bv_to_name x,
          {p with v=Pat_wild x},
          Env.trivial_guard,
          false

        | Pat_var x ->
          let x = {x with sort=t} in
          [x],
          [id],
          S.bv_to_name x,
          {p with v=Pat_var x},
          Env.trivial_guard,
          false

        | Pat_constant c ->
          (*
           * AR: enforcing decidable equality, since the branch guards are in boolean now
           *     so whereas earlier we did scrutinee == c,
           *     we now have scrutinee = c, so we need decidable equality on c
           *)
          (match c with
           | Const_unit | Const_bool _ | Const_int _ | Const_char _ | Const_float _ | Const_string _ -> ()
           | _ ->
             fail (BU.format1
                     "Pattern matching a constant that does not have decidable equality: %s"
                     (Print.const_to_string c)));
          let _, e_c, _, _ = PatternUtils.pat_as_exp false false env p in
          let e_c, lc, g = tc_tot_or_gtot_term env e_c in
          Rel.force_trivial_guard env g;
          let expected_t = expected_pat_typ env p0.p t in
          if not (Rel.teq_nosmt_force env lc.res_typ expected_t)
          then fail (BU.format2 "Type of pattern (%s) does not match type of scrutinee (%s)"
                                (Print.term_to_string lc.res_typ)
                                (Print.term_to_string expected_t));
          [],
          [],
          e_c,
          p,
          Env.trivial_guard,
          false

        | Pat_cons(fv, sub_pats) ->
          let simple_pat =
            let simple_sub_pats =
                List.map (fun (p, b) ->
                    match p.v with
                    | Pat_dot_term _ -> p, b
                    | _ -> S.withinfo (Pat_var (S.new_bv (Some p.p) S.tun)) p.p, b)
                sub_pats in
            {p with v = Pat_cons (fv, simple_sub_pats)}
          in
          let sub_pats =
            sub_pats
            |> List.filter (fun (x, _) ->
                            match x.v with
                            | Pat_dot_term _ -> false
                            | _ -> true)
          in
          let simple_bvs, simple_pat_e, g0, simple_pat_elab =
              PatternUtils.pat_as_exp false false env simple_pat
          in
          if List.length simple_bvs <> List.length sub_pats
          then failwith (BU.format4 "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                                          (Range.string_of_range p.p)
                                          (Print.pat_to_string simple_pat)
                                          (BU.string_of_int (List.length sub_pats))
                                          (BU.string_of_int (List.length simple_bvs)));
          let simple_pat_e, simple_bvs, g1, erasable =
              let simple_pat_e, simple_pat_t, simple_bvs, guard, erasable =
                  type_of_simple_pat env simple_pat_e
              in
              let g' = pat_typ_ok env simple_pat_t (expected_pat_typ env p0.p t) in
              let guard = Env.conj_guard guard g' in
              if Env.debug env <| Options.Other "Patterns"
              then BU.print3 "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                            (Print.term_to_string simple_pat_e)
                            (Print.term_to_string simple_pat_t)
                            (List.map (fun x -> "(" ^ Print.bv_to_string x ^ " : " ^ Print.term_to_string x.sort ^ ")") simple_bvs
                              |> String.concat " ");
              simple_pat_e, simple_bvs, guard, erasable
          in
          let _env, bvs, tms, checked_sub_pats, subst, g, erasable, _ =
            List.fold_left2
              (fun (env, bvs, tms, pats, subst, g, erasable, i) (p, b) x ->
                let expected_t = SS.subst subst x.sort in
                let bvs_p, tms_p, e_p, p, g', erasable_p = check_nested_pattern env p expected_t in
                let env = Env.push_bvs env bvs_p in
                let tms_p =
                  let disc_tm = TcUtil.get_field_projector_name env (S.lid_of_fv fv) i in
                  tms_p |> List.map (mk_disc_t (S.fvar disc_tm (S.Delta_constant_at_level 1) None)) in
                env, bvs@bvs_p, tms@tms_p, pats@[(p,b)], NT(x, e_p)::subst, Env.conj_guard g g', erasable || erasable_p, i+1)
              (env, [], [], [], [], Env.conj_guard g0 g1, erasable, 0)
              sub_pats
              simple_bvs
          in
          let pat_e = SS.subst subst simple_pat_e in
          let reconstruct_nested_pat pat =
              let rec aux simple_pats bvs sub_pats =
                match simple_pats with
                | [] -> []
                | (hd, b)::simple_pats ->
                  match hd.v with
                  | Pat_dot_term(x, e) ->
                    let e = SS.subst subst e in
                    let hd = {hd with v=Pat_dot_term(x, e)} in
                    (hd, b) :: aux simple_pats bvs sub_pats
                  | Pat_var x ->
                    begin
                      match bvs, sub_pats with
                      | x'::bvs, (hd, _)::sub_pats
                          when S.bv_eq x x' ->
                        (hd, b) :: aux simple_pats bvs sub_pats

                      | _ ->
                        failwith "Impossible: simple pat variable mismatch"
                    end
                  | _ -> failwith "Impossible: expected a simple pattern"
              in
              match pat.v with
              | Pat_cons(fv, simple_pats) ->
                let nested_pats = aux simple_pats simple_bvs checked_sub_pats in
                {pat with v=Pat_cons(fv, nested_pats)}
              | _ -> failwith "Impossible"
          in
          bvs,
          tms,
          pat_e,
          reconstruct_nested_pat simple_pat_elab,
          g,
          erasable
    in
    if Env.debug env <| Options.Other "Patterns"
    then BU.print1 "Checking pattern: %s\n" (Print.pat_to_string p0);
    let bvs, tms, pat_e, pat, g, erasable =
        check_nested_pattern
            ({(Env.clear_expected_typ env |> fst) with use_eq=true})
            (PatternUtils.elaborate_pat env p0)
            pat_t
    in
    if Env.debug env <| Options.Other "Patterns"
    then BU.print2 "Done checking pattern %s as expression %s\n"
                    (Print.pat_to_string pat)
                    (Print.term_to_string pat_e);
    pat, bvs, tms, Env.push_bvs env bvs, pat_e, N.normalize [Env.Beta] env pat_e, g, erasable


(********************************************************************************************************************)
(* Type-checking a pattern-matching branch                                                                          *)
(* the pattern, when_clause and branch are closed                                                                   *)
(* scrutinee is the logical name of the expression being matched; it is not in scope in the branch                  *)
(*           but it is in scope for the VC of the branch                                                            *)
(* env does not contain scrutinee, or any of the pattern-bound variables                                            *)
(* the returned terms are well-formed in an environment extended with the scrutinee only                            *)

(*
 * ret_opt is the optional return annotation on the match
 * if this is set, then ascribe it on the branches for typechecking
 * but unascribe it before returning to the caller
 *)
(********************************************************************************************************************)
and tc_eqn scrutinee env ret_opt branch
        : (pat * option<term> * term)                                                             (* checked branch *)
        * term       (* the guard condition for taking this branch, used by the caller for the exhaustiveness check *)
        * lident                                                                 (* effect label of the lcomp below *)
        * list<cflag>                                                                       (* flags for each lcomp *)
        * (bool -> lcomp)                     (* computation type of the branch, with or without a "return" equation *)
        * guard_t                                                                      (* well-formedness condition *)
        * bool                                                      (* true if the pattern matches an erasable type *)
        =
  let pattern, when_clause, branch_exp = SS.open_branch branch in
  let cpat, _, cbr = branch in

  let pat_t = scrutinee.sort in
  let scrutinee_tm = S.bv_to_name scrutinee in
  let scrutinee_env, _ = Env.push_bv env scrutinee |> Env.clear_expected_typ in

  (* 1. Check the pattern *)
  (*    pat_bvs are the pattern variables, and pat_bv_tms are syntax for a single argument functions that *)
  (*    when applied to the scrutinee return an expression for the bv in terms of projectors *)
  let pattern, pat_bvs, pat_bv_tms, pat_env, pat_exp, norm_pat_exp, guard_pat, erasable =
    tc_pat env pat_t pattern
  in

  if Env.debug env <| Options.Extreme then
    BU.print3 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
      (Print.pat_to_string pattern) (Print.bvs_to_string ";" pat_bvs)
      (List.fold_left (fun s t -> s ^ ";" ^ (Print.term_to_string t)) "" pat_bv_tms);

  (* 2. Check the when clause *)
  let when_clause, g_when = match when_clause with
    | None -> None, Env.trivial_guard
    | Some e ->
        if Env.should_verify env
        then raise_error (Errors.Fatal_WhenClauseNotSupported, "When clauses are not yet supported in --verify mode; they will be some day") e.pos
        //             let e, c, g = no_logical_guard pat_env <| tc_total_exp (Env.set_expected_typ pat_env TcUtil.t_bool) e in
        //             Some e, g
        else let e, c, g = tc_term (Env.set_expected_typ pat_env t_bool) e in
             Some e, g in

  (* 3. Check the branch *)
  let branch_exp, c, g_branch =
    let branch_exp =  //ascribe with the return annotation, if it exists
      match ret_opt with
      | None -> branch_exp
      | Some asc ->
        asc
        |> SS.subst_ascription [NT (scrutinee, norm_pat_exp)]
        |> U.ascribe branch_exp in
    let branch_exp, c, g_branch = tc_term pat_env branch_exp in
    let branch_exp =  //unascribe if we added ascription
      match ret_opt with
      | None -> branch_exp
      | Some _ ->
        match (SS.compress branch_exp).n with
        | Tm_ascribed (branch_exp, _, _) -> branch_exp
        | _ -> failwith "Impossible (expected the match branch with an ascription)" in
    branch_exp, c, g_branch in

  Env.def_check_guard_wf cbr.pos "tc_eqn.1" pat_env g_branch;

  (* 4. Lift the when clause to a logical condition. *)
  (*    It is used in step 5 (a) below, and in step 6 (d) to build the branch guard *)
  let when_condition = match when_clause with
        | None -> None
        | Some w -> Some <| U.mk_eq2 U_zero U.t_bool w U.exp_true_bool in


  (*      logically the same as step 5(a),                                                              *)


  (* 5. Building the guard for this branch;                                                             *)
  (*        the caller assembles the guards for each branch into an exhaustiveness check.               *)
  (*                                                                                                    *)
  (* (a) Compute the branch guard for each arm of a disjunctive pattern.                                *)
  (*      expressed in terms for discriminators and projectors on sub-terms of scrutinee                *)
  (*      for the benefit of the caller, who works in an environment without the pattern-bound vars     *)
  (*                                                                                                    *)
  (* (b) Type-check the condition computed in 5 (a)                                                     *)
  (*                                                                                                    *)
  (* (c) Make a disjunctive formula out of 5 (b) for each arm of the pattern                             *)
  (*                                                                                                    *)
  (* (d) Strengthen 5 (c) with the when condition, if there is one                                      *)

  (* This used to be step 6 earlier (after weakening the branch VC with scrutinee equality with pattern etc.) *)
  (*   but we do it before that now, since for layered effects, we use this branch guard to weaken      *)

  (* TODO: this seems very similar to constructing the terms for pattern variables in terms of scrutinee *)
  (*       and projectors. Can this be done in tc_pat too? That should save us repeated iterations on the pattern *)

  (* The branch guard is a boolean expression *)

  let branch_guard =
      if not (Env.should_verify env)
      then U.exp_true_bool
      else (* 5 (a) *)
          let rec build_branch_guard (scrutinee_tm:option<term>) (pattern:pat) pat_exp : list<typ> =
            let discriminate scrutinee_tm f =
                let is_induc, datacons = Env.datacons_of_typ env (Env.typ_of_datacon env f.v) in
                (* Why the `not is_induc`? We may be checking an exception pattern. See issue #1535. *)
                if not is_induc || List.length datacons > 1
                then
                    let discriminator = U.mk_discriminator f.v in
                    match Env.try_lookup_lid env discriminator with
                        | None -> []  // We don't use the discriminator if we are typechecking it
                        | _ ->
                            let disc = S.fvar discriminator (Delta_equational_at_level 1) None in
                            [mk_Tm_app disc [as_arg scrutinee_tm] scrutinee_tm.pos]
                else []
            in

            let fail () =
                failwith (BU.format3 "tc_eqn: Impossible (%s) %s (%s)"
                                            (Range.string_of_range pat_exp.pos)
                                            (Print.term_to_string pat_exp)
                                            (Print.tag_of_term pat_exp))  in

            let rec head_constructor t = match t.n with
                | Tm_fvar fv -> fv.fv_name
                | Tm_uinst(t, _) -> head_constructor t
                | _ -> fail () in

            let force_scrutinee () =
                match scrutinee_tm with
                | None -> failwith (BU.format2 "Impossible (%s): scrutinee of match is not defined %s"
                                                (Range.string_of_range pattern.p)
                                                (Print.pat_to_string pattern))
                | Some t -> t
            in
            let pat_exp = SS.compress pat_exp |> U.unmeta in
            match pattern.v, pat_exp.n with
            | _, Tm_name _ ->
              [] //no guard for variables; they always match

            | _, Tm_constant Const_unit ->
              [] //no guard for the unit pattern; it's a singleton

            | Pat_constant _c, Tm_constant c ->

              [U.mk_decidable_eq (tc_constant env pat_exp.pos c) (force_scrutinee ()) pat_exp]

            | Pat_constant (FStar.Const.Const_int(_, Some _)), _ ->
              //machine integer pattern, cf. #1572
              let _, t, _ =
                let env, _ = Env.clear_expected_typ env in
                env.typeof_tot_or_gtot_term env pat_exp true
              in
              [U.mk_decidable_eq t (force_scrutinee ()) pat_exp]

            | Pat_cons (_, []), Tm_uinst _
            | Pat_cons (_, []), Tm_fvar _ ->
                //nullary pattern
                let f = head_constructor pat_exp in
                if not (Env.is_datacon env f.v)
                then failwith "Impossible: nullary patterns must be data constructors"
                else discriminate (force_scrutinee ()) (head_constructor pat_exp)

            | Pat_cons (_, pat_args), Tm_app(head, args) ->
                //application pattern
                let f = head_constructor head in
                if not (Env.is_datacon env f.v)
                || List.length pat_args <> List.length args
                then failwith "Impossible: application patterns must be fully-applied data constructors"
                else let sub_term_guards =
                        List.zip pat_args args |>
                        List.mapi (fun i ((pi, _), (ei, _)) ->
                            let projector = Env.lookup_projector env f.v i in
                            //NS: TODO ... should this be a marked as a record projector? But it doesn't matter for extraction
                            let scrutinee_tm =
                                match Env.try_lookup_lid env projector with
                                | None ->
                                  None //no projector, e.g., because we are actually typechecking the projector itself
                                | _ ->
                                  let proj = S.fvar (Ident.set_lid_range projector f.p) (Delta_equational_at_level 1) None in
                                  Some (mk_Tm_app proj [as_arg (force_scrutinee())] f.p)
                            in
                            build_branch_guard scrutinee_tm pi ei) |>
                        List.flatten
                     in
                     discriminate (force_scrutinee()) f @ sub_term_guards

            | Pat_dot_term _, _ -> []
              //a non-pattern sub-term computed via unification; no guard needeed since it is from a dot pattern

            | _ -> failwith (BU.format2 "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                        (Print.pat_to_string pattern)
                                        (Print.term_to_string pat_exp))
          in

          (* 5 (b) *)
          let build_and_check_branch_guard scrutinee_tm pattern pat =
             if not (Env.should_verify env)
             then U.exp_true_bool //if we're not verifying, then don't even bother building it
             else let t = U.mk_and_l <| build_branch_guard scrutinee_tm pattern pat in
                  let t, _, _ = tc_check_tot_or_gtot_term scrutinee_env t U.t_bool "" in
                  //NS: discarding the guard here means that the VC is not fully type-checked
                  //    and may contain unresolved unification variables, e.g. FIXME!
                  t in

          (* 5 (c) *)
         let branch_guard = build_and_check_branch_guard (Some scrutinee_tm) pattern norm_pat_exp in

          (* 5 (d) *)
         let branch_guard =
            match when_condition with
            | None -> branch_guard
            | Some w -> U.mk_and branch_guard w in

          branch_guard
  in

  if Env.debug env <| Options.Extreme then
  BU.print1 "tc_eqn: branch guard : %s\n" (Print.term_to_string branch_guard);

  (* 6 (a). Build equality conditions between the pattern and the scrutinee                                    *)
  (*   (b). Weaken the VCs of the branch and when clause with the equalities from 6 (a) and the when condition *)
  (*        For layered effects, we weaken with the branch guard instead                                       *)
  (*   (c). Close the VCs so that they no longer have the pattern-bound variables occurring free in them       *)
  (*        For wp-based effects, closing means applying the close_wp combinator                               *)
  (*        For layered effects, we substitute the pattern variables with their projector expressions applied  *)
  (*          to the scrutinee                                                                                 *)

  let effect_label, cflags, maybe_return_c, g_when, g_branch =
    (* (a) eqs are equalities between the scrutinee and the pattern *)
    let eqs =
      if not (Env.should_verify env)
      then None
      else let e = SS.compress pat_exp in
           Some (U.mk_eq2 (env.universe_of env pat_t) pat_t scrutinee_tm e) in
    match ret_opt with
    | Some (Inr c, _) ->
      let pat_bs = List.map S.mk_binder pat_bvs in
      let g_branch =
        (if eqs |> is_some
         then TcComm.weaken_guard_formula g_branch (eqs |> must)
         else g_branch)
        |> Env.close_guard env pat_bs
        |> TcUtil.close_guard_implicits env true pat_bs in
      U.comp_effect_name c, U.comp_flags c, (fun _ -> TcComm.lcomp_of_comp c), g_when, g_branch
    | _ ->
     let c, g_branch = TcUtil.strengthen_precondition None env branch_exp c g_branch in

     //g_branch is trivial, its logical content is now incorporated within c
        
     let branch_has_layered_effect = c.eff_name |> Env.norm_eff_name env |> Env.is_layered_effect env in

     (* (b) *)
     let c_weak, g_when_weak =
       let env = Env.push_binders scrutinee_env (pat_bvs |> List.map S.mk_binder) in
       if branch_has_layered_effect
       then
         //branch_guard is a boolean, so b2t it
         let c = TcUtil.weaken_precondition env c (NonTrivial (U.b2t branch_guard)) in
         c, Env.trivial_guard  //use branch guard for weakening
       else
         match eqs, when_condition with
         | _ when not (Env.should_verify env) ->
           c, g_when

         | None, None ->
           c, g_when

         | Some f, None ->
           let gf = NonTrivial f in
           let g = Env.guard_of_guard_formula gf in
           TcUtil.weaken_precondition env c gf,
           Env.imp_guard g g_when

         | Some f, Some w ->
           let g_f = NonTrivial f in
           let g_fw = NonTrivial (U.mk_conj f w) in
           TcUtil.weaken_precondition env c g_fw,
           Env.imp_guard (Env.guard_of_guard_formula g_f) g_when

         | None, Some w ->
           let g_w = NonTrivial w in
           let g = Env.guard_of_guard_formula g_w in
           TcUtil.weaken_precondition env c g_w,
           g_when in

     (* (c) *)
     let binders = List.map S.mk_binder pat_bvs in
     let maybe_return_c_weak should_return =
       let c_weak =
         if should_return &&
            TcComm.is_pure_or_ghost_lcomp c_weak
         then TcUtil.maybe_assume_result_eq_pure_term env branch_exp c_weak
         else c_weak in
       if branch_has_layered_effect
       then
         let _ =
           if Env.debug env <| Options.Other "LayeredEffects"
           then BU.print_string "Typechecking pat_bv_tms ...\n" in

         (*
          * AR: typecheck the pat_bv_tms, to resolve implicits etc.
          * 
          * recall that pat_bv_tms are terms that are definitionally equal to the pat_bvs
          *   but are in terms of projectors on the scrutinee term
          * these will be used to substitute pat bvs in the computation type
          * of the corresponding branch
          *
          * a pat_bv_tm's expected type is the sort of the corresponding pat bv
          * however, we need to be careful about dependent pat bvs of the like (a:Type) (x:a)
          *
          * so when we typecheck a pat_bv_tm with expected type as corresponding pat_bv.sort,
          *   we substitute the already seen pat bvs with their pat bv tms in the sort
          *)

         //first apply the pat_bv_tms to the scrutinee term
         let pat_bv_tms = pat_bv_tms |> List.map (fun pat_bv_tm ->
           mk_Tm_app pat_bv_tm [scrutinee_tm |> S.as_arg] Range.dummyRange) in

         let pat_bv_tms =
           //note, we are explicitly setting lax = true, since these terms apply projectors
           //which we know are sound as per the branch guard, but hard to convince the typechecker
           //AR: TODO: should we instead do the non-lax typechecking but drop the logical payload in the guard?
           let env = { (Env.push_bv env scrutinee) with lax = true } in
           List.fold_left2 (fun (substs, acc) pat_bv_tm bv ->
             let expected_t = SS.subst substs bv.sort in
             //we also substitute in the pat_bv_tm, since in the case of nested patterns,
             //  there are cases when sorts of the bound scrutinee variable for the inner pattern vars
             //  contains some outer patterns vars
             let pat_bv_tm =
               pat_bv_tm
               |> SS.subst substs
               |> tc_trivial_guard (Env.set_expected_typ env expected_t)
               |> fst in
             substs@[NT (bv, pat_bv_tm)], acc@[pat_bv_tm]) ([], []) pat_bv_tms pat_bvs

             |> snd
             |> List.map (N.normalize [Env.Beta] env) in

         let _ =
           if Env.debug env <| Options.Other "LayeredEffects"
           then BU.print2 "tc_eqn: typechecked pat_bv_tms %s (pat_bvs : %s)\n"
                  (List.fold_left (fun s t -> s ^ ";" ^ (Print.term_to_string t)) "" pat_bv_tms)
                  (List.fold_left (fun s t -> s ^ ";" ^ (Print.bv_to_string t)) "" pat_bvs) in
 
         c_weak
         |> TcComm.apply_lcomp (fun c -> c) (fun g -> match eqs with
                                               | None -> g
                                               | Some eqs -> TcComm.weaken_guard_formula g eqs)
         |> TcUtil.close_layered_lcomp (Env.push_bv env scrutinee) pat_bvs pat_bv_tms

       else TcUtil.close_wp_lcomp env pat_bvs c_weak in

    c_weak.eff_name,
    c_weak.cflags,
    maybe_return_c_weak,
    Env.close_guard env binders g_when_weak,
    Env.conj_guard guard_pat g_branch in

  let guard = Env.conj_guard g_when g_branch in

  if Env.debug env Options.High
  then BU.print1 "Carrying guard from match: %s\n" <| guard_to_string env guard;

  SS.close_branch (pattern, when_clause, branch_exp),
  branch_guard,   //expressed in terms of discriminators and projectors on scrutinee---does not contain the pattern-bound variables
  effect_label,
  cflags,
  maybe_return_c, //closed already---does not contain free pattern-bound variables
  TcUtil.close_guard_implicits env false (List.map S.mk_binder pat_bvs) guard,
  erasable

(******************************************************************************)
(* Checking a top-level, non-recursive let-binding:                           *)
(* top-level let's may be generalized, if they are not annotated              *)
(* the body of a top-level let is always ()---no point in checking it         *)
(******************************************************************************)
and check_top_level_let env e =
   let env = instantiate_both env in
   match e.n with
      | Tm_let((false, [lb]), e2) ->
(*open*) let e1, univ_vars, c1, g1, annotated = check_let_bound_def true env lb in
         (* Maybe generalize its type *)
         let g1, e1, univ_vars, c1 =
            if annotated && not env.generalize
            then g1, N.reduce_uvar_solutions env e1, univ_vars, c1
            else let g1 = Rel.solve_deferred_constraints env g1 |> Rel.resolve_implicits env in
                 let comp1, g_comp1 = lcomp_comp c1 in
                 let g1 = Env.conj_guard g1 g_comp1 in
                 let _, univs, e1, c1, gvs = List.hd (Gen.generalize env false [lb.lbname, e1, comp1]) in
                 let g1 = map_guard g1 <| N.normalize [Env.Beta; Env.DoNotUnfoldPureLets; Env.CompressUvars; Env.NoFullNorm; Env.Exclude Env.Zeta] env in
                 let g1 = abstract_guard_n gvs g1 in
                 g1, e1, univs, TcComm.lcomp_of_comp c1
         in

         (* Check that it doesn't have a top-level effect; warn if it does *)
         let e2, c1 =
            if Env.should_verify env
            then
                let ok, c1 = TcUtil.check_top_level env g1 c1 in //check that it has no effect and a trivial pre-condition
                if ok
                then e2, c1
                else (Errors.log_issue (Env.get_range env) Err.top_level_effect;
                      mk (Tm_meta(e2, Meta_desugared Masked_effect)) e2.pos, c1) //and tag it as masking an effect
            else //even if we're not verifying, still need to solve remaining unification/subtyping constraints
                 let _ = Rel.force_trivial_guard env g1 in
                 let comp1, g_comp1 = TcComm.lcomp_comp c1 in
                 let _ = Rel.force_trivial_guard env g_comp1 in
                 let c = comp1 |> N.normalize_comp [Env.Beta; Env.NoFullNorm; Env.DoNotUnfoldPureLets] env in
                 let e2 = if Util.is_pure_comp c
                          then e2
                          else (Errors.log_issue (Env.get_range env) Err.top_level_effect;
                                mk (Tm_meta(e2, Meta_desugared Masked_effect)) e2.pos) in
                 e2, c
         in

         (* Unfold all @tcnorm subterms in the binding *)
         if Env.debug env Options.Medium then
                BU.print1 "Let binding BEFORE tcnorm: %s\n" (Print.term_to_string e1);
         let e1 = if Options.tcnorm () then
                    N.normalize [Env.UnfoldAttr [Const.tcnorm_attr];
                                 Env.Exclude Env.Beta; Env.Exclude Env.Zeta;
                                 Env.NoFullNorm; Env.DoNotUnfoldPureLets] env e1
                  else e1
         in
         if Env.debug env Options.Medium then
                BU.print1 "Let binding AFTER tcnorm: %s\n" (Print.term_to_string e1);

         (*
          * AR: we now compute comp for the whole `let x = e1 in e2`, where e2 = ()
          *
          *     we have already checked that c1 has a trivial precondition
          *       and in most cases, c1 is some variant of PURE (top-level functions)
          *     so if that's the case, we simply make cres as Tot unit
          *
          *     if c1 is not PURE, then we take a longer route and compute:
          *       M.bind wp1 (fun _ -> (M.return_wp unit))
          *
          *     all this to remove the earlier usage of M.null_wp
          *)
         let cres =
           if U.is_pure_or_ghost_comp c1 then S.mk_Total' S.t_unit (Some S.U_zero)
           else let c1_comp_typ = c1 |> Env.unfold_effect_abbrev env in
                let c1_wp =
                  match c1_comp_typ.effect_args with
                  | [(wp, _)] -> wp
                  | _ -> failwith "Impossible! check_top_level_let: got unexpected effect args"
                in
                let c1_eff_decl = Env.get_effect_decl env c1_comp_typ.effect_name in

                (* wp2 = M.return_wp unit () *)
                let wp2 =
                  let ret = c1_eff_decl |> U.get_return_vc_combinator in
                  mk_Tm_app
                    (inst_effect_fun_with [ S.U_zero ] env c1_eff_decl ret)
                    [S.as_arg S.t_unit; S.as_arg S.unit_const]
                    e2.pos in

                (* wp = M.bind wp_c1 (fun _ -> wp2) *)
                let wp =
                  let bind = c1_eff_decl |> U.get_bind_vc_combinator in
                  mk_Tm_app
                    (inst_effect_fun_with (c1_comp_typ.comp_univs @ [S.U_zero]) env c1_eff_decl bind)
                    [ S.as_arg <| S.mk (S.Tm_constant (FStar.Const.Const_range lb.lbpos)) lb.lbpos;
                      S.as_arg <| c1_comp_typ.result_typ;
                      S.as_arg S.t_unit;
                      S.as_arg c1_wp;
                      S.as_arg <| U.abs [null_binder c1_comp_typ.result_typ] wp2 (Some (U.mk_residual_comp Const.effect_Tot_lid None [TOTAL])) ]
                    lb.lbpos in
                mk_Comp ({
                  comp_univs=[S.U_zero];
                  effect_name=c1_comp_typ.effect_name;
                  result_typ=S.t_unit;
                  effect_args=[S.as_arg wp];
                  flags=[]})
         in

(*close*)let lb = U.close_univs_and_mk_letbinding None lb.lbname univ_vars (U.comp_result c1) (U.comp_effect_name c1) e1 lb.lbattrs lb.lbpos in
         mk (Tm_let((false, [lb]), e2))
            e.pos,
         TcComm.lcomp_of_comp cres,
         Env.trivial_guard

     | _ -> failwith "Impossible"

and maybe_intro_smt_lemma env lem_typ c2 =
    if U.is_smt_lemma lem_typ
    then let universe_of_binders bs =
             let _, us =
               List.fold_left
                 (fun (env, us) b ->
                   let u = env.universe_of env b.binder_bv.sort in
                   let env = Env.push_binders env [b] in
                   env, u::us)
                 (env, [])
                 bs
             in
             List.rev us
         in
         let quant = U.smt_lemma_as_forall lem_typ universe_of_binders in
         TcUtil.weaken_precondition env c2 (NonTrivial quant)
    else c2

(******************************************************************************)
(* Checking an inner non-recursive let-binding:                               *)
(* inner let's are never implicitly generalized                               *)
(* let x = e1 in e2  is logically a bind (lift c1) (\x. lift c2)              *)
(*    except that we also need to strengthen it with well-formedness checks   *)
(*    and a check that x does not escape its scope in the type of c2          *)
(******************************************************************************)
and check_inner_let env e =
   let env = instantiate_both env in
   match e.n with
     | Tm_let((false, [lb]), e2) ->
       let env = {env with top_level=false} in
       let e1, _, c1, g1, annotated = check_let_bound_def false (Env.clear_expected_typ env |> fst) lb in
       let pure_or_ghost = TcComm.is_pure_or_ghost_lcomp c1 in
       let is_inline_let = BU.for_some (U.is_fvar FStar.Parser.Const.inline_let_attr) lb.lbattrs in
       let _ =
        if is_inline_let
        && not (pure_or_ghost || Env.is_erasable_effect env c1.eff_name)  //inline let is allowed on erasable effects
        then raise_error (Errors.Fatal_ExpectedPureExpression,
                          BU.format2 "Definitions marked @inline_let are expected to be pure or ghost; \
                                      got an expression \"%s\" with effect \"%s\""
                                       (Print.term_to_string e1)
                                       (Print.lid_to_string c1.eff_name))
                          e1.pos
       in
       let x = {BU.left lb.lbname with sort=c1.res_typ} in
       let xb, e2 = SS.open_term [S.mk_binder x] e2 in
       let xbinder = List.hd xb in
       let x = xbinder.binder_bv in
       let env_x = Env.push_bv env x in
       let e2, c2, g2 =
         (*
          * AR: we typecheck e2 and fold its guard into the returned lcomp
          *     so that the guard is under the equality x=e1 when we later (in the next line)
          *     bind c1 and c2
          *)
         tc_term env_x e2
         |> (fun (e2, c2, g2) ->
            let c2, g2 = TcUtil.strengthen_precondition
              ((fun _ -> "folding guard g2 of e2 in the lcomp") |> Some)
              env_x
              e2
              c2
              g2 in
            e2, c2, g2) in
       //g2 now has no logical payload after this, it may have unresolved implicits
       let c2 = maybe_intro_smt_lemma env_x c1.res_typ c2 in
       let cres =
         TcUtil.maybe_return_e2_and_bind
           e1.pos
           env
           (Some e1)
           c1
           e2
           (Some x, c2)
       in
       //AR: TODO: FIXME: monadic annotations need to be adjusted for polymonadic binds
       let e1 = TcUtil.maybe_lift env e1 c1.eff_name cres.eff_name c1.res_typ in
       let e2 = TcUtil.maybe_lift env e2 c2.eff_name cres.eff_name c2.res_typ in
       let lb = 
         let attrs =
           let add_inline_let =  //add inline_let if
             not is_inline_let &&  //the letbinding is not already inline_let, and
             ((pure_or_ghost &&  //either it is pure/ghost with unit type, or
               U.is_unit c1.res_typ) ||
              (Env.is_erasable_effect env c1.eff_name &&  //c1 is erasable and cres is not
               not (Env.is_erasable_effect env cres.eff_name))) in
           if add_inline_let
           then U.inline_let_attr::lb.lbattrs
           else lb.lbattrs in
         U.mk_letbinding (Inl x) [] c1.res_typ cres.eff_name e1 attrs lb.lbpos in
       let e = mk (Tm_let((false, [lb]), SS.close xb e2)) e.pos in
       let e = TcUtil.maybe_monadic env e cres.eff_name cres.res_typ in

       //AR: for layered effects, solve any deferred constraints first
       //    we can do it at other calls to close_guard_implicits too, but let's see
       let g2 = TcUtil.close_guard_implicits env
         (cres.eff_name |> Env.norm_eff_name env |> Env.is_layered_effect env)
         xb g2 in
       let guard = Env.conj_guard g1 g2 in

       if Option.isSome (Env.expected_typ env)
       then (let tt = Env.expected_typ env |> Option.get in
             if Env.debug env <| Options.Other "Exports"
             then BU.print2 "Got expected type from env %s\ncres.res_typ=%s\n"
                        (Print.term_to_string tt)
                        (Print.term_to_string cres.res_typ);
             e, cres, guard)
       else (* no expected type; check that x doesn't escape it's scope *)
            (let t, g_ex = check_no_escape None env [x] cres.res_typ in
             if Env.debug env <| Options.Other "Exports"
             then BU.print2 "Checked %s has no escaping types; normalized to %s\n"
                        (Print.term_to_string cres.res_typ)
                        (Print.term_to_string t);
             e, ({cres with res_typ=t}), Env.conj_guard g_ex guard)

    | _ -> failwith "Impossible (inner let with more than one lb)"

(******************************************************************************)
(* top-level let rec's may be generalized, if they are not annotated          *)
(******************************************************************************)
and check_top_level_let_rec env top =
    let env = instantiate_both env in
    match top.n with
        | Tm_let((true, lbs), e2) ->
           (* replace bound variables in terms and of universes with new names (free variables) *)
(*open*)   let lbs, e2 = SS.open_let_rec lbs e2 in

           (* expected types for top level definitions are stored in the lbs and we therefore just
            * remove previous, unrelated, expected type in env
            * the expected type is defined within lbs
            * *)
           let env0, topt = Env.clear_expected_typ env in
           let lbs, rec_env, g_t = build_let_rec_env true env0 lbs in
           (* now we type check each let rec *)
           let lbs, g_lbs = check_let_recs rec_env lbs in
           let g_lbs = Env.conj_guard g_t g_lbs |> Rel.solve_deferred_constraints env |> Rel.resolve_implicits env in

           let all_lb_names = lbs |> List.map (fun lb -> right lb.lbname) |> Some in

           let lbs =
              if not env.generalize
              then lbs |> List.map (fun lb ->
            (* TODO : Should we gather the fre univnames ? e.g. (TcUtil.gather_free_univnames env e1)@lb.lbunivs *)
                    let lbdef = N.reduce_uvar_solutions env lb.lbdef in
                    if lb.lbunivs = []
                    then lb
                    else U.close_univs_and_mk_letbinding all_lb_names lb.lbname lb.lbunivs lb.lbtyp lb.lbeff lbdef lb.lbattrs lb.lbpos)
              else let ecs = Gen.generalize env true (lbs |> List.map (fun lb ->
                                lb.lbname,
                                lb.lbdef,
                                S.mk_Total lb.lbtyp)) in
                   List.map2 (fun (x, uvs, e, c, gvs) lb ->
                                  U.close_univs_and_mk_letbinding
                                        all_lb_names
                                        x
                                        uvs
                                        (U.comp_result c)
                                        (U.comp_effect_name c)
                                        e
                                        lb.lbattrs
                                        lb.lbpos)
                              ecs
                              lbs
           in

          let cres = TcComm.lcomp_of_comp <| S.mk_Total t_unit in

(*close*) let lbs, e2 = SS.close_let_rec lbs e2 in
          Rel.discharge_guard env g_lbs |> Rel.force_trivial_guard env;
          mk (Tm_let((true, lbs), e2)) top.pos,
          cres,
          Env.trivial_guard

        | _ -> failwith "Impossible"

(******************************************************************************)
(* inner let rec's are never implicitly generalized *)
(******************************************************************************)
and check_inner_let_rec env top =
    let env = instantiate_both env in
    match top.n with
        | Tm_let((true, lbs), e2) ->
(*open*)  let lbs, e2 = SS.open_let_rec lbs e2 in

          let env0, topt = Env.clear_expected_typ env in
          let lbs, rec_env, g_t = build_let_rec_env false env0 lbs in
          let lbs, g_lbs = check_let_recs rec_env lbs |> (fun (lbs, g) -> lbs, Env.conj_guard g_t g) in

          let env, lbs = lbs |> BU.fold_map (fun env lb ->
            let x = {left lb.lbname with sort=lb.lbtyp} in
            let lb = {lb with lbname=Inl x} in
            let env = Env.push_let_binding env lb.lbname ([], lb.lbtyp) in //local let recs are not universe polymorphic
            env, lb) env in

          let bvs = lbs |> List.map (fun lb -> left (lb.lbname)) in

          let e2, cres, g2 = tc_term env e2 in
          let cres =
            List.fold_right
              (fun lb cres -> maybe_intro_smt_lemma env lb.lbtyp cres)
              lbs
              cres
          in
          let cres = TcUtil.maybe_assume_result_eq_pure_term env e2 cres in
          let cres = TcComm.lcomp_set_flags cres [SHOULD_NOT_INLINE] in //cf. issue #1362
          let guard = Env.conj_guard g_lbs (Env.close_guard env (List.map S.mk_binder bvs) g2) in
          let cres = TcUtil.close_wp_lcomp env bvs cres in
          let tres = norm env cres.res_typ in
          let cres = {cres with res_typ=tres} in

          let guard =
            let bs = lbs |> List.map (fun lb -> S.mk_binder (BU.left lb.lbname)) in
            TcUtil.close_guard_implicits env false bs guard
          in

(*close*) let lbs, e2 = SS.close_let_rec lbs e2 in
          let e = mk (Tm_let((true, lbs), e2)) top.pos in

          begin match topt with
              | Some _ -> e, cres, guard //we have an annotation
              | None ->
                let tres, g_ex = check_no_escape None env bvs tres in
                let cres = {cres with res_typ=tres} in
                e, cres, Env.conj_guard g_ex guard
          end

        | _ -> failwith "Impossible"

(******************************************************************************)
(* build an environment with recursively bound names.                         *)
(* refining the types of those names with decreases clauses is done in tc_abs *)
(******************************************************************************)
and build_let_rec_env _top_level env lbs : list<letbinding> * env_t * guard_t =
   let env0 = env in
   let termination_check_enabled (lbname:lbname) (lbdef:term) (lbtyp:term)
     : option<(int * term)> // when enabled returns recursion arity;
                            // plus the term elaborated with implicit binders
                            // (TODO: move all that logic to desugaring)
     =
     if Options.ml_ish () then None else

     let lbtyp0 = lbtyp in
     let actuals, body, body_lc = abs_formals lbdef in

     //add implicit binders, in case, for instance
     //lbtyp is of the form x:'a -> t
     //lbdef is of the form (fun x -> t)
     //in which case, we need to add (#'a:Type) to the actuals
     //See the handling in Tm_abs case of tc_value, roughly line 703 (location may have changed since this comment was written)
     let actuals = TcUtil.maybe_add_implicit_binders (Env.set_expected_typ env lbtyp) actuals in
     let nactuals = List.length actuals in

     (* Grab binders from the type. At most as many as we have in
      * the abstraction. *)
     let formals, c = N.get_n_binders env nactuals lbtyp in

     // TODO: There's a similar error in check_let_recs, would be nice
     // to remove this one.
     if List.isEmpty formals || List.isEmpty actuals then
       raise_error (Errors.Fatal_RecursiveFunctionLiteral,
                    (BU.format3 "Only function literals with arrow types can be defined recursively; got (%s) %s : %s"
                               (Print.tag_of_term lbdef)
                               (Print.term_to_string lbdef)
                               (Print.term_to_string lbtyp)))
                   lbtyp.pos; // TODO: GM: maybe point to the one that's actually empty?

     let nformals = List.length formals in

     (* `nformals` is exactly the arity of recursion. It is either
      * the amount of binders we traversed until we ran into an effect
      * in the expected type, or the total amount of binders in the
      * abstraction's body. So we can just check the effect `c` for
      * totality. Another way of seeing this check is that we take
      * the minimum amount of binders from the actuals and formals. *)
     if U.comp_effect_name c |> Env.lookup_effect_quals env |> List.contains TotalEffect then
       Some (nformals, U.abs actuals body body_lc)
     else
       None
   in
   let check_annot univ_vars t =
       let env0 = Env.push_univ_vars env0 univ_vars in
       let t, _, g = tc_check_tot_or_gtot_term ({env0 with check_uvars=true}) t (fst <| U.type_u()) "" in
       env0, g |> Rel.resolve_implicits env |> Rel.discharge_guard env0, t
   in
   let lbs, env, g = List.fold_left (fun (lbs, env, g_acc) lb ->
        let univ_vars, lbtyp, lbdef, check_t = TcUtil.extract_let_rec_annotation env lb in
        let env = Env.push_univ_vars env univ_vars in //no polymorphic recursion on universes
        let g, lbtyp = 
            if not check_t 
            then g_acc, lbtyp
            else let _, g, t = check_annot univ_vars lbtyp in
                 Env.conj_guard g_acc g, t
        in
        // AR: This code (below) also used to have && Env.should_verify env
        // i.e. when lax checking it was adding lbname in the second branch
        // this was a problem for 2-phase, if an implicit type was the type of a let rec (see bug056)
        // Removed that check. Rest of the code relies on env.letrecs = []
        let lb, env =
            match termination_check_enabled lb.lbname lbdef lbtyp with
            // AR: we need to add the binding of the let rec after adding the
            // binders of the lambda term, and so, here we just note in the env that
            // we are typechecking a let rec, the recursive binding will be added in
            // tc_abs adding universes here so that when we add the let binding, we
            // can add a typescheme with these universes
            | Some (arity, lbdef) ->
              let lb = {lb with lbtyp=lbtyp; lbunivs=univ_vars; lbdef=lbdef} in
              let env = {env with letrecs=(lb.lbname, arity, lbtyp, univ_vars)::env.letrecs} in
              lb, env
            | None ->
              let lb = {lb with lbtyp=lbtyp; lbunivs=univ_vars; lbdef=lbdef} in
              lb, Env.push_let_binding env lb.lbname (univ_vars, lbtyp)
        in
        lb::lbs,  env, g)
    ([], env, Env.trivial_guard)
    lbs  in
  List.rev lbs, env, g

and check_let_recs env lbts =
    let lbs, gs = lbts |> List.map (fun lb ->
        (* here we set the expected type in the environment to the annotated expected type
         * and use it in order to type check the body of the lb
         * *)
        let bs, t, lcomp = abs_formals lb.lbdef in
        //see issue #1017
        match bs with
        | [] -> raise_error (Errors.Fatal_RecursiveFunctionLiteral, 
                            BU.format2
                            "Only function literals may be defined recursively; %s is defined to be %s"
                               (Print.lbname_to_string lb.lbname)
                               (Print.term_to_string lb.lbdef)
                            ) (S.range_of_lbname lb.lbname)
        | _ -> ();

        (* HACK ALERT: arity
         *
         * We build a Tm_abs node with exactly [arity] binders,
         * and put the rest in another node in the body, so `tc_abs`
         * will do the right thing when computing a decreases clauses.
        *)
        let arity = match Env.get_letrec_arity env lb.lbname with
                    | Some n -> n
                    | None -> List.length bs (* Keep the node as-is *)
        in
        let bs0, bs1 = List.splitAt arity bs in
        let def =
            if List.isEmpty bs1
            then U.abs bs0 t lcomp
            else let inner = U.abs bs1 t lcomp in
                 let inner = SS.close bs0 inner in
                 let bs0 = SS.close_binders bs0 in
                 S.mk (Tm_abs (bs0, inner, None)) inner.pos
                 // ^ using abs again would flatten the abstraction
        in
        (* / HACK *)

        let lb = { lb with lbdef = def } in

        let e, c, g = tc_tot_or_gtot_term (Env.set_expected_typ env lb.lbtyp) lb.lbdef in
        if not (TcComm.is_total_lcomp c)
        then raise_error (Errors.Fatal_UnexpectedGTotForLetRec, "Expected let rec to be a Tot term; got effect GTot") e.pos;
        (* replace the body lb.lbdef with the type checked body e with elaboration on monadic application *)
        let lb = U.mk_letbinding lb.lbname lb.lbunivs lb.lbtyp Const.effect_Tot_lid e lb.lbattrs lb.lbpos in
        lb, g) |> List.unzip in
    let g_lbs = List.fold_right Env.conj_guard gs Env.trivial_guard in
    lbs, g_lbs


(******************************************************************************)
(* Several utility functions follow                                           *)
(******************************************************************************)
and check_let_bound_def top_level env lb
                               : term       (* checked lbdef                   *)
                               * univ_names (* univ_vars, if any               *)
                               * lcomp      (* type of lbdef                   *)
                               * guard_t    (* well-formedness of lbtyp        *)
                               * bool       (* true iff lbtyp was annotated    *)
                               =
    let env1, _ = Env.clear_expected_typ env in
    let e1 = lb.lbdef in

    (* 1. extract the annotation of the let-bound term, e1, if any *)
    let topt, wf_annot, univ_vars, univ_opening, env1 = check_lbtyp top_level env lb in

    if not top_level && univ_vars <> []
    then raise_error (Errors.Fatal_UniversePolymorphicInnerLetBound, "Inner let-bound definitions cannot be universe polymorphic") e1.pos;

    (* 2. type-check e1 *)
    (* Only toplevel terms should have universe openings *)
    assert ( top_level || List.length univ_opening = 0 );
    let e1 = subst univ_opening e1 in
    let e1, c1, g1 = tc_maybe_toplevel_term ({env1 with top_level=top_level}) e1 in

    (* and strengthen its VC with and well-formedness condition on its annotated type *)
    //NS: Maybe redundant strengthen
    // let c1, guard_f = c1, wf_annot in
    let c1, guard_f = TcUtil.strengthen_precondition
                        (Some (fun () -> return_all Err.ill_kinded_type))
                        (Env.set_range env1 e1.pos) e1 c1 wf_annot in
    let g1 = Env.conj_guard g1 guard_f in

    if Env.debug env Options.Extreme
    then BU.print3 "checked let-bound def %s : %s guard is %s\n"
            (Print.lbname_to_string lb.lbname)
            (TcComm.lcomp_to_string c1)
            (Rel.guard_to_string env g1);

    e1, univ_vars, c1, g1, Option.isSome topt


(* Extracting the type of non-recursive let binding *)
and check_lbtyp top_level env lb : option<typ>  (* checked version of lb.lbtyp, if it was not Tm_unknown *)
                                 * guard_t      (* well-formedness condition for that type               *)
                                 * univ_names   (* explicit universe variables, if any                   *)
                                 * list<subst_elt> (* subtistution of the opened universes               *)
                                 * Env.env      (* env extended with univ_vars                           *)
                                 =
    let t = SS.compress lb.lbtyp in
    match t.n with
        | Tm_unknown ->
          //if lb.lbunivs <> [] then failwith "Impossible: non-empty universe variables but the type is unknown";  //AR: do we need this check? this situation arises in phase 2
          let univ_opening, univ_vars = univ_var_opening lb.lbunivs in
          None, Env.trivial_guard, univ_vars, univ_opening, Env.push_univ_vars env univ_vars

        | _ ->
          let univ_opening, univ_vars = univ_var_opening lb.lbunivs in
          let t = subst univ_opening t in
          let env1 = Env.push_univ_vars env univ_vars in
          if top_level
          && not (env.generalize) //clearly, x has an annotated type ... could env.generalize ever be true here?
                                  //yes. x may not have a val declaration, only an inline annotation
                                  //so, not (env.generalize) signals that x has been declared as val x : t, and t has already been checked
          then Some t, Env.trivial_guard, univ_vars, univ_opening, Env.set_expected_typ env1 t //t has already been kind-checked
          else //we have an inline annotation
               let k, _ = U.type_u () in
               let t, _, g = tc_check_tot_or_gtot_term env1 t k "" in
               if debug env Options.Medium
               then BU.print2 "(%s) Checked type annotation %s\n"
                        (Range.string_of_range (range_of_lbname lb.lbname))
                        (Print.term_to_string t);
               let t = norm env1 t in
               Some t, g, univ_vars, univ_opening, Env.set_expected_typ env1 t


and tc_binder env ({binder_bv=x;binder_qual=imp;binder_attrs=attrs}) =
    let tu, u = U.type_u () in
    if Env.debug env Options.Extreme
    then BU.print3 "Checking binder %s:%s at type %s\n"
                   (Print.bv_to_string x)
                   (Print.term_to_string x.sort)
                   (Print.term_to_string tu);
    let t, _, g = tc_check_tot_or_gtot_term env x.sort tu "" in //ghost effect ok in the types of binders
    let imp, g' =
        match imp with
        | Some (Meta tau) ->
          let tau, _, g = tc_tactic t_unit t_unit env tau in
          Some (Meta tau), g
        | _ -> imp, Env.trivial_guard
    in
    let attrs =
      attrs |> List.map (fun attr ->
        let attr, _, _ = tc_check_tot_or_gtot_term env attr t_unit "" in
        attr) in
    let x = S.mk_binder_with_attrs ({x with sort=t}) imp attrs in
    if Env.debug env Options.High
    then BU.print2 "Pushing binder %s at type %s\n" (Print.bv_to_string x.binder_bv) (Print.term_to_string t);
    x, push_binding env x, g, u

and tc_binders env bs =
    if Env.debug env Options.Extreme then
        BU.print1 "Checking binders %s\n" (Print.binders_to_string ", " bs);
    let rec aux env bs = match bs with
        | [] -> [], env, Env.trivial_guard, []
        | b::bs ->
          let b, env', g, u = tc_binder env b in
          let bs, env', g', us = aux env' bs in
          b::bs, env', Env.conj_guard g (Env.close_guard_univs [u] [b] g'), u::us in
    aux env bs

and tc_smt_pats en pats =
    let tc_args en args : Syntax.args * guard_t =
       //an optimization for checking arguments in cases where we know that their types match the types of the corresponding formal parameters
       //notably, this is used when checking the application  (?u x1 ... xn). NS: which we do not currently do!
       List.fold_right (fun (t, imp) (args, g) ->
                             t |> check_no_smt_theory_symbols en;
                             let t, _, g' = tc_term en t in
                             (t, imp)::args, Env.conj_guard g g')
          args ([], Env.trivial_guard) in
    List.fold_right (fun p (pats, g) ->
      let args, g' = tc_args en p in
      (args::pats, Env.conj_guard g g')) pats ([], Env.trivial_guard)

and tc_tot_or_gtot_term' (env:env) (e:term) (msg:string)
: term * lcomp * guard_t
= let e, c, g = tc_maybe_toplevel_term env e in
  if TcComm.is_tot_or_gtot_lcomp c
  then e, c, g
  else let g = Rel.solve_deferred_constraints env g in
       let c, g_c = TcComm.lcomp_comp c in
       let c = norm_c env c in
       let target_comp, allow_ghost =
            if TcUtil.is_pure_effect env (U.comp_effect_name c)
            then S.mk_Total (U.comp_result c), false
            else S.mk_GTotal (U.comp_result c), true in
       match Rel.sub_comp env c target_comp with
        | Some g' -> e, TcComm.lcomp_of_comp target_comp, Env.conj_guard g (Env.conj_guard g_c g')
        | _ ->
          if allow_ghost
          then raise_error (Err.expected_ghost_expression e c msg) e.pos
          else raise_error (Err.expected_pure_expression e c msg) e.pos

and tc_tot_or_gtot_term env e = tc_tot_or_gtot_term' env e ""

and tc_check_tot_or_gtot_term env e t msg
: term * lcomp * guard_t
= let env = Env.set_expected_typ env t in
  tc_tot_or_gtot_term' env e msg

and tc_trivial_guard env t =
  let t, c, g = tc_tot_or_gtot_term env t in
  Rel.force_trivial_guard env g;
  t,c

let tc_check_trivial_guard env t k =
  let t, _, g = tc_check_tot_or_gtot_term env t k "" in
  Rel.force_trivial_guard env g;
  t


(* type_of_tot_term env e : e', t, g
      checks that env |- e' : Tot t' <== g
      i.e., e' is an elaboration of e
            such that it has type Tot t
            subject to the guard g
            in environment env
 *)
let typeof_tot_or_gtot_term env e must_tot =
    if Env.debug env <| Options.Other "RelCheck" then BU.print1 "Checking term %s\n" (Print.term_to_string e);
    //let env, _ = Env.clear_expected_typ env in
    let env = {env with top_level=false; letrecs=[]} in
    let t, c, g =
        try tc_tot_or_gtot_term env e
        with Error(e, msg, _, ctx) -> raise (Error (e, msg, Env.get_range env, ctx))
    in
    if must_tot then
      let c = N.maybe_ghost_to_pure_lcomp env c in
      if TcComm.is_total_lcomp c
      then t, c.res_typ, g
      else raise_error (Errors.Fatal_UnexpectedImplictArgument, (BU.format1 "Implicit argument: Expected a total term; got a ghost term: %s" (Print.term_to_string e))) (Env.get_range env)
    else t, c.res_typ, g

let level_of_type_fail env e t =
    raise_error (Errors.Fatal_UnexpectedTermType, (BU.format2 "Expected a term of type 'Type'; got %s : %s"
                                (Print.term_to_string e) t)) (Env.get_range env)

let level_of_type env e t =
    let rec aux retry t =
        match (U.unrefine t).n with
        | Tm_type u -> u
        | _ ->
          if retry
          then let t = Normalize.normalize [Env.UnfoldUntil delta_constant] env t in
               aux false t
          else let t_u, u = U.type_u() in
               let env = {env with lax=true} in
               (*
                * AR: This is a little harsh
                *     If t is a uvar, then this prevents t to be inferred as something more
                *       precise than Type, e.g. eqtype
                *     So ideally, we could here generate a subtyping constraint
                *     But for that this function needs to return a guard, and
                *       the guard needs to be accounted for in the callers
                *)
               let g = FStar.TypeChecker.Rel.teq env t t_u in
               begin match g.guard_f with
                     | NonTrivial f ->
                       level_of_type_fail env e (Print.term_to_string t)
                     | _ ->
                       Rel.force_trivial_guard env g
               end;
               u
    in aux true t

(* universe_of_aux env e:
      During type-inference, we build terms like WPs for which we need to compute
      explicit universe instantiations.

      This is generally called from within TypeChecker.Util
      when building WPs. For example, in building (return_value<u> t e),
      u=universe_of env t.

      We don't aim to compute a precise type for e.
      Rather, we look to compute the universe level of e's type,
      presuming that e must have type Type

      For instance, if e is an application (f _), we compute the type of f to be bs -> C,
      and we take the universe level of e to be (level_of (comp_result C)),
      disregarding the arguments of f.
 *)
let rec universe_of_aux env e =
   match (SS.compress e).n with
   | Tm_bvar _
   | Tm_unknown
   | Tm_delayed _ -> failwith "Impossible"
   //normalize let bindings away and then compute the universe
   | Tm_let _ ->
     let e = N.normalize [] env e in
     universe_of_aux env e
   //we expect to compute (Type u); so an abstraction always fails
   | Tm_abs(bs, t, _) ->
     level_of_type_fail env e "arrow type"
   //these next few cases are easy; we just use the type stored at the node
   | Tm_uvar (u, s) -> SS.subst' s u.ctx_uvar_typ
   | Tm_meta(t, _) -> universe_of_aux env t
   | Tm_name n -> n.sort
   | Tm_fvar fv ->
     let (_, t), _ = Env.lookup_lid env fv.fv_name.v in
     t
   | Tm_lazy i -> universe_of_aux env (U.unfold_lazy i)
   | Tm_ascribed(_, (Inl t, _), _) -> t
   | Tm_ascribed(_, (Inr c, _), _) -> U.comp_result c
   //also easy, since we can quickly recompute the type
   | Tm_type u -> S.mk (Tm_type (U_succ u)) e.pos
   | Tm_quoted _ -> U.ktype0
   | Tm_constant sc -> tc_constant env e.pos sc
   //slightly subtle, since fv is a type-scheme; instantiate it with us
   | Tm_uinst({n=Tm_fvar fv}, us) ->
     let (us', t), _ = Env.lookup_lid env fv.fv_name.v in
     if List.length us <> List.length us' then
       raise_error (Errors.Fatal_UnexpectedNumberOfUniverse, "Unexpected number of universe instantiations") (Env.get_range env);
     (* FIXME: this logic is repeated from the Tm_uinst case of tc_value *)
     List.iter2
       (fun ul ur -> match ul, ur with
        | U_unif u'', _ -> UF.univ_change u'' ur
        // TODO: more cases? we cannot get U_succ or U_max here I believe...
        | U_name n1, U_name n2 when Ident.ident_equals n1 n2 -> ()
        | _ ->
          raise_error (Errors.Fatal_IncompatibleUniverse,
                       BU.format3 "Incompatible universe application for %s, expected %s got %s\n"
                                  (Print.fv_to_string fv)
                                  (Print.univ_to_string ul)
                                  (Print.univ_to_string ur))
                      (Env.get_range env))
       us' us;
     t

   | Tm_uinst _ ->
     failwith "Impossible: Tm_uinst's head must be an fvar"
   //the refinement formula plays no role in the universe computation; so skip it
   | Tm_refine(x, _) -> universe_of_aux env x.sort
   //U_max(univ_of bs, univ_of c)
   | Tm_arrow(bs, c) ->
     let bs, c = SS.open_comp bs c in
     let us = List.map (fun ({binder_bv=b}) -> level_of_type env b.sort (universe_of_aux env b.sort)) bs in
     let u_res =
        let res = U.comp_result c in
        level_of_type env res (universe_of_aux env res) in
     let u_c = c |> TcUtil.universe_of_comp env u_res in
     let u = N.normalize_universe env (S.U_max (u_c::us)) in
     S.mk (Tm_type u) e.pos
   //See the comment at the top of this function; we just compute the universe of hd's result type
   | Tm_app(hd, args) ->
     let rec type_of_head retry hd args =
        let hd = SS.compress hd in
        match hd.n with
        | Tm_unknown
        | Tm_bvar _
        | Tm_delayed _ ->
          failwith "Impossible"
        | Tm_fvar _
        | Tm_name _
        | Tm_uvar _
        | Tm_uinst _
        | Tm_ascribed _
        | Tm_refine _
        | Tm_constant _
        | Tm_arrow _
        | Tm_meta _
        | Tm_type _ ->
          universe_of_aux env hd, args
        | Tm_match(_, _, hd::_) ->  //AR: TODO: use return annotation?
          let (_, _, hd) = SS.open_branch hd in
          let hd, args' = U.head_and_args hd in
          type_of_head retry hd (args'@args)
        | _ when retry ->
          //head is either an abs, so we have a beta-redex
          //      or a let,
          // GM: NOTE: not using hd and args here,
          //     this is calling itself with the `e` from
          //     universe_of_aux and splitting it again.
          let e = N.normalize [Env.Beta; Env.DoNotUnfoldPureLets] env e in
          let hd, args = U.head_and_args e in
          type_of_head false hd args
        | _ ->
          let env, _ = Env.clear_expected_typ env in
          let env = {env with lax=true; use_bv_sorts=true; top_level=false} in
          if Env.debug env <| Options.Other "UniverseOf"
          then BU.print2 "%s: About to type-check %s\n"
                        (Range.string_of_range (Env.get_range env))
                        (Print.term_to_string hd);
          let _, ({res_typ=t}), g = tc_term env hd in
          Rel.solve_deferred_constraints env g |> ignore;
          t, args
     in
     let t, args = type_of_head true hd args in
     let t = N.normalize [Env.UnfoldUntil delta_constant] env t in
     let bs, res = U.arrow_formals_comp t in
     let res = U.comp_result res in
     if List.length bs = List.length args
     then let subst = U.subst_of_list bs args in
          SS.subst subst res
     else level_of_type_fail env e (Print.term_to_string res)
   | Tm_match(_, _, hd::_) ->  //AR: TODO: use return annotation?
     let (_, _, hd) = SS.open_branch hd in
     universe_of_aux env hd
   | Tm_match(_, _, []) ->  //AR: TODO: use return annotation?
     level_of_type_fail env e "empty match cases"

let universe_of env e =
    if debug env Options.High then
      BU.print1 "Calling universe_of_aux with %s {\n" (Print.term_to_string e);
    let r = universe_of_aux env e in
    if debug env Options.High then
      BU.print1 "Got result from universe_of_aux = %s }\n" (Print.term_to_string r);
    level_of_type env e r

let tc_tparams env0 (tps:binders) : (binders * Env.env * universes) =
    let tps, env, g, us = tc_binders env0 tps in
    Rel.force_trivial_guard env0 g;
    tps, env, us

////////////////////////////////////////////////////////////////////////////////

(*
    Pre-condition: exists k. env |- t : (G)Tot k
    i.e., t is well-typed in env at some type k

    And t is Tot or GTot, meaning if it is PURE or GHOST, its wp has been accounted for
      (which is the case for the terms in the unifier)

    Returns (Some k), if it can find k quickly and the effect of t is consistent with must_tot

    If either the type cannot be computed or effect does not match with must_tot, returns None

    A possible restructuring would be to treat these two (type and effect) separately
      in the return type
*)

let rec typeof_tot_or_gtot_term_fastpath (env:env) (t:term) (must_tot:bool) : option<typ> =
  let mk_tm_type u = S.mk (Tm_type u) t.pos in
  let effect_ok k = (not must_tot) || (N.non_info_norm env k) in
  let t = SS.compress t in
  match t.n with
  | Tm_delayed _
  | Tm_bvar _ -> failwith ("Impossible: " ^ Print.term_to_string t)

  (* Can't (easily) do this one efficiently, just return None *)
  | Tm_constant Const_reify
  | Tm_constant (Const_reflect _) -> None

  //For the following nodes, use the universe_of_aux function
  //since these are already Tot, we don't need to check the must_tot flag
  | Tm_name _
  | Tm_fvar _
  | Tm_uinst _
  | Tm_constant _
  | Tm_type _
  | Tm_arrow _ -> universe_of_aux env t |> Some

  | Tm_lazy i ->
    typeof_tot_or_gtot_term_fastpath env (U.unfold_lazy i) must_tot

  | Tm_abs(bs, body, Some ({residual_effect=eff; residual_typ=tbody})) ->  //AR: maybe keep residual univ too?
    let mk_comp =
      if Ident.lid_equals eff Const.effect_Tot_lid
      then Some S.mk_Total'
      else if Ident.lid_equals eff Const.effect_GTot_lid
      then Some S.mk_GTotal'
      else None
    in
    bind_opt mk_comp (fun f ->
      let tbody =
        match tbody with
        | Some _ -> tbody
        | None ->
          let bs, body = SS.open_term bs body in
          BU.map_opt (typeof_tot_or_gtot_term_fastpath (Env.push_binders env bs) body false) (SS.close bs) in
      bind_opt tbody (fun tbody ->
        let bs, tbody = SS.open_term bs tbody in
        let u = universe_of (Env.push_binders env bs) tbody in
        Some (U.arrow bs (f tbody (Some u)))))

  | Tm_abs _ -> None

  | Tm_refine(x, _) -> typeof_tot_or_gtot_term_fastpath env x.sort must_tot

  (* Unary operators. Explicitly curry extra arguments *)
  | Tm_app({n=Tm_constant Const_range_of}, a::hd::rest) ->
    let rest = hd::rest in //no 'as' clauses in F* yet, so we need to do this ugliness
    let unary_op, _ = U.head_and_args t in
    let head = mk (Tm_app(unary_op, [a])) (Range.union_ranges unary_op.pos (fst a).pos) in
    let t = mk (Tm_app(head, rest)) t.pos in
    typeof_tot_or_gtot_term_fastpath env t must_tot

  (* Binary operators *)
  | Tm_app({n=Tm_constant Const_set_range_of}, a1::a2::hd::rest) ->
    let rest = hd::rest in //no 'as' clauses in F* yet, so we need to do this ugliness
    let unary_op, _ = U.head_and_args t in
    let head = mk (Tm_app(unary_op, [a1; a2])) (Range.union_ranges unary_op.pos (fst a1).pos) in
    let t = mk (Tm_app(head, rest)) t.pos in
    typeof_tot_or_gtot_term_fastpath env t must_tot

  | Tm_app({n=Tm_constant Const_range_of}, [_]) ->
    Some (t_range)

  | Tm_app({n=Tm_constant Const_set_range_of}, [(t, _); _]) ->
    typeof_tot_or_gtot_term_fastpath env t must_tot

  | Tm_app(hd, args) ->
    let t_hd = typeof_tot_or_gtot_term_fastpath env hd must_tot in

    let rec aux args t_hd =
      match (N.unfold_whnf env t_hd).n with
      | Tm_arrow(bs, c) ->
        let n_args = List.length args in
        let n_bs = List.length bs in
        let bs_t_opt =  (* bs (opened), args (length args = length bs), comp result type, remaining args *)
          if n_args < n_bs
          then let bs, rest = BU.first_N n_args bs in
               let t = S.mk (Tm_arrow (rest, c)) t_hd.pos in
               let bs, c = SS.open_comp bs (S.mk_Total t) in
               Some (bs, args, U.comp_result c, [])
          else let bs, c = SS.open_comp bs c in
               let args, remaining_args = List.splitAt n_bs args in
               Some (bs, args, U.comp_result c, remaining_args)
        in
        bind_opt bs_t_opt (fun (bs, args, t, remaining_args) ->
          let subst = List.map2 (fun b a -> NT (b.binder_bv, fst a)) bs args in
          let t = SS.subst subst t in
          if List.length remaining_args = 0 then Some t else aux remaining_args t)
      | Tm_refine(x, _) -> aux args x.sort
      | Tm_ascribed(t, _, _) -> aux args t
      | _ -> None
    in

    bind_opt t_hd (fun t_hd ->
      bind_opt (aux args t_hd) (fun t ->
        if (effect_ok t) ||
           (List.for_all (fun (a, _) -> typeof_tot_or_gtot_term_fastpath env a must_tot |> is_some) args)
        then Some t
        else None))

  | Tm_ascribed(t, (Inl k, _), _) ->
    if effect_ok k
    then Some k
    else typeof_tot_or_gtot_term_fastpath env t must_tot

  | Tm_ascribed(_, (Inr c, _), _) ->
    let k = U.comp_result c in
    if (not must_tot) ||
       (c |> U.comp_effect_name |> Env.norm_eff_name env |> lid_equals Const.effect_PURE_lid) ||
       (N.non_info_norm env k)
    then Some k
    else None

  | Tm_uvar (u, s) -> if not must_tot then Some (SS.subst' s u.ctx_uvar_typ) else None

  | Tm_quoted (tm, qi) -> if not must_tot then Some (S.t_term) else None

  | Tm_meta(t, _) -> typeof_tot_or_gtot_term_fastpath env t must_tot

  | Tm_match _
  | Tm_let _
  | Tm_unknown
  | Tm_uinst _ -> None
  | _ -> failwith ("Impossible! (" ^ (Print.tag_of_term t) ^ ")")

(*
 * Precondition: G |- t : Tot _ or G |- t : GTot _
 *   Meaning, even if t is PURE or GHOST, its wp has been accounted for already,
 *   which is the case for terms in the unifier
 *
 * It returns either PURE or GHOST (or None if fast path fails)
 *)
let rec effectof_tot_or_gtot_term_fastpath (env:env) (t:term) : option<lident> =
  match (SS.compress t).n with
  | Tm_delayed _ | Tm_bvar _ -> failwith "Impossible!"
  
  | Tm_name _ -> Const.effect_PURE_lid |> Some
  | Tm_lazy _ -> Const.effect_PURE_lid |> Some
  | Tm_fvar _ -> Const.effect_PURE_lid |> Some
  | Tm_uinst _ -> Const.effect_PURE_lid |> Some
  | Tm_constant _ -> Const.effect_PURE_lid |> Some
  | Tm_type _ -> Const.effect_PURE_lid |> Some
  | Tm_abs _ -> Const.effect_PURE_lid |> Some
  | Tm_arrow _ -> Const.effect_PURE_lid |> Some
  | Tm_refine _ -> Const.effect_PURE_lid |> Some
  
  | Tm_app (hd, args) ->
    let join_effects eff1 eff2 =
      let eff1, eff2 = Env.norm_eff_name env eff1, Env.norm_eff_name env eff2 in
      let pure, ghost = Const.effect_PURE_lid, Const.effect_GHOST_lid in

      if lid_equals eff1 pure && lid_equals eff2 pure then Some pure
      else if (lid_equals eff1 ghost || lid_equals eff1 pure)
           && (lid_equals eff2 ghost || lid_equals eff2 pure)
      then Some ghost
      else None in

    bind_opt (effectof_tot_or_gtot_term_fastpath env hd) (fun eff_hd ->
      bind_opt (List.fold_left (fun eff_opt arg ->
                                bind_opt eff_opt (fun eff ->
                                  bind_opt (effectof_tot_or_gtot_term_fastpath env (fst arg))
                                    (join_effects eff))) (Some eff_hd) args) (fun eff_hd_and_args ->
        bind_opt (typeof_tot_or_gtot_term_fastpath env hd true) (fun t_hd ->
          let rec maybe_arrow t =
            let t = N.unfold_whnf env t in
            match t.n with
            | Tm_arrow _ -> t
            | Tm_refine (x, _) -> maybe_arrow x.sort
            | Tm_ascribed (t, _, _) -> maybe_arrow t
            | _ -> t in
          match (maybe_arrow t_hd).n with
          | Tm_arrow (bs, c) ->
            let eff_app =
              if List.length args < List.length bs
              then Const.effect_PURE_lid
              else U.comp_effect_name c in
            join_effects eff_hd_and_args eff_app
          | _ -> None)))
  | Tm_ascribed (t, (Inl _, _), _) -> effectof_tot_or_gtot_term_fastpath env t
  | Tm_ascribed (_, (Inr c, _), _) ->
    let c_eff = c |> U.comp_effect_name |> Env.norm_eff_name env in
    if lid_equals c_eff Const.effect_PURE_lid ||
       lid_equals c_eff Const.effect_GHOST_lid
    then Some c_eff
    else None
  | Tm_uvar _ -> None
  | Tm_quoted _ -> None
  | Tm_meta (t, _) -> effectof_tot_or_gtot_term_fastpath env t
  | Tm_match _ -> None
  | Tm_let _ -> None
  | Tm_unknown -> None
  | Tm_uinst _ -> None
  | _ -> None
