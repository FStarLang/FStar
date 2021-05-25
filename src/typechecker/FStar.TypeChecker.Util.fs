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
// (c) Microsoft Corporation. All rights reserved

module FStar.TypeChecker.Util
open FStar.Pervasives
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.TypeChecker.Rel
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Syntax.Subst
open FStar.TypeChecker.Common
open FStar.Syntax
open FStar.Dyn

type lcomp_with_binder = option<bv> * lcomp

module SS = FStar.Syntax.Subst
module S = FStar.Syntax.Syntax
module BU = FStar.Util
module U = FStar.Syntax.Util
module N = FStar.TypeChecker.Normalize
module TcComm = FStar.TypeChecker.Common
module P = FStar.Syntax.Print
module C = FStar.Parser.Const

//Reporting errors
let report env errs =
    Errors.log_issue (Env.get_range env)
               (Err.failed_to_prove_specification errs)

(************************************************************************)
(* Unification variables *)
(************************************************************************)
let new_implicit_var reason r env k =
    new_implicit_var_aux reason r env k Strict None

let close_guard_implicits env solve_deferred (xs:binders) (g:guard_t) : guard_t =
  if Options.eager_subtyping ()
  || solve_deferred
  then
    let solve_now, defer =
      g.deferred |> List.partition (fun (_, _, p) -> Rel.flex_prob_closing env xs p)
    in
    if Env.debug env <| Options.Other "Rel"
    then begin
      BU.print_string "SOLVE BEFORE CLOSING:\n";
      List.iter (fun (_, s, p) -> BU.print2 "%s: %s\n" s (Rel.prob_to_string env p)) solve_now;
      BU.print_string " ...DEFERRED THE REST:\n";
      List.iter (fun (_, s, p) -> BU.print2 "%s: %s\n" s (Rel.prob_to_string env p)) defer;
      BU.print_string "END\n"
    end;
    let g = Rel.solve_non_tactic_deferred_constraints env ({g with deferred=solve_now}) in
    let g = {g with deferred=defer} in
    g
  else g

let check_uvars r t =
  let uvs = Free.uvars t in
  if not (BU.set_is_empty uvs)
  then
    let us = List.map (fun u -> Print.uvar_to_string u.ctx_uvar_head) (BU.set_elements uvs) |> String.concat ", " in
    (* ignoring the hide_uvar_nums and print_implicits flags here *)
    Options.push();
    Options.set_option "hide_uvar_nums" (Options.Bool false);
    Options.set_option "print_implicits" (Options.Bool true);
    Errors.log_issue r
      (Errors.Error_UncontrainedUnificationVar, (BU.format2 "Unconstrained unification variables %s in type signature %s; \
       please add an annotation" us (Print.term_to_string t)));
    Options.pop()

(************************************************************************)
(* Extracting annotations, notably the decreases clause, for a recursive definion *)
(* We support several styles of writing decreases clauses:

   1. val f (x:t) : Tot t' (decreases d)
      let rec f x = e

      and variations such as the following, where the definition is
      partially annotated.

      val f (x:t) : Tot t' (decreases d)
      let rec f (x:t) : t' = e

   2. val f (x:t) : Tot t'
      let rec f x : Tot _ (decreases d) = e

   3. let rec f (x:t) : Tot t' (decreases d) = e

   4. let rec f x = e

   The first style is mainly for legacy reasons. Annotating a `val`
   with a decreases clause isn't pretty, but there is a fair bit of
   code using it.

   The second style is useful in conjunction with interfaces, where
   the val may appear in the interface and is defined using a
   recursive function separately. It may also be useful when the user
   wants to check the type of f first and separately from the
   definition, and then try to define it afterwards.

   The third style is common in another scenarios.

   The fourth style leaves it to type inference to figure output.

   A fifth style is the following:

   5. val f (x:t) : Tot t (decreases d)
      let rec f (x:t) : Tot t' (decreases d) = e

   where the decreases clause appears more than once. This style now
   raises a warning.

   In the function below,
       extract_let_rec_annotation env lb

   the general idea is to

     1. prefer the decreases clause annotated on the
        term, if any

     2. Remove the decreases clause from the ascription on the body

     3. construct a type with the decreases clause and use that as the
        lbtyp, which TcTerm will use to implement the termination
        check

   returns the following:

   - lb.univ_vars: The opened universe names for the letbinding
     (incidentally, they are the same as the input univ_vars)

   - lbtyp: This is the type to be used to check the recursive
     definition.

       - In case 1, it is simply the annotated type from the
         val, i.e., lb.lbtyp

       - In case 2, we lift the decreases clause from the ascription
         and return  `x:t -> Tot t' (decreases d)`

       - In case 3, it is simply the ascribed type

       - In case 4, just build a type `_ -> _` and return it

       - In case 5, warn and ignore the decrease clause on the val,
         and treat it as case 2

   - lbdef: lb.lbdef adapted to remove any decreases clause annotation

   - check: A flag that signals when the constructed type should be
     re-typechecked. Except in case 1, the flag is set.
*)
(************************************************************************)
let extract_let_rec_annotation env {lbname=lbname; lbunivs=univ_vars; lbtyp=t; lbdef=e} :
    list<univ_name>
   * typ
   * term
   * bool //true indicates that the type needs to be checked; false indicates that it is already checked
   =
  let rng = S.range_of_lbname lbname in
  let t = SS.compress t in
  let u_subst, univ_vars = SS.univ_var_opening univ_vars in
  let e = SS.subst u_subst e in
  let t = SS.subst u_subst t in
  if Env.debug env <| Options.Other "Dec"
  then BU.print2 "extract_let_rec_annotation lbdef=%s; lbtyp=%s\n"
                 (Print.term_to_string e)
                 (Print.term_to_string t);
  let env = Env.push_univ_vars env univ_vars in
  let un_arrow t =
    //Rather than use U.arrow_formals_comp, we use un_arrow here
    //since the former collapses adjacent Tot annotations, e.g.,
    //    x:t -> Tot (y:t -> M)
    // is collapsed, breaking arities
      match (SS.compress t).n with
      | Tm_arrow (bs, c) ->
        Subst.open_comp bs c
      | _ ->
        Errors.raise_error (Errors.Fatal_LetRecArgumentMismatch, "Recursive functions must be introduced at arrow types")
                           rng
  in
  let reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt =
      let get_decreases c =
          U.comp_flags c |> BU.prefix_until (function DECREASES _ -> true | _ -> false)
      in
      match lbtyp_opt with
      | None ->
        let bs, c = un_arrow tarr in
        (match get_decreases c with
         | Some (pfx, DECREASES d, sfx) ->
           let c = U.comp_set_flags c (pfx @ sfx) in
           U.arrow bs c, tarr, true
         | _ -> tarr, tarr, true)

      | Some annot ->
        let bs, c = un_arrow tarr in
        let bs', c' = un_arrow annot in
        if List.length bs <> List.length bs'
        then Errors.raise_error (Errors.Fatal_LetRecArgumentMismatch, "Arity mismatch on let rec annotation")
                                rng;
        let move_decreases d flags flags' =
          let d' =
            let s = U.rename_binders bs bs' in
            List.map (SS.subst s) d
          in
          let c = U.comp_set_flags c flags in
          let tarr = U.arrow bs c in
          let c' = U.comp_set_flags c' (DECREASES (Decreases_lex d')::flags') in
          let tannot = U.arrow bs' c' in
          tarr, tannot, true
        in
        match get_decreases c, get_decreases c' with
        | None, _ -> tarr, annot, false
        | Some (pfx, DECREASES (Decreases_lex d), sfx), Some (pfx', DECREASES (Decreases_lex d'), sfx') ->
          Errors.log_issue rng
             (Warning_DeprecatedGeneric,
              "Multiple decreases clauses on this definition; the decreases clause on the declaration is ignored, please remove it");
          move_decreases d (pfx@sfx) (pfx'@sfx')
        | Some (pfx, DECREASES (Decreases_lex d), sfx), None ->
          move_decreases d (pfx@sfx) (U.comp_flags c')
        | _ -> failwith "Impossible"
  in
  let extract_annot_from_body (lbtyp_opt:option<typ>)
    : typ
    * term
    * bool
    = let rec aux_lbdef e
        : typ * term * bool
        = let e = SS.compress e in
          match e.n with
          | Tm_meta(e', m) ->
            let t, e', recheck = aux_lbdef e' in
            t, { e with n = Tm_meta(e', m) }, recheck

          | Tm_ascribed(e', (Inr c, tac_opt), lopt) ->
            if U.is_total_comp c
            then let t, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type (U.comp_result c) lbtyp_opt in
                 let e = { e with n = Tm_ascribed(e', (Inr (S.mk_Total t), tac_opt), lopt) } in
                 lbtyp, e, recheck
            else raise_error (Errors.Fatal_UnexpectedComputationTypeForLetRec,
                              BU.format1 "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                                   (Print.comp_to_string c))
                              rng

          | Tm_ascribed(e', (Inl t, tac_opt), lopt) ->
            let t, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type t lbtyp_opt in
            let e = { e with n = Tm_ascribed(e', (Inl t, tac_opt), lopt) } in
            lbtyp, e, recheck

          | Tm_abs _ ->
            let bs, body, rcopt = U.abs_formals_maybe_unascribe_body false e in
            let mk_comp t =
              if Options.ml_ish()
              then U.ml_comp t t.pos
              else S.mk_Total t
            in
            let mk_arrow c = U.arrow bs c in
            let rec aux_abs_body body =
              let body = SS.compress body in
              match body.n with
              | Tm_meta (body, m) ->
                let t, body', recheck = aux_abs_body body in
                let body = { body with n = Tm_meta(body', m) } in
                t, body, recheck

              | Tm_ascribed (_, (Inl t, _), _) -> //no decreases clause here
                begin
                match lbtyp_opt with
                | Some lbtyp ->
                  lbtyp, body, false

                | None ->
                  let t = mk_arrow (mk_comp t) in
                  t, body, true
                end

              | Tm_ascribed (body', (Inr c, tac_opt), lopt) ->
                let tarr = mk_arrow c in
                let tarr, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt in
                let bs', c = un_arrow tarr in
                if List.length bs' <> List.length bs
                then failwith "Impossible"
                else let subst = U.rename_binders bs' bs in
                     let c = SS.subst_comp subst c in
                     let body = { body with n = Tm_ascribed(body', (Inr c, tac_opt), lopt) } in
                     lbtyp, body, recheck

              | _ ->
                match lbtyp_opt with
                | Some lbtyp ->
                  lbtyp, body, false

                | None ->
                  let tarr = mk_arrow (mk_comp S.tun) in
                  tarr, body, true
            in
            let lbtyp, body, recheck = aux_abs_body body in
            lbtyp, U.abs bs body rcopt, recheck
      in
      aux_lbdef e
    in
    match t.n with
    | Tm_unknown ->
      let lbtyp, e, _ = extract_annot_from_body None in
      univ_vars, lbtyp, e, true

    | _ ->
      let _, c = U.arrow_formals_comp t in
      if not (U.comp_effect_name c |> Env.lookup_effect_quals env |> List.contains TotalEffect)
      then //no termination check anyway, so don't bother rearranging decreases clauses
           univ_vars, t, e, false
      else
        let lbtyp, e, check_lbtyp = extract_annot_from_body (Some t) in
        univ_vars, lbtyp, e, check_lbtyp

(************************************************************************)
(* Utilities on patterns  *)
(************************************************************************)

//let decorate_pattern env p exp =
//    let qq = p in
//    let rec aux p e : pat  =
//        let pkg q = withinfo q p.p in
//        let e = U.unmeta e in
//        match p.v, e.n with
//            | _, Tm_uinst(e, _) -> aux p e

//            | Pat_constant _, _ ->
//              pkg p.v

//            | Pat_var x, Tm_name y ->
//              if not (bv_eq x y)
//              then failwith (BU.format2 "Expected pattern variable %s; got %s" (Print.bv_to_string x) (Print.bv_to_string y));
//              if Env.debug env <| Options.Other "Pat"
//              then BU.print2 "Pattern variable %s introduced at type %s\n" (Print.bv_to_string x) (Normalize.term_to_string env y.sort);
//              let s = Normalize.normalize [Env.Beta] env y.sort in
//              let x = {x with sort=s} in
//              pkg (Pat_var x)

//            | Pat_wild x, Tm_name y ->
//              if bv_eq x y |> not
//              then failwith (BU.format2 "Expected pattern variable %s; got %s" (Print.bv_to_string x) (Print.bv_to_string y));
//              let s = Normalize.normalize [Env.Beta] env y.sort in
//              let x = {x with sort=s} in
//              pkg (Pat_wild x)

//            | Pat_dot_term(x, _), _ ->
//              pkg (Pat_dot_term(x, e))

//            | Pat_cons(fv, []), Tm_fvar fv' ->
//              if not (Syntax.fv_eq fv fv')
//              then failwith (BU.format2 "Expected pattern constructor %s; got %s" (string_of_lid fv.fv_name.v) (string_of_lid fv'.fv_name.v));
//              pkg (Pat_cons(fv', []))

//            | Pat_cons(fv, argpats), Tm_app({n=Tm_fvar(fv')}, args)
//            | Pat_cons(fv, argpats), Tm_app({n=Tm_uinst({n=Tm_fvar(fv')}, _)}, args) ->

//              if fv_eq fv fv' |> not
//              then failwith (BU.format2 "Expected pattern constructor %s; got %s" (string_of_lid fv.fv_name.v) (string_of_lid fv'.fv_name.v));

//              let fv = fv' in
//              let rec match_args matched_pats args argpats = match args, argpats with
//                | [], [] -> pkg (Pat_cons(fv, List.rev matched_pats))
//                | arg::args, (argpat, _)::argpats ->
//                  begin match arg, argpat.v with
//                        | (e, Some (Implicit true)), Pat_dot_term _ ->
//                          let x = Syntax.new_bv (Some p.p) S.tun in
//                          let q = withinfo (Pat_dot_term(x, e)) p.p in
//                          match_args ((q, true)::matched_pats) args argpats

//                        | (e, imp), _ ->
//                          let pat = aux argpat e, S.is_implicit imp in
//                          match_args (pat::matched_pats) args argpats
//                 end

//                | _ -> failwith (BU.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" (Print.pat_to_string p) (Print.term_to_string e)) in

//              match_args [] args argpats

//           | _ ->
//            failwith (BU.format3
//                            "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
//                            (Range.string_of_range qq.p)
//                            (Print.pat_to_string qq)
//                            (Print.term_to_string exp))
//    in
//    aux p exp

 let rec decorated_pattern_as_term (pat:pat) : list<bv> * term =
    let mk f : term = mk f pat.p in

    let pat_as_arg (p, i) =
        let vars, te = decorated_pattern_as_term p in
        vars, (te, as_implicit i) in
    match pat.v with
    | Pat_constant c ->
        [], mk (Tm_constant c)

    | Pat_wild x
    | Pat_var x  ->
        [x], mk (Tm_name x)

    | Pat_cons(fv, pats) ->
        let vars, args = pats |> List.map pat_as_arg |> List.unzip in
        let vars = List.flatten vars in
        vars,  mk (Tm_app(Syntax.fv_to_tm fv, args))

    | Pat_dot_term(x, e) ->
        [], e


(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)

let comp_univ_opt c =
    match c.n with
    | Total (_, uopt)
    | GTotal (_, uopt) -> uopt
    | Comp c ->
      match c.comp_univs with
      | [] -> None
      | hd::_ -> Some hd

let lcomp_univ_opt lc = lc |> TcComm.lcomp_comp |> (fun (c, g) -> comp_univ_opt c, g)

let destruct_wp_comp c : (universe * typ * typ) = U.destruct_comp c

let mk_comp_l mname u_result result wp flags =
  mk_Comp ({ comp_univs=[u_result];
             effect_name=mname;
             result_typ=result;
             effect_args=[S.as_arg wp];
             flags=flags})

let mk_comp md = mk_comp_l md.mname

let effect_args_from_repr (repr:term) (is_layered:bool) (r:Range.range) : list<term> =
  let err () =
    raise_error (Errors.Fatal_UnexpectedEffect,
      BU.format2 "Could not get effect args from repr %s with is_layered %s"
        (Print.term_to_string repr) (string_of_bool is_layered)) r in
  let repr = SS.compress repr in
  if is_layered
  then match repr.n with
       | Tm_app (_, _::is) -> is |> List.map fst
       | _ -> err ()
  else match repr.n with
       | Tm_arrow (_, c) -> c |> U.comp_to_comp_typ |> (fun ct -> ct.effect_args |> List.map fst)
       | _ -> err ()


(*
 * Build the M.return comp for a wp effect
 *
 * Caller must ensure that ed is a wp-based effect
 *)
let mk_wp_return env (ed:S.eff_decl) (u_a:universe) (a:typ) (e:term) (r:Range.range)
: comp
= let c =
    if not <| Env.lid_exists env C.effect_GTot_lid //we're still in prims, not yet having fully defined the primitive effects
    then mk_Total a
    else if U.is_unit a
    then S.mk_Total' a (Some U_zero)
    else let wp =
           if env.lax
           && Options.ml_ish() //NS: Disabling this optimization temporarily
           then S.tun
           else let ret_wp = ed |> U.get_return_vc_combinator in
                mk_Tm_app
                  (inst_effect_fun_with [u_a] env ed ret_wp)
                  [S.as_arg a; S.as_arg e]
                  e.pos in
         mk_comp ed u_a a wp [RETURN]
  in
  if debug env <| Options.Other "Return"
  then BU.print3 "(%s) returning %s at comp type %s\n"
                    (Range.string_of_range e.pos)
                    (P.term_to_string e)
                    (N.comp_to_string env c);
  c

(*
 * Build the M.return comp for an indexed effect
 *
 * Caller must ensure that ed is an indexed effect
 *)
let mk_indexed_return env (ed:S.eff_decl) (u_a:universe) (a:typ) (e:term) (r:Range.range)
: comp * guard_t
= if Env.debug env <| Options.Other "LayeredEffects"
  then BU.print4 "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
         (Ident.string_of_lid ed.mname) (Print.univ_to_string u_a)
         (Print.term_to_string a) (Print.term_to_string e);

  let _, return_t = Env.inst_tscheme_with
    (ed |> U.get_return_vc_combinator)
    [u_a] in

  let return_t_shape_error (s:string) =
    (Errors.Fatal_UnexpectedEffect, BU.format3
      "%s.return %s does not have proper shape (reason:%s)"
      (Ident.string_of_lid ed.mname) (Print.term_to_string return_t) s) in

  let a_b, x_b, rest_bs, return_ct =
    match (SS.compress return_t).n with
    | Tm_arrow (bs, c) when List.length bs >= 2 ->
      let ((a_b::x_b::bs, c)) = SS.open_comp bs c in
      a_b, x_b, bs, U.comp_to_comp_typ c
    | _ -> raise_error (return_t_shape_error "Either not an arrow or not enough binders") r in

  let rest_bs_uvars, g_uvars = Env.uvars_for_binders
    env rest_bs [NT (a_b.binder_bv, a); NT (x_b.binder_bv, e)]
    (fun b -> BU.format3 "implicit var for binder %s of %s at %s"
             (Print.binder_to_string b)
             (BU.format1 "%s.return" (Ident.string_of_lid ed.mname))
             (Range.string_of_range r)) r in

  let subst = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::x_b::rest_bs) (a::e::rest_bs_uvars) in

  let is =
    effect_args_from_repr (SS.compress return_ct.result_typ) (U.is_layered ed) r
    |> List.map (SS.subst subst) in

  let c = mk_Comp ({
    comp_univs = [u_a];
    effect_name = ed.mname;
    result_typ = a;
    effect_args = is |> List.map S.as_arg;
    flags = []
  }) in

  if Env.debug env <| Options.Other "LayeredEffects"
  then BU.print1 "} c after return %s\n" (Print.comp_to_string c);

  c, g_uvars


(*
 * Wrapper over mk_wp_return and mk_indexed_return
 *)
let mk_return env (ed:S.eff_decl) (u_a:universe) (a:typ) (e:term) (r:Range.range)
: comp * guard_t
= if ed |> U.is_layered
  then mk_indexed_return env ed u_a a e r
  else mk_wp_return env ed u_a a e r, Env.trivial_guard


let lift_comp env (c:comp_typ) lift : comp * guard_t =
  ({ c with flags = [] }) |> S.mk_Comp |> lift.mlift_wp env

let join_effects env l1_in l2_in =
  let l1, l2 = Env.norm_eff_name env l1_in, Env.norm_eff_name env l2_in in
  match Env.join_opt env l1 l2 with
  | Some (m, _, _) -> m
  | None ->
    match Env.exists_polymonadic_bind env l1 l2 with
    | Some (m, _) -> m
    | None ->
      raise_error (Errors.Fatal_EffectsCannotBeComposed,
        (BU.format2 "Effects %s and %s cannot be composed"
          (Print.lid_to_string l1_in) (Print.lid_to_string l2_in))) env.range

let join_lcomp env c1 c2 =
  if TcComm.is_total_lcomp c1
  && TcComm.is_total_lcomp c2
  then C.effect_Tot_lid
  else join_effects env c1.eff_name c2.eff_name

(*
 * This functions returns the two lifted computations,
 *   and guards for each of them
 *
 * The separate guards are important when it is called from the pattern matching code (bind_cases)
 *   where the two guards are weakened using different branch conditions
 *)
let lift_comps_sep_guards env c1 c2 (b:option<bv>) (for_bind:bool)
: lident * comp * comp * guard_t * guard_t =
  let c1 = Env.unfold_effect_abbrev env c1 in
  let c2 = Env.unfold_effect_abbrev env c2 in
  match Env.join_opt env c1.effect_name c2.effect_name with
  | Some (m, lift1, lift2) ->
    let c1, g1 = lift_comp env c1 lift1 in
    let c2, g2 =
      if not for_bind then lift_comp env c2 lift2
      else
        let x_a =
          match b with
          | None -> S.null_binder (U.comp_result c1)
          | Some x -> S.mk_binder x in
        let env_x = Env.push_binders env [x_a] in
        let c2, g2 = lift_comp env_x c2 lift2 in
        c2, Env.close_guard env [x_a] g2 in
    m, c1, c2, g1, g2
  | None ->
    raise_error (Errors.Fatal_EffectsCannotBeComposed,
      (BU.format2 "Effects %s and %s cannot be composed"
        (Print.lid_to_string c1.effect_name) (Print.lid_to_string c2.effect_name))) env.range

let lift_comps env c1 c2 (b:option<bv>) (for_bind:bool)
: lident * comp * comp * guard_t
= let l, c1, c2, g1, g2 = lift_comps_sep_guards env c1 c2 b for_bind in
  l, c1, c2, Env.conj_guard g1 g2

let is_pure_effect env l =
  let l = norm_eff_name env l in
  lid_equals l C.effect_PURE_lid

let is_ghost_effect env l =
  let l = norm_eff_name env l in
  lid_equals l C.effect_GHOST_lid

let is_pure_or_ghost_effect env l =
  let l = norm_eff_name env l in
  lid_equals l C.effect_PURE_lid
  || lid_equals l C.effect_GHOST_lid

let lax_mk_tot_or_comp_l mname u_result result flags =
    if Ident.lid_equals mname C.effect_Tot_lid
    then S.mk_Total' result (Some u_result)
    else mk_comp_l mname u_result result S.tun flags

let is_function t = match (compress t).n with
    | Tm_arrow _ -> true
    | _ -> false

let label reason r f : term =
    mk (Tm_meta(f, Meta_labeled(reason, r, false))) f.pos

let label_opt env reason r f = match reason with
    | None -> f
    | Some reason ->
        if not <| Env.should_verify env
        then f
        else label (reason()) r f

let label_guard r reason (g:guard_t) = match g.guard_f with
    | Trivial -> g
    | NonTrivial f -> {g with guard_f=NonTrivial (label reason r f)}

let close_wp_comp env bvs (c:comp) =
    if U.is_ml_comp c then c
    else if env.lax
    && Options.ml_ish() //NS: disabling this optimization temporarily
    then c
    else begin
            let close_wp u_res md res_t bvs wp0 =
              let close = md |> U.get_wp_close_combinator |> must in
              List.fold_right (fun x wp ->
                  let bs = [mk_binder x] in
                  let us = u_res::[env.universe_of env x.sort] in
                  let wp = U.abs bs wp (Some (U.mk_residual_comp C.effect_Tot_lid None [TOTAL])) in
                  mk_Tm_app (inst_effect_fun_with us env md close) [S.as_arg res_t; S.as_arg x.sort; S.as_arg wp] wp0.pos)
              bvs wp0 in
            let c = Env.unfold_effect_abbrev env c in
            let u_res_t, res_t, wp = destruct_wp_comp c in
            let md = Env.get_effect_decl env c.effect_name in
            let wp = close_wp u_res_t md res_t bvs wp in
            mk_comp md u_res_t c.result_typ wp c.flags
        end

let close_wp_lcomp env bvs (lc:lcomp) =
  let bs = bvs |> List.map S.mk_binder in
  lc |>
  TcComm.apply_lcomp
    (close_wp_comp env bvs)
    (fun g -> g |> Env.close_guard env bs |> close_guard_implicits env false bs)

(*
 * Closing of layered computations happens via substitution
 *)
let close_layered_lcomp env bvs tms (lc:lcomp) =
  let bs = bvs |> List.map S.mk_binder in
  let substs = List.map2 (fun bv tm ->
    NT (bv, tm)
  ) bvs tms in
  lc |>
  TcComm.apply_lcomp
    (SS.subst_comp substs)
    (fun g -> g |> Env.close_guard env bs |> close_guard_implicits env false bs)

let should_not_inline_lc (lc:lcomp) =
    lc.cflags |> BU.for_some (function SHOULD_NOT_INLINE -> true | _ -> false)

(* should_return env (Some e) lc:
 * We will "return" e, adding an equality to the VC, if all of the following conditions hold
 * (a) e is a pure or ghost term
 * (b) Its return type, lc.res_typ, is not a sub-singleton (unit, squash, etc), if lc.res_typ is an arrow, then we check the comp type of the arrow
 *     An exception is made for reifiable effects -- they are useful even if they return unit
 * (c) Its head symbol is not marked irreducible (in this case inlining is not going to help, it is equivalent to having a bound variable)
 * (d) It's not a let rec, as determined by the absence of the SHOULD_NOT_INLINE flag---see issue #1362. Would be better to just encode inner let recs to the SMT solver properly
 *)
let should_return env eopt lc =
    //if lc.res_typ is not an arrow, arrow_formals_comp returns Tot lc.res_typ
    let lc_is_unit_or_effectful =
      lc.res_typ |> U.arrow_formals_comp |> snd |> (fun c ->
        (not (Env.is_reifiable_comp env c &&
              not (Env.is_layered_effect env (Env.norm_eff_name env lc.eff_name)))) &&
        (U.comp_result c |> U.is_unit || not (U.is_pure_or_ghost_comp c)))
    in
    match eopt with
    | None -> false //no term to return
    | Some e ->
      TcComm.is_pure_or_ghost_lcomp lc                &&  //condition (a), (see above)
      not lc_is_unit_or_effectful                &&  //condition (b)
      (let head, _ = U.head_and_args_full e in
       match (U.un_uinst head).n with
       | Tm_fvar fv ->  not (Env.is_irreducible env (lid_of_fv fv)) //condition (c)
       | _ -> true)                              &&
     not (should_not_inline_lc lc)                   //condition (d)

(*
 * Return a value in eff_lid
 *)
let return_value env eff_lid u_t_opt t v =
  let u =
    match u_t_opt with
    | None -> env.universe_of env t
    | Some u -> u in
  mk_return env (Env.get_effect_decl env eff_lid) u t v v.pos

(* private *)

(*
 * Bind for indexed effects
 *
 * This covers both the binds of an effect M,
 *   and polymonadic binds (M, N) |> P (this former is just (M, M) |> M)
 *
 * Let c1 = M c1_a (t1 ... tm)
 *     c2 = N c2_a (s1 ... sn) - where b is free in (s1 ... sn)
 *
 *     bind_t = ((u_a, u_b), a:Type -> b:Type -> <some binders> ->
 *                           f:M.repr a i_1 ... i_n ->
 *                           g:(x:a -> N.repr b j_1 ... j_n) ->
 *                           PURE (P.repr b k_1 ... k_p) wp)
 *
 * First we instantiate bind_t with [u_c1_a, u_c2_a]
 *
 * Then we substitute [a/c1_a; b/c2_a] in <some binders>
 *
 * Next we create ?u1 ... ?un for each of the binders in <some binders>
 *   while substituting [bi/?ui] in subsequent binders (so that their sorts are well-typed)
 *
 * Let substs = [a/c1_a; b/c2_a; bi/?ui]
 *
 * let i_i = i_i[substs]  //i_i are the indices of f in the bind_wp
 * let j_i = j_i[x/b; substs]  //j_i are the indices of g in the bind_wp and x/x is replacing x with the binder b
 * let k_i = k_i[substs]  //k_i are the indices of the return type in bind
 *
 * We now unify i_i with t_i (where t_i are the indices of c1)
 *        unify j_i with s_i (where s_i are the indices of c2,
 *                            these are done in an env with b, and the returned guard is closed over b)
 * and return k_i as the output indices
 *
 * In addition, we add ((wp[substs]) (fun _ -> True)) to the returned guard
 *)
let mk_indexed_bind env
  (m:lident) (n:lident) (p:lident) (bind_t:tscheme)
  (ct1:comp_typ) (b:option<bv>) (ct2:comp_typ)
  (flags:list<cflag>) (r1:Range.range) : comp * guard_t =

  let bind_name = BU.format3 "(%s, %s) |> %s"
    (m |> Ident.ident_of_lid |> string_of_id)
    (n |> Ident.ident_of_lid |> string_of_id)
    (p |> Ident.ident_of_lid |> string_of_id) in

  if (Env.is_erasable_effect env m &&
      not (Env.is_erasable_effect env p) &&
      not (N.non_info_norm env ct1.result_typ)) ||
     (Env.is_erasable_effect env n &&
      not (Env.is_erasable_effect env p) &&
      not (N.non_info_norm env ct2.result_typ))
  then raise_error (Errors.Fatal_UnexpectedEffect,
                    BU.format2 "Cannot apply bind %s since %s is not erasable and one of the computations is informative"
                      bind_name (string_of_lid p)) r1;

  if Env.debug env <| Options.Other "LayeredEffects" then
    BU.print2 "Binding c1:%s and c2:%s {\n"
      (Print.comp_to_string (S.mk_Comp ct1)) (Print.comp_to_string (S.mk_Comp ct2));

  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then BU.print2 "///////////////////////////////Bind at %s/////////////////////\n\
                  with bind_t = %s\n"
                 (Range.string_of_range (Env.get_range env))
                 (Print.tscheme_to_string bind_t);

  let m_ed, n_ed, p_ed = Env.get_effect_decl env m, Env.get_effect_decl env n, Env.get_effect_decl env p in

  let u1, t1, is1 = List.hd ct1.comp_univs, ct1.result_typ, List.map fst ct1.effect_args in
  let u2, t2, is2 = List.hd ct2.comp_univs, ct2.result_typ, List.map fst ct2.effect_args in

  let _, bind_t = Env.inst_tscheme_with bind_t [u1; u2] in

  let bind_t_shape_error (s:string) =
    (Errors.Fatal_UnexpectedEffect, BU.format3
       "bind %s (%s) does not have proper shape (reason:%s)"
       (Print.term_to_string bind_t) bind_name s) in

  let a_b, b_b, rest_bs, f_b, g_b, bind_c =
    match (SS.compress bind_t).n with
    | Tm_arrow (bs, c) when List.length bs >= 4 ->
      let ((a_b::b_b::bs), c) = SS.open_comp bs c in
      let rest_bs, f_b, g_b =
        List.splitAt (List.length bs - 2) bs |> (fun (l1, l2) -> l1, List.hd l2, List.hd (List.tl l2)) in
      a_b, b_b, rest_bs, f_b, g_b, c
    | _ -> raise_error (bind_t_shape_error "Either not an arrow or not enough binders") r1 in

  //create uvars for rest_bs, with proper substitutions of a_b, b_b, and b_i with t1, t2, and ?ui
  let rest_bs_uvars, g_uvars = Env.uvars_for_binders
    env rest_bs [NT (a_b.binder_bv, t1); NT (b_b.binder_bv, t2)]
    (fun b -> BU.format3
      "implicit var for binder %s of %s at %s"
      (Print.binder_to_string b) bind_name (Range.string_of_range r1)) r1 in

  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then rest_bs_uvars |>
       List.iter (fun t ->
         match (SS.compress t).n with
         | Tm_uvar (u, _ ) ->
           BU.print2 "Generated uvar %s with attribute %s\n"
             (Print.term_to_string t)
             (match u.ctx_uvar_meta with
              | Some (Ctx_uvar_meta_attr a) -> Print.term_to_string a
              | _ -> "<no attr>")
         | _ -> failwith ("Impossible, expected a uvar, got : " ^ Print.term_to_string t));

  let subst = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::b_b::rest_bs) (t1::t2::rest_bs_uvars) in

  let f_guard =  //unify c1's indices with f's indices in the bind_wp
    let f_sort_is = effect_args_from_repr
      (SS.compress f_b.binder_bv.sort)
      (U.is_layered m_ed) r1 |> List.map (SS.subst subst) in
    List.fold_left2
      (fun g i1 f_i1 ->
        if Env.debug env <| Options.Other "ResolveImplicitsHook"
        then BU.print2 "Generating constraint %s = %s\n"
                                   (Print.term_to_string i1)
                                   (Print.term_to_string f_i1);
        Env.conj_guard g (Rel.layered_effect_teq env i1 f_i1 (Some bind_name)))
      Env.trivial_guard is1 f_sort_is
  in

  let g_guard =  //unify c2's indices with g's indices in the bind_wp
    let x_a =
      match b with
      | None -> S.null_binder ct1.result_typ
      | Some x -> S.mk_binder x in

    let g_sort_is : list<term> =
      match (SS.compress g_b.binder_bv.sort).n with
      | Tm_arrow (bs, c) ->
        let bs, c = SS.open_comp bs c in
        let bs_subst = NT ((List.hd bs).binder_bv, x_a.binder_bv |> S.bv_to_name) in
        let c = SS.subst_comp [bs_subst] c in
        effect_args_from_repr (SS.compress (U.comp_result c)) (U.is_layered n_ed) r1
        |> List.map (SS.subst subst)
      | _ -> failwith "impossible: mk_indexed_bind"
    in

    let env_g = Env.push_binders env [x_a] in
    List.fold_left2
      (fun g i1 g_i1 ->
        if Env.debug env <| Options.Other "ResolveImplicitsHook"
        then BU.print2 "Generating constraint %s = %s\n"
                                   (Print.term_to_string i1)
                                   (Print.term_to_string g_i1);
         Env.conj_guard g (Rel.layered_effect_teq env_g i1 g_i1 (Some bind_name)))
      Env.trivial_guard is2 g_sort_is
    |> Env.close_guard env [x_a]
  in

  let bind_ct = bind_c |> SS.subst_comp subst |> U.comp_to_comp_typ in

  //compute the formula `bind_c.wp (fun _ -> True)` and add it to the final guard
  let fml =
    let u, wp = List.hd bind_ct.comp_univs, fst (List.hd bind_ct.effect_args) in
    Env.pure_precondition_for_trivial_post env u bind_ct.result_typ wp Range.dummyRange in

  let is : list<term> =  //indices of the resultant computation
    effect_args_from_repr (SS.compress bind_ct.result_typ) (U.is_layered p_ed) r1 in

  let c = mk_Comp ({
    comp_univs = ct2.comp_univs;
    effect_name = p_ed.mname;
    result_typ = t2;
    effect_args = List.map S.as_arg is;
    flags = flags
  }) in

  if Env.debug env <| Options.Other "LayeredEffects"
  then
    BU.print1 "} c after bind: %s\n" (Print.comp_to_string c);

  let guard =
    Env.conj_guards [
      g_uvars;
      f_guard;
      g_guard;
      Env.guard_of_guard_formula (TcComm.NonTrivial fml)]
  in

  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then BU.print2 "///////////////////////////////EndBind at %s/////////////////////\n\
                 guard = %s\n"
                 (Range.string_of_range (Env.get_range env))
                 (guard_to_string env guard);

  c, guard

let mk_wp_bind env (m:lident) (ct1:comp_typ) (b:option<bv>) (ct2:comp_typ) (flags:list<cflag>) (r1:Range.range)
  : comp =

  let (md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2) =
    let md = Env.get_effect_decl env m in
    let a, kwp = Env.wp_signature env m in
    (md, a, kwp), destruct_wp_comp ct1, destruct_wp_comp ct2 in

  let bs =
    match b with
    | None -> [null_binder t1]
    | Some x -> [S.mk_binder x]
  in
  let mk_lam wp =
    //we know it's total; indicate for the normalizer reduce it by adding  the TOTAL flag
    U.abs bs wp (Some (U.mk_residual_comp C.effect_Tot_lid None [TOTAL]))
  in
  let r1 = S.mk (S.Tm_constant (FStar.Const.Const_range r1)) r1 in
  let wp_args = [
    S.as_arg r1;
    S.as_arg t1;
    S.as_arg t2;
    S.as_arg wp1;
    S.as_arg (mk_lam wp2)]
  in
  let bind_wp = md |> U.get_bind_vc_combinator in
  let wp = mk_Tm_app (inst_effect_fun_with [u_t1;u_t2] env md bind_wp) wp_args t2.pos in
  mk_comp md u_t2 t2 wp flags

let mk_bind env (c1:comp) (b:option<bv>) (c2:comp) (flags:list<cflag>) (r1:Range.range) : comp * guard_t =
  let ct1, ct2 = Env.unfold_effect_abbrev env c1, Env.unfold_effect_abbrev env c2 in

  match Env.exists_polymonadic_bind env ct1.effect_name ct2.effect_name with
  | Some (p, f_bind) -> f_bind env ct1 b ct2 flags r1
  | None ->
    (*
     * AR: g_lift here consists of the guard of lifting c1 and c2
     *     the guard of c2 could contain the bound variable b
     *       and when returning this gurd, we must close it
     *
     *     however, if you see lift_comps_sep_guards, it is already doing the closing
     *       so it's fine to return g_return as is
     *)
    let m, c1, c2, g_lift = lift_comps env c1 c2 b true in
    let ct1, ct2 = U.comp_to_comp_typ c1, U.comp_to_comp_typ c2 in

    let c, g_bind =
      if Env.is_layered_effect env m
      then
        let bind_t = m |> Env.get_effect_decl env |> U.get_bind_vc_combinator in
        mk_indexed_bind env m m m bind_t ct1 b ct2 flags r1
      else mk_wp_bind env m ct1 b ct2 flags r1, Env.trivial_guard in
    c, Env.conj_guard g_lift g_bind

let bind_pure_wp_with env (wp1:typ) (c:comp) (flags:list<cflag>) : comp * guard_t =
  let r = Env.get_range env in

  let pure_c = S.mk_Comp ({
    comp_univs = [S.U_zero];
    effect_name = C.effect_PURE_lid;
    result_typ = S.t_unit;
    effect_args = [wp1 |> S.as_arg];
    flags = []
  }) in

  mk_bind env pure_c None c flags r

let weaken_flags flags =
    if flags |> BU.for_some (function SHOULD_NOT_INLINE -> true | _ -> false)
    then [SHOULD_NOT_INLINE]
    else flags |> List.collect (function
         | TOTAL -> [TRIVIAL_POSTCONDITION]
         | RETURN -> [PARTIAL_RETURN; TRIVIAL_POSTCONDITION]
         | f -> [f])

let weaken_comp env (c:comp) (formula:term) : comp * guard_t =
  if U.is_ml_comp c
  then c, Env.trivial_guard
  else let ct = Env.unfold_effect_abbrev env c in

       (*
        * The following code does:
        *   M.bind_wp (lift_pure_M (Prims.pure_assume_wp f)) (fun _ -> wp)
        *)

       (*
        * lookup the pure_assume_wp from prims
        * its type is p:Type -> pure_wp unit
        *  and it is not universe polymorphic
        *)
       let pure_assume_wp = S.fv_to_tm (S.lid_as_fv C.pure_assume_wp_lid (Delta_constant_at_level 1) None) in

       (* apply it to f, after decorating f with the reason *)
       let pure_assume_wp = mk_Tm_app
         pure_assume_wp
         [ S.as_arg <| formula ]
         (Env.get_range env)
       in

       bind_pure_wp_with env pure_assume_wp c (weaken_flags ct.flags)

let weaken_precondition env lc (f:guard_formula) : lcomp =
  let weaken () =
      let c, g_c = TcComm.lcomp_comp lc in
      if env.lax
      && Options.ml_ish() //NS: Disabling this optimization temporarily
      then c, g_c
      else match f with
           | Trivial -> c, g_c
           | NonTrivial f ->
             let c, g_w = weaken_comp env c f in
             c, Env.conj_guard g_c g_w
  in
  TcComm.mk_lcomp lc.eff_name lc.res_typ (weaken_flags lc.cflags) weaken


let strengthen_comp env (reason:option<(unit -> string)>) (c:comp) (f:formula) flags : comp * guard_t =
    if env.lax
    then c, Env.trivial_guard
    else let r = Env.get_range env in
         (*
          * The following code does:
          *   M.bind_wp (lift_pure_M (Prims.pure_assert_wp f)) (fun _ -> wp)
          *)

         (*
          * lookup the pure_assert_wp from prims
          * its type is p:Type -> pure_wp unit
          *  and it is not universe polymorphic
          *)
         let pure_assert_wp = S.fv_to_tm (S.lid_as_fv C.pure_assert_wp_lid (Delta_constant_at_level 1) None) in

         (* apply it to f, after decorating f with the reason *)
         let pure_assert_wp = mk_Tm_app
           pure_assert_wp
           [ S.as_arg <| label_opt env reason r f ]
           r
         in

         bind_pure_wp_with env pure_assert_wp c flags

let strengthen_precondition
            (reason:option<(unit -> string)>)
            env
            (e_for_debugging_only:term)
            (lc:lcomp)
            (g0:guard_t)
    : lcomp * guard_t =
    if Env.is_trivial_guard_formula g0
    then lc, g0
    else let flags =
            let maybe_trivial_post, flags =
              if TcComm.is_tot_or_gtot_lcomp lc then true, [TRIVIAL_POSTCONDITION] else false, []
            in
            flags @ (
            lc.cflags
            |> List.collect (function
                 | RETURN
                 | PARTIAL_RETURN -> [PARTIAL_RETURN]
                 | SOMETRIVIAL
                 | TRIVIAL_POSTCONDITION
                    when not maybe_trivial_post ->
                   [TRIVIAL_POSTCONDITION]
                 | SHOULD_NOT_INLINE -> [SHOULD_NOT_INLINE]
                 | _ -> []))
         in
         let strengthen () =
            let c, g_c = TcComm.lcomp_comp lc in
            if env.lax
            then c, g_c
            else let g0 = Rel.simplify_guard env g0 in
                 match guard_form g0 with
                 | Trivial -> c, g_c
                 | NonTrivial f ->
                   if Env.debug env <| Options.Extreme
                   then BU.print2 "-------------Strengthening pre-condition of term %s with guard %s\n"
                     (N.term_to_string env e_for_debugging_only)
                     (N.term_to_string env f);
                   let c, g_s = strengthen_comp env reason c f flags in
                   c, Env.conj_guard g_c g_s
         in
       TcComm.mk_lcomp (norm_eff_name env lc.eff_name)
                       lc.res_typ
                       flags
                       strengthen,
       {g0 with guard_f=Trivial}


let lcomp_has_trivial_postcondition lc =
    TcComm.is_tot_or_gtot_lcomp lc
    || BU.for_some (function SOMETRIVIAL | TRIVIAL_POSTCONDITION -> true | _ -> false)
                   lc.cflags

let maybe_add_with_type env uopt lc e =
    if TcComm.is_lcomp_partial_return lc
    || env.lax
    then e
    else if lcomp_has_trivial_postcondition lc
         && Option.isSome (Env.try_lookup_lid env C.with_type_lid) //we have with_type in the environment
    then let u = match uopt with
                 | Some u -> u
                 | None -> env.universe_of env lc.res_typ
         in
         U.mk_with_type u lc.res_typ e
    else e


(*
 * This is used in bind, when c1 is a Tot (x:unit{phi})
 * In such cases, e1 is inlined in c2, but we still want to capture inhabitance of phi
 *
 * For wp-effects, we do forall (x:unit{phi}). c2
 * For layered effects, we do: weaken_comp (phi[x/()]) c2
 *
 * We should make wp-effects also same as the layered effects
 *)
let maybe_capture_unit_refinement (env:env) (t:term) (x:bv) (c:comp) : comp * guard_t =
  let t = N.normalize_refinement N.whnf_steps env t in
  match t.n with
  | Tm_refine (b, phi) ->
    let is_unit =
      match b.sort.n with
      | Tm_fvar fv -> S.fv_eq_lid fv C.unit_lid
      | _ -> false in
    if is_unit then
      if c |> U.comp_effect_name |> Env.norm_eff_name env |> Env.is_layered_effect env
      then
        let b, phi = SS.open_term_bv b phi in
        let phi = SS.subst [NT (b, S.unit_const)] phi in
        weaken_comp env c phi
      else close_wp_comp env [x] c, Env.trivial_guard
    else c, Env.trivial_guard
  | _ -> c, Env.trivial_guard

let bind r1 env e1opt (lc1:lcomp) ((b, lc2):lcomp_with_binder) : lcomp =
  let debug f =
      if debug env Options.Extreme
      || debug env <| Options.Other "bind"
      then f ()
  in
  let lc1, lc2 = N.ghost_to_pure_lcomp2 env (lc1, lc2) in  //downgrade from ghost to pure, if possible
  let joined_eff = join_lcomp env lc1 lc2 in
  let bind_flags =
      if should_not_inline_lc lc1
      || should_not_inline_lc lc2
      then [SHOULD_NOT_INLINE]
      else let flags =
              if TcComm.is_total_lcomp lc1
              then if TcComm.is_total_lcomp lc2
                   then [TOTAL]
                   else if TcComm.is_tot_or_gtot_lcomp lc2
                   then [SOMETRIVIAL]
                   else []
              else if TcComm.is_tot_or_gtot_lcomp lc1
                   && TcComm.is_tot_or_gtot_lcomp lc2
              then [SOMETRIVIAL]
              else []
          in
          if lcomp_has_trivial_postcondition lc2
          then TRIVIAL_POSTCONDITION::flags
          else flags
  in
  let bind_it () =
      if env.lax
      && Options.ml_ish() //NS: disabling this optimization temporarily
      then
         let u_t = env.universe_of env lc2.res_typ in
         lax_mk_tot_or_comp_l joined_eff u_t lc2.res_typ [], Env.trivial_guard  //AR: TODO: FIXME: fix for layered effects
      else begin
          let c1, g_c1 = TcComm.lcomp_comp lc1 in
          let c2, g_c2 = TcComm.lcomp_comp lc2 in

          (*
           * AR: we need to be careful about handling g_c2 since it may have x free
           *     whereever we return/add this, we have to either close it or substitute it
           *)

          let trivial_guard = Env.conj_guard g_c1 (
            match b with
            | Some x ->
              let b = S.mk_binder x in
              if S.is_null_binder b
              then g_c2
              else Env.close_guard env [b] g_c2
            | None -> g_c2) in

          debug (fun () ->
            BU.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
            (Print.comp_to_string c1)
            (match b with
                | None -> "none"
                | Some x -> Print.bv_to_string x)
            (Print.comp_to_string c2));
          let aux () =
            if U.is_trivial_wp c1
            then match b with
                 | None ->
                   Inl (c2, "trivial no binder")
                 | Some _ ->
                   if U.is_ml_comp c2 //|| not (U.is_free [Inr x] (U.freevars_comp c2))
                   then Inl (c2, "trivial ml")
                   else Inr "c1 trivial; but c2 is not ML"
            else if U.is_ml_comp c1 && U.is_ml_comp c2
            then Inl (c2, "both ml")
            else Inr "c1 not trivial, and both are not ML"
          in
          let try_simplify () : either<(comp * guard_t * string), string> =
            let aux_with_trivial_guard () =
              match aux () with
              | Inl (c, reason) -> Inl (c, trivial_guard, reason)
              | Inr reason -> Inr reason in
            if Env.too_early_in_prims env  //if we're very early in prims
            then //if U.is_tot_or_gtot_comp c1
                 //&& U.is_tot_or_gtot_comp c2
                 Inl (c2, trivial_guard, "Early in prims; we don't have bind yet")
                 // else raise_error (Errors.Fatal_NonTrivialPreConditionInPrims,
                 //                   "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                 //                   (Env.get_range env)
            else if U.is_total_comp c1
            then (*
                  * Helper routine to close the compuation c with c1's return type
                  * When c1's return type is of the form _:t{phi}, is is useful to know
                  *   that t{phi} is inhabited, even if c1 is inlined etc.
                  *)
                 let close_with_type_of_x (x:bv) (c:comp) =
                   let x = { x with sort = U.comp_result c1 } in
                   maybe_capture_unit_refinement env x.sort x c in
                 match e1opt, b with
                 | Some e, Some x ->
                   let c2, g_close = c2 |> SS.subst_comp [NT (x, e)] |> close_with_type_of_x x in
                   Inl (c2, Env.conj_guards [
                     g_c1;
                     Env.map_guard g_c2 (SS.subst [NT (x, e)]);
                     g_close ], "c1 Tot")
                 | _, Some x ->
                   let c2, g_close = c2 |> close_with_type_of_x x in
                   Inl (c2, Env.conj_guards [
                     g_c1;
                     Env.close_guard env [S.mk_binder x] g_c2;
                     g_close ], "c1 Tot only close")
                 | _, _ -> aux_with_trivial_guard ()
            else if U.is_tot_or_gtot_comp c1
                 && U.is_tot_or_gtot_comp c2
            then Inl (S.mk_GTotal (U.comp_result c2), trivial_guard, "both GTot")
            else aux_with_trivial_guard ()
          in
          match try_simplify () with
          | Inl (c, g, reason) ->
            debug (fun () ->
                BU.print2 "(2) bind: Simplified (because %s) to\n\t%s\n"
                            reason
                            (Print.comp_to_string c));
            c, g
          | Inr reason ->
            debug (fun () ->
                BU.print1 "(2) bind: Not simplified because %s\n" reason);

            let mk_bind c1 b c2 g =  (* AR: end code for inlining pure and ghost terms *)
              let c, g_bind = mk_bind env c1 b c2 bind_flags r1 in
              c, Env.conj_guard g g_bind in

            let mk_seq c1 b c2 =
                //c1 is PURE or GHOST
                let c1 = Env.unfold_effect_abbrev env c1 in
                let c2 = Env.unfold_effect_abbrev env c2 in
                let m, _, lift2 = Env.join env c1.effect_name c2.effect_name in
                let c2, g2 = lift_comp env c2 lift2 in
                let u1, t1, wp1 = destruct_wp_comp c1 in
                let md_pure_or_ghost = Env.get_effect_decl env c1.effect_name in
                let trivial = md_pure_or_ghost |> U.get_wp_trivial_combinator |> must in
                let vc1 = mk_Tm_app (inst_effect_fun_with [u1] env md_pure_or_ghost trivial)
                                    [S.as_arg t1; S.as_arg wp1]
                                    r1
                in
                let c, g_s = strengthen_comp env None c2 vc1 bind_flags in
                c, Env.conj_guards [g_c1; g_c2; g2; g_s]
            in
            (* AR: we have let the previously applied bind optimizations take effect, below is the code to do more inlining for pure and ghost terms *)
            let u_res_t1, res_t1 =
              let t = U.comp_result c1 in
              match comp_univ_opt c1 with
              | None -> env.universe_of env t, t
              | Some u -> u, t in
            //c1 and c2 are bound to the input comps
            if Option.isSome b
            && should_return env e1opt lc1
            then let e1 = Option.get e1opt in
                 let x = Option.get b in
                 //we will inline e1 in the WP of c2
                 //Aiming to build a VC of the form
                 //
                 //     M.bind (lift_(Pure/Ghost)_M wp1)
                 //            (x == e1 ==> lift_M2_M (wp2[e1/x]))
                 //
                 //
                 //The additional equality hypothesis may seem
                 //redundant, but c1's post-condition or type may carry
                 //some meaningful information Then, it's important to
                 //weaken wp2 to with the equality, So that whatever
                 //property is proven about the result of wp1 (i.e., x)
                 //is still available in the proof of wp2 However, we
                 //apply two optimizations:

                 //   a. if c1 is already a return or a partial return,
                 //      then it already provides this equality, so no
                 //      need to add it again and instead generate
                 //
                 //         M.bind (lift_(Pure/Ghost)_M wp1)
                 //                (lift_M2_M (wp2[e1/x]))

                 //   b. if c1 is marked with TRIVIAL_POSTCONDITION,
                 //      then the post-condition does not carry any
                 //      useful information. We have two sub-cases:

                 //      (i) In case the user option
                 //          `vcgen.optimize_bind_as_seq = without_type`
                 //          rather than generating
                 //          M.bind wp1 (\x. wp2), we generate:
                 //
                 //           M.assert_wp (wp1 (\x. True))
                 //                       (lift_M2_M  (wp2[e1/x]))
                 //
                 //      Note, although the post-condition of c1 does
                 //      not carry useful information, its result type
                 //      might. When applying the optimization above,
                 //      the SMT solver is faced with reconstructing
                 //      the type of e1. Usually, it can do this, but
                 //      in some cases (e.g., if the result type has a
                 //      complex refinement), then this optimization
                 //      can actually cause a VC to fail. So, we add an
                 //      option to recover from this, at the cost of
                 //      some VC bloat:
                 //
                 //      (ii). In case the user option
                 //            `vcgen.optimize_bind_as_seq = with_type`,
                 //            we build
                 //
                 //             M.assert_wp (wp1 (\x. True))
                 //                        (lift_M2_M (wp2[with_type e1 t1/x]))
                 //
                 //      Where `with_type e1 t1`, decorates `e1` with
                 //      its type before substituting. This allows the
                 //      SMT solver to recover the type of `e1` (using
                 //      a primitive axiom about with_type), without
                 //      polluting the VC with an additional equality.
                 //      Note, specific occurrences of `with_type e t`
                 //      can be normalized away to `e` if requested
                 //      explicitly by a user tactic.
                 //
                 //   c. If neither of the optimizations above apply,
                 //   then we generate the WP mentioned at the top,
                 //   i.e.
                 //
                 //      M.bind (lift_(Pure/Ghost)_M wp1)
                 //             (x == e1 ==> lift_M2_M (wp2[e1/x]))

                 if U.is_partial_return c1
                 then // case (a)
                      let _ = debug (fun () ->
                        BU.print2 "(3) bind (case a): Substituting %s for %s" (N.term_to_string env e1) (Print.bv_to_string x)) in
                      let c2 = SS.subst_comp [NT(x,e1)] c2 in
                      let g = Env.conj_guard g_c1 (Env.map_guard g_c2 (SS.subst [NT (x, e1)])) in
                      mk_bind c1 b c2 g
                 else if Options.vcgen_optimize_bind_as_seq()
                      && lcomp_has_trivial_postcondition lc1
                      && Option.isSome (Env.try_lookup_lid env C.with_type_lid) //and we have with_type in the environment
                 then // case (b)
                      let e1' =
                        if Options.vcgen_decorate_with_type()
                        then U.mk_with_type u_res_t1 res_t1 e1 // case (b) (ii)
                        else e1                                // case (b) (i)
                      in
                      let _ = debug (fun () ->
                        BU.print2 "(3) bind (case b): Substituting %s for %s" (N.term_to_string env e1') (Print.bv_to_string x)) in
                      let c2 = SS.subst_comp [NT(x, e1')] c2 in
                      mk_seq c1 b c2
                 else // case (c)
                      let _ = debug (fun () ->
                        BU.print2 "(3) bind (case c): Adding equality %s = %s" (N.term_to_string env e1) (Print.bv_to_string x)) in
                      let c2 = SS.subst_comp [NT(x,e1)] c2 in
                      let x_eq_e = U.mk_eq2 u_res_t1 res_t1 e1 (bv_to_name x) in
                      let c2, g_w = weaken_comp (Env.push_binders env [S.mk_binder x]) c2 x_eq_e in
                      let g = Env.conj_guards [
                        g_c1;
                        Env.close_guard env [S.mk_binder x] g_w;
                        Env.close_guard env [S.mk_binder x] (TcComm.weaken_guard_formula g_c2 x_eq_e) ] in
                      mk_bind c1 b c2 g
                //Caution: here we keep the flags for c2 as is, these flags will be overwritten later when we do md.bind below
                //If we decide to return c2 as is (after inlining), we should reset these flags else bad things will happen
            else mk_bind c1 b c2 trivial_guard
      end
  in TcComm.mk_lcomp joined_eff
                     lc2.res_typ
      (* TODO : these cflags might be inconsistent with the one returned by bind_it  !!! *)
                     bind_flags
                     bind_it

let weaken_guard g1 g2 = match g1, g2 with
    | NonTrivial f1, NonTrivial f2 ->
      let g = (U.mk_imp f1 f2) in
      NonTrivial g
    | _ -> g2


(*
 * e has type lc, and lc is either pure or ghost
 * This function inserts a return (x==e) in lc
 *
 * Optionally, callers can provide an effect M that they would like to return
 * into
 *
 * If lc is PURE, the return happens in M
 * else if it is GHOST, the return happens in PURE
 *
 * If caller does not provide the m effect, return happens in PURE
 *
 * This forces the lcomp thunk and recreates it to keep the callers same
 *)
let assume_result_eq_pure_term_in_m env (m_opt:option<lident>) (e:term) (lc:lcomp) : lcomp =
  (*
   * AR: m is the effect that we are going to do return in
   *)
  let m =
    if m_opt |> is_none || is_ghost_effect env lc.eff_name
    then C.effect_PURE_lid
    else m_opt |> must in

  let flags =
    if TcComm.is_total_lcomp lc then RETURN::lc.cflags else PARTIAL_RETURN::lc.cflags in

  let refine () : comp * guard_t =
      let c, g_c = TcComm.lcomp_comp lc in
      let u_t =
          match comp_univ_opt c with
          | Some u_t -> u_t
          | None -> env.universe_of env (U.comp_result c)
      in
      if U.is_tot_or_gtot_comp c
      then //AR: insert an M.return
           let retc, g_retc = return_value env m (Some u_t) (U.comp_result c) e in
           let g_c = Env.conj_guard g_c g_retc in
           if not (U.is_pure_comp c) //it started in GTot, so it should end up in Ghost
           then let retc = U.comp_to_comp_typ retc in
                let retc = {retc with effect_name=C.effect_GHOST_lid; flags=flags} in
                S.mk_Comp retc, g_c
           else U.comp_set_flags retc flags, g_c
       else //AR: augment c's post-condition with a M.return
            let c = Env.unfold_effect_abbrev env c in
            let t = c.result_typ in
            let c = mk_Comp c in
            let x = S.new_bv (Some t.pos) t in
            let xexp = S.bv_to_name x in
            let env_x = Env.push_bv env x in
            let ret, g_ret = return_value env_x m (Some u_t) t xexp in
            let ret = TcComm.lcomp_of_comp <| U.comp_set_flags ret [PARTIAL_RETURN] in
            let eq = U.mk_eq2 u_t t xexp e in
            let eq_ret = weaken_precondition env_x ret (NonTrivial eq) in
            let bind_c, g_bind = TcComm.lcomp_comp (bind e.pos env None (TcComm.lcomp_of_comp c) (Some x, eq_ret)) in
            U.comp_set_flags bind_c flags, Env.conj_guards [g_c; g_ret; g_bind]
  in

  if should_not_inline_lc lc
  then raise_error (Errors.Fatal_UnexpectedTerm,
         BU.format1 "assume_result_eq_pure_term cannot inline an non-inlineable lc : %s"
           (Print.term_to_string e)) e.pos
  else let c, g = refine () in
       TcComm.lcomp_of_comp_guard c g

let maybe_assume_result_eq_pure_term_in_m env (m_opt:option<lident>) (e:term) (lc:lcomp) : lcomp =
  let should_return =
      not (env.lax)
   && not (Env.too_early_in_prims env) //we're not too early in prims
   && should_return env (Some e) lc
   && not (TcComm.is_lcomp_partial_return lc)
  in
  if not should_return then lc
  else assume_result_eq_pure_term_in_m env m_opt e lc

let maybe_assume_result_eq_pure_term env e lc =
  maybe_assume_result_eq_pure_term_in_m env None e lc

let maybe_return_e2_and_bind
        (r:Range.range)
        (env:env)
        (e1opt:option<term>)
        (lc1:lcomp)
        (e2:term)
        (x, lc2)
   : lcomp =
   let env_x =
     match x with
     | None -> env
     | Some x -> Env.push_bv env x in

   let lc1, lc2 = N.ghost_to_pure_lcomp2 env (lc1, lc2) in

   //AR: use c1's effect to return c2 into
   let lc2 =
        let eff1 = Env.norm_eff_name env lc1.eff_name in
        let eff2 = Env.norm_eff_name env lc2.eff_name in

        (*
         * AR: If eff1 and eff2 cannot be composed, and eff2 is PURE,
         *     we must return eff2 into eff1,
         *)
        if lid_equals eff2 C.effect_PURE_lid &&
           Env.join_opt env eff1 eff2 |> is_none &&
           Env.exists_polymonadic_bind env eff1 eff2 |> is_none
        then assume_result_eq_pure_term_in_m env_x (eff1 |> Some) e2 lc2
        else if (not (is_pure_or_ghost_effect env eff1)
             ||  should_not_inline_lc lc1)
             && is_pure_or_ghost_effect env eff2
        then maybe_assume_result_eq_pure_term_in_m env_x (eff1 |> Some) e2 lc2
        else lc2 in //the resulting computation is still pure/ghost and inlineable; no need to insert a return
   bind r env e1opt lc1 (x, lc2)

let fvar_const env lid =  S.fvar (Ident.set_lid_range lid (Env.get_range env)) delta_constant None


(*
 * Conjunction combinator for layered effects
 *
 * let ct1 = M a (t1...tn)
 *     ct2 = M a (s1...sn)
 *
 *     M.conjunction = fun (a_b:Type) ..<some binders>.. (f:repr a i1...in) (g:repr a j1...jn) (p_b:Type0) -> repr a k1...n
 *
 * First we instantiate M.conjunction with [u_a]
 *
 * Then we create uvars ?u1..?un for each of the binders in <some binder>
 *   while substituting [a_b/a] and [bi/?ui] in subsequent binders (handled by Env.uvars_for_binders)
 *
 * let substs = [a_b/a; bi/?ui; p_b/p]
 *
 * let i_i = i_i[substs]
 * let j_i = i_i[substs]
 * let k_i = i_i[substs]
 *
 * Unify i_i with t_i (where t_i are the indices of ct1)
 * Unify j_i with s_i (where t_i are the indices of ct2)
 *
 * And return k_i
 *)
let mk_layered_conjunction env (ed:S.eff_decl) (u_a:universe) (a:term) (p:typ) (ct1:comp_typ) (ct2:comp_typ) (r:Range.range)
: comp * guard_t =

  let conjunction_name = BU.format1 "%s.conjunction" (string_of_lid ed.mname) in

  let _, conjunction =
    Env.inst_tscheme_with (ed |> U.get_layered_if_then_else_combinator |> must) [u_a] in
  let is1, is2 = List.map fst ct1.effect_args, List.map fst ct2.effect_args in

  let conjunction_t_error (s:string) =
    (Errors.Fatal_UnexpectedEffect, BU.format3
      "conjunction %s (%s) does not have proper shape (reason:%s)"
      (Print.term_to_string conjunction) conjunction_name s) in

  let a_b, rest_bs, f_b, g_b, p_b, body =
    match (SS.compress conjunction).n with
    | Tm_abs (bs, body, _) when List.length bs >= 4 ->
      let (a_b::bs), body = SS.open_term bs body in
      let rest_bs, (f_b::g_b::p_b::[]) = List.splitAt (List.length bs - 3) bs in
      a_b, rest_bs, f_b, g_b, p_b, body |> U.unascribe
    | _ -> raise_error (conjunction_t_error "Either not an abstraction or not enough binders") r in

  let rest_bs_uvars, g_uvars = Env.uvars_for_binders
    env rest_bs [NT (a_b.binder_bv, a)]
    (fun b -> BU.format3
      "implicit var for binder %s of %s:conjunction at %s"
      (Print.binder_to_string b) (Ident.string_of_lid ed.mname)
      (r |> Range.string_of_range)) r in

  let substs = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::(rest_bs@[p_b])) (a::(rest_bs_uvars@[p])) in

  let f_guard =
    let f_sort_is =
      match (SS.compress f_b.binder_bv.sort).n with
      | Tm_app (_, _::is) ->
        is |> List.map fst |> List.map (SS.subst substs)
      | _ -> raise_error (conjunction_t_error "f's type is not a repr type") r in
    List.fold_left2
      (fun g i1 f_i -> Env.conj_guard g (Rel.layered_effect_teq env i1 f_i (Some conjunction_name)))
      Env.trivial_guard is1 f_sort_is in

  let g_guard =
    let g_sort_is =
      match (SS.compress g_b.binder_bv.sort).n with
      | Tm_app (_, _::is) ->
        is |> List.map fst |> List.map (SS.subst substs)
      | _ -> raise_error (conjunction_t_error "g's type is not a repr type") r in
    List.fold_left2
      (fun g i2 g_i -> Env.conj_guard g (Rel.layered_effect_teq env i2 g_i (Some conjunction_name)))
      Env.trivial_guard is2 g_sort_is in

  let body = SS.subst substs body in

  let is =
    match (SS.compress body).n with
    | Tm_app (_, a::args) -> List.map fst args
    | _ -> raise_error (conjunction_t_error "body is not a repr type") r in

  mk_Comp ({
    comp_univs = [u_a];
    effect_name = ed.mname;
    result_typ = a;
    effect_args = is |> List.map S.as_arg;
    flags = []
  }), Env.conj_guard (Env.conj_guard g_uvars f_guard) g_guard

(*
 * For non-layered effects, just apply the if_then_else combinator
 *)
let mk_non_layered_conjunction env (ed:S.eff_decl) (u_a:universe) (a:term) (p:typ) (ct1:comp_typ) (ct2:comp_typ) (_:Range.range)
: comp * guard_t =
  //p is a boolean guard, so b2t it
  let p = U.b2t p in
  let if_then_else = ed |> U.get_wp_if_then_else_combinator |> must in
  let _, _, wp_t = destruct_wp_comp ct1 in
  let _, _, wp_e = destruct_wp_comp ct2 in
  let wp = mk_Tm_app (inst_effect_fun_with [u_a] env ed if_then_else)
    [S.as_arg a; S.as_arg p; S.as_arg wp_t; S.as_arg wp_e]
    (Range.union_ranges wp_t.pos wp_e.pos) in
  mk_comp ed u_a a wp [], Env.trivial_guard

(*
 * PURE<u> t (fun _ -> False)
 *
 * This is the comp type for a match with no cases (used in bind_cases)
 *)
let comp_pure_wp_false env (u:universe) (t:typ) =
  let post_k = U.arrow [null_binder t] (S.mk_Total U.ktype0) in
  let kwp    = U.arrow [null_binder post_k] (S.mk_Total U.ktype0) in
  let post   = S.new_bv None post_k in
  let wp     = U.abs [S.mk_binder post]
               (fvar_const env C.false_lid)
               (Some (U.mk_residual_comp C.effect_Tot_lid None [TOTAL])) in
  let md     = Env.get_effect_decl env C.effect_PURE_lid in
  mk_comp md u t wp []

(*
 * When typechecking a match term, typechecking each branch returns
 *   a branch condition
 *
 * E.g. match e with | C -> ... | D -> ...
 *   the two branch conditions would be (is_C e) and (is_D e)
 *
 * This function builds a list of formulas that are the negation of
 *   all the previous branches
 *
 * In the example, neg_branch_conds would be:
 *   [True; not (is_C e); not (is_C e) /\ not (is_D e)]
 *   thus, the length of the list is one more than lcases
 *
 * The return value is then ([True; not (is_C e)], not (is_C e) /\ not (is_D e))
 *
 * (The last element of the list becomes the branch condition for the
     unreachable branch to check for pattern exhaustiveness)
 *)
let get_neg_branch_conds (branch_conds:list<formula>)
  : list<formula> * formula
  = branch_conds
    |> List.fold_left (fun (conds, acc) g ->
        let cond = U.mk_conj acc (g |> U.b2t |> U.mk_neg) in
        (conds@[cond]), cond) ([U.t_true], U.t_true)
    |> fst
    |> (fun l -> List.splitAt (List.length l - 1) l)  //the length of the list is at least 1
    |> (fun (l1, l2) -> l1, List.hd l2)

(*
 * The formula in lcases is the individual branch guard, a boolean
 *)
let bind_cases env0 (res_t:typ)
  (lcases:list<(formula * lident * list<cflag> * (bool -> lcomp))>)
  (scrutinee:bv) : lcomp =

    let env = Env.push_binders env0 [scrutinee |> S.mk_binder] in
    let eff = List.fold_left (fun eff (_, eff_label, _, _) -> join_effects env eff eff_label)
                             C.effect_PURE_lid
                             lcases
    in
    let should_not_inline_whole_match, bind_cases_flags =
        if lcases |> BU.for_some (fun (_, _, flags, _) ->
           flags |> BU.for_some (function SHOULD_NOT_INLINE -> true | _ -> false))
        then true, [SHOULD_NOT_INLINE]
        else false, []
    in
    let bind_cases () =
        let u_res_t = env.universe_of env res_t in
        if env.lax
        && Options.ml_ish() //NS: Disabling this optimization temporarily
        then
             lax_mk_tot_or_comp_l eff u_res_t res_t [], Env.trivial_guard
        else begin
            let maybe_return eff_label_then cthen =
               if should_not_inline_whole_match
               || not (is_pure_or_ghost_effect env eff)
               then cthen true //inline each the branch, if eligible
               else cthen false //the entire match is pure and inlineable, so no need to inline each branch
            in

            (*
             * The formula in each of the branches of lcases is the branch condition of *just* that branch,
             *   e.g. match e with | C -> ... | D -> ...
             *        the formula in the two branches is is_C e and is_D e
             *
             * neg_branch_conds builds a list where the formulas are negation of
             *   all the previous branches
             *
             * In the example, neg_branch_conds would be:
             *   [True; not (is_C e); not (is_C e) /\ not (is_D e)]
             *   thus, the length of the list is one more than lcases
             *
             * The last element of the list becomes the branch condition for the
             *   unreachable branch (will be used to check pattern exhaustiveness)
             *
             * The rest of the list will be used to weaken the lift guards when combining the branches (for layered effects, lift guards can be non-trivial)
             *
             * note that we don't need to this just to combine cases because the shape of if_then_else
             *   (p ==> ...) /\ (not p ==> ...) takes care of it
             *)
            let neg_branch_conds, exhaustiveness_branch_cond =
              get_neg_branch_conds (lcases |> List.map (fun (g, _, _, _) -> g)) in

            let md, comp, g_comp =
              match lcases with
              | [] -> None, comp_pure_wp_false env u_res_t res_t, Env.trivial_guard
              | _ ->
                (*
                 * We will now compute the VC with a fold_right2 over lcases
                 *   and neg_branch_conds
                 * Split the last element of lcases (and branch conditions)
                 *   to form the base case
                 *)

                let lcases, neg_branch_conds, md, comp, g_comp =
                  let neg_branch_conds, neg_last =
                    neg_branch_conds
                    |> List.splitAt (List.length lcases - 1)
                    |> (fun (l1, l2) -> l1, List.hd l2) in

                  let lcases, (g_last, eff_last, _, c_last) =
                    lcases
                    |> List.splitAt (List.length lcases - 1)
                    |> (fun (l1, l2) -> l1, List.hd l2) in

                  let c, g =
                    let lc = maybe_return eff_last c_last in
                    let c, g = TcComm.lcomp_comp lc in
                    c, TcComm.weaken_guard_formula g (U.mk_conj (U.b2t g_last) neg_last) in

                  lcases,
                  neg_branch_conds,
                  eff_last |> Env.norm_eff_name env |> Env.get_effect_decl env,
                  c, g in

                List.fold_right2 (fun (g, eff_label, _, cthen) neg_cond (_, celse, g_comp) ->
                  let cthen, g_then = TcComm.lcomp_comp (maybe_return eff_label cthen) in
                  //lift both the branches
                  //separate guards so that we can weaken them appropriately later
                  let md, ct_then, ct_else, g_lift_then, g_lift_else =
                    let m, cthen, celse, g_lift_then, g_lift_else =
                      lift_comps_sep_guards env cthen celse None false in
                    let md = Env.get_effect_decl env m in
                    md,
                    cthen |> U.comp_to_comp_typ, celse |> U.comp_to_comp_typ,
                    g_lift_then, g_lift_else in

                  //function to apply the if-then-else combinator
                  let fn =
                    if md |> U.is_layered then mk_layered_conjunction
                    else mk_non_layered_conjunction in

                  let c, g_conjunction = fn env md u_res_t res_t g ct_then ct_else (Env.get_range env) in

                  //weaken the then and else guards
                  //neg_cond is the negated branch condition upto this branch
                  let g_then, g_else =
                    let g = U.b2t g in
                    TcComm.weaken_guard_formula
                      (Env.conj_guard g_then g_lift_then)
                      (U.mk_conj neg_cond g),
                    TcComm.weaken_guard_formula
                      g_lift_else
                      (U.mk_conj neg_cond (U.mk_neg g)) in

                  Some md,
                  c,
                  Env.conj_guards [g_comp; g_then; g_else; g_conjunction]
                ) lcases neg_branch_conds (Some md, comp, g_comp) in

            //strengthen comp with the exhaustiveness check
            let comp, g_comp =
              let c, g =
                let check = U.mk_imp exhaustiveness_branch_cond U.t_false in
                let check = label Err.exhaustiveness_check (Env.get_range env) check   in
                strengthen_comp env None comp check bind_cases_flags in
              c, Env.conj_guard g_comp g in

            //AR: 11/18: we don't need to close this guard with the scrutinee bv
            //           since the tc_match code does a bind with the scrutinee
            //           expression, which will take care of this bv
            //close g_comp with the scrutinee bv
            //let g_comp = Env.close_guard env0 [scrutinee |> S.mk_binder] g_comp in

            match lcases with
            | []
            | [_] -> comp, g_comp
            | _ ->
              if md |> must |> U.is_layered then comp, g_comp
              else
                let comp = Env.comp_to_comp_typ env comp in
                let md = Env.get_effect_decl env comp.effect_name in
                let _, _, wp = destruct_wp_comp comp in
                let ite_wp = md |> U.get_wp_ite_combinator |> must in
                let wp = mk_Tm_app (inst_effect_fun_with [u_res_t] env md ite_wp)
                                   [S.as_arg res_t; S.as_arg wp]
                                   wp.pos in
                mk_comp md u_res_t res_t wp bind_cases_flags, g_comp
        end
    in
    TcComm.mk_lcomp eff res_t bind_cases_flags bind_cases

let check_comp env (e:term) (c:comp) (c':comp) : term * comp * guard_t =
  if false then
    BU.print3 "Checking sub_comp:\n%s has type %s\n\t<:\n%s\n"
            (Print.term_to_string e)
            (Print.comp_to_string c)
            (Print.comp_to_string c');
  match Rel.sub_comp env c c' with
    | None ->
        if env.use_eq
        then raise_error (Err.computed_computation_type_does_not_match_annotation_eq env e c c') (Env.get_range env)
        else raise_error (Err.computed_computation_type_does_not_match_annotation env e c c') (Env.get_range env)
    | Some g -> e, c', g

let universe_of_comp env u_res c =
  (*
   * Universe computation for M t wp:
   *   if M is pure or ghost, then return universe of t
   *   else if M is not marked Total, then return u0
   *        else if M has no additional binders, then return universe of t
   *        else delegate the computation to repr of M, error out of no repr
   *)
  let c_lid = c |> U.comp_effect_name |> Env.norm_eff_name env in
  if U.is_pure_or_ghost_effect c_lid then u_res  //if pure or ghost, return the universe of the return type
  else
    let is_total = Env.lookup_effect_quals env c_lid |> List.existsb (fun q -> q = S.TotalEffect) in
    if not is_total then S.U_zero  //if it is a non-total effect then u0
    else match Env.effect_repr env c u_res with
         | None ->
           raise_error (Errors.Fatal_EffectCannotBeReified,
                        (BU.format1 "Effect %s is marked total but does not have a repr" (Print.lid_to_string c_lid)))
                        c.pos
         | Some tm -> env.universe_of env tm

let check_trivial_precondition env c =
  let ct = c |> Env.unfold_effect_abbrev env in
  let md = Env.get_effect_decl env ct.effect_name in
  let u_t, t, wp = destruct_wp_comp ct in
  let vc = mk_Tm_app
    (inst_effect_fun_with [u_t] env md (md |> U.get_wp_trivial_combinator |> must))
    [S.as_arg t; S.as_arg wp]
    (Env.get_range env)
  in

  ct, vc, Env.guard_of_guard_formula <| NonTrivial vc

let coerce_with (env:Env.env)
                (e : term) (lc : lcomp) // original term and its computation type
                (ty : typ) // new result typ
                (f : lident) // coercion
                (us : universes) (eargs : args) // extra arguments to coertion
                (mkcomp : term -> comp)
                : term * lcomp =
    match Env.try_lookup_lid env f with
    | Some _ ->
        if Env.debug env (Options.Other "Coercions") then
            BU.print1 "Coercing with %s!\n" (Ident.string_of_lid f);
        let coercion = S.fvar (Ident.set_lid_range f e.pos) (Delta_constant_at_level 1) None in
        let coercion = S.mk_Tm_uinst coercion us in
        let coercion = U.mk_app coercion eargs in
        let lc = bind e.pos env (Some e) lc (None, TcComm.lcomp_of_comp <| mkcomp ty) in
        let e = mk_Tm_app coercion [S.as_arg e] e.pos in
        e, lc
    | None ->
        Errors.log_issue e.pos (Errors.Warning_CoercionNotFound,
                                (BU.format1 "Coercion %s was not found in the environment, not coercing."
                                            (string_of_lid f)));
        e, lc

type isErased =
    | Yes of term
    | Maybe
    | No

let rec check_erased (env:Env.env) (t:term) : isErased =
  let norm' = N.normalize [Env.Beta; Env.Eager_unfolding;
                           Env.UnfoldUntil delta_constant;
                           Env.Exclude Env.Zeta; Env.Primops;
                           Env.Weak; Env.HNF; Env.Iota]
  in
  let t = norm' env t in
  let t = U.unrefine t in
  let h, args = U.head_and_args t in
  let h = U.un_uinst h in
  let r =
    match (SS.compress h).n, args with
    | Tm_fvar fv, [(a, None)] when S.fv_eq_lid fv C.erased_lid ->
      Yes a

    (* In these two cases, we cannot guarantee that `t` is not
     * an erased, so we're conservatively returning `false` *)
    | Tm_uvar _, _
    | Tm_unknown, _ -> Maybe

    (*
     * AR: For Tm_match:
     *     We are only interested in returning a No or Maybe
     *     Since even if all the branched are erased types,
     *       we need to find their join to return to the caller
     *     That's messy
     *     We can't always return Maybe, since that breaks simple
     *       cases like the int types in FStar.Integers
     *     So we iterate over all the branches and return a No if possible
     *)
    | Tm_match (_, _, branches), _ ->
      branches |> List.fold_left (fun acc br ->
        match acc with
        | Yes _ | Maybe -> Maybe
        | No ->
          let _, _, br_body = Subst.open_branch br in
          match
            br_body
            |> check_erased
                (br_body
                 |> Free.names
                 |> BU.set_elements
                 |> Env.push_bvs env) with
          | No -> No
          | _ -> Maybe) No


    (* Anything else cannot be `erased` *)
    | _ ->
      No
  in
  (* if Options.debug_any () then *)
  (*   BU.print2 "check_erased (%s) = %s\n" *)
  (*     (Print.term_to_string t) *)
  (*     (match r with *)
  (*      | Yes a -> "Yes " ^ Print.term_to_string a *)
  (*      | Maybe -> "Maybe" *)
  (*      | No -> "No"); *)
  r

let maybe_coerce_lc env (e:term) (lc:lcomp) (exp_t:term) : term * lcomp * guard_t =
    let should_coerce =
        env.phase1
      || env.lax
      || Options.lax ()
    in
    if not should_coerce
    then (e, lc, Env.trivial_guard)
    else
    let is_t_term t =
        let t = N.unfold_whnf env t in
        match (SS.compress t).n with
        | Tm_fvar fv -> S.fv_eq_lid fv C.term_lid
        | _ -> false
    in
    let is_t_term_view t =
        let t = N.unfold_whnf env t in
        match (SS.compress t).n with
        | Tm_fvar fv -> S.fv_eq_lid fv C.term_view_lid
        | _ -> false
    in
    let is_type t =
        let t = N.unfold_whnf env t in
        let t = U.unrefine t in (* mostly to catch `prop` too *)
        match (SS.compress t).n with
        | Tm_type _ -> true
        | _ -> false
    in
    let res_typ = U.unrefine lc.res_typ in
    let head, args = U.head_and_args res_typ in
    if Env.debug env (Options.Other "Coercions") then
            BU.print4 "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                    (Range.string_of_range e.pos)
                    (Print.term_to_string e)
                    (Print.term_to_string res_typ)
                    (Print.term_to_string exp_t);

    let mk_erased u t =
      U.mk_app
        (S.mk_Tm_uinst (fvar_const env C.erased_lid) [u])
        [S.as_arg t]
    in
    match (U.un_uinst head).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv C.bool_lid && is_type exp_t ->
        let e, lc = coerce_with env e lc U.ktype0 C.b2t_lid [] [] S.mk_Total in
        e, lc, Env.trivial_guard


    | Tm_fvar fv, [] when S.fv_eq_lid fv C.term_lid && is_t_term_view exp_t ->
        let e, lc = coerce_with env e lc S.t_term_view C.inspect [] [] S.mk_Tac in
        e, lc, Env.trivial_guard

    | Tm_fvar fv, [] when S.fv_eq_lid fv C.term_view_lid && is_t_term exp_t ->
        let e, lc = coerce_with env e lc S.t_term C.pack [] [] S.mk_Tac in
        e, lc, Env.trivial_guard

    | Tm_fvar fv, [] when S.fv_eq_lid fv C.binder_lid && is_t_term exp_t ->
        let e, lc = coerce_with env e lc S.t_term C.binder_to_term [] [] S.mk_Tac in
        e, lc, Env.trivial_guard

    | _ ->
    match check_erased env res_typ, check_erased env exp_t with
    | No, Yes ty ->
        begin
        let u = env.universe_of env ty in
        match Rel.get_subtyping_predicate env res_typ ty with
        | None ->
          e, lc, Env.trivial_guard
        | Some g ->
          let g = Env.apply_guard g e in
          let e, lc = coerce_with env e lc exp_t C.hide [u] [S.iarg ty] S.mk_Total in
          e, lc, g
        end

    | Yes ty, No ->
        let u = env.universe_of env ty in
        let e, lc = coerce_with env e lc ty C.reveal [u] [S.iarg ty] S.mk_GTotal in
        e, lc, Env.trivial_guard

    | _ ->
      e, lc, Env.trivial_guard

(* Coerces regardless of expected type if a view exists, useful for matches *)
(* Returns `None` if no coercion was applied. *)
let coerce_views (env:Env.env) (e:term) (lc:lcomp) : option<(term * lcomp)> =
    let rt = lc.res_typ in
    let rt = U.unrefine rt in
    let hd, args = U.head_and_args rt in
    match (SS.compress hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv C.term_lid ->
        Some <| coerce_with env e lc S.t_term_view C.inspect [] [] S.mk_Tac
    | _ ->
        None

let weaken_result_typ env (e:term) (lc:lcomp) (t:typ) : term * lcomp * guard_t =
  if Env.debug env Options.High then
    BU.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
            (Print.term_to_string e)
            (TcComm.lcomp_to_string lc)
            (Print.term_to_string t);
  let use_eq =
    env.use_eq_strict ||
    env.use_eq        ||
    (match Env.effect_decl_opt env lc.eff_name with
     // See issue #881 for why weakening result type of a reifiable computation is problematic
     | Some (ed, qualifiers) -> qualifiers |> List.contains Reifiable
     | _ -> false) in
  let gopt = if use_eq
             then Rel.try_teq true env lc.res_typ t, false
             else Rel.get_subtyping_predicate env lc.res_typ t, true in
  match gopt with
    | None, _ ->
        (*
         * AR: 11/18: should this always fail hard?
         *)
        if env.failhard
        then raise_error (Err.basic_type_error env (Some e) t lc.res_typ) e.pos
        else (
            subtype_fail env e lc.res_typ t; //log a sub-typing error
            e, {lc with res_typ=t}, Env.trivial_guard //and keep going to type-check the result of the program
        )
    | Some g, apply_guard ->
      match guard_form g with
        | Trivial ->
          (*
           * AR: when the guard is trivial, simply setting the result type to t might lose some precision
           *     e.g. when input lc has return type x:int{phi} and we are weakening it to int
           *     so we should capture the precision before setting the comp type to t (see e.g. #1500, #1470)
           *)
          let strengthen_trivial () =
            let c, g_c = TcComm.lcomp_comp lc in
            let res_t = Util.comp_result c in

            let set_result_typ (c:comp) :comp = Util.set_result_typ c t in

            if Util.eq_tm t res_t = Util.Equal then begin  //if the two types res_t and t are same, then just set the result type
              if Env.debug env <| Options.Extreme
              then BU.print2 "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                             (Print.term_to_string res_t) (Print.term_to_string t);
              set_result_typ c, g_c
            end
            else
              let is_res_t_refinement =
                let res_t = N.normalize_refinement N.whnf_steps env res_t in
                match res_t.n with
                | Tm_refine _ -> true
                | _ -> false
              in
              //if t is a refinement, insert a return to capture the return type res_t
              //we are not inlining e, rather just adding (fun (x:res_t) -> p x) at the end
              if is_res_t_refinement then
                let x = S.new_bv (Some res_t.pos) res_t in
                //AR: build M.return, where M is c's effect
                let cret, gret = return_value env (c |> U.comp_effect_name |> Env.norm_eff_name env)
                  (comp_univ_opt c) res_t (S.bv_to_name x) in
                  //AR: an M_M bind
                let lc = bind e.pos env (Some e) (TcComm.lcomp_of_comp c) (Some x, TcComm.lcomp_of_comp cret) in
                if Env.debug env <| Options.Extreme
                then BU.print4 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                               (Print.term_to_string e) (Print.comp_to_string c) (Print.term_to_string t) (TcComm.lcomp_to_string lc);
                let c, g_lc = TcComm.lcomp_comp lc in
                set_result_typ c, Env.conj_guards [g_c; gret; g_lc]
              else begin
                if Env.debug env <| Options.Extreme
                then BU.print2 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                               (Print.term_to_string res_t) (Print.comp_to_string c);
                set_result_typ c, g_c
              end
          in
          let lc = TcComm.mk_lcomp lc.eff_name t lc.cflags strengthen_trivial in
          e, lc, g

        | NonTrivial f ->
          let g = {g with guard_f=Trivial} in
          let strengthen () =
              if env.lax
              && Options.ml_ish() //NS: disabling this optimization temporarily
              then
                TcComm.lcomp_comp lc
              else begin
                  //try to normalize one more time, since more unification variables may be resolved now
                  let f = N.normalize [Env.Beta; Env.Eager_unfolding; Env.Simplify; Env.Primops] env f in
                  match (SS.compress f).n with
                      | Tm_abs(_, {n=Tm_fvar fv}, _) when S.fv_eq_lid fv C.true_lid ->
                        //it's trivial
                        let lc = {lc with res_typ=t} in //NS: what's the point of this?
                        TcComm.lcomp_comp lc

                      | _ ->
                          let c, g_c = TcComm.lcomp_comp lc in
                          if Env.debug env <| Options.Extreme
                          then BU.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  (N.term_to_string env lc.res_typ)
                                  (N.term_to_string env t)
                                  (N.comp_to_string env c)
                                  (N.term_to_string env f);

                          let u_t_opt = comp_univ_opt c in
                          let x = S.new_bv (Some t.pos) t in
                          let xexp = S.bv_to_name x in
                          //AR: M.return
                          let cret, gret = return_value env
                            (c |> U.comp_effect_name |> Env.norm_eff_name env)
                            u_t_opt t xexp in
                          let guard = if apply_guard
                                      then mk_Tm_app f [S.as_arg xexp] f.pos
                                      else f
                          in
                          let eq_ret, _trivial_so_ok_to_discard =
                              strengthen_precondition (Some <| Err.subtyping_failed env lc.res_typ t)
                                                      (Env.set_range (Env.push_bvs env [x]) e.pos)
                                                      e  //use e for debugging only
                                                      (TcComm.lcomp_of_comp cret)
                                                      (guard_of_guard_formula <| NonTrivial guard)
                          in
                          let x = {x with sort=lc.res_typ} in
                          //AR: M_M bind
                          let c = bind e.pos env (Some e) (TcComm.lcomp_of_comp c) (Some x, eq_ret) in
                          let c, g_lc = TcComm.lcomp_comp c in
                          if Env.debug env <| Options.Extreme
                          then BU.print1 "Strengthened to %s\n" (Normalize.comp_to_string env c);
                          c, Env.conj_guards [g_c; gret; g_lc]
                end
          in
          let flags = lc.cflags |> List.collect (function
                                                 | RETURN | PARTIAL_RETURN -> [PARTIAL_RETURN]
                                                 | CPS -> [CPS] // KM : Not exactly sure if it is necessary
                                                 | _ -> [])
          in
          let lc = TcComm.mk_lcomp (norm_eff_name env lc.eff_name) t flags strengthen in
          let g = {g with guard_f=Trivial} in
          (e, lc, g)

let pure_or_ghost_pre_and_post env comp =
    let mk_post_type res_t ens =
        let x = S.new_bv None res_t in
        U.refine x (S.mk_Tm_app ens [S.as_arg (S.bv_to_name x)] res_t.pos) in
    let norm t = Normalize.normalize [Env.Beta;Env.Eager_unfolding;Env.EraseUniverses] env t in
    if U.is_tot_or_gtot_comp comp
    then None, U.comp_result comp
    else begin match comp.n with
            | GTotal _
            | Total _ -> failwith "Impossible"
            | Comp ct ->
              if lid_equals ct.effect_name C.effect_Pure_lid
              || lid_equals ct.effect_name C.effect_Ghost_lid
              then begin match ct.effect_args with
                      | (req, _)::(ens, _)::_ ->
                         Some (norm req), (norm <| mk_post_type ct.result_typ ens)
                      | _ ->
                        raise_error (Errors.Fatal_EffectConstructorNotFullyApplied, (BU.format1 "Effect constructor is not fully applied; got %s" (Print.comp_to_string comp))) comp.pos
                   end
              else let ct = Env.unfold_effect_abbrev env comp in
                   begin match ct.effect_args with
                            | (wp, _)::_ ->
                              let us_r, _ = fst <| Env.lookup_lid env C.as_requires in
                              let us_e, _ = fst <| Env.lookup_lid env C.as_ensures in
                              let r = ct.result_typ.pos in
                              let as_req = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range C.as_requires r) delta_equational None) us_r in
                              let as_ens = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range C.as_ensures r) delta_equational None) us_e in
                              let req = mk_Tm_app as_req [(ct.result_typ, Some S.imp_tag); S.as_arg wp] ct.result_typ.pos in
                              let ens = mk_Tm_app as_ens [(ct.result_typ, Some S.imp_tag); S.as_arg wp] ct.result_typ.pos in
                              Some (norm req), norm (mk_post_type ct.result_typ ens)
                            | _ -> failwith "Impossible"
                  end

         end

(* [reify_body env t] assumes that [t] has a reifiable computation type *)
(* that is env |- t : M t' for some effect M and type t' where M is reifiable *)
(* and returns the result of reifying t *)
let reify_body (env:Env.env) (steps:Env.steps) (t:S.term) : S.term =
    let tm = U.mk_reify t in
    let tm' = N.normalize
      ([Env.Beta; Env.Reify; Env.Eager_unfolding; Env.EraseUniverses; Env.AllowUnboundUniverses; Env.Exclude Env.Zeta]@steps)
      env tm in
    if Env.debug env <| Options.Other "SMTEncodingReify"
    then BU.print2 "Reified body %s \nto %s\n"
        (Print.term_to_string tm)
        (Print.term_to_string tm') ;
    tm'

let reify_body_with_arg (env:Env.env) (steps:Env.steps) (head:S.term) (arg:S.arg): S.term =
    let tm = S.mk (S.Tm_app(head, [arg])) head.pos in
    let tm' = N.normalize
      ([Env.Beta; Env.Reify; Env.Eager_unfolding; Env.EraseUniverses; Env.AllowUnboundUniverses; Env.Exclude Env.Zeta]@steps)
      env tm in
    if Env.debug env <| Options.Other "SMTEncodingReify"
    then BU.print2 "Reified body %s \nto %s\n"
        (Print.term_to_string tm)
        (Print.term_to_string tm') ;
    tm'

let remove_reify (t: S.term): S.term =
  if (match (SS.compress t).n with | Tm_app _ -> false | _ -> true)
  then t
  else
    let head, args = U.head_and_args t in
    if (match (SS.compress head).n with Tm_constant FStar.Const.Const_reify -> true | _ -> false)
    then begin match args with
        | [x] -> fst x
        | _ -> failwith "Impossible : Reify applied to multiple arguments after normalization."
    end
    else t


(*********************************************************************************************)
(* Instantiation and generalization *)
(*********************************************************************************************)
let maybe_implicit_with_meta_or_attr aq (attrs:list<attribute>) =
  match aq, attrs with
  | Some (Meta _), _
  | Some (Implicit _), _::_ -> true
  | _ -> false

let maybe_instantiate (env:Env.env) e t =
  let torig = SS.compress t in
  if not env.instantiate_imp
  then e, torig, Env.trivial_guard
  else begin
       if Env.debug env Options.High then
         BU.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                 (Print.term_to_string e) (Print.term_to_string t) (FStar.Common.string_of_option Print.term_to_string (Env.expected_typ env));
       (* Similar to U.arrow_formals, but makes sure to unfold
        * recursively to catch all the binders across type
        * definitions. TODO: Move to library? Revise other uses
        * of arrow_formals{,_comp}?*)
       let unfolded_arrow_formals (t:term) : list<binder> =
         let rec aux (bs:list<binder>) (t:term) : list<binder> =
           let t = N.unfold_whnf env t in
           let bs', t = U.arrow_formals t in
           match bs' with
           | [] -> bs
           | bs' -> aux (bs@bs') t
         in
         aux [] t
       in
       let number_of_implicits t =
            let formals = unfolded_arrow_formals t in
            let n_implicits =
            match formals |> BU.prefix_until (fun ({binder_qual=imp}) -> Option.isNone imp || U.eq_aqual imp (Some Equality) = U.Equal) with
                | None -> List.length formals
                | Some (implicits, _first_explicit, _rest) -> List.length implicits in
            n_implicits
       in
       let inst_n_binders t =
           match Env.expected_typ env with
           | None -> None
           | Some expected_t ->
             let n_expected = number_of_implicits expected_t in
             let n_available = number_of_implicits t in
             if n_available < n_expected
             then raise_error (Errors.Fatal_MissingImplicitArguments, (BU.format3 "Expected a term with %s implicit arguments, but %s has only %s"
                                        (BU.string_of_int n_expected)
                                        (Print.term_to_string e)
                                        (BU.string_of_int n_available))) (Env.get_range env)
             else Some (n_available - n_expected)
        in
        let decr_inst = function
                | None -> None
                | Some i -> Some (i - 1)
        in
        let t = N.unfold_whnf env t in
        begin match t.n with
            | Tm_arrow(bs, c) ->
              let bs, c = SS.open_comp bs c in
              //instantiate at most inst_n implicit binders, when inst_n = Some n
              //otherwise, instantate all implicits
              //See issue #807 for why this is important
              let rec aux subst inst_n bs =
                  match inst_n, bs with
                  | Some 0, _ -> [], bs, subst, Env.trivial_guard //no more instantiations to do
                  | _, ({binder_bv=x; binder_qual=Some (Implicit _);binder_attrs=[]})::rest ->
                      let t = SS.subst subst x.sort in
                      let v, _, g = new_implicit_var "Instantiation of implicit argument" e.pos env t in
                      if Env.debug env Options.High then
                        BU.print1 "maybe_instantiate: Instantiating implicit with %s\n"
                                (Print.term_to_string v);
                      let subst = NT(x, v)::subst in
                      let args, bs, subst, g' = aux subst (decr_inst inst_n) rest in
                      (v, Some S.imp_tag)::args, bs, subst, Env.conj_guard g g'

                  | _, ({binder_bv=x; binder_qual=qual; binder_attrs=attrs})::rest
                    when maybe_implicit_with_meta_or_attr qual attrs ->
                      let t = SS.subst subst x.sort in
                      let meta_t =
                        match qual, attrs with
                        | Some (Meta tau), _ ->
                          Ctx_uvar_meta_tac (mkdyn env, tau)
                        | _, attr::_ ->
                          Ctx_uvar_meta_attr attr
                        | _ -> failwith "Impossible, match is under a guard, did not expect this case"
                      in
                      let v, _, g = new_implicit_var_aux "Instantiation of meta argument"
                                                         e.pos env t Strict
                                                         (Some meta_t) in
                      if Env.debug env Options.High then
                        BU.print1 "maybe_instantiate: Instantiating meta argument with %s\n"
                                (Print.term_to_string v);
                      let subst = NT(x, v)::subst in
                      let args, bs, subst, g' = aux subst (decr_inst inst_n) rest in
                      (v, Some S.imp_tag)::args, bs, subst, Env.conj_guard g g'

                 | _, bs -> [], bs, subst, Env.trivial_guard
              in
              let args, bs, subst, guard = aux [] (inst_n_binders t) bs in
              begin match args, bs with
                | [], _ -> //no implicits were instantiated
                  e, torig, guard

                | _, [] when not (U.is_total_comp c) ->
                  //don't instantiate implicitly, if it has an effect
                  e, torig, Env.trivial_guard

                | _ ->

                  let t = match bs with
                    | [] -> U.comp_result c
                    | _ -> U.arrow bs c in
                  let t = SS.subst subst t in
                  let e = S.mk_Tm_app e args e.pos in
                  e, t, guard
              end

            | _ -> e, torig, Env.trivial_guard
       end
  end

(************************************************************************)
(* Convertibility *)
(************************************************************************)
//check_has_type env e t1 t2
//checks is e:t1 has type t2, subject to some guard.

let check_has_type env (e:term) (t1:typ) (t2:typ) : guard_t =
  let env = Env.set_range env e.pos in

  let g_opt =
    if env.use_eq_strict
    then match Rel.teq_nosmt_force env t1 t2 with
       | false -> None
       | true -> Env.trivial_guard |> Some
    else if env.use_eq
    then Rel.try_teq true env t1 t2
    else match Rel.get_subtyping_predicate env t1 t2 with
             | None -> None
             | Some f -> apply_guard f e |> Some in

  match g_opt with
  | None -> raise_error (Err.expected_expression_of_type env t2 e t1) (Env.get_range env)
  | Some g -> g

let check_has_type_maybe_coerce env (e:term) (lc:lcomp) (t2:typ) : term * lcomp * guard_t =
  let env = Env.set_range env e.pos in
  let e, lc, g_c = maybe_coerce_lc env e lc t2 in
  let g = check_has_type env e lc.res_typ t2 in
  if debug env <| Options.Other "Rel" then
    BU.print1 "Applied guard is %s\n" <| guard_to_string env g;
  e, lc, (Env.conj_guard g g_c)

/////////////////////////////////////////////////////////////////////////////////
let check_top_level env g lc : (bool * comp) =
  if debug env Options.Medium then
    BU.print1 "check_top_level, lc = %s\n" (TcComm.lcomp_to_string lc);
  let discharge g =
    force_trivial_guard env g;
    TcComm.is_pure_lcomp lc in
  let g = Rel.solve_deferred_constraints env g in
  let c, g_c = TcComm.lcomp_comp lc in
  if TcComm.is_total_lcomp lc
  then discharge (Env.conj_guard g g_c), c
  else let steps = [Env.Beta; Env.NoFullNorm; Env.DoNotUnfoldPureLets] in
       let c = Env.unfold_effect_abbrev env c
              |> S.mk_Comp
              |> Normalize.normalize_comp steps env in
       let ct, vc, g_pre = check_trivial_precondition env c in
       if Env.debug env <| Options.Other "Simplification"
       then BU.print1 "top-level VC: %s\n" (Print.term_to_string vc);
       discharge (Env.conj_guard g (Env.conj_guard g_c g_pre)), ct |> mk_Comp

(* Having already seen_args to head (from right to left),
   compute the guard, if any, for the next argument,
   if head is a short-circuiting operator *)
let short_circuit (head:term) (seen_args:args) : guard_formula =
    let short_bin_op f : args -> guard_formula = function
        | [] -> (* no args seen yet *) Trivial
        | [(fst, _)] -> f fst
        | _ -> failwith "Unexpexted args to binary operator" in

    let op_and_e e = U.b2t e   |> NonTrivial in
    let op_or_e e  = U.mk_neg (U.b2t e) |> NonTrivial in
    let op_and_t t = t |> NonTrivial in
    let op_or_t t  = t |> U.mk_neg |> NonTrivial in
    let op_imp_t t = t |> NonTrivial in

    let short_op_ite : args -> guard_formula = function
        | [] -> Trivial
        | [(guard, _)] -> NonTrivial guard
        | [_then;(guard, _)] -> U.mk_neg guard |> NonTrivial
        | _ -> failwith "Unexpected args to ITE" in
    let table =
        [(C.op_And,  short_bin_op op_and_e);
         (C.op_Or,   short_bin_op op_or_e);
         (C.and_lid, short_bin_op op_and_t);
         (C.or_lid,  short_bin_op op_or_t);
         (C.imp_lid, short_bin_op op_imp_t);
         (C.ite_lid, short_op_ite);] in

     match head.n with
        | Tm_fvar fv ->
          let lid = fv.fv_name.v in
          begin match BU.find_map table (fun (x, mk) -> if lid_equals x lid then Some (mk seen_args) else None) with
            | None ->   Trivial
            | Some g -> g
          end
        | _ -> Trivial

let short_circuit_head l =
    match (U.un_uinst l).n with
        | Tm_fvar fv ->
           BU.for_some (S.fv_eq_lid fv)
                   [C.op_And;
                    C.op_Or;
                    C.and_lid;
                    C.or_lid;
                    C.imp_lid;
                    C.ite_lid]
        | _ -> false



(************************************************************************)
(* maybe_add_implicit_binders (env:env) (bs:binders)                    *)
(* Adding implicit binders for ticked variables                         *)
(* in case the expected type is of the form #'a1 -> ... -> #'an -> t    *)
(* and bs does not begin with any implicit binders                      *)
(* add #'a1 ... #'an to bs                                              *)
(************************************************************************)
let maybe_add_implicit_binders (env:env) (bs:binders)  : binders =
    let pos bs = match bs with
        | ({binder_bv=hd})::_ -> S.range_of_bv hd
        | _ -> Env.get_range env in
    match bs with
        | ({binder_qual=Some (Implicit _)})::_ -> bs //bs begins with an implicit binder; don't add any
        | _ ->
          match Env.expected_typ env with
            | None -> bs
            | Some t ->
                match (SS.compress t).n with
                    | Tm_arrow(bs', _) ->
                      begin match BU.prefix_until (function ({binder_qual=Some (Implicit _)}) -> false | _ -> true) bs' with
                        | None -> bs
                        | Some ([], _, _) -> bs //no implicits
                        | Some (imps, _,  _) ->
                          if imps |> BU.for_all (fun ({binder_bv=x}) -> BU.starts_with (string_of_id x.ppname) "'")
                          then let r = pos bs in
                               let imps = imps |> List.map (fun b -> { b with binder_bv = (S.set_range_of_bv b.binder_bv r) }) in
                               imps@bs //we have a prefix of ticked variables
                          else bs
                      end

                    | _ -> bs


//Decorating terms with monadic operators
let maybe_lift env e c1 c2 t =
    let m1 = Env.norm_eff_name env c1 in
    let m2 = Env.norm_eff_name env c2 in
    if Ident.lid_equals m1 m2
    || (U.is_pure_effect c1 && U.is_ghost_effect c2)
    || (U.is_pure_effect c2 && U.is_ghost_effect c1)
    then e
    else mk (Tm_meta(e, Meta_monadic_lift(m1, m2, t))) e.pos

let maybe_monadic env e c t =
    let m = Env.norm_eff_name env c in
    if is_pure_or_ghost_effect env m
    || Ident.lid_equals m C.effect_Tot_lid
    || Ident.lid_equals m C.effect_GTot_lid //for the cases in prims where Pure is not yet defined
    then e
    else mk (Tm_meta(e, Meta_monadic (m, t))) e.pos

let d s = BU.print1 "\x1b[01;36m%s\x1b[00m\n" s

// Takes care of creating the [fv], generating the top-level let-binding, and
// return a term that's a suitable reference (a [Tm_fv]) to the definition
let mk_toplevel_definition (env: env_t) lident (def: term): sigelt * term =
  // Debug
  if Env.debug env (Options.Other "ED") then begin
    d (string_of_lid lident);
    BU.print2 "Registering top-level definition: %s\n%s\n" (string_of_lid lident) (Print.term_to_string def)
  end;
  // Allocate a new top-level name.
  let fv = S.lid_as_fv lident (U.incr_delta_qualifier def) None in
  let lbname: lbname = Inr fv in
  let lb: letbindings =
    // the effect label will be recomputed correctly
    false, [U.mk_letbinding lbname [] S.tun C.effect_Tot_lid def [] Range.dummyRange]
  in
  // [Inline] triggers a "Impossible: locally nameless" error // FIXME: Doc?
  let sig_ctx = mk_sigelt (Sig_let (lb, [ lident ])) in
  {sig_ctx with sigquals=[ Unfold_for_unification_and_vcgen ]},
  mk (Tm_fvar fv) Range.dummyRange

/////////////////////////////////////////////////////////////////////////////
//Checks that the qualifiers on this sigelt are legal for it
/////////////////////////////////////////////////////////////////////////////
let check_sigelt_quals (env:FStar.TypeChecker.Env.env) se =
    let visibility = function Private -> true | _ -> false in
    let reducibility = function
        | Irreducible
        | Unfold_for_unification_and_vcgen | Visible_default
        | Inline_for_extraction -> true
        | _ -> false in
    let assumption = function Assumption | New -> true | _ -> false in
    let reification = function Reifiable | Reflectable _ -> true | _ -> false in
    let inferred = function
      | Discriminator _
      | Projector _
      | RecordType _
      | RecordConstructor _
      | ExceptionConstructor
      | HasMaskedEffect
      | Effect -> true
      | _ -> false in
    let has_eq = function Noeq | Unopteq -> true | _ -> false in
    let quals_combo_ok quals q =
        match q with
        | Assumption ->
          quals
          |> List.for_all (fun x -> x=q
                              || x=Logic
                              || inferred x
                              || visibility x
                              || assumption x
                              || (env.is_iface && x=Inline_for_extraction)
                              || x=NoExtract)

        | New -> //no definition provided
          quals
          |> List.for_all (fun x -> x=q || inferred x || visibility x || assumption x)

        | Inline_for_extraction ->
          quals |> List.for_all (fun x -> x=q || x=Logic || visibility x || reducibility x
                                              || reification x || inferred x || has_eq x
                                              || (env.is_iface && x=Assumption)
                                              || x=NoExtract)

        | Unfold_for_unification_and_vcgen
        | Visible_default
        | Irreducible
        | Noeq
        | Unopteq ->
          quals
          |> List.for_all (fun x -> x=q || x=Logic || x=Inline_for_extraction || x=NoExtract || has_eq x || inferred x || visibility x || reification x)

        | TotalEffect ->
          quals
          |> List.for_all (fun x -> x=q || inferred x || visibility x || reification x)

        | Logic ->
          quals
          |> List.for_all (fun x -> x=q || x=Assumption || inferred x || visibility x || reducibility x)

        | Reifiable
        | Reflectable _ ->
          quals
          |> List.for_all (fun x -> reification x || inferred x || visibility x || x=TotalEffect || x=Visible_default)

        | Private ->
          true //only about visibility; always legal in combination with others

        | _ -> //inferred
          true
    in
    let check_erasable quals se r =
        let lids = U.lids_of_sigelt se in
        let val_exists =
          lids |> BU.for_some (fun l -> Option.isSome (Env.try_lookup_val_decl env l))
        in
        let val_has_erasable_attr =
          lids |> BU.for_some (fun l ->
            let attrs_opt = Env.lookup_attrs_of_lid env l in
            Option.isSome attrs_opt
            && U.has_attribute (Option.get attrs_opt) FStar.Parser.Const.erasable_attr)
        in
        let se_has_erasable_attr = U.has_attribute se.sigattrs FStar.Parser.Const.erasable_attr in
        if ((val_exists && val_has_erasable_attr) && not se_has_erasable_attr)
        then raise_error
             (Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributes between declaration and definition: \
               Declaration is marked `erasable` but the definition is not")
              r;
        if ((val_exists && not val_has_erasable_attr) && se_has_erasable_attr)
        then raise_error
             (Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributed between declaration and definition: \
               Definition is marked `erasable` but the declaration is not")
              r;
        if se_has_erasable_attr
        then begin
          match se.sigel with
          | Sig_bundle _ ->
            if not (quals |> BU.for_some (function Noeq -> true | _ -> false))
            then raise_error
                   (Errors.Fatal_QulifierListNotPermitted,
                    "Incompatible attributes and qualifiers: \
                     erasable types do not support decidable equality and must be marked `noeq`")
                    r
          | Sig_declare_typ _ ->
            ()
          | Sig_fail _ ->
            () (* just ignore it, the member ses have the attribute too *)

          | Sig_let((false, [lb]), _) ->
            let _, body, _ = U.abs_formals lb.lbdef in
            if not (N.non_info_norm env body)
            then raise_error
                   (Errors.Fatal_QulifierListNotPermitted,
                    BU.format1
                    "Illegal attribute: \
                     the `erasable` attribute is only permitted on inductive type definitions \
                     and abbreviations for non-informative types. %s is considered informative."
                     (Print.term_to_string body))
                    body.pos

          | Sig_new_effect ({mname=eff_name}) ->  //AR: allow erasable on total effects
            if not (List.contains TotalEffect quals)
            then raise_error
                   (Errors.Fatal_QulifierListNotPermitted,
                    BU.format1
                      "Effect %s is marked erasable but only total effects are allowed to be erasable"
                      (string_of_lid eff_name)) r

          | _ ->
            raise_error
              (Errors.Fatal_QulifierListNotPermitted,
               "Illegal attribute: \
                the `erasable` attribute is only permitted on inductive type definitions \
                and abbreviations for non-informative types")
               r
        end
    in
    let quals = U.quals_of_sigelt se |> List.filter (fun x -> not (x = Logic)) in  //drop logic since it is deprecated
    if quals |> BU.for_some (function OnlyName -> true | _ -> false) |> not
    then
      let r = U.range_of_sigelt se in
      let no_dup_quals = BU.remove_dups (fun x y -> x=y) quals in
      let err' msg =
          raise_error (Errors.Fatal_QulifierListNotPermitted, (BU.format2
                          "The qualifier list \"[%s]\" is not permissible for this element%s"
                          (Print.quals_to_string quals) msg)) r in
      let err msg = err' (": " ^ msg) in
      let err' () = err' "" in
      if List.length quals <> List.length no_dup_quals
      then err "duplicate qualifiers";
      if not (quals |> List.for_all (quals_combo_ok quals))
      then err "ill-formed combination";
      check_erasable quals se r;
      match se.sigel with
      | Sig_let((is_rec, _), _) -> //let rec
        if is_rec && quals |> List.contains Unfold_for_unification_and_vcgen
        then err "recursive definitions cannot be marked inline";
        if quals |> BU.for_some (fun x -> assumption x || has_eq x)
        then err "definitions cannot be assumed or marked with equality qualifiers"
      | Sig_bundle _ ->
        if not (quals |> BU.for_all (fun x ->
              x=Inline_for_extraction
              || x=NoExtract
              || inferred x
              || visibility x
              || has_eq x))
        then err' ();
        if quals |> List.existsb (function Unopteq -> true | _ -> false) &&
           U.has_attribute se.sigattrs FStar.Parser.Const.erasable_attr
        then err "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
      | Sig_declare_typ _ ->
        if quals |> BU.for_some has_eq
        then err' ()
      | Sig_assume _ ->
        if not (quals |> BU.for_all (fun x -> visibility x || x=Assumption))
        then err' ()
      | Sig_new_effect _ ->
        if not (quals |> BU.for_all (fun x ->
              x=TotalEffect
              || inferred x
              || visibility x
              || reification x))
        then err' ()
      | Sig_effect_abbrev _ ->
        if not (quals |> BU.for_all (fun x -> inferred x || visibility x))
        then err' ()
      | _ -> ()

let must_erase_for_extraction (g:env) (t:typ) =
    let rec descend env t = //t is expected to b in WHNF
      match (SS.compress t).n with
      | Tm_arrow _ ->
           let bs, c = U.arrow_formals_comp t in
           let env = FStar.TypeChecker.Env.push_binders env bs in
           (Env.is_erasable_effect env (U.comp_effect_name c))  //includes GHOST
           || (U.is_pure_or_ghost_comp c && aux env (U.comp_result c))
      | Tm_refine({sort=t}, _) ->
           aux env t
      | Tm_app (head, _)
      | Tm_uinst (head, _) ->
           descend env head
      | Tm_fvar fv ->
           //special treatment for must_erase_for_extraction here
           //See Env.type_is_erasable for more explanations
           Env.fv_has_attr env fv C.must_erase_for_extraction_attr
      | _ -> false
    and aux env t =
        let t = N.normalize [Env.Primops;
                             Env.Weak;
                             Env.HNF;
                             Env.UnfoldUntil delta_constant;
                             Env.Beta;
                             Env.AllowUnboundUniverses;
                             Env.Zeta;
                             Env.Iota;
                             Env.Unascribe] env t in
//        debug g (fun () -> BU.print1 "aux %s\n" (Print.term_to_string t));
        let res = Env.non_informative env t || descend env t in
        if Env.debug env <| Options.Other "Extraction"
        then BU.print2 "must_erase=%s: %s\n" (if res then "true" else "false") (Print.term_to_string t);
        res
    in
    aux g t

let fresh_effect_repr env r eff_name signature_ts repr_ts_opt u a_tm =
  let fail t = raise_error (Err.unexpected_signature_for_monad env eff_name t) r in

  let _, signature = Env.inst_tscheme signature_ts in

  (*
   * We go through the binders in the signature a -> bs
   * For each binder in bs, create a fresh uvar
   * But keep substituting [a/a_tm, b_i/?ui] in the sorts of the subsequent binders
   *)
  match (SS.compress signature).n with
  | Tm_arrow (bs, _) ->
    let bs = SS.open_binders bs in
    (match bs with
     | a::bs ->
       //is is all the uvars, and g is their collective guard
       let is, g = Env.uvars_for_binders env bs [NT (a.binder_bv, a_tm)]
         (fun b -> BU.format3
           "uvar for binder %s when creating a fresh repr for %s at %s"
           (Print.binder_to_string b) (string_of_lid eff_name) (Range.string_of_range r)) r in
       (match repr_ts_opt with
        | None ->  //no repr, return thunked computation type
          let eff_c = mk_Comp ({
            comp_univs = [u];
            effect_name = eff_name;
            result_typ = a_tm;
            effect_args = List.map S.as_arg is;
            flags = [] }) in
          S.mk (Tm_arrow ([S.null_binder S.t_unit], eff_c)) r
        | Some repr_ts ->
          let repr = Env.inst_tscheme_with repr_ts [u] |> snd in
          let is_args = List.map2 (fun i ({binder_qual=aqual}) -> (i, aqual)) is bs in
          S.mk_Tm_app
            repr
            (S.as_arg a_tm::is_args)
            r), g
     | _ -> fail signature)
  | _ -> fail signature

let fresh_effect_repr_en env r eff_name u a_tm =
  eff_name
  |> Env.get_effect_decl env
  |> (fun ed -> fresh_effect_repr env r eff_name ed.signature (ed |> U.get_eff_repr)  u a_tm)

let layered_effect_indices_as_binders env r eff_name sig_ts u a_tm =
  let _, sig_tm = Env.inst_tscheme_with sig_ts [u] in

  let fail t = raise_error (Err.unexpected_signature_for_monad env eff_name t) r in

  match (SS.compress sig_tm).n with
  | Tm_arrow (bs, _) ->
    let bs = SS.open_binders bs in
    (match bs with
     | ({binder_bv=a'})::bs -> bs |> SS.subst_binders [NT (a', a_tm)]
     | _ -> fail sig_tm)
  | _ -> fail sig_tm


let check_non_informative_type_for_lift env m1 m2 t r : unit =
  //raise an error if m1 is erasable, m2 is not erasable, and t is informative
  if Env.is_erasable_effect env m1       &&
     not (Env.is_erasable_effect env m2) &&
     not (N.non_info_norm env t)
  then Errors.raise_error
         (Errors.Error_TypeError,
          BU.format3 "Cannot lift erasable expression from %s ~> %s since its type %s is informative"
            (string_of_lid m1)
            (string_of_lid m2)
            (Print.term_to_string t))
         r

(*
 * Lifting a comp c to the layered effect eff_name
 *
 * let c = M<u_c> a_c wp_c
 *
 * let lift_M_eff_name = (u, lift_t) where
 *   lift_t = a:Type u -> wp:M_wp a -> (x_i:t_i) -> f:(unit -> M a wp) -> PURE (repr<u> a i_1 ... i_n) wp
 *
 * We first instantiate lift_t with u_c
 *
 * Then we create uvars (?u_i:t_i), while subtituting [a/a_c; wp/wp_c; x_j/?u_j] (forall j < i)
 *
 * let substs = [a/a_c; wp/wp_c; x_i/?u_i]
 *
 * We return M'<u_c> a_c i_i[substs]
 *
 * + we add (wp[substs] (fun _ -> True)) to the returned guard
 *)
let lift_tf_layered_effect (tgt:lident) (lift_ts:tscheme) env (c:comp) : comp * guard_t =
  if Env.debug env <| Options.Other "LayeredEffects" then
    BU.print2 "Lifting comp %s to layered effect %s {\n"
      (Print.comp_to_string c) (Print.lid_to_string tgt);

  let r = Env.get_range env in

  let ct = U.comp_to_comp_typ c in

  check_non_informative_type_for_lift env ct.effect_name tgt ct.result_typ r;

  let lift_name = BU.format2 "%s ~> %s" (string_of_lid ct.effect_name) (string_of_lid tgt) in

  let u, a, c_is = List.hd ct.comp_univs, ct.result_typ, ct.effect_args |> List.map fst in

  //lift_ts has the arrow type: <u>a:Type -> ..bs.. -> f -> repr a is

  let _, lift_t = Env.inst_tscheme_with lift_ts [u] in

  let lift_t_shape_error s =
    BU.format4 "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
      (Ident.string_of_lid ct.effect_name) (Ident.string_of_lid tgt)
      s (Print.term_to_string lift_t) in

  let a_b, (rest_bs, [f_b]), lift_c =  //lift_c is the computation type of the lift combinator (PURE/GHOST a wp)
    match (SS.compress lift_t).n with
    | Tm_arrow (bs, c) when List.length bs >= 2 ->
      let ((a_b::bs), c) = SS.open_comp bs c in
      a_b, bs |> List.splitAt (List.length bs - 1), c
    | _ ->
      raise_error (Errors.Fatal_UnexpectedEffect, lift_t_shape_error
        "either not an arrow or not enough binders") r in

  let rest_bs_uvars, g = Env.uvars_for_binders env rest_bs
    [NT (a_b.binder_bv, a)]
    (fun b -> BU.format4
      "implicit var for binder %s of %s~>%s at %s"
      (Print.binder_to_string b) (Ident.string_of_lid ct.effect_name)
      (Ident.string_of_lid tgt) (Range.string_of_range r)) r in

  if debug env <| Options.Other "LayeredEffects" then
    BU.print1 "Introduced uvars: %s\n"
      (List.fold_left (fun s u -> s ^ ";;;;" ^ (Print.term_to_string u)) "" rest_bs_uvars);

  let substs = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::rest_bs) (a::rest_bs_uvars) in

  let guard_f =
    let f_sort = f_b.binder_bv.sort |> SS.subst substs |> SS.compress in
    let f_sort_is = effect_args_from_repr f_sort (Env.is_layered_effect env ct.effect_name) r in
    List.fold_left2
      (fun g i1 i2 -> Env.conj_guard g (Rel.layered_effect_teq env i1 i2 (Some lift_name)))
      Env.trivial_guard c_is f_sort_is in

  let lift_ct = lift_c |> SS.subst_comp substs |> U.comp_to_comp_typ in

  let is = effect_args_from_repr lift_ct.result_typ (Env.is_layered_effect env tgt) r in

  //compute the formula `lift_c.wp (fun _ -> True)` and add it to the final guard
  let fml =
    let u, wp = List.hd lift_ct.comp_univs, fst (List.hd lift_ct.effect_args) in
    Env.pure_precondition_for_trivial_post env u lift_ct.result_typ wp Range.dummyRange in

  if Env.debug env <| Options.Other "LayeredEffects" &&
     Env.debug env <| Options.Extreme
  then BU.print1 "Guard for lift is: %s" (Print.term_to_string fml);

  let c = mk_Comp ({
    comp_univs = [u];
    effect_name = tgt;
    result_typ = a;
    effect_args = is |> List.map S.as_arg;
    flags = []  //AR: setting the flags to empty
  }) in

  if debug env <| Options.Other "LayeredEffects" then
    BU.print1 "} Lifted comp: %s\n" (Print.comp_to_string c);

  c, Env.conj_guard (Env.conj_guard g guard_f) (Env.guard_of_guard_formula (TcComm.NonTrivial fml))

(*
 * Creating the Env.mlift.mlift_term function for layered effects
 * Quite simple, just apply the lift term, passing units for the
 * binders that are meant to compute indices
 *)
let lift_tf_layered_effect_term env (sub:sub_eff)
  (u:universe) (a:typ) (e:term) : term =

  let lift = sub.lift |> must |> (fun ts -> inst_tscheme_with ts [u]) |> snd in

  let rest_bs =
    let lift_t = sub.lift_wp |> must in
    match (lift_t |> snd |> SS.compress).n with
    | Tm_arrow (_::bs, _) when List.length bs >= 1 ->
      bs |> List.splitAt (List.length bs - 1) |> fst
    | _ ->
      raise_error (Errors.Fatal_UnexpectedEffect,
        BU.format1 "lift_t tscheme %s is not an arrow with enough binders"
          (Print.tscheme_to_string lift_t)) (snd lift_t).pos in

  let args = (S.as_arg a)::((rest_bs |> List.map (fun _ -> S.as_arg S.unit_const))@[S.as_arg e]) in
  mk (Tm_app (lift, args)) e.pos

let get_field_projector_name env datacon index =
  let _, t = Env.lookup_datacon env datacon in
  let err n =
    raise_error (Errors.Fatal_UnexpectedDataConstructor,
      BU.format3 "Data constructor %s does not have enough binders (has %s, tried %s)"
        (Ident.string_of_lid datacon) (string_of_int n) (string_of_int index)) (Env.get_range env) in
  match (SS.compress t).n with
  | Tm_arrow (bs, _) ->
    let bs = bs |> List.filter (fun ({binder_qual=q}) -> match q with | Some (Implicit true) -> false | _ -> true) in
    if List.length bs <= index then err (List.length bs)
    else
      let b = List.nth bs index in
      U.mk_field_projector_name datacon b.binder_bv index
  | _ -> err 0


let get_mlift_for_subeff env (sub:S.sub_eff) : Env.mlift =
  if Env.is_layered_effect env sub.source || Env.is_layered_effect env sub.target

  then
    ({ mlift_wp = lift_tf_layered_effect sub.target (sub.lift_wp |> must);
       mlift_term = Some (lift_tf_layered_effect_term env sub) })

  else
    let mk_mlift_wp ts env c =
      let ct = U.comp_to_comp_typ c in
      check_non_informative_type_for_lift env ct.effect_name sub.target ct.result_typ env.range;
      let _, lift_t = inst_tscheme_with ts ct.comp_univs in
      let wp = List.hd ct.effect_args in
      S.mk_Comp ({ ct with
        effect_name = sub.target;
        effect_args =
          [mk (Tm_app (lift_t, [as_arg ct.result_typ; wp])) (fst wp).pos |> S.as_arg]
      }), TcComm.trivial_guard
    in

    let mk_mlift_term ts u r e =
      let _, lift_t = inst_tscheme_with ts [u] in
      mk (Tm_app (lift_t, [as_arg r; as_arg S.tun; as_arg e])) e.pos
    in

    ({ mlift_wp = sub.lift_wp |> must |> mk_mlift_wp;
       //AR: this is funky
       //it is saying, if you don't give us a lift term (a function that lifts terms),
       //we are assuming that the function is an identity
       //so for example, primitive effects just specify lift wps, and not terms
       //for them we assume that the terms are identity functions
       //why do we need it?
       //suppose programmer writes a layered effect M and defines a lift from DIV to M
       //now a PURE computation in the VC gets lifted via: PURE ~> DIV ~> M
       //when extracting (and reifying the monadic lifts), we go the same route
       //but if there is no lift term from PURE ~> DIV, we get an error
       //is this ok to do for DM4F? not sure in general
       //but currently PURE and DIV are lifted to DM4F effects using M.return
       //and not using the lift term (I don't think the lift term is even supported for DM4F, is it?)
       mlift_term =
         match sub.lift with
         | None -> Some (fun _ _ e -> return_all e)
         | Some ts -> Some (mk_mlift_term ts) })


let update_env_sub_eff env sub r =
  let r0 = env.range in
  let env = Env.update_effect_lattice
    ({ env with range = r }) sub.source sub.target (get_mlift_for_subeff env sub) in
  { env with range = r0 }

let update_env_polymonadic_bind env m n p ty =
  Env.add_polymonadic_bind env m n p
    (fun env c1 bv_opt c2 flags r -> mk_indexed_bind env m n p ty c1 bv_opt c2 flags r)
