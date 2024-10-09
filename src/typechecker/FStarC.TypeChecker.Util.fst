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

module FStarC.TypeChecker.Util
open FStar.Pervasives
open FStarC.Compiler.Effect
open FStarC.Compiler.List
open FStar open FStarC
open FStarC.Compiler
open FStarC.Compiler.Util
open FStarC.Errors
open FStarC.Errors.Msg
open FStarC.Pprint
open FStarC.Defensive
open FStarC.TypeChecker
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Rel
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Syntax.Subst
open FStarC.Syntax
open FStarC.Dyn
open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Class.Monoid

module Listlike = FStarC.Class.Listlike

module SS = FStarC.Syntax.Subst
module S = FStarC.Syntax.Syntax
module BU = FStarC.Compiler.Util
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module TcComm = FStarC.TypeChecker.Common
module P = FStarC.Syntax.Print
module C = FStarC.Parser.Const
module UF = FStarC.Syntax.Unionfind
module TEQ = FStarC.TypeChecker.TermEqAndSimplify

open FStarC.Class.Setlike

let dbg_bind                 = Debug.get_toggle "Bind"
let dbg_Coercions            = Debug.get_toggle "Coercions"
let dbg_Dec                  = Debug.get_toggle "Dec"
let dbg_Extraction           = Debug.get_toggle "Extraction"
let dbg_LayeredEffects       = Debug.get_toggle "LayeredEffects"
let dbg_LayeredEffectsApp    = Debug.get_toggle "LayeredEffectsApp"
let dbg_Pat                  = Debug.get_toggle "Pat"
let dbg_Rel                  = Debug.get_toggle "Rel"
let dbg_ResolveImplicitsHook = Debug.get_toggle "ResolveImplicitsHook"
let dbg_Return               = Debug.get_toggle "Return"
let dbg_Simplification       = Debug.get_toggle "Simplification"
let dbg_SMTEncodingReify     = Debug.get_toggle "SMTEncodingReify"

(************************************************************************)
(* Unification variables *)
(************************************************************************)
let new_implicit_var reason r env k unrefine =
  Env.new_implicit_var_aux reason r env k Strict None unrefine

let close_guard_implicits env solve_deferred (xs:binders) (g:guard_t) : guard_t =
  if Options.eager_subtyping ()
  || solve_deferred
  then
    let solve_now, defer =
      g.deferred |> Listlike.to_list |> List.partition (fun (_, _, p) -> Rel.flex_prob_closing env xs p)
    in
    if !dbg_Rel
    then begin
      BU.print_string "SOLVE BEFORE CLOSING:\n";
      List.iter (fun (_, s, p) -> BU.print2 "%s: %s\n" s (Rel.prob_to_string env p)) solve_now;
      BU.print_string " ...DEFERRED THE REST:\n";
      List.iter (fun (_, s, p) -> BU.print2 "%s: %s\n" s (Rel.prob_to_string env p)) defer;
      BU.print_string "END\n"
    end;
    let g = Rel.solve_non_tactic_deferred_constraints false env ({g with deferred = Listlike.from_list solve_now}) in
    let g = {g with deferred = Listlike.from_list defer} in
    g
  else g

let check_uvars r t =
  let uvs = Free.uvars t in
  if not (is_empty uvs) then begin
    (* ignoring the hide_uvar_nums and print_implicits flags here *)
    Options.push();
    Options.set_option "hide_uvar_nums" (Options.Bool false);
    Options.set_option "print_implicits" (Options.Bool true);
    Errors.log_issue r Errors.Error_UncontrainedUnificationVar
      (BU.format2 "Unconstrained unification variables %s in type signature %s; \
       please add an annotation" (show uvs) (show t));
    Options.pop()
  end

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
    list univ_name
   & typ
   & term
   & bool //true indicates that the type needs to be checked; false indicates that it is already checked
   =
  let rng = S.range_of_lbname lbname in
  let t = SS.compress t in
  let u_subst, univ_vars = SS.univ_var_opening univ_vars in
  let e = SS.subst u_subst e in
  let t = SS.subst u_subst t in
  if !dbg_Dec
  then BU.print2 "extract_let_rec_annotation lbdef=%s; lbtyp=%s\n"
                 (show e)
                 (show t);
  let env = Env.push_univ_vars env univ_vars in
  let un_arrow t =
    //Rather than use U.arrow_formals_comp, we use un_arrow here
    //since the former collapses adjacent Tot annotations, e.g.,
    //    x:t -> Tot (y:t -> M)
    // is collapsed, possibly breaking arities.
      match (SS.compress t).n with
      | Tm_arrow {bs; comp=c} ->
        Subst.open_comp bs c
      | _ ->
        raise_error rng Errors.Fatal_LetRecArgumentMismatch [
            text "Recursive functions must be introduced at arrow types.";
        ]
  in
  let reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt =
      let get_decreases c =
          U.comp_flags c |> BU.prefix_until (function DECREASES _ -> true | _ -> false)
      in
      let fallback () =
        let bs, c = U.arrow_formals_comp tarr in
        match get_decreases c with
        | Some (pfx, DECREASES d, sfx) ->
           let c = Env.comp_set_flags env c (pfx @ sfx) in
           U.arrow bs c, tarr, true
        | _ -> tarr, tarr, true
      in
      match lbtyp_opt with
      | None ->
        fallback()

      | Some annot ->
        let bs, c = un_arrow tarr in
        let n_bs = List.length bs in
        let bs', c' = N.get_n_binders env n_bs annot in
        if List.length bs' <> n_bs
        then raise_error rng Errors.Fatal_LetRecArgumentMismatch [
                 text "Arity mismatch on let rec annotation";
                 text "(explain)";
               ];
        let move_decreases d flags flags' =
          let d' =
            let s = U.rename_binders bs bs' in
            SS.subst_decreasing_order s d
          in
          let c = Env.comp_set_flags (Env.push_binders env bs) c flags in
          let tarr = U.arrow bs c in
          let c' = Env.comp_set_flags (Env.push_binders env bs') c' (DECREASES d'::flags') in
          let tannot = U.arrow bs' c' in
          tarr, tannot, true
        in
        match get_decreases c, get_decreases c' with
        | None, _ -> tarr, annot, false
        | Some (pfx, DECREASES d, sfx), Some (pfx', DECREASES d', sfx') ->
          Errors.log_issue rng Warning_DeprecatedGeneric [
              text "This definitions has multiple decreases clauses.";
              text "The decreases clause on the declaration is ignored, please remove it."
          ];
          move_decreases d (pfx@sfx) (pfx'@sfx')
        | Some (pfx, DECREASES d, sfx), None ->
          move_decreases d (pfx@sfx) (U.comp_flags c')
        | _ -> failwith "Impossible"
  in
  let extract_annot_from_body (lbtyp_opt:option typ)
    : typ
    & term
    & bool
    = let rec aux_lbdef e
        : typ & term & bool
        = let e = SS.compress e in
          match e.n with
          | Tm_meta {tm=e';meta=m} ->
            let t, e', recheck = aux_lbdef e' in
            t, { e with n = Tm_meta {tm=e'; meta=m} }, recheck

          | Tm_ascribed {tm=e'; asc=(Inr c, tac_opt, use_eq); eff_opt=lopt} ->
            if U.is_total_comp c
            then let t, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type (U.comp_result c) lbtyp_opt in
                 let e = { e with n = Tm_ascribed {tm=e';
                                                   asc=(Inr (S.mk_Total t), tac_opt, use_eq);
                                                   eff_opt=lopt} } in
                 lbtyp, e, recheck
            else raise_error rng Errors.Fatal_UnexpectedComputationTypeForLetRec [
                     text "Expected a 'let rec' to be annotated with a value type";
                     text "Got a computation type" ^/^ pp c ^/^ text "instead";
                   ]

          | Tm_ascribed {tm=e'; asc=(Inl t, tac_opt, use_eq); eff_opt=lopt} ->
            let t, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type t lbtyp_opt in
            let e = { e with n = Tm_ascribed {tm=e'; asc=(Inl t, tac_opt, use_eq); eff_opt=lopt} } in
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
              | Tm_meta {tm=body; meta=m} ->
                let t, body', recheck = aux_abs_body body in
                let body = { body with n = Tm_meta {tm=body'; meta=m} } in
                t, body, recheck

              | Tm_ascribed {asc=(Inl t, _, use_eq)} -> //no decreases clause here
                //
                //AR: In this case, the type in the ascription is moving to lbtyp
                //    if use_eq is true, then we are in trouble
                //    since we don't yet support equality in lbtyp
                //
                if use_eq
                then raise_error t Errors.Fatal_NotSupported [
                         text "Equality ascription in this case" ^/^ parens (pp t) ^/^ text "is not yet supported.";
                         text "Please use subtyping instead";
                       ];
                begin
                match lbtyp_opt with
                | Some lbtyp ->
                  lbtyp, body, false

                | None ->
                  let t = mk_arrow (mk_comp t) in
                  t, body, true
                end

              | Tm_ascribed {tm=body'; asc=(Inr c, tac_opt, use_eq); eff_opt=lopt} ->
                let tarr = mk_arrow c in
                let tarr, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt in
                let n_bs = List.length bs in
                let bs', c = N.get_n_binders env n_bs tarr in
                if List.length bs' <> n_bs
                then failwith "Impossible"
                else let subst = U.rename_binders bs' bs in
                     let c = SS.subst_comp subst c in
                     let body = { body with n = Tm_ascribed {tm=body';
                                                             asc=(Inr c, tac_opt, use_eq);
                                                             eff_opt=lopt} } in
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
            
          | _ ->
            raise_error e Errors.Fatal_UnexpectedComputationTypeForLetRec [
                text "The definition of a 'let rec' must be a function literal";
                text "Got" ^/^ pp e ^/^ text "instead";
            ]
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
//              then failwith (BU.format2 "Expected pattern variable %s; got %s" (show x) (show y));
//              if !dbg_Pat
//              then BU.print2 "Pattern variable %s introduced at type %s\n" (show x) (Normalize.term_to_string env y.sort);
//              let s = Normalize.normalize [Env.Beta] env y.sort in
//              let x = {x with sort=s} in
//              pkg (Pat_var x)

//            | Pat_wild x, Tm_name y ->
//              if bv_eq x y |> not
//              then failwith (BU.format2 "Expected pattern variable %s; got %s" (show x) (show y));
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

//                | _ -> failwith (BU.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" (show p) (show e)) in

//              match_args [] args argpats

//           | _ ->
//            failwith (BU.format3
//                            "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
//                            (Range.string_of_range qq.p)
//                            (show qq)
//                            (show exp))
//    in
//    aux p exp

 let rec decorated_pattern_as_term (pat:pat) : list bv & term =
    let mk f : term = mk f pat.p in

    let pat_as_arg (p, i) =
        let vars, te = decorated_pattern_as_term p in
        vars, (te, S.as_aqual_implicit i)
    in
    match pat.v with
    | Pat_constant c ->
        [], mk (Tm_constant c)

    | Pat_var x  ->
        [x], mk (Tm_name x)

    | Pat_cons(fv, us_opt, pats) ->
        let vars, args = pats |> List.map pat_as_arg |> List.unzip in
        let vars = List.flatten vars in
        let head = Syntax.fv_to_tm fv in
        let head = 
          match us_opt with
          | None -> head
          | Some us -> S.mk_Tm_uinst head us
        in
        vars,  mk (Tm_app {hd=head; args})

    | Pat_dot_term eopt ->
        (match eopt with
         | None -> failwith "TcUtil::decorated_pattern_as_term: dot pattern not resolved"
         | Some e -> [], e)


(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)

let comp_univ_opt c =
    match c.n with
    | Total _ | GTotal _ -> None
    | Comp c ->
      match c.comp_univs with
      | [] -> None
      | hd::_ -> Some hd

let lcomp_univ_opt lc = lc |> TcComm.lcomp_comp |> (fun (c, g) -> comp_univ_opt c, g)

let destruct_wp_comp c : (universe & typ & typ) = U.destruct_comp c

let mk_comp_l mname u_result result wp flags =
  mk_Comp ({ comp_univs=[u_result];
             effect_name=mname;
             result_typ=result;
             effect_args=[S.as_arg wp];
             flags=flags})

let mk_comp md = mk_comp_l md.mname

let effect_args_from_repr (repr:term) (is_layered:bool) (r:Range.range) : list term =
  let err () =
    raise_error r Errors.Fatal_UnexpectedEffect [
        text "Could not get effect args from repr" ^/^ pp repr ^/^ text "with is_layered=" ^^ pp is_layered
    ]
  in
  let repr = SS.compress repr in
  if is_layered
  then match repr.n with
       | Tm_app {args=_::is} -> is |> List.map fst
       | _ -> err ()
  else match repr.n with
       | Tm_arrow {comp=c} -> c |> U.comp_eff_name_res_and_args |> (fun (_, _, args) -> args |> List.map fst)
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
    then S.mk_Total a
    else let wp =
           if Options.lax()
           && Options.ml_ish() //NS: Disabling this optimization temporarily
           then S.tun
           else let ret_wp = ed |> U.get_return_vc_combinator in
                mk_Tm_app
                  (inst_effect_fun_with [u_a] env ed ret_wp)
                  [S.as_arg a; S.as_arg e]
                  e.pos in
         mk_comp ed u_a a wp [RETURN]
  in
  if !dbg_Return
  then BU.print3 "(%s) returning %s at comp type %s\n"
                    (Range.string_of_range e.pos)
                    (show e)
                    (N.comp_to_string env c);
  c

let label reason r f : term =
    mk (Tm_meta {tm=f; meta=Meta_labeled(reason, r, false)}) f.pos

let label_opt env reason r f = match reason with
    | None -> f
    | Some reason ->
        if not <| Env.should_verify env
        then f
        else label (reason()) r f

let label_guard r reason (g:guard_t) = match g.guard_f with
    | Trivial -> g
    | NonTrivial f -> {g with guard_f=NonTrivial (label reason r f)}

let lift_comp env (c:comp_typ) lift : comp & guard_t =
  ({ c with flags = [] }) |> S.mk_Comp |> lift.mlift_wp env

let join_effects env l1_in l2_in =
  let l1, l2 = Env.norm_eff_name env l1_in, Env.norm_eff_name env l2_in in
  match Env.join_opt env l1 l2 with
  | Some (m, _, _) -> m
  | None ->
    match Env.exists_polymonadic_bind env l1 l2 with
    | Some (m, _) -> m
    | None ->
      raise_error env Errors.Fatal_EffectsCannotBeComposed [
          text "Effects" ^/^ pp l1_in ^/^ text "and" ^/^ pp l2_in ^/^ text "cannot be composed"
      ]

let join_lcomp env c1 c2 =
  if TcComm.is_total_lcomp c1
  && TcComm.is_total_lcomp c2
  then C.effect_Tot_lid
  else join_effects env c1.eff_name c2.eff_name

// GM, 2023/01/30: This is here to make c2 well-scoped in lift_comps_sep_guards
// below. Is it needed to push a null_binder, as below, when b is None? Not for
// scoping, at least.
let maybe_push (env : Env.env) (b : option bv) : Env.env =
  match b with
  | None -> env
  | Some bv -> Env.push_bv env bv

(*
 * This functions returns the two lifted computations,
 *   and guards for each of them
 *
 * The separate guards are important when it is called from the pattern matching code (bind_cases)
 *   where the two guards are weakened using different branch conditions
 *)
let lift_comps_sep_guards env c1 c2 (b:option bv) (for_bind:bool)
: lident & comp & comp & guard_t & guard_t =
  let c1 = Env.unfold_effect_abbrev env c1 in
  let env2 = maybe_push env b in
  let c2 = Env.unfold_effect_abbrev env2 c2 in
  match Env.join_opt env c1.effect_name c2.effect_name with
  | Some (m, lift1, lift2) ->
    let c1, g1 = lift_comp env c1 lift1 in
    let c2, g2 =
      if not for_bind then lift_comp env2 c2 lift2
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
    raise_error env Errors.Fatal_EffectsCannotBeComposed [
      text "Effects" ^/^ pp c1.effect_name ^/^ text "and" ^/^ pp c2.effect_name ^/^ text "cannot be composed"
    ]

let lift_comps env c1 c2 (b:option bv) (for_bind:bool)
  : lident & comp & comp & guard_t =
  let l, c1, c2, g1, g2 = lift_comps_sep_guards
    env
    c1
    c2
    b
    for_bind in
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
    then S.mk_Total result
    else mk_comp_l mname u_result result S.tun flags

let is_function t = match (compress t).n with
    | Tm_arrow _ -> true
    | _ -> false

let close_wp_comp env bvs (c:comp) =
    def_check_scoped c.pos "close_wp_comp" (Env.push_bvs env bvs) c;
    if U.is_ml_comp c then c
    else if Options.lax()
    && Options.ml_ish() //NS: disabling this optimization temporarily
    then c
    else begin
            (*
             * We make an environment containing all the BVs so the calls
             * to env.universe_of and unfold_effect_abbrev below are properly scoped.
             * Note: this only works since variables in the environment are named and
             * fresh, so it is OK to use a larger environment to check a term.
             *)
            let env_bvs = Env.push_bvs env bvs in
            let close_wp u_res md res_t bvs wp0 =
              let close = md |> U.get_wp_close_combinator |> must in
              List.fold_right (fun x wp ->
                  let bs = [mk_binder x] in
                  let us = u_res::[env.universe_of env_bvs x.sort] in
                  let wp = U.abs bs wp (Some (U.mk_residual_comp C.effect_Tot_lid None [TOTAL])) in
                  mk_Tm_app (inst_effect_fun_with us env md close) [S.as_arg res_t; S.as_arg x.sort; S.as_arg wp] wp0.pos)
              bvs wp0 in
            let c = Env.unfold_effect_abbrev env_bvs c in
            let u_res_t, res_t, wp = destruct_wp_comp c in
            let md = Env.get_effect_decl env c.effect_name in
            let wp = close_wp u_res_t md res_t bvs wp in
            (*
             * AR: a note re. comp flags:
             *     earlier this code was setting the flags of the closed computation as c.flags
             *
             *     cf. #2352, when this code was called from
             *       weaken_result_typ -> bind -> maybe_capture_unit_refinement,
             *     the input comp was Tot had RETURN flag set, which means the closed comp also had RETURN
             *
             *     so when this closed computation was later `bind` with another comp,
             *       we simply dropped the it (see code path in bind under U.is_trivial_wp)
             *     thereby losing the captured refinement
             *
             *     in general, comp flags need some cleanup
             *)
            mk_comp md u_res_t c.result_typ wp
              (c.flags |> List.filter (function | MLEFFECT | SHOULD_NOT_INLINE -> true | _ -> false))
        end

let close_wp_lcomp env bvs (lc:lcomp) : lcomp =
  let bs = bvs |> List.map S.mk_binder in
  lc |>
  TcComm.apply_lcomp
    (close_wp_comp env bvs)
    (fun g -> g |> Env.close_guard env bs |> close_guard_implicits env false bs)

//
// Apply substitutive close combinator for indexed effects
//
// The effect indices binders in the close combinator are arrows,
//   so we abstract b_bv on the effect args for the substitutions
//
let substitutive_indexed_close_substs (env:env)
  (close_bs:binders)
  (a:typ)
  (b_bv:bv)
  (ct_args:args)
  (num_effect_params:int)
  (r:Range.range)

  : list subst_elt =
  
  let debug = !dbg_LayeredEffectsApp in

  // go through the binders bs and aggregate substitutions
  let close_bs, subst =
    let a_b::b_b::close_bs = close_bs in
    close_bs, [NT (a_b.binder_bv, a); NT (b_b.binder_bv, b_bv.sort)] in
  
  let close_bs, subst, ct_args =
    let eff_params_bs, close_bs = List.splitAt num_effect_params close_bs in
    let ct_eff_params_args, ct_args = List.splitAt num_effect_params ct_args in
    close_bs,
    (subst@
     List.map2 (fun b (arg, _) -> NT (b.binder_bv, arg)) eff_params_bs ct_eff_params_args),
    ct_args in

  let close_bs, _ = List.splitAt (List.length close_bs - 1) close_bs in
  List.fold_left2 (fun ss b (ct_arg, _) ->
    ss@[NT (b.binder_bv, U.abs [b_bv |> S.mk_binder] ct_arg None)]
  ) subst close_bs ct_args

//
// The caller ensures that the effect has the close combinator defined
//
let close_layered_comp_with_combinator (env:env) (bvs:list bv) (c:comp) : comp =
  let r = c.pos in
  
  let env_bvs = Env.push_bvs env bvs in
  let ct = Env.unfold_effect_abbrev env_bvs c in
  let ed = Env.get_effect_decl env_bvs ct.effect_name in
  let num_effect_params =
    match ed.signature with
    | Layered_eff_sig (n, _) -> n
    | _ -> raise_error r Errors.Fatal_UnexpectedEffect "mk_indexed_close called with a non-indexed effect"
  in
  let close_ts = U.get_layered_close_combinator ed |> must in
  let effect_args = List.fold_right (fun x args ->
    let u_a = List.hd ct.comp_univs in
    let u_b = env.universe_of env_bvs x.sort in
    let _, close_t = Env.inst_tscheme_with close_ts [u_a; u_b] in
    let close_bs, close_body, _ = U.abs_formals close_t in
    let ss = substitutive_indexed_close_substs
      env_bvs close_bs ct.result_typ x args num_effect_params r in
    match (SS.compress (SS.subst ss close_body)).n with
    | Tm_app { args = _::args} -> args
    | _ -> raise_error r Errors.Fatal_UnexpectedEffect "Unexpected close combinator shape"
  ) bvs ct.effect_args in
  S.mk_Comp {ct with effect_args}

let close_layered_lcomp_with_combinator env bvs lc =
  let bs = bvs |> List.map S.mk_binder in
  lc |>
  TcComm.apply_lcomp
    (close_layered_comp_with_combinator env bvs)
    (fun g -> g |> Env.close_guard env bs |> close_guard_implicits env false bs)

(*
 * Closing of layered computations via substitution
 *)
let close_layered_lcomp_with_substitutions env bvs tms (lc:lcomp) =
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
 *     An exception is made for reifiable effects -- they are useful even if they return unit -- except when it is an layered effect, we never return layered effects
 * (c) Its head symbol is not marked irreducible (in this case inlining is not going to help, it is equivalent to having a bound variable)
 * (d) It's not a let rec, as determined by the absence of the SHOULD_NOT_INLINE flag---see issue #1362. Would be better to just encode inner let recs to the SMT solver properly
 *)
let should_return env eopt lc =
  let lc_is_unit_or_effectful =
    //if lc.res_typ is not an arrow, arrow_formals_comp returns Tot lc.res_typ
    let c = lc.res_typ |> U.arrow_formals_comp |> snd in
    if Env.is_reifiable_comp env c
    then
      //
      //if c (the comp of the result type of lc) is reifiable
      //  we always return it, unless it is a non TAC layered effect
      //      
      let c_eff_name = c |> U.comp_effect_name |> Env.norm_eff_name env in
      if is_pure_or_ghost_lcomp lc &&  //check that lc was pure or ghost
         lid_equals c_eff_name C.effect_TAC_lid  //and c is TAC
      then false  //then not effectful (i.e. return)
      else c_eff_name |> Env.is_layered_effect env
    else
         //
         // if c is not a reifiable effect, check that it is pure or ghost
         //
         if U.is_pure_or_ghost_comp c
         then
              //
              // if it is pure or ghost, it must be a non-singleton
              //
              // adding a bit of normalization to unfold abbreviations
              //
              c |> U.comp_result |> N.unfold_whnf env |> U.is_unit
         else 
              //
              // if it is not pure or ghost, don't return
              //
              true in

  match eopt with
  | None -> false //no term to return
  | Some e ->
    TcComm.is_pure_or_ghost_lcomp lc           &&  //condition (a), (see above)
    not lc_is_unit_or_effectful                &&  //condition (b)
    (let head, _ = U.head_and_args_full e in
     match (U.un_uinst head).n with
     | Tm_fvar fv ->  not (Env.is_irreducible env (lid_of_fv fv))  //condition (c)
     | _ -> true)                               &&
   not (should_not_inline_lc lc)                   //condition (d)

//
// apply a substitutive indexed bind (including a polymonadic bind)
//
// bs are the opened binders in the type of the bind
//
let substitutive_indexed_bind_substs env
  (m_ed n_ed p_ed:S.eff_decl)
  (bs:binders)
  (binder_kinds:list indexed_effect_binder_kind)
  (ct1:comp_typ) (b:option bv) (ct2:comp_typ)
  (r1:Range.range)
  (num_effect_params:int)
  (has_range_binders:bool)

  : list subst_elt & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  let bind_name () =
    if debug
    then BU.format3 "(%s, %s) |> %s"
           (m_ed.mname |> Ident.ident_of_lid |> string_of_id)
           (n_ed.mname |> Ident.ident_of_lid |> string_of_id)
          (p_ed.mname |> Ident.ident_of_lid |> string_of_id)
    else "" in

  // we are going to move through the binders and aggregate their substitutions

  let bs, binder_kinds, subst =
    let a_b::b_b::bs = bs in
    bs,
    List.splitAt 2 binder_kinds |> snd,
    [NT (a_b.binder_bv, ct1.result_typ); NT (b_b.binder_bv, ct2.result_typ)] in

  // effect parameters
  let bs, binder_kinds, subst, guard, args1, args2 =
    if num_effect_params = 0
    then bs, binder_kinds, subst, Env.trivial_guard, ct1.effect_args, ct2.effect_args
    else // peel off num effect params args from both c1 and c2,
         //   and equate them
         let split (l:list 'a) = List.splitAt num_effect_params l in
         let eff_params_bs, bs = split bs in
         let _, binder_kinds = split binder_kinds in
         let param_args1, args1 = split ct1.effect_args in
         let param_args2, args2 = split ct2.effect_args in
         let g = List.fold_left2 (fun g (arg1, _) (arg2, _) ->
           Env.conj_guard g
             (Rel.layered_effect_teq env arg1 arg2 (Some "effect param bind"))
         ) Env.trivial_guard param_args1 param_args2 in
         let param_subst = List.map2 (fun b (arg, _) ->
           NT (b.binder_bv, arg)) eff_params_bs param_args1 in
         bs, binder_kinds, subst@param_subst, g, args1, args2 in

  // f binders
  let bs, binder_kinds, subst =
    let m_num_effect_args = List.length args1 in
    let f_bs, bs = List.splitAt m_num_effect_args bs in
    let f_subst = List.map2 (fun f_b (arg:S.arg) -> NT (f_b.binder_bv, fst arg)) f_bs args1 in
    bs,
    List.splitAt m_num_effect_args binder_kinds |> snd,
    subst@f_subst in

  // g binders
  // a bit more involved since g binders may be substitutive or no abstraction
  let bs, subst, guard =
    let n_num_effect_args = List.length args2 in
    let g_bs, bs = List.splitAt n_num_effect_args bs in
    let g_bs_kinds = List.splitAt n_num_effect_args binder_kinds |> fst in

    let x_bv =
      match b with
      | None -> S.null_bv ct1.result_typ
      | Some x -> x in

    let subst, guard =
      List.fold_left2 (fun (ss, g) (g_b, g_b_kind) (arg:S.arg) ->
        if g_b_kind = Substitutive_binder
        then begin
          let arg_t = U.abs [x_bv |> S.mk_binder] (fst arg) None in
          ss@[NT (g_b.binder_bv, arg_t)],
          g
        end
        else if g_b_kind = BindCont_no_abstraction_binder
        then begin
          let [uv_t], g_uv =
            Env.uvars_for_binders env [g_b] ss
              (fun b ->
               if debug
               then BU.format3 "implicit var for no abs g binder %s of %s at %s"
                      (show b)
                      (bind_name ())
                      (Range.string_of_range r1)
               else "substitutive_indexed_bind_substs.1")
               r1 in
          let g_unif = Rel.layered_effect_teq
            (Env.push_binders env [x_bv |> S.mk_binder])
            uv_t
            (arg |> fst)
            (Some "") in
          ss@[NT (g_b.binder_bv, uv_t)],
          Env.conj_guards [g; g_uv; g_unif]
        end
        else failwith "Impossible (standard bind with unexpected binder kind)"
      ) (subst, guard) (List.zip g_bs g_bs_kinds) args2 in

    bs,
    subst,
    guard in

  let bs =
    if has_range_binders
    then List.splitAt 2 bs |> snd
    else bs in

  let bs = List.splitAt (List.length bs - 2) bs |> fst in

  // create uvars for remaining bs
  List.fold_left (fun (ss, g) b ->
    let [uv_t], g_uv = Env.uvars_for_binders env [b] ss
      (fun b ->
       if debug
       then BU.format3 "implicit var for additional g binder %s of %s at %s"
              (show b)
              (bind_name ())
              (Range.string_of_range r1)
       else "substitutive_indexed_bind_substs.2") r1 in
    ss@[NT (b.binder_bv, uv_t)],
    Env.conj_guard g g_uv
  ) (subst, guard) bs

//
// Apply an ad-hoc indexed bind (uvars for all binders)
//
let ad_hoc_indexed_bind_substs env
  (m_ed n_ed p_ed:S.eff_decl)
  (bs:binders)
  (ct1:comp_typ) (b:option bv) (ct2:comp_typ)
  (r1:Range.range)
  (has_range_binders:bool)

  : list subst_elt & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  let bind_name () =
    if debug
    then BU.format3 "(%s, %s) |> %s"
           (m_ed.mname |> Ident.ident_of_lid |> string_of_id)
           (n_ed.mname |> Ident.ident_of_lid |> string_of_id)
           (p_ed.mname |> Ident.ident_of_lid |> string_of_id)
    else "" in

  let bind_t_shape_error r (s:string) =
    raise_error r Errors.Fatal_UnexpectedEffect
      (BU.format2 "bind %s does not have proper shape (reason:%s)" (bind_name ()) s)
  in

  let num_range_binders =
    if has_range_binders then 2
    else 0 in

  let a_b, b_b, rest_bs, f_b, g_b =
    if List.length bs >= num_range_binders + 4
    then let a_b::b_b::bs =bs in
         let rest_bs, f_b, g_b =
           List.splitAt (List.length bs - 2 - num_range_binders) bs
             |> (fun ((l1, l2):(binders & binders)) ->
                let _, l2 = List.splitAt num_range_binders l2 in
                l1, List.hd l2, List.hd (List.tl l2)) in
         a_b, b_b, rest_bs, f_b, g_b
    else bind_t_shape_error r1 "Either not an arrow or not enough binders" in
         
  //create uvars for rest_bs, with proper substitutions of a_b, b_b, and b_i with t1, t2, and ?ui
  let rest_bs_uvars, g_uvars =
    Env.uvars_for_binders
      env rest_bs [NT (a_b.binder_bv, ct1.result_typ); NT (b_b.binder_bv, ct2.result_typ)]
      (fun b ->
       if debug
       then BU.format3
              "implicit var for binder %s of %s at %s"
              (show b) (bind_name ()) (Range.string_of_range r1)
       else "ad_hoc_indexed_bind_substs") r1 in

  if !dbg_ResolveImplicitsHook
  then rest_bs_uvars |>
       List.iter (fun t ->
         match (SS.compress t).n with
         | Tm_uvar (u, _ ) ->
           BU.print2 "Generated uvar %s with attribute %s\n"
             (show t) (show u.ctx_uvar_meta)
         | _ -> failwith ("Impossible, expected a uvar, got : " ^ show t));

  let subst = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::b_b::rest_bs) (ct1.result_typ::ct2.result_typ::rest_bs_uvars) in

  let f_guard =  //unify c1's indices with f's indices in the bind_wp
    let f_sort_is = effect_args_from_repr
      (SS.compress f_b.binder_bv.sort)
      (U.is_layered m_ed) r1 |> List.map (SS.subst subst) in
    List.fold_left2
      (fun g i1 f_i1 ->
        if !dbg_ResolveImplicitsHook
        then BU.print2 "Generating constraint %s = %s\n"
                                   (show i1)
                                   (show f_i1);
        Env.conj_guard g (Rel.layered_effect_teq env i1 f_i1 (Some (bind_name ()))))
      Env.trivial_guard (List.map fst ct1.effect_args) f_sort_is
  in

  let g_guard =  //unify c2's indices with g's indices in the bind_wp
    let x_a =
      match b with
      | None -> S.null_binder ct1.result_typ
      | Some x -> S.mk_binder {x with sort=ct1.result_typ} in

    let g_sort_is : list term =
      match (SS.compress g_b.binder_bv.sort).n with
      | Tm_arrow {bs; comp=c} ->
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
        if !dbg_ResolveImplicitsHook
        then BU.print2 "Generating constraint %s = %s\n"
                                   (show i1)
                                   (show g_i1);
         Env.conj_guard g (Rel.layered_effect_teq env_g i1 g_i1 (Some (bind_name ()))))
      Env.trivial_guard (List.map fst ct2.effect_args) g_sort_is
    |> Env.close_guard env [x_a]
  in

  subst,
  Env.conj_guards [g_uvars; f_guard; g_guard]

(* private *)

(*
 * Build the M.return comp for an indexed effect
 *
 * Caller must ensure that ed is an indexed effect
 *)
let mk_indexed_return env (ed:S.eff_decl) (u_a:universe) (a:typ) (e:term) (r:Range.range)
  : comp & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  if debug
  then BU.print4 "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
         (Ident.string_of_lid ed.mname) (show u_a)
         (show a) (show e);

  let _, return_t = Env.inst_tscheme_with
    (ed |> U.get_return_vc_combinator)
    [u_a] in

  let return_t_shape_error r (s:string) =
    raise_error r Errors.Fatal_UnexpectedEffect [
         pp ed.mname ^/^ text ".return" ^/^ text "does not have proper shape";
         text "Reason: " ^^ text s
    ]
  in
  let a_b, x_b, rest_bs, return_typ =
    match (SS.compress return_t).n with
    | Tm_arrow {bs; comp=c} when List.length bs >= 2 ->
      let ((a_b::x_b::bs, c)) = SS.open_comp bs c in
      a_b, x_b, bs, U.comp_result c
    | _ -> return_t_shape_error r "Either not an arrow or not enough binders" in

  let rest_bs_uvars, g_uvars =
    Env.uvars_for_binders
      env rest_bs [NT (a_b.binder_bv, a); NT (x_b.binder_bv, e)]
      (fun b ->
       if debug
       then BU.format3 "implicit var for binder %s of %s at %s"
              (show b)
              (BU.format1 "%s.return" (Ident.string_of_lid ed.mname))
              (Range.string_of_range r)
       else "mk_indexed_return_env") r in

  let subst = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::x_b::rest_bs) (a::e::rest_bs_uvars) in

  let is =
    effect_args_from_repr (SS.compress return_typ) (U.is_layered ed) r
    |> List.map (SS.subst subst) in

  let c = mk_Comp ({
    comp_univs = [u_a];
    effect_name = ed.mname;
    result_typ = a;
    effect_args = is |> List.map S.as_arg;
    flags = []
  }) in

  if debug
  then BU.print1 "} c after return %s\n" (show c);

  c, g_uvars

let mk_indexed_bind env
  (m:lident) (n:lident) (p:lident) (bind_t:tscheme)
  (bind_combinator_kind:indexed_effect_combinator_kind)
  (ct1:comp_typ) (b:option bv) (ct2:comp_typ)
  (flags:list cflag) (r1:Range.range)
  (num_effect_params:int)
  (has_range_binders:bool)
  : comp & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  if debug then
    BU.print2 "Binding indexed effects: c1:%s and c2:%s {\n"
      (show (S.mk_Comp ct1)) (show (S.mk_Comp ct2));

  if !dbg_ResolveImplicitsHook
  then BU.print2 "///////////////////////////////Bind at %s/////////////////////\n\
                  with bind_t = %s\n"
                 (Range.string_of_range (Env.get_range env))
                 (Print.tscheme_to_string bind_t);

  let m_ed, n_ed, p_ed = Env.get_effect_decl env m, Env.get_effect_decl env n, Env.get_effect_decl env p in

  let bind_name () = BU.format3 "(%s, %s) |> %s"
    (m_ed.mname |> Ident.ident_of_lid |> string_of_id)
    (n_ed.mname |> Ident.ident_of_lid |> string_of_id)
    (p_ed.mname |> Ident.ident_of_lid |> string_of_id) in

  if (Env.is_erasable_effect env m &&
      not (Env.is_erasable_effect env p) &&
      None? (N.non_info_norm env ct1.result_typ)) ||
     (Env.is_erasable_effect env n &&
      not (Env.is_erasable_effect env p) &&
      None? (N.non_info_norm env ct2.result_typ))
  then raise_error r1 Errors.Fatal_UnexpectedEffect [
           text "Cannot apply bind" ^/^ doc_of_string (bind_name ()) ^/^ text "since" ^/^ pp p
             ^/^ text "is not erasable and one of the computations is informative."
         ];

  let _, bind_t = Env.inst_tscheme_with bind_t [List.hd ct1.comp_univs; List.hd ct2.comp_univs] in

  let bind_t_bs, bind_c = U.arrow_formals_comp bind_t in

  let subst, g =
    if bind_combinator_kind = Ad_hoc_combinator
    then ad_hoc_indexed_bind_substs env m_ed n_ed p_ed
           bind_t_bs ct1 b ct2 r1 has_range_binders
    else let Substitutive_combinator binder_kinds = bind_combinator_kind in
         substitutive_indexed_bind_substs env m_ed n_ed p_ed
           bind_t_bs binder_kinds ct1 b ct2 r1 num_effect_params has_range_binders in

  let bind_ct = bind_c |> SS.subst_comp subst |> Env.comp_to_comp_typ env in

  //compute the formula `bind_c.wp (fun _ -> True)` and add it to the final guard
  let fml =
    let u, wp = List.hd bind_ct.comp_univs, fst (List.hd bind_ct.effect_args) in
    Env.pure_precondition_for_trivial_post env u bind_ct.result_typ wp Range.dummyRange in

  let is : list term =  //indices of the resultant computation
    effect_args_from_repr (SS.compress bind_ct.result_typ) (U.is_layered p_ed) r1 in

  let c = mk_Comp ({
    comp_univs = ct2.comp_univs;
    effect_name = p_ed.mname;
    result_typ = ct2.result_typ;
    effect_args = List.map S.as_arg is;
    flags = flags
  }) in

  if debug
  then BU.print1 "} c after bind: %s\n" (show c);

  let guard =
    Env.conj_guards [
      g;
      Env.guard_of_guard_formula (TcComm.NonTrivial fml)]
  in

  if !dbg_ResolveImplicitsHook
  then BU.print2 "///////////////////////////////EndBind at %s/////////////////////\n\
                 guard = %s\n"
                 (Range.string_of_range (Env.get_range env))
                 (guard_to_string env guard);

  c, guard

let mk_wp_bind env (m:lident) (ct1:comp_typ) (b:option bv) (ct2:comp_typ) (flags:list cflag) (r1:Range.range)
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
  let wp_args = [
    S.as_arg t1;
    S.as_arg t2;
    S.as_arg wp1;
    S.as_arg (mk_lam wp2)]
  in
  let bind_wp, _ = md |> U.get_bind_vc_combinator in
  let wp = mk_Tm_app (inst_effect_fun_with [u_t1;u_t2] env md bind_wp) wp_args t2.pos in
  mk_comp md u_t2 t2 wp flags

let mk_bind env
  (c1:comp)
  (b:option bv)
  (c2:comp)
  (flags:list cflag)
  (r1:Range.range) : comp & guard_t =

  let env2 = maybe_push env b in
  let ct1, ct2 = Env.unfold_effect_abbrev env c1, Env.unfold_effect_abbrev env2 c2 in

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
    let ct1, ct2 = Env.comp_to_comp_typ env c1, Env.comp_to_comp_typ env2 c2 in

    let c, g_bind =
      if Env.is_layered_effect env m
      then
        let m_ed = m |> Env.get_effect_decl env in
        let num_effect_params =
          match m_ed.signature with
          | Layered_eff_sig (n, _) -> n
          | _ -> failwith "Impossible (mk_bind expected an indexed effect)" in
        let bind_t, bind_kind = m_ed |> U.get_bind_vc_combinator in
        let has_range_args = U.has_attribute m_ed.eff_attrs C.bind_has_range_args_attr in
        mk_indexed_bind env m m m bind_t (bind_kind |> must) ct1 b ct2 flags r1 num_effect_params has_range_args
      else mk_wp_bind env m ct1 b ct2 flags r1, Env.trivial_guard in
    c, Env.conj_guard g_lift g_bind

let strengthen_comp env (reason:option (unit -> list Pprint.document)) (c:comp) (f:formula) flags : comp & guard_t =
    if env.phase1 || Env.too_early_in_prims env
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
         let pure_assert_wp = S.fv_to_tm (S.lid_as_fv C.pure_assert_wp_lid None) in

         (* apply it to f, after decorating f with the reason *)
         let pure_assert_wp = mk_Tm_app
           pure_assert_wp
           [ S.as_arg <| label_opt env reason r f ]
           r
         in

         let r = Env.get_range env in

         let pure_c = S.mk_Comp ({
           comp_univs = [S.U_zero];
           effect_name = C.effect_PURE_lid;
           result_typ = S.t_unit;
           effect_args = [pure_assert_wp |> S.as_arg];
           flags = []
         }) in

         mk_bind env pure_c None c flags r

(*
 * Wrapper over mk_wp_return and mk_indexed_return
 *)
let mk_return env (ed:S.eff_decl) (u_a:universe) (a:typ) (e:term) (r:Range.range)
: comp & guard_t
= if ed |> U.is_layered
  then mk_indexed_return env ed u_a a e r
  else mk_wp_return env ed u_a a e r, Env.trivial_guard

(*
 * Return a value in eff_lid
 *)
let return_value env eff_lid u_t_opt t v =
  let u =
    match u_t_opt with
    | None -> env.universe_of env t
    | Some u -> u in
  mk_return env (Env.get_effect_decl env eff_lid) u t v v.pos

let weaken_flags flags =
    if flags |> BU.for_some (function SHOULD_NOT_INLINE -> true | _ -> false)
    then [SHOULD_NOT_INLINE]
    else flags |> List.collect (function
         | TOTAL -> [TRIVIAL_POSTCONDITION]
         | RETURN -> [PARTIAL_RETURN; TRIVIAL_POSTCONDITION]
         | f -> [f])

let weaken_comp env (c:comp) (formula:term) : comp & guard_t =
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
       let pure_assume_wp = S.fv_to_tm (S.lid_as_fv C.pure_assume_wp_lid None) in

       (* apply it to f, after decorating f with the reason *)
       let pure_assume_wp = mk_Tm_app
         pure_assume_wp
         [ S.as_arg <| formula ]
         (Env.get_range env)
       in

       let r = Env.get_range env in

       let pure_c = S.mk_Comp ({
         comp_univs = [S.U_zero];
         effect_name = C.effect_PURE_lid;
         result_typ = S.t_unit;
         effect_args = [pure_assume_wp |> S.as_arg];
         flags = []
       }) in

       mk_bind env pure_c None c (weaken_flags ct.flags) r

let weaken_precondition env lc (f:guard_formula) : lcomp =
  let weaken () =
      let c, g_c = TcComm.lcomp_comp lc in
      if Options.lax ()
      && Options.ml_ish() //NS: Disabling this optimization temporarily
      then c, g_c
      else match f with
           | Trivial -> c, g_c
           | NonTrivial f ->
             let c, g_w = weaken_comp env c f in
             c, Env.conj_guard g_c g_w
  in
  TcComm.mk_lcomp lc.eff_name lc.res_typ (weaken_flags lc.cflags) weaken

let strengthen_precondition
            (reason:option (unit -> list Pprint.document))
            env
            (e_for_debugging_only:term)
            (lc:lcomp)
            (g0:guard_t)
    : lcomp & guard_t =
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
            if Options.lax ()
            then c, g_c
            else let g0 = Rel.simplify_guard env g0 in
                 match guard_form g0 with
                 | Trivial -> c, g_c
                 | NonTrivial f ->
                   if Debug.extreme ()
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


let lcomp_has_trivial_postcondition (lc:lcomp) =
    TcComm.is_tot_or_gtot_lcomp lc
    || BU.for_some (function SOMETRIVIAL | TRIVIAL_POSTCONDITION -> true | _ -> false)
                   lc.cflags


(*
 * This is used in bind, when c1 is a Tot (x:unit{phi})
 * In such cases, e1 is inlined in c2, but we still want to capture inhabitance of phi
 *
 * For wp-effects, we do forall (x:unit{phi}). c2
 * For layered effects, we do: weaken_comp (phi[x/()]) c2
 *
 * We should make wp-effects also same as the layered effects
 *)
let maybe_capture_unit_refinement (env:env) (t:term) (x:bv) (c:comp) : comp & guard_t =
  let t = N.normalize_refinement N.whnf_steps env t in
  match t.n with
  | Tm_refine {b; phi} ->
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

let bind (r1:Range.range) (env:Env.env) (e1opt:option term) (lc1:lcomp) ((b, lc2):lcomp_with_binder) : lcomp =
  let debug f =
      if Debug.extreme () || !dbg_bind
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
      if Options.lax ()
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
            BU.print4 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n\te1=%s\n(1. end bind)\n"
            (show c1)
            (match b with
                | None -> "none"
                | Some x -> show x)
            (show c2)
            (match e1opt with
             | None -> "none"
             | Some e1 -> show e1));
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
          let try_simplify () : either (comp & guard_t & string) string =
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
                            (show c));
            c, g
          | Inr reason ->
            debug (fun () ->
                BU.print1 "(2) bind: Not simplified because %s\n" reason);

            let mk_bind c1 b c2 g =  (* AR: end code for inlining pure and ghost terms *)
              let c, g_bind = mk_bind env c1 b c2 bind_flags r1 in
              c, Env.conj_guard g g_bind in

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
                 //do one optimization:
																	
																	//if c1 is already a return or a
																	//partial return, then it already provides this equality,
																	//so no need to add it again and instead generate
                 //
                 //    M.bind (lift_(Pure/Ghost)_M wp1)
                 //           (lift_M2_M (wp2[e1/x]))
                 
																 //If the optimization does not apply,
                 //then we generate the WP mentioned at the top,
                 //i.e.
                 //
                 //    M.bind (lift_(Pure/Ghost)_M wp1)
                 //           (x == e1 ==> lift_M2_M (wp2[e1/x]))

                 if U.is_partial_return c1
                 then
                      let _ = debug (fun () ->
                        BU.print2 "(3) bind (case a): Substituting %s for %s\n" (N.term_to_string env e1) (show x)) in
                      let c2 = SS.subst_comp [NT(x,e1)] c2 in
                      let g = Env.conj_guard g_c1 (Env.map_guard g_c2 (SS.subst [NT (x, e1)])) in
                      mk_bind c1 b c2 g
                 else
                      let _ = debug (fun () ->
                        BU.print2 "(3) bind (case b): Adding equality %s = %s\n" (N.term_to_string env e1) (show x)) in
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
let assume_result_eq_pure_term_in_m env (m_opt:option lident) (e:term) (lc:lcomp) : lcomp =
  (*
   * AR: m is the effect that we are going to do return in
   *)
  let m =
    if m_opt |> is_none || is_ghost_effect env lc.eff_name
    then C.effect_PURE_lid
    else m_opt |> must in

  let flags =
    if TcComm.is_total_lcomp lc then RETURN::lc.cflags else PARTIAL_RETURN::lc.cflags in

  let refine () : comp & guard_t =
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
           then let retc = Env.comp_to_comp_typ env retc in
                let retc = {retc with effect_name=C.effect_GHOST_lid; flags=flags} in
                S.mk_Comp retc, g_c
           else Env.comp_set_flags env retc flags, g_c
       else //AR: augment c's post-condition with a M.return
            let c = Env.unfold_effect_abbrev env c in
            let t = c.result_typ in
            let c = mk_Comp c in
            let x = S.new_bv (Some t.pos) t in
            let xexp = S.bv_to_name x in
            let env_x = Env.push_bv env x in
            let ret, g_ret = return_value env_x m (Some u_t) t xexp in
            let ret = TcComm.lcomp_of_comp <| Env.comp_set_flags env_x ret [PARTIAL_RETURN] in
            let eq = U.mk_eq2 u_t t xexp e in
            let eq_ret = weaken_precondition env_x ret (NonTrivial eq) in
            let bind_c, g_bind = TcComm.lcomp_comp (bind e.pos env None (TcComm.lcomp_of_comp c) (Some x, eq_ret)) in
            Env.comp_set_flags env bind_c flags, Env.conj_guards [g_c; g_ret; g_bind]
  in

  if should_not_inline_lc lc
  then raise_error e Errors.Fatal_UnexpectedTerm  [
         text "assume_result_eq_pure_term cannot inline an non-inlineable lc : " ^^ pp e;
       ]

  else let c, g = refine () in
       TcComm.lcomp_of_comp_guard c g

let maybe_assume_result_eq_pure_term_in_m env (m_opt:option lident) (e:term) (lc:lcomp) : lcomp =
  let should_return =
      not env.phase1
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
        (e1opt:option term)
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

let fvar_env env lid =  S.fvar (Ident.set_lid_range lid (Env.get_range env)) None

//
// Apply substitutive ite combinator for indexed effects
//
let substitutive_indexed_ite_substs (env:env)
  (k:S.indexed_effect_combinator_kind)
  (bs:binders)
  (a:typ)
  (p:term)
  (ct_then:comp_typ)
  (ct_else:comp_typ)
  (num_effect_params:int)
  (r:Range.range)

  : list subst_elt & guard_t =
  
  let debug = !dbg_LayeredEffectsApp in

  // go through the binders bs and aggregate substitutions and guards

  let bs, subst =
    let a_b::bs = bs in
    bs, [NT (a_b.binder_bv, a)] in

  // effect parameters
  let bs, subst, guard, args1, args2 =
    if num_effect_params = 0
    then bs, subst, Env.trivial_guard, ct_then.effect_args, ct_else.effect_args
    else // peel off effect parameters from ct_then and ct_else,
         //   and equate them
         let split (l:list 'a) = List.splitAt num_effect_params l in
         let eff_params_bs, bs = split bs in
         let param_args1, args1 = split ct_then.effect_args in
         let param_args2, args2 = split ct_else.effect_args in
         let g = List.fold_left2 (fun g (arg1, _) (arg2, _) ->
           Env.conj_guard g
             (Rel.layered_effect_teq env arg1 arg2 (Some "effect param ite"))
         ) Env.trivial_guard param_args1 param_args2 in
         let param_subst = List.map2 (fun b (arg, _) ->
           NT (b.binder_bv, arg)) eff_params_bs param_args1 in
         bs, subst@param_subst, g, args1, args2 in

  // f binders
  let bs, subst =
    let m_num_effect_args = List.length args1 in
    let f_bs, bs = List.splitAt m_num_effect_args bs in
    let f_subst = List.map2 (fun f_b (arg, _) -> NT (f_b.binder_bv, arg)) f_bs args1 in
    bs, subst@f_subst in

  // g binders
  let bs, subst, guard =
    if Substitutive_combinator? k
    then begin
      let n_num_effect_args = List.length args2 in
      let g_bs, bs = List.splitAt n_num_effect_args bs in
      let g_subst = List.map2 (fun g_b (arg, _) -> NT (g_b.binder_bv, arg)) g_bs args2 in
      bs, subst@g_subst, guard
    end
    else if Substitutive_invariant_combinator? k
    then begin
      bs,
      subst,
      List.fold_left2 (fun guard (arg1, _) (arg2, _) ->
        Env.conj_guard guard
          (Rel.layered_effect_teq env arg1 arg2 (Some "substitutive_inv ite args"))
      ) guard args1 args2
    end
    else failwith "Impossible (substitutive_indexed_ite: unexpected k)" in

  let bs, [_; _; p_b] = List.splitAt (List.length bs - 3) bs in

  let subst, g =
    List.fold_left (fun (subst, g) b ->
    let [uv_t], g_uv = Env.uvars_for_binders env [b] subst
      (fun b ->
       if debug
       then BU.format3 "implicit var for additional ite binder %s of %s at %s)"
              (show b)
              (string_of_lid ct_then.effect_name)
             (Range.string_of_range r)
       else "substitutive_indexed_ite_substs")
      r in
    subst@[NT (b.binder_bv, uv_t)],
    Env.conj_guard g g_uv) (subst, guard) bs in

  subst@[NT (p_b.binder_bv, p)],
  g

let ad_hoc_indexed_ite_substs (env:env)
  (bs:binders)
  (a:typ)
  (p:term)
  (ct_then:comp_typ)
  (ct_else:comp_typ)
  (r:Range.range)

  : list subst_elt & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  let conjunction_name () =
    if debug then BU.format1 "%s.conjunction" (string_of_lid ct_then.effect_name)
    else "" in

  let conjunction_t_error #a r (s:string) : a =
    raise_error r Errors.Fatal_UnexpectedEffect [
      text "Conjunction" ^^ pp ct_then.effect_name ^^ text "does not have proper shape.";
      text "Reason: " ^^ text s;
    ]
  in
  let a_b, rest_bs, f_b, g_b, p_b =
    if List.length bs >= 4
    then let a_b::bs = bs in
         let rest_bs, [f_b; g_b; p_b] = List.splitAt (List.length bs - 3) bs in
         a_b, rest_bs, f_b, g_b, p_b
    else conjunction_t_error r "Either not an abstraction or not enough binders" in

  let rest_bs_uvars, g_uvars =
    Env.uvars_for_binders
      env rest_bs [NT (a_b.binder_bv, a)]
      (fun b ->
       if debug
       then BU.format3
              "implicit var for binder %s of %s:conjunction at %s"
              (show b) (Ident.string_of_lid ct_then.effect_name)
              (r |> Range.string_of_range)
       else "ad_hoc_indexed_ite_substs") r in

  let substs = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::(rest_bs@[p_b])) (a::(rest_bs_uvars@[p])) in

  let f_guard =
    let f_sort_is =
      match (SS.compress f_b.binder_bv.sort).n with
      | Tm_app {args=_::is} ->
        is |> List.map fst |> List.map (SS.subst substs)
      | _ -> conjunction_t_error r "f's type is not a repr type" in
    List.fold_left2
      (fun g i1 f_i ->
       Env.conj_guard
         g
         (Rel.layered_effect_teq env i1 f_i (Some (conjunction_name ()))))
      Env.trivial_guard (List.map fst ct_then.effect_args) f_sort_is in

  let g_guard =
    let g_sort_is =
      match (SS.compress g_b.binder_bv.sort).n with
      | Tm_app {args=_::is} ->
        is |> List.map fst |> List.map (SS.subst substs)
      | _ -> conjunction_t_error r "g's type is not a repr type" in
    List.fold_left2
      (fun g i2 g_i -> Env.conj_guard g (Rel.layered_effect_teq env i2 g_i (Some (conjunction_name ()))))
      Env.trivial_guard (List.map fst ct_else.effect_args) g_sort_is in

  substs,
  Env.conj_guards [g_uvars; f_guard; g_guard]

let mk_layered_conjunction env (ed:S.eff_decl) (u_a:universe) (a:term) (p:typ) (ct1:comp_typ) (ct2:comp_typ) (r:Range.range)
: comp & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  let conjunction_t_error #a r (s:string) : a =
    raise_error r Errors.Fatal_UnexpectedEffect [
      text "Conjunction" ^^ pp ct1.effect_name ^^ text "does not have proper shape.";
      text "Reason: " ^^ text s;
    ]
  in

  let conjunction, kind =
    let ts, kopt = ed |> U.get_layered_if_then_else_combinator |> must in
    let _, conjunction = Env.inst_tscheme_with ts [u_a] in
    conjunction, kopt |> must in

  let bs, body, _ = U.abs_formals conjunction in

  if debug then
    BU.print2 "layered_ite c1: %s and c2: %s {\n"
      (ct1 |> S.mk_Comp |> show)
      (ct2 |> S.mk_Comp |> show);

  let substs, g =
    if kind = Ad_hoc_combinator
    then ad_hoc_indexed_ite_substs env bs a p ct1 ct2 r
    else let num_effect_params =
           match ed.signature with
           | Layered_eff_sig (n, _) -> n
           | _ -> failwith "Impossible!" in
        substitutive_indexed_ite_substs env kind bs a p ct1 ct2 num_effect_params r in
    
  let body = SS.subst substs body in

  let is =
    match (SS.compress body).n with
    | Tm_app {args=a::args} -> List.map fst args
    | _ -> conjunction_t_error r "body is not a repr type" in

  let c = mk_Comp ({
    comp_univs = [u_a];
    effect_name = ed.mname;
    result_typ = a;
    effect_args = is |> List.map S.as_arg;
    flags = []
  }) in

  if debug then BU.print_string "\n}\n";

  c, g

(*
 * For non-layered effects, just apply the if_then_else combinator
 *)
let mk_non_layered_conjunction env (ed:S.eff_decl) (u_a:universe) (a:term) (p:typ) (ct1:comp_typ) (ct2:comp_typ) (_:Range.range)
: comp & guard_t =
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
               (fvar_env env C.false_lid)
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
let get_neg_branch_conds (branch_conds:list formula)
  : list formula & formula
  = branch_conds
    |> List.fold_left (fun (conds, acc) g ->
        let cond = U.mk_conj acc (g |> U.b2t |> U.mk_neg) in
        (conds@[cond]), cond) ([U.t_true], U.t_true)
    |> fst
    |> (fun l -> List.splitAt (List.length l - 1) l)  //the length of the list is at least 1
    |> (fun (l1, l2) -> l1, List.hd l2)

(*
 * The formula in each element of lcases is the individual branch guard, a boolean
 *
 * This function returns a computation type for the match expression, though
 * without considering the scrutinee expression (that is the job of tc_match).
 * The most interesting bit is its WP, which combines the WP for each branch
 * under the appropriate reachability hypothesis (see also get_neg_branch_conds
 * above). It also includes a `False` obligation under the hypothesis that no
 * branch matches: i.e. the exhaustiveness check.
 *)
let bind_cases env0 (res_t:typ)
  (lcases:list (formula & lident & list cflag & (bool -> lcomp)))
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
        if Options.lax()
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
             * The rest of the list will be used to weaken the lift guards when combining the
             * branches (for layered effects, lift guards can be non-trivial). Note that
             * we don't need to do this to combine cases, because the shape of if_then_else
             *   (p ==> ...) /\ (not p ==> ...)
             * already takes care of it
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
                    cthen |> Env.comp_to_comp_typ env, celse |> Env.comp_to_comp_typ env,
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

let check_comp env (use_eq:bool) (e:term) (c:comp) (c':comp) : term & comp & guard_t =
  def_check_scoped c.pos "check_comp.c" env c;
  def_check_scoped c'.pos "check_comp.c'" env c';
  if Debug.extreme () then
    BU.print4 "Checking comp relation:\n%s has type %s\n\t %s \n%s\n"
            (show e)
            (show c)
            (if use_eq then "$:" else "<:")
            (show c');
  let f = if use_eq then Rel.eq_comp else Rel.sub_comp in
  match f env c c' with
    | None ->
        if use_eq
        then Err.computed_computation_type_does_not_match_annotation_eq env (Env.get_range env) e c c'
        else Err.computed_computation_type_does_not_match_annotation env (Env.get_range env) e c c'
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
           raise_error c Errors.Fatal_EffectCannotBeReified
                        (BU.format1 "Effect %s is marked total but does not have a repr" (show c_lid))
         | Some tm -> env.universe_of env tm

let check_trivial_precondition_wp env c =
  let ct = c |> Env.unfold_effect_abbrev env in
  let md = Env.get_effect_decl env ct.effect_name in
  let u_t, t, wp = destruct_wp_comp ct in
  let vc = mk_Tm_app
    (inst_effect_fun_with [u_t] env md (md |> U.get_wp_trivial_combinator |> must))
    [S.as_arg t; S.as_arg wp]
    (Env.get_range env)
  in

  ct, vc, Env.guard_of_guard_formula <| NonTrivial vc

//Decorating terms with monadic operators
let maybe_lift env e c1 c2 t =
    let m1 = Env.norm_eff_name env c1 in
    let m2 = Env.norm_eff_name env c2 in
    if Ident.lid_equals m1 m2
    || (U.is_pure_effect c1 && U.is_ghost_effect c2)
    || (U.is_pure_effect c2 && U.is_ghost_effect c1)
    then e
    else mk (Tm_meta {tm=e; meta=Meta_monadic_lift(m1, m2, t)}) e.pos

let maybe_monadic env e c t =
    let m = Env.norm_eff_name env c in
    if is_pure_or_ghost_effect env m
    || Ident.lid_equals m C.effect_Tot_lid
    || Ident.lid_equals m C.effect_GTot_lid //for the cases in prims where Pure is not yet defined
    then e
    else mk (Tm_meta {tm=e; meta=Meta_monadic (m, t)}) e.pos

let coerce_with (env:Env.env)
                (e : term) (lc : lcomp) // original term and its computation type
                (f : lident) // coercion
                (us : universes) (eargs : args) // extra arguments to coertion
                (comp2 : comp) // new result computation type
                : term & lcomp =
    match Env.try_lookup_lid env f with
    | Some _ ->
        if !dbg_Coercions then
            BU.print1 "Coercing with %s!\n" (Ident.string_of_lid f);
        let lc2 = TcComm.lcomp_of_comp <| comp2 in
        let lc_res = bind e.pos env (Some e) lc (None, lc2) in
        let coercion = S.fvar (Ident.set_lid_range f e.pos) None in
        let coercion = S.mk_Tm_uinst coercion us in

        //
        //Creating the coerced term:
        //  If lc is pure or ghost, then just create the application node
        //  Else create let x = e in f x
        //    with appropriate meta monadic nodes
        //
        let e =
          if TcComm.is_pure_or_ghost_lcomp lc
          then mk_Tm_app coercion (eargs@[S.as_arg e]) e.pos
          else let x = S.new_bv (Some e.pos) lc.res_typ in
               let e2 = mk_Tm_app coercion (eargs@[x |> S.bv_to_name |> S.as_arg]) e.pos in
               let e = maybe_lift env e lc.eff_name lc_res.eff_name lc.res_typ in
               let e2 = maybe_lift (Env.push_bv env x) e2 lc2.eff_name lc_res.eff_name lc2.res_typ in
               let lb = U.mk_letbinding (Inl x) [] lc.res_typ lc_res.eff_name e [] e.pos in
               let e = mk (Tm_let {lbs=(false, [lb]); body=SS.close [S.mk_binder x] e2}) e.pos in
               maybe_monadic env e lc_res.eff_name lc_res.res_typ in
        e, lc_res
    | None ->
        Errors.log_issue e Errors.Warning_CoercionNotFound
                                (BU.format1 "Coercion %s was not found in the environment, not coercing."
                                            (string_of_lid f));
        e, lc

type isErased =
    | Yes of term
    | Maybe
    | No

let rec check_erased (env:Env.env) (t:term) : isErased =
  let norm' = N.normalize [Beta; Eager_unfolding;
                           UnfoldUntil delta_constant;
                           Exclude Zeta; Primops;
                           Unascribe; Unmeta; Unrefine;
                           Weak; HNF; Iota]
  in
  let t = norm' env t in
  let h, args = U.head_and_args t in
  let h = U.un_uinst h in
  let r =
    match (SS.compress h).n, args with
    | Tm_fvar fv, [(a, _)] when S.fv_eq_lid fv C.erased_lid ->
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
    | Tm_match {brs=branches}, _ ->
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
                 |> elems // GGG: bad, order-depending
                 |> Env.push_bvs env) with
          | No -> No
          | _ -> Maybe) No


    (* Anything else cannot be `erased` *)
    | _ ->
      No
  in
  (* if Debug.any () then *)
  (*   BU.print2 "check_erased (%s) = %s\n" *)
  (*     (show t) *)
  (*     (match r with *)
  (*      | Yes a -> "Yes " ^ show a *)
  (*      | Maybe -> "Maybe" *)
  (*      | No -> "No"); *)
  r

let rec first_opt (f : 'a -> option 'b) (xs : list 'a) : option 'b =
  match xs with
  | [] -> None
  | x::xs -> BU.catch_opt (f x) (fun () -> first_opt f xs)

let (let?) = BU.bind_opt
let bool_guard (b:bool) : option unit =
  if b then Some () else None

let find_coercion (env:Env.env) (checked: lcomp) (exp_t: typ) (e:term)
: option (term & lcomp & guard_t)
// returns coerced term, new lcomp type, and guard
// or None if no coercion applied
=
 Errors.with_ctx "find_coercion" (fun () ->
  let is_type t =
      let t = N.unfold_whnf env t in
      let t = U.unrefine t in (* mostly to catch `prop` too *)
      match (SS.compress t).n with
      | Tm_type _ -> true
      | _ -> false
  in
  let rec head_of (t : term) : term =
      match (compress t).n with
      | Tm_app {hd=t}
      | Tm_match {scrutinee=t}
      | Tm_abs {body=t}
      | Tm_ascribed {tm=t}
      | Tm_meta {tm=t} -> head_of t
      | Tm_refine {b} -> head_of b.sort
      | _ -> t
  in
  let is_head_defined t =
    let h = head_of t in
    let h = SS.compress h in
    Tm_fvar? h.n || Tm_uinst? h.n || Tm_type? h.n
  in

  let head_unfold env t = N.unfold_whnf' [Unascribe; Unmeta; Unrefine] env t in

  (* Bail out early if either the computed or expected type are not
  defined at the head *)
  bool_guard (is_head_defined exp_t && is_head_defined checked.res_typ);?

  (* The computed type for `e`. *)
  let computed_t = head_unfold env checked.res_typ in
  let head, args = U.head_and_args computed_t in

  (* The expected type according to the context. *)
  let exp_t = head_unfold env exp_t in

  match (U.un_uinst head).n, args with
  (* b2t is primitive... for now *)
  | Tm_fvar fv, [] when S.fv_eq_lid fv C.bool_lid && is_type exp_t ->
    let lc2 = TcComm.lcomp_of_comp <| S.mk_Total U.ktype0 in
    let lc_res = bind e.pos env (Some e) checked (None, lc2) in
    Some (U.mk_app (S.fvar C.b2t_lid None) [S.as_arg e], lc_res, Env.trivial_guard)

  (* user coercions, find candidates with the @@coercion attribute and try. *)
  |  _ ->
    let head_lid_of t =
      match (SS.compress (head_of t)).n with
      | Tm_fvar fv
      | Tm_uinst ({ n = Tm_fvar fv }, _) ->
        Some (S.lid_of_fv fv)
      | _ -> None
    in

    let? exp_head_lid = head_lid_of exp_t in
    let? computed_head_lid = head_lid_of computed_t in

    let candidates = Env.lookup_attr env "FStar.Pervasives.coercion" in
    candidates |> first_opt (fun se ->
      (* `f` is the candidate coercion, `e` the term to coerce *)
      let? f_name, f_us, f_typ =
        match se.sigel with
        | Sig_let {lbs=(_,[lb])} -> Some (S.lid_of_fv (BU.right lb.lbname), lb.lbunivs, lb.lbtyp)
        | Sig_declare_typ {lid; us; t} -> Some (lid, us, t)
        | _ -> None
      in

      let _, f_typ = SS.open_univ_vars f_us f_typ in

      (* `f` must have type `b1 -> b2 -> .... -> bN -> TB -> M TC ...,
         Before attempting unification, which is expensive, we will
         check that the head of B is an fvar which matches the expected
         type, and that the head of A is and fvar which matches the type
         of e.
      *)
      let f_bs, f_c = U.arrow_formals_comp f_typ in
      bool_guard (f_bs <> []);? (* If not a function, ignore *)
      let f_res = U.comp_result f_c in
      let f_res = head_unfold (Env.push_binders env f_bs) f_res in
      let? f_res_head_lid = head_lid_of f_res in
      (* ^ The lid at the head of TC, the result type *)
      bool_guard (lid_equals exp_head_lid f_res_head_lid);?

      let b = List.last f_bs in
      let b_ty = b.binder_bv.sort in
      let b_ty = head_unfold (Env.push_binders env (List.init f_bs)) b_ty in
      let? b_head_lid = head_lid_of b_ty in
      (* ^ The lid at the head of TB, the last argument *)
      bool_guard (lid_equals computed_head_lid b_head_lid);?

      (* We will now typecheck the coercion applied to `e` at expected type
         `exp_t` likely causing implicits to be instantiated for the coercion
         function (if any). If this succeeds, the elaborated term is the
         result we want.

         FIXME: ideally, we would not pass `e` through the typechecker again,
         but checking the coercion alone means we need to compute its effect (easy)
         and effect indices (not easy).

         Note: we could perhaps backtrack on an error here (using
         catch_errors and UF.new_transaction), but that can get
         expensive, and it's perhaps unexpected. Currently, the head FVs
         define which coercions apply, and that's a firm choice.
       *)

      let f_tm = S.fvar f_name None in
      let tt = U.mk_app f_tm [S.as_arg e] in
      Some (env.tc_term { env with nocoerce=true; admit=true; expected_typ = Some (exp_t, false) } tt)
      // NB: tc_term returns exactly elaborated term, lcomp, and guard, so we just return that.
    )
)

let maybe_coerce_lc env (e:term) (lc:lcomp) (exp_t:term) : term & lcomp & guard_t =
  let should_coerce =
      (env.phase1
    || Options.lax ()) && not env.nocoerce
  in
  if not should_coerce then (
    if !dbg_Coercions then
      BU.print4 "(%s) NOT Trying to coerce %s from type (%s) to type (%s)\n"
              (show e.pos) (show e) (show lc.res_typ) (show exp_t);
    (e, lc, Env.trivial_guard)
  ) else (
    if !dbg_Coercions then
      BU.print4 "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
              (show e.pos) (show e) (show lc.res_typ) (show exp_t);
    match find_coercion env lc exp_t e with
    | Some (coerced, lc, g) ->
      let _ = if !dbg_Coercions then
              BU.print3 "(%s) COERCING %s to %s\n"
                      (Range.string_of_range e.pos)
                      (show e)
                      (show coerced)
      in
      coerced, lc, g
    | None ->
      let _ = if !dbg_Coercions then
              BU.print1 "(%s) No user coercion found\n"
                      (Range.string_of_range e.pos)
      in
      
      (* TODO: hide/reveal also user coercions? it's trickier for sure *)

      let strip_hide_or_reveal (e:term) (hide_or_reveal:lident) : option term =
        let hd, args = U.leftmost_head_and_args e in
        match (SS.compress hd).n, args with
        | Tm_uinst (hd, _), [(_, aq_t); (e, aq_e)]
          when U.is_fvar hide_or_reveal hd &&
               Some? aq_t && (Some?.v aq_t).aqual_implicit &&
               (aq_e = None || not (Some?.v aq_e).aqual_implicit) ->
          Some e
        | _ -> None
      in

      match check_erased env lc.res_typ, check_erased env exp_t with
      | No, Yes ty ->
          begin
          let u = env.universe_of env ty in
          match Rel.get_subtyping_predicate env lc.res_typ ty with
          | None ->
            e, lc, Env.trivial_guard
          | Some g ->
            let g = Env.apply_guard g e in
            let e_hide, lc = coerce_with env e lc C.hide [u] [S.iarg ty] (S.mk_Total exp_t) in
            //
            // AR: an optimization to see if input e is a reveal e',
            //     we can just take e', rather than hide (reveal e') 
            //
            //     we still let coerce_with happen just above,
            //     since it has logic to compute the correct lc
            //  
            let e_hide = BU.dflt e_hide (strip_hide_or_reveal e C.reveal) in
            e_hide, lc, g
          end

      | Yes ty, No ->
        let u = env.universe_of env ty in
        let e_reveal, lc = coerce_with env e lc C.reveal [u] [S.iarg ty] (S.mk_GTotal ty) in
        let e_reveal = BU.dflt e_reveal (strip_hide_or_reveal e C.hide) in
        e_reveal, lc, Env.trivial_guard

      | _ ->
        e, lc, Env.trivial_guard
  )

let weaken_result_typ env (e:term) (lc:lcomp) (t:typ) (use_eq:bool) : term & lcomp & guard_t =
  if Debug.high () then
    BU.print4 "weaken_result_typ use_eq=%s e=(%s) lc=(%s) t=(%s)\n"
            (show use_eq) (show e) (TcComm.lcomp_to_string lc) (show t);
  let use_eq =
    use_eq            ||  //caller wants to check equality
    env.use_eq_strict ||
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
        then Err.raise_basic_type_error env e.pos (Some e) t lc.res_typ
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

            if TEQ.eq_tm env t res_t = TEQ.Equal then begin  //if the two types res_t and t are same, then just set the result type
              if Debug.extreme()
              then BU.print2 "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                             (show res_t) (show t);
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
                if Debug.extreme ()
                then BU.print4 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                               (show e) (show c) (show t) (TcComm.lcomp_to_string lc);
                let c, g_lc = TcComm.lcomp_comp lc in
                set_result_typ c, Env.conj_guards [g_c; gret; g_lc]
              else begin
                if Debug.extreme ()
                then BU.print2 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                               (show res_t) (show c);
                set_result_typ c, g_c
              end
          in
          let lc = TcComm.mk_lcomp lc.eff_name t lc.cflags strengthen_trivial in
          e, lc, g

        | NonTrivial f ->
          let g = {g with guard_f=Trivial} in
          let strengthen () =
              if Options.lax()
              && Options.ml_ish() //NS: disabling this optimization temporarily
              then
                TcComm.lcomp_comp lc
              else begin
                  //try to normalize one more time, since more unification variables may be resolved now
                  let f = N.normalize [Env.Beta; Env.Eager_unfolding; Env.Simplify; Env.Primops] env f in
                  match (SS.compress f).n with
                      | Tm_abs {body={n=Tm_fvar fv}} when S.fv_eq_lid fv C.true_lid ->
                        //it's trivial
                        let lc = {lc with res_typ=t} in //NS: what's the point of this?
                        TcComm.lcomp_comp lc

                      | _ ->
                          let c, g_c = TcComm.lcomp_comp lc in
                          if Debug.extreme ()
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
                          if Debug.extreme ()
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
                        raise_error comp Errors.Fatal_EffectConstructorNotFullyApplied
                          (BU.format1 "Effect constructor is not fully applied; got %s" (show comp))
                   end
              else let ct = Env.unfold_effect_abbrev env comp in
                   begin match ct.effect_args with
                            | (wp, _)::_ ->
                              let us_r, _ = fst <| Env.lookup_lid env C.as_requires in
                              let us_e, _ = fst <| Env.lookup_lid env C.as_ensures in
                              let r = ct.result_typ.pos in
                              let as_req = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range C.as_requires r) None) us_r in
                              let as_ens = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range C.as_ensures r) None) us_e in
                              let req = mk_Tm_app as_req [(ct.result_typ, S.as_aqual_implicit true); S.as_arg wp] ct.result_typ.pos in
                              let ens = mk_Tm_app as_ens [(ct.result_typ, S.as_aqual_implicit true); S.as_arg wp] ct.result_typ.pos in
                              Some (norm req), norm (mk_post_type ct.result_typ ens)
                            | _ -> failwith "Impossible"
                  end

         end

(* [norm_reify env t] assumes that [t] has the shape reify t0 *)
(* where env |- t0 : M t' for some effect M and type t' where M is reifiable *)
(* and returns the result of reducing t with reification on *)
let norm_reify (env:Env.env) (steps:Env.steps) (t:S.term) : S.term =
    def_check_scoped t.pos "norm_reify" env t;
    let t' = N.normalize
      ([Env.Beta; Env.Reify; Env.Eager_unfolding; Env.EraseUniverses; Env.AllowUnboundUniverses; Env.Exclude Env.Zeta]@steps)
      env t in
    if !dbg_SMTEncodingReify
    then BU.print2 "Reified body %s \nto %s\n"
        (show t)
        (show t') ;
    t'

let remove_reify (t: S.term): S.term =
  if (match (SS.compress t).n with | Tm_app _ -> false | _ -> true)
  then t
  else
    let head, args = U.head_and_args t in
    if (match (SS.compress head).n with Tm_constant (FStarC.Const.Const_reify _) -> true | _ -> false)
    then begin match args with
        | [x] -> fst x
        | _ -> failwith "Impossible : Reify applied to multiple arguments after normalization."
    end
    else t


(*********************************************************************************************)
(* Instantiation and generalization *)
(*********************************************************************************************)
let maybe_implicit_with_meta_or_attr aq (attrs:list attribute) =
  match aq, attrs with
  | Some (Meta _), _
  | Some (Implicit _), _::_ -> true
  | _ -> false

(* Instantiation of implicit arguments (meta or implicit)
 *
 * For meta arguments, we follow the exact same procedure as for instantiating an implicit,
 * except that we keep track of the (uvar, env, metaprogram) triple in the environment
 * so we can later come back to the implicit and, if it wasn't solved by unification,
 * run the metaprogram on it.
 *
 * Why don't we run the metaprogram here? At this stage, it's very likely that `t`
 * is full of unresolved uvars, and it wouldn't be a whole lot useful to try
 * to find an instance for it. We might not even be able to, since instances
 * are for concrete types.
 *)
let instantiate_one_binder (env:env_t) (r:Range.range) (b:binder) : term & typ & aqual & guard_t =
  if Debug.high () then
    BU.print1 "instantiate_one_binder: Instantiating implicit binder %s\n" (show b);
  let (++) = Env.conj_guard in
  let { binder_bv=x } = b in
  let ctx_uvar_meta, should_unrefine = uvar_meta_for_binder b in (* meta/attrs computed here *)
  let t = x.sort in
  let varg, _, implicits =
    let msg =
      let is_typeclass =
        match ctx_uvar_meta with
        | Some (Ctx_uvar_meta_tac tau) -> U.is_fvar C.tcresolve_lid tau
        | _ -> false
      in
      if is_typeclass then "Typeclass constraint argument"
      else if Some? ctx_uvar_meta then "Instantiating meta argument"
      else "Instantiating implicit argument"
    in
    Env.new_implicit_var_aux msg r env t Strict ctx_uvar_meta should_unrefine
  in
  let aq = U.aqual_of_binder b in
  let arg = varg, aq in

  let r = varg, t, aq, implicits in
  if Debug.high () then
    BU.print1 "instantiate_one_binder: result = %s\n" (show (r._1, r._2));
  r

(* Will instantiate e, by applying it to some unification variables for its implicit
arguments, if that is needed to match the expected type in the environment. [t] is the type
of [e]. Returns elaborated [e'], its type [t'], and a guard. *)
let maybe_instantiate (env:Env.env) (e:term) (t:typ) : term & typ & guard_t =
  let torig = SS.compress t in
  if not env.instantiate_imp
  then e, torig, mzero
  else begin
       if Debug.high () then
         BU.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                 (show e) (show t) (show (Env.expected_typ env));
       (* Similar to U.arrow_formals, but makes sure to unfold
        * recursively to catch all the binders across type
        * definitions. TODO: Move to library? Revise other uses
        * of arrow_formals{,_comp}?*)
       let unfolded_arrow_formals env (t:term) : list binder =
         let rec aux (env:Env.env) (bs:list binder) (t:term) : list binder =
           let t = N.unfold_whnf env t in
           let bs', t = U.arrow_formals t in
           match bs' with
           | [] -> bs
           | bs' -> aux (Env.push_binders env bs') (bs@bs') t
         in
         aux env [] t
       in
       let number_of_implicits t =
            let formals = unfolded_arrow_formals env t in
            let n_implicits =
            match formals |> BU.prefix_until (fun ({binder_qual=imp}) -> Option.isNone imp || U.eq_bqual imp (Some Equality)) with
                | None -> List.length formals
                | Some (implicits, _first_explicit, _rest) -> List.length implicits in
            n_implicits
       in
       let inst_n_binders t =
           match Env.expected_typ env with
           | None -> None
           | Some (expected_t, _) ->  //the use_eq flag is irrelevant for instantiation
             let n_expected = number_of_implicits expected_t in
             let n_available = number_of_implicits t in
             if n_available < n_expected
             then raise_error env Errors.Fatal_MissingImplicitArguments [
                    text "Expected a term with " ^/^ pp #int n_expected ^/^ text " implicit arguments, but " ^/^
                      pp e ^/^ text " has only " ^/^ pp #int n_available ^^ text "."]
             else Some (n_available - n_expected)
        in
        let decr_inst = function
                | None -> None
                | Some i -> Some (i - 1)
        in
        let t = N.unfold_whnf env t in
        begin match t.n with
            | Tm_arrow {bs; comp=c} ->
              let bs, c = SS.open_comp bs c in
              //instantiate at most inst_n implicit binders, when inst_n = Some n
              //otherwise, instantate all implicits
              //See issue #807 for why this is important
              let rec aux (subst:list subst_elt) inst_n bs =
                  match inst_n, bs with
                  | Some 0, _ -> [], bs, subst, Env.trivial_guard //no more instantiations to do
                  | _, {binder_qual = Some (Implicit _)} ::rest
                  | _, {binder_qual = Some (Meta _)} ::rest
                  | _, {binder_attrs = _::_} :: rest ->
                      let b = List.hd bs in
                      let b = SS.subst_binder subst b in
                      let tm, ty, aq, g = instantiate_one_binder env e.pos b in
                      let subst = NT(b.binder_bv, tm)::subst in
                      let args, bs, subst, g' = aux subst (decr_inst inst_n) rest in
                      (tm, aq)::args, bs, subst, g ++ g'

                 | _, bs -> [], bs, subst, mzero
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

let check_has_type env (e:term) (t1:typ) (t2:typ) (use_eq:bool) : guard_t =
  let env = Env.set_range env e.pos in

  let g_opt =
    if env.use_eq_strict
    then match Rel.teq_nosmt_force env t1 t2 with
       | false -> None
       | true -> Env.trivial_guard |> Some
    else if use_eq
    then Rel.try_teq true env t1 t2
    else match Rel.get_subtyping_predicate env t1 t2 with
             | None -> None
             | Some f -> apply_guard f e |> Some in

  match g_opt with
  | None -> Err.expected_expression_of_type env (Env.get_range env) t2 e t1
  | Some g -> g

let check_has_type_maybe_coerce env (e:term) (lc:lcomp) (t2:typ) use_eq : term & lcomp & guard_t =
  let env = Env.set_range env e.pos in
  let e, lc, g_c = maybe_coerce_lc env e lc t2 in
  let g = check_has_type env e lc.res_typ t2 use_eq in
  if !dbg_Rel then
    BU.print1 "Applied guard is %s\n" <| guard_to_string env g;
  e, lc, (Env.conj_guard g g_c)

/////////////////////////////////////////////////////////////////////////////////
let check_top_level env g lc : (bool & comp) =
 Errors.with_ctx "While checking for top-level effects" (fun () ->
  if Debug.medium () then
    BU.print1 "check_top_level, lc = %s\n" (TcComm.lcomp_to_string lc);
  let discharge g =
    force_trivial_guard env g;
    TcComm.is_pure_lcomp lc in
  let g = Rel.solve_deferred_constraints env g in
  let c, g_c = TcComm.lcomp_comp lc in
  if TcComm.is_total_lcomp lc
  then discharge (Env.conj_guard g g_c), c
  else let c = Env.unfold_effect_abbrev env c in
       let us = c.comp_univs in
       if Env.is_layered_effect env c.effect_name
       then begin
         //
         // A top-level indexed effect
         // We will look at the top_level_effect attr for the effect definition
         //   and make sure that c unifies with it
         //
         let c_eff = c.effect_name in
         let ret_comp = c |> S.mk_Comp in
         //
         // Using simplify etc. to help unificiation of logical effect arguments
         // E.g., F* may insert returns, equalities, with which a precondition
         //   may look like e ==> True,
         //   as opposed to just True specified in the top-level effect abbreviation
         //
         // But this is just for unification, we return the original comp (ret_comp)
         //   without normalization
         //
         let steps = [Env.Eager_unfolding; Env.Simplify; Env.Primops; Env.NoFullNorm] in
         let c =
           c
           |> S.mk_Comp
           |> Normalize.normalize_comp steps env in
         let top_level_eff_opt = Env.get_top_level_effect env c_eff in
         match top_level_eff_opt with
         | None ->
           raise_error
             (Env.get_range env)
             Errors.Fatal_UnexpectedEffect
              (BU.format1 "Indexed effect %s cannot be used as a top-level effect" (c_eff |> Ident.string_of_lid))
         | Some top_level_eff ->
           // If top-level effect is same as c_eff, return
           if Ident.lid_equals top_level_eff c_eff
           then discharge g_c, ret_comp
           else
             let bc_opt = Env.lookup_effect_abbrev env us top_level_eff in
             match bc_opt with
             | None -> 
               raise_error env Errors.Fatal_UnexpectedEffect
                  (BU.format2 "Could not find top-level effect abbreviation %s for %s"
                    (Ident.string_of_lid top_level_eff)
                    (c_eff |> Ident.string_of_lid))
             | Some (bs, _) ->
               let debug = !dbg_LayeredEffectsApp in
               //
               // Typechecking of effect abbreviation ensures that there is at least
               //   one return type argument, so the following a::bs is ok
               //
               let a::bs = SS.open_binders bs in
               let uvs, g_uvs =
                 Env.uvars_for_binders
                   env
                   bs
                   [NT (a.binder_bv, U.comp_result c)]
                   (fun b ->
                    if debug
                    then BU.format2
                           "implicit for binder %s in effect abbreviation %s while checking top-level effect"
                           (show b)
                          (Ident.string_of_lid top_level_eff)
                    else "check_top_level")
                   (Env.get_range env) in
               let top_level_comp =
                 ({ comp_univs = us;
                    effect_name = top_level_eff;
                    result_typ = U.comp_result c;
                    effect_args = uvs |> List.map S.as_arg;
                    flags = [] }) |> S.mk_Comp in
               // Unify
               let gopt = Rel.eq_comp env top_level_comp c in
               match gopt with
               | None -> 
                 raise_error env Errors.Fatal_UnexpectedEffect
                    (BU.format2 "Could not unify %s and %s when checking top-level effect"
                      (show top_level_comp)
                      (show c))
               | Some g ->
                 discharge (Env.conj_guards [g_c; g_uvs; g]), ret_comp
       end
       else let steps = [Env.Beta; Env.NoFullNorm; Env.DoNotUnfoldPureLets] in
            let c = c
              |> S.mk_Comp
              |> Normalize.normalize_comp steps env in
            let ct, vc, g_pre = check_trivial_precondition_wp env c in
            if !dbg_Simplification
            then BU.print1 "top-level VC: %s\n" (show vc);
            discharge (Env.conj_guard g (Env.conj_guard g_c g_pre)), ct |> S.mk_Comp
 )

(* Having already seen_args to head (from right to left),
   compute the guard, if any, for the next argument,
   if head is a short-circuiting operator *)
let short_circuit (head:term) (seen_args:args) : guard_formula =
    let short_bin_op f : args -> guard_formula = function
        | [] -> (* no args seen yet *) Trivial
        | [(fst, _)] -> f fst
        | _ -> failwith "Unexpected args to binary operator" in

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
(* Adding implicit binders                                              *)
(* in case the expected type is of the form #a1 -> ... -> #an -> t      *)
(* and bs does not begin with any implicit binders                      *)
(* add #a1 ... #an to bs                                                *)
(* Note that there may be other implicit binders in t that bs don't     *)
(* We don't add them here, so in that sense it is best case effort      *)
(* This helps us sometimes to build a better decreases clause           *)
(*   since it helps us count the arity by including implicits           *)
(************************************************************************)
let maybe_add_implicit_binders (env:env) (bs:binders) : binders =
    let is_implicit_binder ({binder_qual=q}) : bool =
        match q with
        | Some (Implicit _)
        | Some (Meta _) -> true
        | _ -> false in

    let pos bs = match bs with
        | ({binder_bv=hd})::_ -> S.range_of_bv hd
        | _ -> Env.get_range env in

    match bs with
        | b :: _ when is_implicit_binder b -> bs // bs begins with an implicit binder; don't add any
        | _ ->
          match Env.expected_typ env with
            | None -> bs
            | Some (t, _) ->  //the use_eq flag is not relevant
                match (SS.compress t).n with
                    | Tm_arrow {bs=bs'} ->
                      begin match BU.prefix_until (fun b -> not (is_implicit_binder b)) bs' with
                        | None -> bs
                        | Some ([], _, _) -> bs // no implicits in the prefix
                        | Some (imps, _,  _) ->
                          let r = pos bs in
                          let imps =
                            imps |> List.map (fun b -> { b with binder_bv = (S.set_range_of_bv b.binder_bv r) }) in
                          imps@bs // we have a prefix of implicits
                      end

                    | _ -> bs


let must_erase_for_extraction (g:env) (t:typ) =
  let res = N.non_info_norm g t in
  if !dbg_Extraction then BU.print2 "must_erase=%s: %s\n" (show res) (show t);
  res

let effect_extraction_mode env l =
  l |> Env.norm_eff_name env
    |> Env.get_effect_decl env
    |> (fun ed -> ed.extraction_mode)

let fresh_effect_repr env r eff_name signature_ts repr_ts_opt u a_tm =
  let fail t = Err.unexpected_signature_for_monad env r eff_name t in

  let _, signature = Env.inst_tscheme signature_ts in

  let debug = !dbg_LayeredEffectsApp in

  (*
   * We go through the binders in the signature a -> bs
   * For each binder in bs, create a fresh uvar
   * But keep substituting [a/a_tm, b_i/?ui] in the sorts of the subsequent binders
   *)
  match (SS.compress signature).n with
  | Tm_arrow {bs} ->
    let bs = SS.open_binders bs in
    (match bs with
     | a::bs ->
       //is is all the uvars, and g is their collective guard
       let is, g =
         Env.uvars_for_binders env bs [NT (a.binder_bv, a_tm)]
           (fun b ->
            if debug
            then BU.format3
                   "uvar for binder %s when creating a fresh repr for %s at %s"
                   (show b) (string_of_lid eff_name) (Range.string_of_range r)
            else "fresh_effect_repr") r in
       (match repr_ts_opt with
        | None ->  //no repr, return thunked computation type
          let eff_c = mk_Comp ({
            comp_univs = [u];
            effect_name = eff_name;
            result_typ = a_tm;
            effect_args = List.map S.as_arg is;
            flags = [] }) in
          S.mk (Tm_arrow {bs=[S.null_binder S.t_unit]; comp=eff_c}) r
        | Some repr_ts ->
          let repr = Env.inst_tscheme_with repr_ts [u] |> snd in
          let is_args = List.map2 (fun i b -> (i, U.aqual_of_binder b)) is bs in
          S.mk_Tm_app
            repr
            (S.as_arg a_tm::is_args)
            r), g
     | _ -> fail signature)
  | _ -> fail signature

let fresh_effect_repr_en env r eff_name u a_tm =
  eff_name
  |> Env.get_effect_decl env
  |> (fun ed -> fresh_effect_repr env r eff_name (U.effect_sig_ts ed.signature) (ed |> U.get_eff_repr)  u a_tm)

let layered_effect_indices_as_binders env r eff_name sig_ts u a_tm =
  let _, sig_tm = Env.inst_tscheme_with sig_ts [u] in

  let fail t = Err.unexpected_signature_for_monad env r eff_name t in

  match (SS.compress sig_tm).n with
  | Tm_arrow {bs} ->
    let bs = SS.open_binders bs in
    (match bs with
     | ({binder_bv=a'})::bs -> bs |> SS.subst_binders [NT (a', a_tm)]
     | _ -> fail sig_tm)
  | _ -> fail sig_tm


let check_non_informative_type_for_lift env m1 m2 t (r:Range.range) : unit =
  //raise an error if m1 is erasable, m2 is not erasable, and t is informative
  if Env.is_erasable_effect env m1       &&
     not (Env.is_erasable_effect env m2) &&
     None? (N.non_info_norm env t)
  then Errors.raise_error r Errors.Error_TypeError
          (BU.format3 "Cannot lift erasable expression from %s ~> %s since its type %s is informative"
            (string_of_lid m1)
            (string_of_lid m2)
            (show t))

//
// Apply a substitutive indexed lift
//
let substitutive_indexed_lift_substs (env:env)
  (bs:binders)
  (ct:comp_typ)
  (lift_name:string)
  (r:Range.range)

  : list subst_elt & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  let bs, subst =
    let a_b::bs = bs in
    bs, [NT (a_b.binder_bv, ct.result_typ)] in

  let bs, subst =
    let m_num_effect_args = List.length ct.effect_args in
    let f_bs, bs = List.splitAt m_num_effect_args bs in
    let f_subst = List.map2 (fun f_b (arg, _) -> NT (f_b.binder_bv, arg)) f_bs ct.effect_args in
    bs, subst@f_subst in

  let bs = List.splitAt (List.length bs - 1) bs |> fst in

  List.fold_left (fun (subst, g) b ->
    let [uv_t], g_uv = Env.uvars_for_binders env [b] subst
      (fun b ->
       if debug
       then BU.format3 "implicit var for additional lift binder %s of %s at %s)"
              (show b)
              lift_name
              (Range.string_of_range r)
       else "substitutive_indexed_lift_substs") r in
    subst@[NT (b.binder_bv, uv_t)],
    Env.conj_guard g g_uv) (subst, Env.trivial_guard) bs

let ad_hoc_indexed_lift_substs (env:env)
  (bs:binders)
  (ct:comp_typ)
  (lift_name:string)
  (r:Range.range)

  : list subst_elt & guard_t =

  let debug = !dbg_LayeredEffectsApp in

  let lift_t_shape_error s =
    BU.format2 "Lift %s has unexpected shape, reason: %s"
      lift_name s in

  let a_b, (rest_bs, [f_b]) =
    if List.length bs >= 2
    then let a_b::bs = bs in
         a_b, List.splitAt (List.length bs - 1) bs
    else raise_error r Errors.Fatal_UnexpectedEffect
                      (lift_t_shape_error "either not an arrow or not enough binders") in

  let rest_bs_uvars, g =
    Env.uvars_for_binders env rest_bs
      [NT (a_b.binder_bv, ct.result_typ)]
      (fun b ->
       if debug
       then BU.format3
              "implicit var for binder %s of %s at %s"
              (show b)
              lift_name
              (Range.string_of_range r)
       else "ad_hoc_indexed_lift_substs") r in

  let substs = List.map2
    (fun b t -> NT (b.binder_bv, t))
    (a_b::rest_bs) (ct.result_typ::rest_bs_uvars) in

  let guard_f =
    let f_sort = f_b.binder_bv.sort |> SS.subst substs |> SS.compress in
    let f_sort_is = effect_args_from_repr f_sort (Env.is_layered_effect env ct.effect_name) r in
    List.fold_left2
      (fun g i1 i2 -> Env.conj_guard g (Rel.layered_effect_teq env i1 i2 (Some lift_name)))
      Env.trivial_guard (List.map fst ct.effect_args) f_sort_is in

  substs,
  Env.conj_guard g guard_f

let lift_tf_layered_effect (tgt:lident) (lift_ts:tscheme) (kind:S.indexed_effect_combinator_kind)
  env (c:comp) : comp & guard_t =

  let debug = !dbg_LayeredEffectsApp in
  
  if debug then
    BU.print2 "Lifting indexed comp %s to  %s {\n"
      (show c) (show tgt);

  let r = Env.get_range env in

  let ct = Env.comp_to_comp_typ env c in

  check_non_informative_type_for_lift env ct.effect_name tgt ct.result_typ r;

  let lift_name () =
    if debug then BU.format2 "%s ~> %s" (string_of_lid ct.effect_name) (string_of_lid tgt)
    else "" in

  let _, lift_t = Env.inst_tscheme_with lift_ts [List.hd ct.comp_univs] in

  let bs, lift_c = U.arrow_formals_comp lift_t in

  let substs, g =
    if kind = S.Ad_hoc_combinator
    then ad_hoc_indexed_lift_substs env bs ct (lift_name ()) r
    else substitutive_indexed_lift_substs env bs ct (lift_name ()) r in
    
  let lift_ct = lift_c |> SS.subst_comp substs |> Env.comp_to_comp_typ env in

  let is = effect_args_from_repr lift_ct.result_typ (Env.is_layered_effect env tgt) r in

  //compute the formula `lift_c.wp (fun _ -> True)` and add it to the final guard
  let fml =
    let u, wp = List.hd lift_ct.comp_univs, fst (List.hd lift_ct.effect_args) in
    Env.pure_precondition_for_trivial_post env u lift_ct.result_typ wp Range.dummyRange in

  if !dbg_LayeredEffects &&
     Debug.extreme ()
  then BU.print1 "Guard for lift is: %s" (show fml);

  let c = mk_Comp ({
    comp_univs = ct.comp_univs;
    effect_name = tgt;
    result_typ = ct.result_typ;
    effect_args = is |> List.map S.as_arg;
    flags = []  //AR: setting the flags to empty
  }) in

  if debug then BU.print1 "} Lifted comp: %s\n" (show c);

  let g = Env.conj_guards [
    g;
    Env.guard_of_guard_formula (TcComm.NonTrivial fml) ] in

  c, g

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
    | Tm_arrow {bs=_::bs} when List.length bs >= 1 ->
      bs |> List.splitAt (List.length bs - 1) |> fst
    | _ ->
      raise_error (snd lift_t) Errors.Fatal_UnexpectedEffect
        (BU.format1 "lift_t tscheme %s is not an arrow with enough binders"
          (Print.tscheme_to_string lift_t))
  in

  let args = (S.as_arg a)::((rest_bs |> List.map (fun _ -> S.as_arg S.unit_const))@[S.as_arg e]) in
  mk (Tm_app {hd=lift; args}) e.pos

let get_field_projector_name env datacon index =
  let _, t = Env.lookup_datacon env datacon in
  let err n =
    raise_error env Errors.Fatal_UnexpectedDataConstructor
      (BU.format3 "Data constructor %s does not have enough binders (has %s, tried %s)"
        (show datacon) (show n) (show index))  in
  match (SS.compress t).n with
  | Tm_arrow {bs} ->
    let bs = bs |> List.filter (fun ({binder_qual=q}) -> match q with | Some (Implicit true) -> false | _ -> true) in
    if List.length bs <= index then err (List.length bs)
    else
      let b = List.nth bs index in
      U.mk_field_projector_name datacon b.binder_bv index
  | _ -> err 0


let get_mlift_for_subeff env (sub:S.sub_eff) : Env.mlift =
  if Env.is_layered_effect env sub.source || Env.is_layered_effect env sub.target

  then
    ({ mlift_wp = lift_tf_layered_effect sub.target (sub.lift_wp |> must) (sub.kind |> must);
       mlift_term = Some (lift_tf_layered_effect_term env sub) })

  else
    let mk_mlift_wp ts env c =
      let ct = Env.comp_to_comp_typ env c in
      check_non_informative_type_for_lift env ct.effect_name sub.target ct.result_typ env.range;
      let _, lift_t = inst_tscheme_with ts ct.comp_univs in
      let wp = List.hd ct.effect_args in
      S.mk_Comp ({ ct with
        effect_name = sub.target;
        effect_args =
          [mk (Tm_app {hd=lift_t; args=[as_arg ct.result_typ; wp]}) (fst wp).pos |> S.as_arg]
      }), TcComm.trivial_guard
    in

    let mk_mlift_term ts u r e =
      let _, lift_t = inst_tscheme_with ts [u] in
      mk (Tm_app {hd=lift_t; args=[as_arg r; as_arg S.tun; as_arg e]}) e.pos
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

let update_env_polymonadic_bind env m n p ty k =
  //
  //false means no range support in polymonadic bind yet
  //
  Env.add_polymonadic_bind env m n p
    (fun env c1 bv_opt c2 flags r ->
     mk_indexed_bind env m n p ty k c1 bv_opt c2 flags r 0 false)

(*** Utilities for type-based record
     disambiguation ***)


(*
   For singleton inductive types named `typename`,
   it looks up the name of the constructor,
   and the field names of that constructor
 *)
let try_lookup_record_type env (typename:lident)
  : option DsEnv.record_or_dc
  = try
      match Env.datacons_of_typ env typename with
      | _, [dc] ->
        let se = Env.lookup_sigelt env dc in
        (match se with
         | Some ({sigel=Sig_datacon {t; num_ty_params=nparms}}) ->
           let formals, c = U.arrow_formals t in
           if nparms < List.length formals
           then let _, fields = List.splitAt nparms formals in //remove params
                let fields = List.filter (fun b -> match b.binder_qual with | Some (Implicit _) -> false | _ -> true) fields in //remove implicits
                let fields = List.map (fun b -> b.binder_bv.ppname, b.binder_bv.sort) fields in
                let is_rec = Env.is_record env typename in
                let r : DsEnv.record_or_dc =
                  {
                    typename = typename;
                    constrname = Ident.ident_of_lid dc;
                    parms = [];
                    fields = fields;
                    is_private = false;
                    is_record = is_rec
                  }
                in
                Some r

           else (
            //  BU.print3 "Not enough formals; nparms=%s; type = %s; formals=%s\n"
            //    (string_of_int nparms)
            //    (show t)
            //    (Print.binders_to_string ", " formals);
             None
           )
         | _ ->
          //  BU.print1 "Could not find %s\n" (string_of_lid dc);
           None)
      | _, dcs ->
        // BU.print2 "Could not find type %s ... Got %s\n"
        //    (string_of_lid typename)
        //    (FStarC.Common.string_of_list Ident.string_of_lid dcs);
        None
    with
    | _ -> None

(*
   If ToSyntax guessed `uc`
   and the typechecker decided that type `t: option typ` was the type
   to be used for disambiguation, then if

    - t is None, the uc is used
    - otherwise t overrides uc
 *)
let find_record_or_dc_from_typ env (t:option typ) (uc:unresolved_constructor) rng =
    let default_rdc () =
      let open FStarC.Errors.Msg in
      match uc.uc_typename, uc.uc_fields with
      | None, [] ->
        raise_error rng Errors.Error_CannotResolveRecord [
          text "Could not resolve the type for this record.";
        ]

      | None, f::_ ->
        let f = List.hd uc.uc_fields in
        raise_error f Errors.Error_CannotResolveRecord [
            text <| BU.format1 "Field name %s could not be resolved." (string_of_lid f);
        ]

      | Some tn, _ ->
        match try_lookup_record_type env tn with
        | Some rdc -> rdc
        | None ->
          raise_error tn Errors.Fatal_NameNotFound 
            (BU.format1 "Record name %s not found." (string_of_lid tn))
    in
    let rdc : DsEnv.record_or_dc =
      match t with
      | None -> default_rdc()
      | Some t ->
        let thead, _ = 
          U.head_and_args (N.unfold_whnf' [Unascribe; Unmeta; Unrefine] env t)
        in
        match (SS.compress (U.un_uinst thead)).n with
        | Tm_fvar type_name ->
          begin
          match try_lookup_record_type env type_name.fv_name.v with
          | None -> default_rdc ()
          | Some r -> r
          end
        | _ -> default_rdc()
    in
    let constrname =
          let name = lid_of_ids (ns_of_lid rdc.typename @ [rdc.constrname]) in
          Ident.set_lid_range name rng
    in
    let constructor =
        let qual =
          if rdc.is_record
            then (Some (Record_ctor(rdc.typename, rdc.fields |> List.map fst)))
          else None
        in
        S.lid_as_fv constrname qual
    in
    rdc, constrname, constructor


(* Check if a user provided `field_name` in a constructor or projector
   matches `field` in `rdc`.

   The main subtlety is that if `field_name` is unqualified, then it only
   has to match `field`.

   Otherwise, its namespace also has to match the module name of `rdc`.

   This ensures that if the user wrote a qualified field name, then it
   has to resolve to a field in the unambiguous module reference in
   the qualifier.
*)
let field_name_matches (field_name:lident) (rdc:DsEnv.record_or_dc) (field:ident) =
    Ident.ident_equals field (Ident.ident_of_lid field_name) &&
    (if ns_of_lid field_name <> []
     then nsstr field_name = nsstr rdc.typename
     else true)

(*
  The field assignments of a record constructor can be given out of
  order.

  Given that we've committed to `rdc` as the record constructor, if
  the user's field assignments are `fas`, then we order the alphas
  by the order in which they appear in `rdc`.

  If a particular field cannot be found, then we call not_found, which
  an provide a default.

  We raise errors if fields are not found and no default exists, or if
  redundant fields are present.
*)
let make_record_fields_in_order env uc topt
       (rdc : DsEnv.record_or_dc)
       (fas : list (lident & 'a))
       (not_found:ident -> option 'a)
       (rng : Range.range)
  : list 'a
  = let debug () =
      let print_rdc (rdc:DsEnv.record_or_dc) =
        BU.format3 "{typename=%s; constrname=%s; fields=[%s]}"
          (string_of_lid rdc.typename)
          (string_of_id rdc.constrname)
          (List.map (fun (i, _) -> string_of_id i) rdc.fields |> String.concat "; ")
      in
      let print_topt topt =
        BU.format2 "topt=%s; rdc=%s" (show topt) (print_rdc rdc)
      in
      BU.print5 "Resolved uc={typename=%s;fields=%s}\n\ttopt=%s\n\t{rdc = %s\n\tfield assignments=[%s]}\n"
          (show uc.uc_typename)
          (show uc.uc_fields)
          (print_topt topt)
          (print_rdc rdc)
          (show (List.map fst fas))
    in
    let rest, as_rev, missing =
      List.fold_left
        (fun (fields, as_rev, missing) (field_name, _) ->
           let matching, rest =
             List.partition
               (fun (fn, _) -> field_name_matches fn rdc field_name)
               fields
           in
           match matching with
           | [(_, a)] ->
             rest, a::as_rev, missing

           | [] -> (
             match not_found field_name with
             | None ->
//               debug();
              rest, as_rev, field_name :: missing
             | Some a ->
               rest, a::as_rev, missing
             )

           | _ ->
//             debug();
             raise_error rng Errors.Fatal_MissingFieldInRecord
                (BU.format2 "Field %s of record type %s is given multiple assignments"
                  (string_of_id field_name)
                  (string_of_lid rdc.typename)))
        (fas, [], [])
        rdc.fields
    in
    let pp_missing () =
      separate_map (comma ^^ break_ 1) (fun f -> squotes (doc_of_string (show f))) missing
    in
    let _ =
      match rest, missing with
      | [], [] -> ()
      | (f, _)::_, _ ->
//        debug();
        raise_error f Errors.Fatal_MissingFieldInRecord [
            Errors.Msg.text <| BU.format2 "Field '%s' is redundant for type %s" (show f) (show rdc.typename);
            if Cons? missing then
              prefix 2 1 (text "Missing fields:")
                (pp_missing ())
            else
              Pprint.empty;
        ]

      | [], _ ->
        raise_error rng Errors.Fatal_MissingFieldInRecord [
            prefix 2 1 (text <| BU.format1 "Missing fields for record type '%s':" (show rdc.typename))
                (pp_missing ())
        ]
    in
    List.rev as_rev
