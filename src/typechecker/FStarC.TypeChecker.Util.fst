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

open FStarC
open FStarC.Effect
open FStarC.List
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
open FStar.Dyn
open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Class.Monoid

module Listlike = FStarC.Class.Listlike

module SS = FStarC.Syntax.Subst
module S = FStarC.Syntax.Syntax
module BU = FStarC.Util
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module TcComm = FStarC.TypeChecker.Common
module C = FStarC.Parser.Const
module UF = FStarC.Syntax.Unionfind
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Print = FStarC.Syntax.Print
module Overload = FStarC.TypeChecker.Overload

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

let close_guard_implicits env solve_deferred (xs:binders) (g:guard_t) : ML guard_t =
  if Options.eager_subtyping ()
  || solve_deferred
  then
    let solve_now, defer =
      g.deferred |> Listlike.to_list |> List.partition (fun (_, _, p) -> Rel.flex_prob_closing env xs p)
    in
    if !dbg_Rel
    then begin
      Format.print_string "SOLVE BEFORE CLOSING:\n";
      List.iter (fun (_, s, p) -> Format.print2 "%s: %s\n" s (Rel.prob_to_string env p)) solve_now;
      Format.print_string " ...DEFERRED THE REST:\n";
      List.iter (fun (_, s, p) -> Format.print2 "%s: %s\n" s (Rel.prob_to_string env p)) defer;
      Format.print_string "END\n"
    end;
    let g = Rel.solve_non_tactic_deferred_constraints false env ({g with deferred = Listlike.from_list solve_now}) in
    let g = {g with deferred = Listlike.from_list defer} in
    g
  else g

let check_uvars r t : ML _ =
  let uvs = Free.uvars t in
  if not (is_empty uvs) then begin
    (* ignoring the hide_uvar_nums and print_implicits flags here *)
    Options.push();
    Options.set_option "hide_uvar_nums" (Options.Bool false);
    Options.set_option "print_implicits" (Options.Bool true);
    Errors.log_issue r Errors.Error_UnconstrainedUnificationVar
      (Format.fmt2 "Unconstrained unification variables %s in type signature %s; \
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
let extract_let_rec_annotation env (lb:letbinding) :
    ML (list univ_name
   & typ
   & term
   & bool) //true indicates that the type needs to be checked; false indicates that it is already checked
   =
  let {lbname; lbunivs=univ_vars; lbtyp=t; lbdef=e} = lb in
  let rng = S.range_of_lbname lbname in
  let t = SS.compress t in
  let u_subst, univ_vars = SS.univ_var_opening univ_vars in
  let e = SS.subst u_subst e in
  let t = SS.subst u_subst t in
  if !dbg_Dec
  then Format.print2 "extract_let_rec_annotation lbdef=%s; lbtyp=%s\n"
                 (show e)
                 (show t);
  let env = Env.push_univ_vars env univ_vars in
  let un_arrow t =
    (* Under the unary representation an n-ary arrow *is* a Tot-nested spine, so
       flattening recovers exactly the binders the arrow was built with. *)
      match (SS.compress t).n with
      | Tm_arrow _ ->
        U.arrow_formals_comp_strict t
      | _ ->
        raise_error rng Errors.Fatal_LetRecArgumentMismatch [
            text "Recursive functions must be introduced at arrow types.";
        ]
  in
  (* [n_opt], when given, is the arity the definition is written at, i.e. the
     number of binders of its outermost lambda. It cannot be recovered from
     [tarr] alone: the arrow node is unary, so a definition ascribed
     [Tot (int -> int)] is indistinguishable from one ascribed [int -> int],
     while [annot] may stop earlier because it carries a decreases clause. *)
  let reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt (n_opt:option int) =
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
        let bs, c =
          match n_opt with
          | Some n -> N.get_n_binders env n tarr
          | None -> un_arrow tarr
        in
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
    : ML (typ
    & term
    & bool)
    = let rec aux_lbdef e
        : ML (typ & term & bool)
        = let e = SS.compress e in
          match e.n with
          | Tm_meta {tm=e';meta=m} ->
            let t, e', recheck = aux_lbdef e' in
            t, { e with n = Tm_meta {tm=e'; meta=m} }, recheck

          | Tm_ascribed {tm=e'; asc=(Inr c, tac_opt, use_eq); eff_opt=lopt} ->
            if U.is_total_comp c
            then let t, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type (U.comp_result c) lbtyp_opt None in
                 let e = { e with n = Tm_ascribed {tm=e';
                                                   asc=(Inr (S.mk_Total t), tac_opt, use_eq);
                                                   eff_opt=lopt} } in
                 lbtyp, e, recheck
            else raise_error rng Errors.Fatal_UnexpectedComputationTypeForLetRec [
                     text "Expected a 'let rec' to be annotated with a value type";
                     text "Got a computation type" ^/^ pp c ^/^ text "instead";
                   ]

          | Tm_ascribed {tm=e'; asc=(Inl t, tac_opt, use_eq); eff_opt=lopt} ->
            let t, lbtyp, recheck = reconcile_let_rec_ascription_and_body_type t lbtyp_opt None in
            let e = { e with n = Tm_ascribed {tm=e'; asc=(Inl t, tac_opt, use_eq); eff_opt=lopt} } in
            lbtyp, e, recheck

          | Tm_abs _ ->
            let bs, body, rcopt = U.abs_formals_maybe_unascribe_body false e in
            let mk_comp t =
              S.mk_Total t
            in
            let mk_arrow c = U.arrow bs c in
            let rec aux_abs_body body : ML _ =
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
                let n_bs = List.length bs in
                let tarr, lbtyp, recheck =
                  reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt (Some n_bs) in
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
//              then failwith (Format.fmt2 "Expected pattern variable %s; got %s" (show x) (show y));
//              if !dbg_Pat
//              then Format.print2 "Pattern variable %s introduced at type %s\n" (show x) (Normalize.term_to_string env y.sort);
//              let s = Normalize.normalize [Env.Beta] env y.sort in
//              let x = {x with sort=s} in
//              pkg (Pat_var x)

//            | Pat_wild x, Tm_name y ->
//              if bv_eq x y |> not
//              then failwith (Format.fmt2 "Expected pattern variable %s; got %s" (show x) (show y));
//              let s = Normalize.normalize [Env.Beta] env y.sort in
//              let x = {x with sort=s} in
//              pkg (Pat_wild x)

//            | Pat_dot_term(x, _), _ ->
//              pkg (Pat_dot_term(x, e))

//            | Pat_cons(fv, []), Tm_fvar fv' ->
//              if not (Syntax.fv_eq fv fv')
//              then failwith (Format.fmt2 "Expected pattern constructor %s; got %s" (string_of_lid fv.fv_name) (string_of_lid fv'.fv_name));
//              pkg (Pat_cons(fv', []))

//            | Pat_cons(fv, argpats), Tm_app({n=Tm_fvar(fv')}, args)
//            | Pat_cons(fv, argpats), Tm_app({n=Tm_uinst({n=Tm_fvar(fv')}, _)}, args) ->

//              if fv_eq fv fv' |> not
//              then failwith (Format.fmt2 "Expected pattern constructor %s; got %s" (string_of_lid fv.fv_name) (string_of_lid fv'.fv_name));

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

//                | _ -> failwith (Format.fmt2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" (show p) (show e)) in

//              match_args [] args argpats

//           | _ ->
//            failwith (Format.fmt3
//                            "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
//                            (Range.string_of_range qq.p)
//                            (show qq)
//                            (show exp))
//    in
//    aux p exp

 let rec decorated_pattern_as_term (pat:pat) : ML (list bv & term) =
    let mk f : ML term = mk f pat.p in

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
        vars,  S.mk_Tm_app head args pat.p

    | Pat_dot_term eopt ->
        (match eopt with
         | None -> failwith "TcUtil::decorated_pattern_as_term: dot pattern not resolved"
         | Some e -> [], e)


(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)

let comp_univ_opt c : ML _ =
    match c.n with
    | Total _ | GTotal _ -> None
    | Comp c ->
      match c.comp_univs with
      | [] -> None
      | hd::_ -> Some hd

let lcomp_univ_opt lc : ML _ = lc |> TcComm.lcomp_comp |> (fun (c, g) -> comp_univ_opt c, g)

let mk_comp_l mname u_result result pre post flags : ML _ =
  mk_Comp ({ comp_univs=[u_result];
             effect_name=mname;
             result_typ=result;
             comp_pre=pre;
             comp_post=post;
             flags=flags})

let mk_comp md : ML _ = mk_comp_l md.mname

(* [forall x1 ... xn. phi]; used to close specifications over pattern variables *)
let close_formula env (bvs:list bv) (phi:term) : ML term =
  List.fold_right (fun x phi -> U.mk_forall (env.universe_of env x.sort) x phi) bvs phi

(* Close a postcondition over [bvs].  A postcondition is a *strongest*
   postcondition, so the pattern variables are closed existentially. *)
let close_post env (bvs:list bv) (t:typ) (post:term) : ML term =
  if U.is_trivial_post post then post
  else let x = S.new_bv None t in
       U.abs [S.mk_binder x]
             (List.fold_right
                (fun (y:bv) phi -> U.mk_exists (env.universe_of env y.sort) y phi)
                bvs
                (U.apply_post post (S.bv_to_name x)))
             (Some S.post_rc)

let label reason r f : ML term =
    mk (Tm_meta {tm=f; meta=Meta_labeled(reason, r, false)}) f.pos

let label_opt env (reason:option (unit -> ML (list Pprint.document))) r f : ML _ = match reason with
    | None -> f
    | Some reason ->
        if not <| Env.should_verify env
        then f
        else label (reason()) r f

let label_guard r reason (g:guard_t) : ML _ = match g.guard_f with
    | Trivial -> g
    | NonTrivial f -> {g with guard_f=NonTrivial (label reason r f)}

(* Lifting a computation to a larger effect is just a rename: specifications
   are effect-independent in the simplified system. *)
let lift_comp env (c:comp_typ) (m:lident) : ML (comp & guard_t) =
  //an erasable computation may only be lifted to a non-erasable effect
  //if its result type is non-informative
  if Env.is_erasable_effect env c.effect_name
  && not (Env.is_erasable_effect env m)
  && not (N.non_info_norm env c.result_typ)
  then raise_error env Errors.Error_TypeError [
         text "Cannot lift erasable expression from" ^/^ pp c.effect_name
           ^/^ text "~>" ^/^ pp m ^/^ text "since its type" ^/^ pp c.result_typ
           ^/^ text "is informative"
       ];
  S.mk_Comp ({ c with effect_name = m; flags = [] }), Env.trivial_guard

let join_effects env l1_in l2_in : ML _ =
  let l1, l2 = Env.norm_eff_name env l1_in, Env.norm_eff_name env l2_in in
  match Env.join_opt env l1 l2 with
  | Some m -> m
  | None ->
    raise_error env Errors.Fatal_EffectsCannotBeComposed [
        text "Effects" ^/^ pp l1_in ^/^ text "and" ^/^ pp l2_in ^/^ text "cannot be composed"
    ]

let join_lcomp env c1 c2 : ML _ =
  if TcComm.is_total_lcomp c1
  && TcComm.is_total_lcomp c2
  then C.effect_Tot_lid
  else join_effects env c1.eff_name c2.eff_name

// GM, 2023/01/30: This is here to make c2 well-scoped in lift_comps_sep_guards
// below. Is it needed to push a null_binder, as below, when b is None? Not for
// scoping, at least.
let maybe_push (env : Env.env) (b : option bv) : ML Env.env =
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
: ML (lident & comp & comp & guard_t & guard_t) =
  let c1 = Env.unfold_effect_abbrev env c1 in
  let env2 = maybe_push env b in
  let c2 = Env.unfold_effect_abbrev env2 c2 in
  match Env.join_opt env c1.effect_name c2.effect_name with
  | Some m ->
    let c1, g1 = lift_comp env c1 m in
    let c2, g2 = lift_comp env2 c2 m in
    m, c1, c2, g1, g2
  | None ->
    raise_error env Errors.Fatal_EffectsCannotBeComposed [
      text "Effects" ^/^ pp c1.effect_name ^/^ text "and" ^/^ pp c2.effect_name ^/^ text "cannot be composed"
    ]

let lift_comps env c1 c2 (b:option bv) (for_bind:bool)
  : ML (lident & comp & comp & guard_t) =
  let l, c1, c2, g1, g2 = lift_comps_sep_guards
    env
    c1
    c2
    b
    for_bind in
  l, c1, c2, Env.conj_guard g1 g2

let is_pure_effect env l : ML _ =
  let l = norm_eff_name env l in
  lid_equals l C.effect_PURE_lid

let is_ghost_effect env l : ML _ =
  let l = norm_eff_name env l in
  lid_equals l C.effect_GHOST_lid

let is_pure_or_ghost_effect env l : ML _ =
  let l = norm_eff_name env l in
  lid_equals l C.effect_PURE_lid
  || (lid_equals l C.effect_GHOST_lid)

(* Closing a computation over the pattern variables [bvs]: universally quantify
   its precondition and postcondition. *)
let close_wp_comp env bvs (c:comp) : ML _ =
    def_check_scoped c.pos "close_wp_comp" (Env.push_bvs env bvs) c;
    if U.is_ml_comp c then c
    else
      let env_bvs = Env.push_bvs env bvs in
      match c.n with
      | Total _
      | GTotal _ -> c
      | Comp ct ->
        S.mk_Comp ({ ct with
          comp_pre  = close_formula env_bvs bvs ct.comp_pre;
          comp_post = close_post env_bvs bvs ct.result_typ ct.comp_post;
          flags     = ct.flags |> List.filter (function MLEFFECT -> true | _ -> false) })

let close_wp_lcomp env bvs (lc:lcomp) : ML lcomp =
  let bs = bvs |> List.map S.mk_binder in
  lc |>
  TcComm.apply_lcomp
    (close_wp_comp env bvs)
    (fun g -> g |> Env.close_guard env bs |> close_guard_implicits env false bs)

let close_layered_lcomp_with_combinator env bvs lc : ML _ = close_wp_lcomp env bvs lc

(*
 * Closing of computations via substitution
 *)
let close_layered_lcomp_with_substitutions env bvs tms (lc:lcomp) : ML _ =
  let bs = bvs |> List.map S.mk_binder in
  let substs = List.map2 (fun bv tm ->
    NT (bv, tm)
  ) bvs tms in
  lc |>
  TcComm.apply_lcomp
    (SS.subst_comp substs)
    (fun g -> g |> Env.close_guard env bs |> close_guard_implicits env false bs)

let should_not_inline_lc (lc:lcomp) : ML _ =
    false

(* should_return env (Some e) lc:
 * We will "return" e, adding an equality to the VC, if all of the following conditions hold
 * (a) e is a pure or ghost term
 * (b) Its return type, lc.res_typ, is not a sub-singleton (unit, squash, etc), if lc.res_typ is an arrow, then we check the comp type of the arrow
 *     An exception is made for reifiable effects -- they are useful even if they return unit -- except when it is an layered effect, we never return layered effects
 * (c) Its head symbol is not marked irreducible (in this case inlining is not going to help, it is equivalent to having a bound variable)
 * (d) It's not a let rec, as determined by the absence of the SHOULD_NOT_INLINE flag---see issue #1362. Would be better to just encode inner let recs to the SMT solver properly
 *)
let should_return env eopt lc : ML _ =
  let lc_is_unit_or_effectful =
    //if lc.res_typ is not an arrow, arrow_formals_comp returns Tot lc.res_typ
    let c = lc.res_typ |> U.arrow_formals_comp |> snd in
    if U.is_pure_or_ghost_comp c
    then c |> U.comp_result |> N.unfold_whnf env |> U.is_unit
    else true
  in

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

(*
 * Sequential composition in the simplified effect system.
 *
 * Given [c1 : M t1 (requires pre1) (ensures post1)] and, under [x:t1],
 * [c2 : N t2 (requires pre2) (ensures post2)], the composite computation is
 *
 *   M|N t2 (requires pre1 /\ (forall x. post1 x ==> pre2))
 *          (ensures fun y -> forall x. post1 x ==> post2 y)
 *
 * The postcondition of [c1] is thus *assumed* while checking the continuation,
 * which is exactly the intended reading of the specification.
 *)
let discard_specs = Env.discard_specs

let mk_bind env
  (c1:comp)
  (b:option bv)
  (c2:comp)
  (flags:list cflag)
  (r1:Range.t) : ML (comp & guard_t) =

  let env2 = maybe_push env b in
  (* Composing specifications is not cheap: every bind costs a normalization
     plus a traversal of both specifications.  When nobody will look at the
     result, keep only the effect label and the result type.  (Compare
     [strengthen_comp], which has always short-circuited in phase 1.) *)
  if discard_specs env
  then
    let m, _c1, c2, g_lift = lift_comps env c1 c2 b true in
    let ct2 = Env.comp_to_comp_typ env2 c2 in
    let u2 =
      match ct2.comp_univs with
      | u::_ -> u
      | [] -> env.universe_of env2 ct2.result_typ in
    S.mk_triv_comp [u2] m ct2.result_typ flags, g_lift
  else begin
  def_check_scoped r1 "mk_bind.in.c1" env c1;
  def_check_scoped r1 "mk_bind.in.c2" env2 c2;
  let m, c1, c2, g_lift = lift_comps env c1 c2 b true in
  let ct1 = Env.comp_to_comp_typ env c1 in
  let ct2 = Env.comp_to_comp_typ env2 c2 in

  let u1 =
    match ct1.comp_univs with
    | u::_ -> u
    | [] -> env.universe_of env ct1.result_typ in
  let u2 =
    match ct2.comp_univs with
    | u::_ -> u
    | [] -> env.universe_of env2 ct2.result_typ in

  let x =
    match b with
    | Some x -> { x with sort = ct1.result_typ }
    | None -> S.new_bv None ct1.result_typ in
  (* [x] may well not occur in the composed specification, in which case the
     quantifier below is dropped; conjoining the logical content of its type
     keeps a refinement (or a [squash]) from being silently lost. *)
  let post1_x =
    let t1 = N.normalize_refinement N.whnf_steps env ct1.result_typ in
    U.mk_conj_simp (Env.type_hypothesis env t1 (S.bv_to_name x))
                   (U.apply_post ct1.comp_post (S.bv_to_name x)) in

  (* When [post1 x] pins [x] down to a term, as in the [fun x -> x == e]
     postcondition that [return_value] produces, we apply the one-point rule
     and substitute instead of quantifying.  Without this every intermediate
     computation would contribute an [exists] to the verification condition. *)
  let one_point : option (term & term) = TcComm.one_point_defn x post1_x in

  (* [forall x. post1 x ==> phi], dropping the quantifier when it is vacuous.
     This is the weakest-precondition direction, used for [pre]. *)
  let quantify (phi:term) : ML term =
    if U.is_t_true phi then phi
    else
      match one_point with
      | Some (v, rest) -> SS.subst [NT (x, v)] (U.mk_imp_simp rest phi)
      | None ->
        let body = U.mk_imp_simp post1_x phi in
        if mem x (Free.names body)
        then U.mk_forall u1 x body
        else body
  in

  (* [exists x. post1 x /\ phi], the strongest-postcondition direction.
     [c1] did produce a value of type [ct1.result_typ], so dropping the
     existential when [x] does not occur is sound. *)
  let compose (phi:term) : ML term =
    match one_point with
    | Some (v, rest) -> SS.subst [NT (x, v)] (U.mk_conj_simp rest phi)
    | None ->
      let body = U.mk_conj_simp post1_x phi in
      if mem x (Free.names body)
      then U.mk_exists u1 x body
      else body
  in

  let pre = U.mk_conj_simp ct1.comp_pre (quantify ct2.comp_pre) in
  let post =
    let y = S.new_bv None ct2.result_typ in
    let body = compose (U.apply_post ct2.comp_post (S.bv_to_name y)) in
    if U.is_t_true body
    then S.trivial_post ct2.result_typ
    else U.abs [S.mk_binder y] body (Some S.post_rc)
  in
  let res = mk_comp_l m u2 ct2.result_typ pre post flags in
  def_check_scoped r1 "mk_bind.out" env res;
  res, g_lift
  end

(* [strengthen_comp env r c f] asserts [f] before running [c] *)
let strengthen_comp env (reason:option (unit -> ML (list Pprint.document))) (c:comp) (f:formula) flags : ML (comp & guard_t) =
    if env.phase1
    then c, Env.trivial_guard
    else
      let r = Env.get_range env in
      let f = label_opt env reason r f in
      let assert_c =
        mk_comp_l C.effect_PURE_lid S.U_zero S.t_unit f (S.trivial_post S.t_unit) [] in
      mk_bind env assert_c None c flags r

(*
 * Return a value in eff_lid: the postcondition records the returned value.
 * Note that the *result type* is left alone: we never refine it.
 *)
let return_value env eff_lid u_t_opt t v : ML (comp & guard_t) =
  let u =
    match u_t_opt with
    | None -> env.universe_of env t
    | Some u -> u in
  let x = S.new_bv None t in
  let post =
    U.abs [S.mk_binder x] (U.mk_eq2 u t (S.bv_to_name x) v) (Some S.post_rc) in
  mk_comp_l (Env.norm_eff_name env eff_lid) u t S.trivial_pre post [],
  Env.trivial_guard

let weaken_flags flags : ML _ =
    flags |> List.filter (function MLEFFECT -> true | _ -> false)

(* [weaken_comp env c f] assumes [f] before running [c] *)
let weaken_comp env (c:comp) (formula:term) : ML (comp & guard_t) =
  if U.is_ml_comp c
  then c, Env.trivial_guard
  else
    let r = Env.get_range env in
    let assume_c =
      mk_comp_l C.effect_PURE_lid S.U_zero S.t_unit
                S.trivial_pre
                (U.abs [S.null_binder S.t_unit] formula (Some S.post_rc))
                [] in
    mk_bind env assume_c None c (weaken_flags (U.comp_flags c)) r

let weaken_precondition env lc (f:guard_formula) : ML lcomp =
  let weaken () =
      let c, g_c = TcComm.lcomp_comp lc in
            match f with
           | Trivial -> c, g_c
           | NonTrivial f ->
             let c, g_w = weaken_comp env c f in
             c, Env.conj_guard g_c g_w
  in
  TcComm.mk_lcomp lc.eff_name lc.res_typ (weaken_flags lc.cflags) weaken

let strengthen_precondition
            (reason:option (unit -> ML (list Pprint.document)))
            env
            (e_for_debugging_only:term)
            (lc:lcomp)
            (g0:guard_t)
    : ML (lcomp & guard_t) =
    if Env.is_trivial_guard_formula g0
    then lc, g0
    else let flags = [] in
         let strengthen () =
            let c, g_c = TcComm.lcomp_comp lc in
            if Options.admit_smt_queries ()
            then c, g_c
            else let g0 = Rel.simplify_guard env g0 in
                 match guard_form g0 with
                 | Trivial -> c, g_c
                 | NonTrivial f ->
                   if Debug.extreme ()
                   then Format.print2 "-------------Strengthening pre-condition of term %s with guard %s\n"
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


let lcomp_has_trivial_postcondition (lc:lcomp) : ML _ =
    TcComm.is_tot_or_gtot_lcomp lc

(*
 * This is used in bind, when c1 is a Tot (x:unit{phi})
 * In such cases, e1 is inlined in c2, but we still want to capture inhabitance of phi
 *
 * For wp-effects, we do forall (x:unit{phi}). c2
 * For layered effects, we do: weaken_comp (phi[x/()]) c2
 *
 * We should make wp-effects also same as the layered effects
 *)
let maybe_capture_unit_refinement (env:env) (t:term) (x:bv) (c:comp)
: ML (comp & guard_t & bool)
= let t = N.normalize_refinement N.whnf_steps env t in
  match t.n with
  | Tm_refine {b; phi} ->
    let is_unit =
      match b.sort.n with
      | Tm_fvar fv -> S.fv_eq_lid fv C.unit_lid
      | _ -> false in
    if is_unit then
      let b, phi = SS.open_term_bv b phi in
      let phi = SS.subst [NT (b, S.unit_const)] phi in
      (* [x : unit{phi}], so its only possible value is [()].  Substituting it
         away is what actually *closes* [c] over [x]; the caller relies on the
         [true] below to skip the universal closure. *)
      let c = SS.subst_comp [NT (x, S.unit_const)] c in
      let c, g = weaken_comp env c phi in
      c, g, true
    else c, Env.trivial_guard, false
  | Tm_fvar fv when S.fv_eq_lid fv C.unit_lid ->
    (* Likewise for an unrefined [unit] binder: [()] is its only value, so the
       binder carries no information and need not be quantified over. *)
    SS.subst_comp [NT (x, S.unit_const)] c, Env.trivial_guard, true
  | _ -> c, Env.trivial_guard, false

let optimize_bind_vc () : ML _ = Options.Ext.enabled "optimize_let_vc"

(* [optimize_let_vc] keeps a let-bound variable opaque in the verification
   condition, turning [phi[e/x]] into [forall x. x == e ==> phi], which the SMT
   encoding emits as a [declare-fun]/[assert] pair.  Substituting instead would
   make VCs blow up exponentially (see issue #3800), so it only happens for
   non-let bindings (intermediate values) and for [let unfold]. *)
let bind
      (r1:Range.t)
      (is_let_binding:bool) 
      (env:Env.env) (e1opt:option term) (lc1:lcomp) (binder_lc2:lcomp_with_binder) : ML lcomp =
  let (b, lc2) = binder_lc2 in
  let debug (f: unit -> ML unit) : ML unit =
      if Debug.extreme () || !dbg_bind
      then f ()
  in
  let lc1, lc2 = N.ghost_to_pure_lcomp2 env (lc1, lc2) in  //downgrade from ghost to pure, if possible
  let joined_eff = join_lcomp env lc1 lc2 in
  let bind_flags =
      if TcComm.is_total_lcomp lc1 && TcComm.is_total_lcomp lc2
      then [TOTAL]
      else []
  in
  let bind_it () =
       begin
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
            Format.print5 "(1) bind (is_let_binding=%s): \n\tc1=%s\n\tx=%s\n\tc2=%s\n\te1=%s\n(1. end bind)\n"
            (show is_let_binding)
            (show c1)
            (match b with
                | None -> "none"
                | Some x -> show x)
            (show c2)
            (match e1opt with
             | None -> "none"
             | Some e1 -> show e1));
          let aux () =
            if U.is_ml_comp c1 && U.is_ml_comp c2
            then Inl (c2, "both ml")
            else Inr "both are not ML"
          in
          let try_simplify () : ML (either (comp & guard_t & string) string) =
            let aux_with_trivial_guard () =
              match aux () with
              | Inl (c, reason) -> Inl (c, trivial_guard, reason)
              | Inr reason -> Inr reason in
            (* If the binder is unused in the continuation, simply dropping it
               would also drop the information that its (refined) type is
               inhabited.  In that case go through mk_bind, which restates the
               typing hypothesis in the postcondition. *)
            (* A term whose head is a data constructor (or a literal) gets its
               type from the constructor's own typing axiom in the SMT
               encoding, so restating it adds nothing.  This matters for
               performance: an application nested [n] deep would otherwise
               contribute [n] typing hypotheses about terms of size O(n),
               i.e. a postcondition quadratic in the size of the term.
               Explicit let bindings are exempt: `let _ = (x, y) in ...` is an
               idiom for bringing exactly this fact into scope. *)
            let has_evident_type () : ML bool =
              match e1opt with
              | None -> false
              | Some e ->
                let hd, _ = U.head_and_args_full e in
                match (U.un_uinst hd).n with
                | Tm_fvar fv -> Env.is_datacon env (S.lid_of_fv fv)
                | Tm_constant _ -> true
                | _ -> false in
            let drops_typing_info () : ML bool =
              match b with
              | Some x when not (discard_specs env)
                         && (is_let_binding || not (has_evident_type ()))
                         && not (mem x (Free.names_comp c2)) ->
                let t = N.normalize_refinement N.whnf_steps env (U.comp_result c1) in
                let is_unit_refinement =
                  match t.n with
                  | Tm_refine {b} ->
                    (match b.sort.n with
                     | Tm_fvar fv -> S.fv_eq_lid fv C.unit_lid
                     | _ -> false)
                  | _ -> false in
                not is_unit_refinement &&
                not (U.is_t_true (Env.type_hypothesis env t (S.bv_to_name x)))
              | _ -> false in
            if drops_typing_info ()
            then Inr "binder is unused but its type carries information"
            else if U.is_total_comp c1
            then (*
                  * Helper routine to close the compuation c with c1's return type
                  * When c1's return type is of the form _:t{phi}, is is useful to know
                  *   that t{phi} is inhabited, even if c1 is inlined etc.
                  *)
                let maybe_close_with_unit_refinement (x:bv) (c:comp) =
                  let x = { x with sort = U.comp_result c1 } in
                  maybe_capture_unit_refinement env x.sort x c
                in
                let close_with_type_of_x (x:bv) (c:comp) =
                  let c, g, closed = maybe_close_with_unit_refinement x c in
                  if closed then c, g
                  else close_wp_comp env [x] c, Env.close_guard env [S.mk_binder x] g
                in
                let is_layered = false in
                match e1opt, b with
                | Some e, Some x when (
                    not (optimize_bind_vc()) || // optimization is disabled
                    not is_let_binding || //non-let bindings, e.g., in applications, are inlined
                    is_layered // layered effects do not always support closing with universal quantification
                  ) ->
                  let c2, g_close, _ =
                    c2 |> SS.subst_comp [NT (x, e)] |> maybe_close_with_unit_refinement x
                  in
                  Inl (c2, Env.conj_guards [
                     g_c1;
                     Env.map_guard g_c2 (SS.subst [NT (x, e)]);
                     g_close ], "c1 Tot")
                | Some e, Some x -> (
                  let default_with_eqn () =
                    let c2, g_c2' = weaken_comp (Env.push_binders env [S.mk_binder x]) c2 (U.mk_eq2 (env.universe_of env x.sort) x.sort e (bv_to_name x)) in
                    let c2, g_close = close_with_type_of_x x c2 in
                    Inl (c2, Env.conj_guards [
                              trivial_guard;
                              Env.close_guard env [S.mk_binder x] g_c2';
                              g_close], "c1 Tot with eq")
                  in
                  if U.is_tot_or_gtot_comp c2
                  then (
                    if is_let_binding
                    then (
                      if not (mem x (Free.names_comp c2))
                      then (
                        //x is not free in c2; but if it is a unit refinement, the
                        //binder may legitimately be unused in the continuation,
                        //with only its type relevant---so close with unit refinement
                        //See, e.g., Unit1.Basic.bind_test2
                        //Note, closing with the type of x unconditionally causes
                        //other examples to blow up, e.g., in Registers.List.fst in native_tactics
                        //closing with the type of every let binding even with a tot continuation
                        //moves the continuation out of Tot to pure, and then
                        //we fall into the default case with equations.
                        //So, this is trying to strike a balance:
                        //Compact VCs for let bound Tot terms with Tot/GTot continuations
                        //remaining in Tot/GTot;
                        //Except if the let-bound terms binds a unit refinement,
                        //then we close with the unit refinement, so that the
                        //the refinement is captured.
                        let c2, g_close, _ = maybe_close_with_unit_refinement x c2 in
                        Inl (c2, Env.conj_guards [ trivial_guard; g_close],  "both Tot/GTot")
                      )
                      else default_with_eqn ()
                    )
                    else Inl (SS.subst_comp [NT(x,e)] c2, trivial_guard, "both Tot/GTot")
                  )
                  else default_with_eqn ()
                )
                | _, Some x ->
                   let c2, g_close = close_with_type_of_x x c2 in
                   Inl (c2, Env.conj_guards [ trivial_guard; g_close ], "c1 Tot only close")
                 | _, _ -> aux_with_trivial_guard ()
            else if U.is_tot_or_gtot_comp c1
                 && U.is_tot_or_gtot_comp c2
            then Inl (S.mk_GTotal (U.comp_result c2), trivial_guard, "both GTot")
            else aux_with_trivial_guard ()
          in
          match try_simplify () with
          | Inl (c, g, reason) ->
            debug (fun () ->
                Format.print2 "(2) bind: Simplified (because %s) to\n\t%s\n"
                            reason
                            (show c));
            c, g
          | Inr reason ->
            debug (fun () ->
                Format.print1 "(2) bind: Not simplified because %s\n" reason);

            let mk_bind c1 b c2 g =  (* AR: end code for inlining pure and ghost terms *)
              let c, g_bind = mk_bind env c1 b c2 bind_flags r1 in
              c, Env.conj_guard g g_bind in

            (* AR: we have let the previously applied bind optimizations take effect,
                below is the code to do more inlining for pure and ghost terms *)
            let u_res_t1, res_t1 =
              let t = U.comp_result c1 in
              match comp_univ_opt c1 with
              | None -> env.universe_of env t, t
              | Some u -> u, t in
            //c1 and c2 are bound to the input comps
            if Some? b
            && should_return env e1opt lc1
            then let e1 = Option.must e1opt in
                 let x = Option.must b in
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

                 if false
                 then
                      let _ = debug (fun () ->
                        Format.print2 "(3) bind (case a): Substituting %s for %s\n" (N.term_to_string env e1) (show x)) in
                      let c2 = SS.subst_comp [NT(x,e1)] c2 in
                      let g = Env.conj_guard g_c1 (Env.map_guard g_c2 (SS.subst [NT (x, e1)])) in
                      mk_bind c1 b c2 g
                 else
                      let _ = debug (fun () ->
                        Format.print2 "(3) bind (case b): Adding equality %s = %s\n" (N.term_to_string env e1) (show x)) in
                      let c2 = 
                        if not (optimize_bind_vc()) || not is_let_binding
                        then SS.subst_comp [NT(x,e1)] c2
                        else c2
                      in
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

let weaken_guard g1 g2 : ML _ = match g1, g2 with
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
let assume_result_eq_pure_term_in_m env (m_opt:option lident) (e:term) (lc:lcomp) : ML lcomp =
  (*
   * AR: m is the effect that we are going to do return in
   *)
  let m =
    if m_opt |> None? || is_ghost_effect env lc.eff_name
    then C.effect_PURE_lid
    else m_opt |> Option.must in

  let flags = lc.cflags in

  let refine () : ML (comp & guard_t) =
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
            let ret = TcComm.lcomp_of_comp <| Env.comp_set_flags env_x ret [] in
            let eq = U.mk_eq2 u_t t xexp e in
            let eq_ret = weaken_precondition env_x ret (NonTrivial eq) in
            let bind_c, g_bind = TcComm.lcomp_comp (bind e.pos false env None (TcComm.lcomp_of_comp c) (Some x, eq_ret)) in
            Env.comp_set_flags env bind_c flags, Env.conj_guards [g_c; g_ret; g_bind]
  in

  if should_not_inline_lc lc
  then raise_error e Errors.Fatal_UnexpectedTerm  [
         text "assume_result_eq_pure_term cannot inline an non-inlineable lc : " ^^ pp e;
       ]

  else let c, g = refine () in
       TcComm.lcomp_of_comp_guard c g

let maybe_assume_result_eq_pure_term_in_m env (m_opt:option lident) (e:term) (lc:lcomp) : ML lcomp =
  let should_return =
      not env.phase1
   && should_return env (Some e) lc
   && not (TcComm.is_lcomp_partial_return lc)
  in
  if not should_return then lc
  else assume_result_eq_pure_term_in_m env m_opt e lc

let maybe_assume_result_eq_pure_term env e lc : ML _ =
  maybe_assume_result_eq_pure_term_in_m env None e lc

let maybe_return_e2_and_bind
        (r:Range.t)
        (is_let_binding:bool)
        (env:env)
        (e1opt:option term)
        (lc1:lcomp)
        (e2:term)
        (xlc2: option bv & lcomp)
   : ML lcomp =
   let (x, lc2) = xlc2 in
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
           Env.join_opt env eff1 eff2 |> None?
        then assume_result_eq_pure_term_in_m env_x (eff1 |> Some) e2 lc2
        else if (not (is_pure_or_ghost_effect env eff1)
             ||  should_not_inline_lc lc1)
             && is_pure_or_ghost_effect env eff2
        then maybe_assume_result_eq_pure_term_in_m env_x (eff1 |> Some) e2 lc2
        else lc2 in //the resulting computation is still pure/ghost and inlineable; no need to insert a return
   bind r is_let_binding env e1opt lc1 (x, lc2)

let fvar_env env lid : ML _ =  S.fvar (Ident.set_lid_range lid (Env.get_range env)) None

(*
 * The comp type for a match with no cases: PURE t (requires False)
 *)
let comp_false env (u:universe) (t:typ) : ML comp =
  mk_comp_l C.effect_PURE_lid u t (fvar_env env C.false_lid) (S.trivial_post t) []

(*
 * Conjunction of two branch computations under the branch condition [p]:
 *
 *   pre  = (p ==> pre1) /\ (~p ==> pre2)
 *   post = fun x -> (p ==> post1 x) /\ (~p ==> post2 x)
 *)
let mk_conjunction env (u_a:universe) (a:term) (p:typ) (ct1:comp_typ) (ct2:comp_typ) (r:Range.t)
: ML (comp & guard_t) =
  let np = U.mk_neg p in
  let pre = U.mk_conj_simp (U.mk_imp_simp p ct1.comp_pre) (U.mk_imp_simp np ct2.comp_pre) in
  let post =
    if U.is_trivial_post ct1.comp_post && U.is_trivial_post ct2.comp_post
    then S.trivial_post a
    else
      let x = S.new_bv None a in
      U.abs [S.mk_binder x]
            (U.mk_conj_simp
               (U.mk_imp_simp p  (U.apply_post ct1.comp_post (S.bv_to_name x)))
               (U.mk_imp_simp np (U.apply_post ct2.comp_post (S.bv_to_name x))))
            (Some S.post_rc)
  in
  mk_comp_l ct1.effect_name u_a a pre post [], Env.trivial_guard

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
  : ML (list formula & formula)
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
  (lcases:list (formula & lident & list cflag & (bool -> ML lcomp)))
  (scrutinee:bv) : ML lcomp =
    let env = Env.push_binders env0 [scrutinee |> S.mk_binder] in
    let eff = List.fold_left (fun eff (_, eff_label, _, _) -> join_effects env eff eff_label)
                             C.effect_PURE_lid
                             lcases
    in
    let bind_cases_flags = [] in
    let bind_cases () =
        let u_res_t = env.universe_of env res_t in
        let maybe_return eff_label_then (cthen: bool -> ML lcomp) : ML lcomp =
           if not (is_pure_or_ghost_effect env eff)
           then cthen true //inline each branch, if eligible
           else cthen false //the entire match is pure and inlineable
        in

        let neg_branch_conds, exhaustiveness_branch_cond =
          get_neg_branch_conds (lcases |> List.map (fun (g, _, _, _) -> g)) in

        let comp, g_comp =
          match lcases with
          | [] -> comp_false env u_res_t res_t, Env.trivial_guard
          | _ ->
            let lcases, neg_branch_conds, comp, g_comp =
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

              lcases, neg_branch_conds, c, g in

            List.fold_right2 (fun (g, eff_label, _, cthen) neg_cond (celse, g_comp) ->
              let cthen, g_then = TcComm.lcomp_comp (maybe_return eff_label cthen) in
              let m, cthen, celse, g_lift_then, g_lift_else =
                lift_comps_sep_guards env cthen celse None false in
              let ct_then = cthen |> Env.comp_to_comp_typ env in
              let ct_else = celse |> Env.comp_to_comp_typ env in

              let c, g_conjunction =
                mk_conjunction env u_res_t res_t (U.b2t g) ct_then ct_else (Env.get_range env) in

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

              c,
              Env.conj_guards [g_comp; g_then; g_else; g_conjunction]
            ) lcases neg_branch_conds (comp, g_comp) in

        //strengthen comp with the exhaustiveness check
        let comp, g_comp =
          let c, g =
            let check = U.mk_imp exhaustiveness_branch_cond U.t_false in
            let check = label Err.exhaustiveness_check (Env.get_range env) check   in
            strengthen_comp env None comp check bind_cases_flags in
          c, Env.conj_guard g_comp g in

        comp, g_comp
    in
    TcComm.mk_lcomp eff res_t bind_cases_flags bind_cases

let check_comp env (use_eq:bool) (e:term) (c:comp) (c':comp) : ML (term & comp & guard_t) =
  def_check_scoped c.pos "check_comp.c" env c;
  def_check_scoped c'.pos "check_comp.c'" env c';
  if Debug.extreme () then
    Format.print4 "Checking comp relation:\n%s has type %s\n\t %s \n%s\n"
            (show e)
            (show c)
            (if use_eq then "$:" else "<:")
            (show c');
  (* [use_eq] (a [$]-marked binder, or an equality-typed ascription) demands
     that the annotation match exactly, so that unification, rather than
     subtyping, is what relates the two and implicit arguments can be solved
     from the computed computation type.  This is what makes the [$f] idiom of
     [FStar.Classical.forall_intro] work: the implicit [p] occurs only in the
     postcondition of [f]'s type, and is solved by unifying that postcondition
     with the one computed for the argument.

     Unification is however too strong to *demand* of a specification: a term
     is free to guarantee more than it was asked to, e.g. a lambda passed to a
     [$]-binder whose expected postcondition is trivial still computes a
     postcondition of its own.  So the specification is unified only when
     there is something to solve in it --- and related by subsumption
     otherwise.  Note that the *result type* is related by equality either way;
     that much is essential, as it is what keeps a [$]-binder from being
     instantiated by subtyping. *)
  let spec_has_uvars (c:comp) : ML bool =
    not (Free.uvars (U.comp_pre c) |> is_empty)
    || not (Free.uvars (U.comp_post c) |> is_empty) in
  let eq_result_and_subsume () =
    match Rel.try_teq true env (U.comp_result c) (U.comp_result c') with
    | None -> None
    | Some g_eq ->
      match Rel.sub_comp env c c' with
      | None -> None
      | Some g -> Some (g_eq ++ g) in
  let g =
    if use_eq
    then if spec_has_uvars c || spec_has_uvars c'
         then match Rel.eq_comp env c c' with
              | Some g -> Some g
              | None -> eq_result_and_subsume ()
         else eq_result_and_subsume ()
    else Rel.sub_comp env c c' in
  match g with
    | None ->
        if use_eq
        then Err.computed_computation_type_does_not_match_annotation_eq env (Env.get_range env) e c c'
        else Err.computed_computation_type_does_not_match_annotation env (Env.get_range env) e c c'
    | Some g -> e, c', g

(*
 * The universe of a computation type [M t (requires pre) (ensures post)].
 *
 * Since an effect is now just a name plus a specification, a computation
 * type is inhabited by (a description of) a value of type [t]: its universe
 * is the universe of [t], whatever the effect.
 *)
(*
 * The universe of [M t]: the universe of [t] if [M] is pure/ghost or marked
 * [total], and u#0 otherwise.  A computation in a partial effect need not
 * return, so an arrow into it is proof-irrelevant and lives in Type0; this
 * is what makes e.g. [unit -> Dv t : Type0] for any [t : Type u#a].
 *)
let universe_of_comp env u_res c : ML _ =
  let c_lid = c |> U.comp_effect_name |> Env.norm_eff_name env in
  if U.is_pure_or_ghost_effect c_lid then u_res
  else if Env.lookup_effect_quals env c_lid |> List.existsb (fun q -> q = S.TotalEffect)
  then u_res
  else S.U_zero

let check_trivial_precondition_wp env c : ML _ =
  let ct = c |> Env.unfold_effect_abbrev env in
  let vc = ct.comp_pre in
  ct, vc, Env.guard_of_guard_formula <| NonTrivial vc

//Decorating terms with monadic operators
let maybe_lift env e c1 c2 t : ML _ =
    // Tot/GTot are abbreviations of PURE/GHOST, but they may be used in Prims
    // before those abbreviations are declared; normalize them by hand.
    let norm_eff l =
      let l = Env.norm_eff_name env l in
      if Ident.lid_equals l C.effect_Tot_lid then C.effect_PURE_lid
      else if Ident.lid_equals l C.effect_GTot_lid then C.effect_GHOST_lid
      else l
    in
    let m1 = norm_eff c1 in
    let m2 = norm_eff c2 in
    if Ident.lid_equals m1 m2
    || (U.is_pure_effect c1 && U.is_ghost_effect c2)
    || (U.is_pure_effect c2 && U.is_ghost_effect c1)
    then e
    else mk (Tm_meta {tm=e; meta=Meta_monadic_lift(m1, m2, t)}) e.pos

let maybe_monadic env e c t : ML _ =
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
                : ML (term & lcomp) =
    match Env.try_lookup_lid env f with
    | Some _ ->
        if !dbg_Coercions then
            Format.print1 "Coercing with %s!\n" (Ident.string_of_lid f);
        let lc2 = TcComm.lcomp_of_comp <| comp2 in
        let lc_res = bind e.pos false env (Some e) lc (None, lc2) in
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
                                (Format.fmt1 "Coercion %s was not found in the environment, not coercing."
                                            (string_of_lid f));
        e, lc

type isErased =
    | Yes of term
    | Maybe
    | No

let rec check_erased (env:Env.env) (t:term) : ML isErased =
  let norm' = N.normalize [Beta; Eager_unfolding;
                           UnfoldUntil delta_constant;
                           Exclude Zeta; Primops;
                           Unascribe; Unmeta; Unrefine;
                           Weak; HNF; Iota]
  in
  let t = norm' env t in
  let h, args = U.head_and_args_full t in
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
  (*   Format.print2 "check_erased (%s) = %s\n" *)
  (*     (show t) *)
  (*     (match r with *)
  (*      | Yes a -> "Yes " ^ show a *)
  (*      | Maybe -> "Maybe" *)
  (*      | No -> "No"); *)
  r

let rec first_opt (f : 'a -> ML (option 'b)) (xs : list 'a) : ML (option 'b) =
  match xs with
  | [] -> None
  | x::xs -> Option.catch (f x) (fun () -> first_opt f xs)

let (let?) = Option.bind
let bool_guard (b:bool) : ML (option unit) =
  if b then Some () else None

let find_coercion (env:Env.env) (checked: lcomp) (exp_t: typ) (e:term)
: ML (option (term & lcomp & guard_t))
// returns coerced term, new lcomp type, and guard
// or None if no coercion applied
=
 Errors.with_ctx "find_coercion" (fun () ->
  let rec is_type retry t : ML bool =
      match (SS.compress t).n with
      | Tm_type _ -> true
      | _ when retry ->
        let t = N.unfold_whnf env t in
        let t = U.unrefine t in (* mostly to catch `prop` too *)
        is_type false t
      | _ -> false
  in
  let is_type = is_type true in
  let rec head_of (t : term) : ML term =
      match (compress t).n with
      | Tm_match {scrutinee=t}
      | Tm_ascribed {tm=t}
      | Tm_meta {tm=t} -> head_of t
      | Tm_app _ ->
        let t, _ = U.head_and_args_full t in
        head_of t
      | Tm_abs _ ->
        let _, t, _ = U.abs_formals_ln t in
        head_of t
      | Tm_refine {b} -> head_of b.sort
      | _ -> t
  in
  let is_prop t : ML bool =
    match (SS.compress (head_of t)).n with
    | Tm_fvar fv -> S.fv_eq_lid fv C.prop_lid
    | _ -> false
  in
  let is_bool t : ML bool =
    match (SS.compress (head_of t)).n with
    | Tm_fvar fv -> S.fv_eq_lid fv C.bool_lid
    | _ -> false
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
  let head, args = U.head_and_args_full computed_t in

  (* The expected type according to the context. *)
  let exp_t = head_unfold env exp_t in

  match (U.un_uinst head).n, args with
  (* b2t is primitive... for now *)
  | Tm_fvar fv, [] when S.fv_eq_lid fv C.bool_lid && is_prop exp_t ->
    let lc2 = TcComm.lcomp_of_comp <| S.mk_Total S.t_prop in
    let lc_res = bind e.pos false env (Some e) checked (None, lc2) in
    Some (U.mk_b2t e, lc_res, Env.trivial_guard)

  (* squash *)
  | Tm_fvar fv, [] when S.fv_eq_lid fv C.prop_lid && is_type exp_t ->
    let lc2 = TcComm.lcomp_of_comp <| S.mk_Total U.ktype0 in
    let lc_res = bind e.pos false env (Some e) checked (None, lc2) in
    Some (U.mk_squash e, lc_res, Env.trivial_guard)
  
  (* squash + b2t *)
  | Tm_fvar fv, [] when S.fv_eq_lid fv C.bool_lid && is_type exp_t ->
    let lc2 = TcComm.lcomp_of_comp <| S.mk_Total U.ktype0 in
    let lc_res = bind e.pos false env (Some e) checked (None, lc2) in
    Some (U.mk_squash (U.mk_b2t e), lc_res, Env.trivial_guard)

  (* t2b *)
  | Tm_fvar fv, [] when S.fv_eq_lid fv C.prop_lid && is_bool exp_t ->
    let lc2 = TcComm.lcomp_of_comp <| S.mk_GTotal U.t_bool in
    let lc_res = bind e.pos false env (Some e) checked (None, lc2) in
    Some (U.mk_t2b e, lc_res, Env.trivial_guard)

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

    let candidates = Env.lookup_attr env (string_of_lid C.coercion_lid) in
    candidates |> first_opt (fun se ->
      (* `f` is the candidate coercion, `e` the term to coerce *)
      let? f_name, f_us, f_typ =
        match se.sigel with
        | Sig_let {lbs=(_,[lb])} -> Some (S.lid_of_fv (Inr?.v lb.lbname), lb.lbunivs, lb.lbtyp)
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

let maybe_coerce_lc env (e:term) (lc:lcomp) (exp_t:term) : ML (term & lcomp & guard_t) =
  let head_types_equal t0 t1 =
    match (U.un_uinst (U.unrefine t0)).n, (U.un_uinst (U.unrefine t1)).n with
    | Tm_fvar fv0, Tm_fvar fv1 -> S.fv_eq fv0 fv1
    | _ -> false
  in
  let should_coerce =
      env.phase1 &&
      not env.nocoerce &&
      not (head_types_equal lc.res_typ exp_t)
  in
  if not should_coerce then (
    if !dbg_Coercions then
      Format.print4 "(%s) NOT Trying to coerce %s from type (%s) to type (%s)\n"
              (show e.pos) (show e) (show lc.res_typ) (show exp_t);
    (e, lc, Env.trivial_guard)
  ) else (
    if !dbg_Coercions then
      Format.print4 "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
              (show e.pos) (show e) (show lc.res_typ) (show exp_t);
    match find_coercion env lc exp_t e with
    | Some (coerced, lc, g) ->
      let _ = if !dbg_Coercions then
              Format.print3 "(%s) COERCING %s to %s\n"
                      (Range.string_of_range e.pos)
                      (show e)
                      (show coerced)
      in
      coerced, lc, g
    | None ->
      let _ = if !dbg_Coercions then
              Format.print1 "(%s) No user coercion found\n"
                      (Range.string_of_range e.pos)
      in
      
      (* TODO: hide/reveal also user coercions? it's trickier for sure *)

      let strip_hide_or_reveal (e:term) (hide_or_reveal:lident) : ML (option term) =
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
            let e_hide = Option.dflt e_hide (strip_hide_or_reveal e C.reveal) in
            e_hide, lc, g
          end

      | Yes ty, No ->
        let u = env.universe_of env ty in
        let e_reveal, lc = coerce_with env e lc C.reveal [u] [S.iarg ty] (S.mk_GTotal ty) in
        let e_reveal = Option.dflt e_reveal (strip_hide_or_reveal e C.hide) in
        e_reveal, lc, Env.trivial_guard

      | _ ->
        e, lc, Env.trivial_guard
  )

let weaken_result_typ env (e:term) (lc:lcomp) (t:typ) (use_eq:bool) : ML (term & lcomp & guard_t) =
  if Debug.high () then
    Format.print4 "weaken_result_typ use_eq=%s e=(%s) lc=(%s) t=(%s)\n"
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

            let set_result_typ (c:comp) : ML comp = Util.set_result_typ c t in

            if TEQ.eq_tm env t res_t = TEQ.Equal then begin  //if the two types res_t and t are same, then just set the result type
              if Debug.extreme()
              then Format.print2 "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
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
                let lc = bind e.pos false env (Some e) (TcComm.lcomp_of_comp c) (Some x, TcComm.lcomp_of_comp cret) in
                if Debug.extreme ()
                then Format.print4 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                               (show e) (show c) (show t) (TcComm.lcomp_to_string lc);
                let c, g_lc = TcComm.lcomp_comp lc in
                set_result_typ c, Env.conj_guards [g_c; gret; g_lc]
              else begin
                if Debug.extreme ()
                then Format.print2 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                               (show res_t) (show c);
                set_result_typ c, g_c
              end
          in
          let lc = TcComm.mk_lcomp lc.eff_name t lc.cflags strengthen_trivial in
          e, lc, g

        | NonTrivial f ->
          let g = {g with guard_f=Trivial} in
          let strengthen () =
              begin
                  //try to normalize one more time, since more unification variables may be resolved now
                  let f = N.normalize [Env.Beta; Env.Eager_unfolding; Env.Simplify; Env.Primops] env f in
                  match (SS.compress f).n with
                      | Tm_abs _ when
                          (match U.abs_formals_ln f with
                           | _, {n=Tm_fvar fv}, _ -> S.fv_eq_lid fv C.true_lid
                           | _ -> false) ->
                        //it's trivial
                        let lc = {lc with res_typ=t} in //NS: what's the point of this?
                        TcComm.lcomp_comp lc

                      | _ ->
                          let c, g_c = TcComm.lcomp_comp lc in
                          if Debug.extreme ()
                          then Format.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n"
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
                          let c = bind e.pos false env (Some e) (TcComm.lcomp_of_comp c) (Some x, eq_ret) in
                          let c, g_lc = TcComm.lcomp_comp c in
                          if Debug.extreme ()
                          then Format.print1 "Strengthened to %s\n" (Normalize.comp_to_string env c);
                          c, Env.conj_guards [g_c; gret; g_lc]
                end
          in
          let flags = [] in
          let lc = TcComm.mk_lcomp (norm_eff_name env lc.eff_name) t flags strengthen in
          let g = {g with guard_f=Trivial} in
          (e, lc, g)

let pure_or_ghost_pre_and_post env comp : ML _ =
    let mk_post_type res_t ens =
        let x = S.new_bv None res_t in
        U.refine x (U.apply_post ens (S.bv_to_name x)) in
    let norm t = Normalize.normalize [Env.Beta;Env.Eager_unfolding] env t in
    if U.is_tot_or_gtot_comp comp
    then None, U.comp_result comp
    else
      let ct = Env.unfold_effect_abbrev env comp in
      let req = ct.comp_pre in
      Some (norm req), (norm <| mk_post_type ct.result_typ ct.comp_post)

(* [norm_reify env t] assumes that [t] has the shape reify t0 *)
(* where env |- t0 : M t' for some effect M and type t' where M is reifiable *)
(* and returns the result of reducing t with reification on *)
let norm_reify (env:Env.env) (steps:Env.steps) (t:S.term) : ML S.term =
    def_check_scoped t.pos "norm_reify" env t;
    let t' = N.normalize
      ([Env.Beta; Env.Reify; Env.Eager_unfolding; Env.AllowUnboundUniverses; Env.Exclude Env.Zeta]@steps)
      env t in
    if !dbg_SMTEncodingReify
    then Format.print2 "Reified body %s \nto %s\n"
        (show t)
        (show t') ;
    t'

let remove_reify (t: S.term): ML S.term =
  if (match (SS.compress t).n with | Tm_app _ -> false | _ -> true)
  then t
  else
    let head, args = U.head_and_args_full t in
    if (match (SS.compress head).n with Tm_constant (FStarC.Const.Const_reify _) -> true | _ -> false)
    then begin match args with
        | [x] -> fst x
        | _ -> failwith "Impossible : Reify applied to multiple arguments after normalization."
    end
    else t


(*********************************************************************************************)
(* Instantiation and generalization *)
(*********************************************************************************************)
let maybe_implicit_with_meta_or_attr aq (attrs:list attribute) : ML _ =
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
let instantiate_one_binder (env:env_t) (r:Range.t) (b:binder) : ML (term & typ & aqual & guard_t) =
  if Debug.high () then
    Format.print1 "instantiate_one_binder: Instantiating implicit binder ‘%s’\n" (show b);
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
      let name = "‘" ^ show x ^ "’" in
      if is_typeclass then "Typeclass constraint argument"
      else if Some? ctx_uvar_meta then "Instantiating meta argument " ^ name
      else "Instantiating implicit argument " ^ name
    in
    Env.new_implicit_var_aux msg r env t Strict ctx_uvar_meta should_unrefine
  in
  let aq = U.aqual_of_binder b in
  let arg = varg, aq in

  let r = varg, t, aq, implicits in
  if Debug.high () then
    Format.print1 "instantiate_one_binder: result = %s\n" (show (r._1, r._2));
  r

(* Will instantiate e, by applying it to some unification variables for its implicit
arguments, if that is needed to match the expected type in the environment. [t] is the type
of [e]. Returns elaborated [e'], its type [t'], and a guard. *)
let maybe_instantiate (env:Env.env) (e:term) (t:typ) : ML (term & typ & guard_t) =
  let torig = SS.compress t in
  if not env.instantiate_imp
  then e, torig, mzero
  else begin
       if Debug.high () then
         Format.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                 (show e) (show t) (show (Env.expected_typ env));
       (* Similar to U.arrow_formals, but makes sure to unfold
        * recursively to catch all the binders across type
        * definitions. TODO: Move to library? Revise other uses
        * of arrow_formals{,_comp}?*)
       let unfolded_arrow_formals env (t:term) : ML (list binder) =
         let rec aux (env:Env.env) (bs:list binder) (t:term) : ML (list binder) =
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
            match formals |> BU.prefix_until (fun ({binder_qual=imp}) -> None? imp || U.eq_bqual imp (Some Equality)) with
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
        begin let bs,c = U.arrow_formals_comp t in
              match bs with
              | _::_ ->
              //instantiate at most inst_n implicit binders, when inst_n = Some n
              //otherwise, instantate all implicits
              //See issue #807 for why this is important
              let rec aux (subst:list subst_elt) inst_n bs : ML _ =
                  match inst_n, bs with
                  | Some 0, _ -> [], bs, subst, Env.trivial_guard //no more instantiations to do
                  | _, {binder_qual = Some (Implicit _)} ::rest
                  | _, {binder_qual = Some (Meta _)} ::rest ->
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

let check_has_type env (e:term) (t1:typ) (t2:typ) (use_eq:bool) : ML guard_t =
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

let check_has_type_maybe_coerce env (e:term) (lc:lcomp) (t2:typ) use_eq : ML (term & lcomp & guard_t) =
  let env = Env.set_range env e.pos in
  let e, lc, g_c = maybe_coerce_lc env e lc t2 in
  let g = check_has_type env e lc.res_typ t2 use_eq in
  if !dbg_Rel then
    Format.print1 "Applied guard is %s\n" <| guard_to_string env g;
  e, lc, (Env.conj_guard g g_c)

/////////////////////////////////////////////////////////////////////////////////
let check_top_level env g lc : ML (bool & comp) =
 Errors.with_ctx "While checking for top-level effects" (fun () ->
  if Debug.medium () then
    Format.print1 "check_top_level, lc = %s\n" (TcComm.lcomp_to_string lc);
  let discharge g =
    force_trivial_guard env g;
    if TcComm.is_pure_lcomp lc then true
    (* An effect marked [@@top_level_effect] may appear at the top level. *)
    else if Some? (Env.get_top_level_effect env lc.eff_name) then true
    (* An effect with a representation is a value of that representation;
       running it at the top level is meaningless. *)
    else if Env.is_reifiable_effect env lc.eff_name then
      raise_error env Errors.Fatal_UnexpectedEffect [
        text "Effect" ^/^ pp lc.eff_name ^/^ text "cannot be used as a top-level effect"
      ]
    (* Otherwise: warn, and mask the effect. *)
    else false in
  let g = Rel.solve_deferred_constraints env g in
  let c, g_c = TcComm.lcomp_comp lc in
  if TcComm.is_total_lcomp lc
  then discharge (Env.conj_guard g g_c), c
  else let c = Env.unfold_effect_abbrev env c in
       let us = c.comp_univs in
       let steps = [Env.Beta; Env.NoFullNorm; Env.DoNotUnfoldPureLets] in
       let c = c
         |> S.mk_Comp
         |> Normalize.normalize_comp steps env in
       let ct, vc, g_pre = check_trivial_precondition_wp env c in
       if !dbg_Simplification
       then Format.print1 "top-level VC: %s\n" (show vc);
       discharge (Env.conj_guard g (Env.conj_guard g_c g_pre)), ct |> S.mk_Comp
 )

(* Having already seen_args to head (from right to left),
   compute the guard, if any, for the next argument,
   if head is a short-circuiting operator *)
let short_circuit (head:term) (seen_args:args) : ML guard_formula =
    let short_bin_op (f: term -> ML guard_formula) : args -> ML guard_formula = function
        | [] -> (* no args seen yet *) Trivial
        | [(fst, _)] -> f fst
        | _ -> failwith "Unexpected args to binary operator" in

    let op_and_e e = U.b2t e   |> NonTrivial in
    let op_or_e e  = U.mk_neg (U.b2t e) |> NonTrivial in
    let op_and_t t = t |> NonTrivial in
    let op_or_t t  = t |> U.mk_neg |> NonTrivial in
    let op_imp_t t = t |> NonTrivial in

    let short_op_ite : args -> ML guard_formula = function
        | [] -> Trivial
        | [(guard, _)] -> NonTrivial guard
        | [_then;(guard, _)] -> U.mk_neg guard |> NonTrivial
        | _ -> failwith "Unexpected args to ITE" in
    let table : list (lident & (args -> ML guard_formula)) =
        [(C.op_And,  short_bin_op op_and_e);
         (C.op_Or,   short_bin_op op_or_e);
         (C.and_lid, short_bin_op op_and_t);
         (C.or_lid,  short_bin_op op_or_t);
         (C.imp_lid, short_bin_op op_imp_t);
         (C.ite_lid, short_op_ite);] in

     match head.n with
        | Tm_fvar fv ->
          let lid = fv.fv_name in
          begin match BU.find_map table (fun (x, mk) -> if lid_equals x lid then Some (mk seen_args) else None) with
            | None ->   Trivial
            | Some g -> g
          end
        | _ -> Trivial

let short_circuit_head l : ML _ =
    let hd, _ = U.head_and_args_full l in
    match (U.un_uinst hd).n with
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
let maybe_add_implicit_binders (env:env) (bs:binders) : ML binders =
    let is_implicit_binder (b:binder) : ML bool =
        let q = b.binder_qual in
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
                let bs', _ = U.arrow_formals_comp_ln_strict t in
                match bs' with
                    | _::_ ->
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
  if !dbg_Extraction then Format.print2 "must_erase=%s: %s\n" (if res then "true" else "false") (show t);
  res

let effect_extraction_mode env l : ML _ =
  l |> Env.norm_eff_name env
    |> Env.get_effect_decl env
    |> (fun ed -> ed.extraction_mode)

let fresh_effect_repr env r eff_name signature_ts repr_ts_opt u a_tm : ML _ =
  raise_error r Errors.Fatal_UnexpectedEffect "Effects no longer have representations"

let fresh_effect_repr_en env r eff_name u a_tm : ML _ =
  let ed = Env.get_effect_decl env (Env.norm_eff_name env eff_name) in
  match U.get_eff_repr ed with
  | None ->
    raise_error r Errors.Fatal_UnexpectedEffect
      (Format.fmt1 "Effect %s does not have a representation" (Ident.string_of_lid eff_name))
  | Some ts ->
    let repr = Env.inst_effect_fun_with [u] env ed ts in
    S.mk_Tm_app repr [S.as_arg a_tm] r, Env.trivial_guard

let layered_effect_indices_as_binders env r eff_name sig_ts u a_tm : ML binders = []

let get_field_projector_name env datacon index : ML _ =
  let _, t = Env.lookup_datacon env datacon in
  let err n =
    raise_error env Errors.Fatal_UnexpectedDataConstructor
      (Format.fmt3 "Data constructor %s does not have enough binders (has %s, tried %s)"
        (show datacon) (show n) (show index))  in
  let bs, _ = U.arrow_formals_comp_ln_strict t in
  match bs with
  | _::_ ->
    let bs = bs |> List.filter (fun ({binder_qual=q}) -> match q with | Some (Implicit true) -> false | _ -> true) in
    if List.length bs <= index then err (List.length bs)
    else
      let b = List.nth bs index in
      U.mk_field_projector_name datacon b.binder_bv index
  | _ -> err 0


let update_env_sub_eff env sub r : ML _ =
  let r0 = env.range in
  let env = Env.update_effect_lattice ({ env with range = r }) sub.source sub.target in
  let env =
    match sub.lift with
    | None -> env
    | Some ts -> Env.add_lift env sub.source sub.target ts in
  { env with range = r0 }

(*** Utilities for type-based record
     disambiguation ***)


(*
   For singleton inductive types named `typename`,
   it looks up the name of the constructor,
   and the field names of that constructor
 *)
let try_lookup_record_type env (typename:lident)
  : ML (option DsEnv.record_or_dc)
  = try
      match Env.datacons_of_typ env typename with
      | _, [dc] ->
        let se = Env.lookup_sigelt env dc in
        (match se with
         | Some ({sigel=Sig_datacon {t; num_ty_params=nparms}}) ->
           let formals, c = U.arrow_formals t in
           if nparms < List.length formals
           then let parms, fields = List.splitAt nparms formals in // Remove params. Whatever remains are fields.
                let fields = List.map (fun b -> b.binder_bv.ppname, S.is_bqual_implicit_or_meta b.binder_qual, b.binder_bv.sort) fields in
                let is_rec = Env.is_record env typename in
                let r : DsEnv.record_or_dc =
                  {
                    typename = typename;
                    constrname = Ident.ident_of_lid dc;
                    parms;
                    fields = fields;
                    is_private = false;
                    is_record = is_rec
                  }
                in
                Some r

           else (
            //  Format.print3 "Not enough formals; nparms=%s; type = %s; formals=%s\n"
            //    (show nparms)
            //    (show t)
            //    (Print.binders_to_string ", " formals);
             None
           )
         | _ ->
          //  Format.print1 "Could not find %s\n" (string_of_lid dc);
           None)
      | _, dcs ->
        // Format.print2 "Could not find type %s ... Got %s\n"
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

let head_fv_of_typ env (t:typ) : ML (option fv) =
    (* One shared implementation of "the rigid head symbol of a type", so that
       record, projector and general-name resolution all classify types the same
       way. See FStarC.TypeChecker.Overload. *)
    Overload.base_head_fv env t

let find_record_or_dc_from_head_fv env (head_fv:option fv) (uc:unresolved_constructor) rng : ML _ =
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
            text <| Format.fmt1 "Field name %s could not be resolved." (string_of_lid f);
        ]

      | Some tn, _ ->
        match try_lookup_record_type env tn with
        | Some rdc -> rdc
        | None ->
          raise_error tn Errors.Fatal_NameNotFound 
            (Format.fmt1 "Record name %s not found." (string_of_lid tn))
    in
    let rdc : DsEnv.record_or_dc =
      match head_fv with
      | None -> default_rdc()
      | Some type_name -> (
        match try_lookup_record_type env type_name.fv_name with
        | None -> default_rdc ()
        | Some r -> r
      )
    in
    let constrname =
          let name = lid_of_ids (ns_of_lid rdc.typename @ [rdc.constrname]) in
          Ident.set_lid_range name rng
    in
    let constructor =
        let qual =
          if rdc.is_record
            then (Some (Record_ctor(rdc.typename, rdc.fields |> List.map (fun (i, _, _) -> i))))
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
let field_name_matches (field_name:lident) (rdc:DsEnv.record_or_dc) (field:ident) : ML _ =
    Ident.ident_equals field (Ident.ident_of_lid field_name) &&
    (if ns_of_lid field_name <> []
     then nsstr field_name = nsstr rdc.typename
     else true)

(*
  The field assignments of a record constructor can be given out of
  order.

  Given that we've committed to `rdc` as the record constructor, if the user's
  field assignments are `fas`, then we order the alphas by the order in which
  they appear in `rdc`. This is the list we return, augmented with a boolean to
  indicate whether the field was implicit or not.

  If a particular field cannot be found, then we call not_found, which
  an provide a default.

  We raise errors if fields are not found and no default exists, or if
  redundant fields are present.
*)
let make_record_fields_in_order
       (env : Env.env)
       (uc : unresolved_constructor)
       (topt : option (either typ typ))
       (rdc : DsEnv.record_or_dc)
       (fas : list (lident & 'a))
       (not_found : (ident -> is_imp:bool -> ML (option 'a)))
       (rng : Range.t)
  : ML (list ('a & bool))
  = let debug () =
      let print_rdc (rdc:DsEnv.record_or_dc) =
        Format.fmt3 "{typename=%s; constrname=%s; fields=[%s]}"
          (string_of_lid rdc.typename)
          (string_of_id rdc.constrname)
          (List.map (fun (i, _, _) -> string_of_id i) rdc.fields |> String.concat "; ")
      in
      let print_topt topt =
        Format.fmt2 "topt=%s; rdc=%s" (show topt) (print_rdc rdc)
      in
      Format.print5 "Resolved uc={typename=%s;fields=%s}\n\ttopt=%s\n\t{rdc = %s\n\tfield assignments=[%s]}\n"
          (show uc.uc_typename)
          (show uc.uc_fields)
          (print_topt topt)
          (print_rdc rdc)
          (show (List.map fst fas))
    in
    let rest, as_rev, missing =
      List.fold_left
        (fun (fields, as_rev, missing) (field_name, is_imp, _) ->
           let matching, rest =
             List.partition
               (fun (fn, _) -> field_name_matches fn rdc field_name)
               fields
           in
           match matching with
           | [(_, a)] ->
             rest, (a, is_imp) ::as_rev, missing

           | [] -> (
             match not_found field_name is_imp with
             | None ->
//               debug();
               rest, as_rev, field_name :: missing
             | Some a ->
               rest, (a, is_imp) ::as_rev, missing
             )

           | x1::x2::_ ->
//             debug();
             raise_error (fst x1) Errors.Fatal_MissingFieldInRecord
                (Format.fmt2 "Field ‘%s’ of record type ‘%s’ is given multiple assignments."
                  (string_of_id field_name)
                  (string_of_lid rdc.typename)))
        (fas, [], [])
        rdc.fields
    in
    let pp_missing () =
      separate_map (comma ^^ break_ 1) (fun f -> fquotes (doc_of_string (show f))) missing
    in
    let _ =
      match rest, missing with
      | [], [] -> ()
      | (f, _)::_, _ ->
//        debug();
        raise_error f Errors.Fatal_MissingFieldInRecord [
            Errors.Msg.text <| Format.fmt2 "No field ‘%s’ in record type ‘%s’." (show f) (show rdc.typename);
            if Cons? missing then
              prefix 2 1 (text "Missing fields:")
                (pp_missing ())
            else
              Pprint.empty;
        ]

      | [], _ ->
        // debug ();
        raise_error rng Errors.Fatal_MissingFieldInRecord [
            prefix 2 1 (text <| Format.fmt1 "Missing fields for record type ‘%s’:" (show rdc.typename))
                (pp_missing ())
        ]
    in
    List.rev as_rev
