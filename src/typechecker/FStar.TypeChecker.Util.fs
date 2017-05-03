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
open FStar.All
open FStar
open FStar.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Rel
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Syntax.Subst
open FStar.TypeChecker.Common

type lcomp_with_binder = option<bv> * lcomp



module SS = FStar.Syntax.Subst
module S = FStar.Syntax.Syntax
module BU = FStar.Util
module U = FStar.Syntax.Util
module N = FStar.TypeChecker.Normalize
module P = FStar.Syntax.Print
module C = FStar.Syntax.Const

//Reporting errors
let report env errs =
    Errors.err (Env.get_range env)
               (Err.failed_to_prove_specification errs)

(************************************************************************)
(* Unification variables *)
(************************************************************************)
let is_type t = match (compress t).n with
    | Tm_type _ -> true
    | _ -> false

let t_binders env =
    Env.all_binders env |> List.filter (fun (x, _) -> is_type x.sort)

//new unification variable
let new_uvar_aux env k =
    let bs = if (Options.full_context_dependency())
             || Ident.lid_equals Const.prims_lid (Env.current_module env)
             then Env.all_binders env
             else t_binders env in
    Rel.new_uvar (Env.get_range env) bs k

let new_uvar env k = fst (new_uvar_aux env k)

let as_uvar : typ -> uvar = function
    | {n=Tm_uvar(uv, _)} -> uv
    | _ -> failwith "Impossible"

let new_implicit_var reason r env k =
    match U.destruct k Const.range_of_lid with
     | Some [_; (tm, _)] ->
       let t = S.mk (S.Tm_constant (FStar.Const.Const_range tm.pos)) None tm.pos in
       t, [], Rel.trivial_guard

     | _ ->
       let t, u = new_uvar_aux env k in
       let g = {Rel.trivial_guard with implicits=[(reason, env, as_uvar u, t, k, r)]} in
       t, [(as_uvar u, r)], g

let check_uvars r t =
  let uvs = Free.uvars t in
  if not (BU.set_is_empty uvs)
  then
    let us = List.map (fun (x, _) -> Print.uvar_to_string x) (BU.set_elements uvs) |> String.concat ", " in
    (* ignoring the hide_uvar_nums and print_implicits flags here *)
    Options.push();
    Options.set_option "hide_uvar_nums" (Options.Bool false);
    Options.set_option "print_implicits" (Options.Bool true);
    Errors.err r
      (BU.format2 "Unconstrained unification variables %s in type signature %s; \
       please add an annotation" us (Print.term_to_string t));
    Options.pop()

(************************************************************************)
(* Extracting annotations from a term *)
(************************************************************************)
let force_sort' s = match !s.tk with
    | None -> failwith (BU.format2 "(%s) Impossible: Forced tk not present on %s" (Range.string_of_range s.pos) (Print.term_to_string s))
    | Some tk -> tk

let force_sort s = mk (force_sort' s) None s.pos

let extract_let_rec_annotation env {lbname=lbname; lbunivs=univ_vars; lbtyp=t; lbdef=e} :
    list<univ_name>
   * typ
   * bool //true indicates that the type needs to be checked; false indicates that it is already checked
   =
  let rng = S.range_of_lbname lbname in
  let t = SS.compress t in
  match t.n with
   | Tm_unknown ->
     if univ_vars <> [] then failwith "Impossible: non-empty universe variables but the type is unknown";
     let r = Env.get_range env in
     let mk_binder scope a =
        match (SS.compress a.sort).n with
        | Tm_unknown ->
          let k, _ = U.type_u() in
          let t =  Rel.new_uvar e.pos scope k |> fst in
          {a with sort=t}, false
        | _ -> a, true in

    let rec aux must_check_ty vars e : either<typ,comp> * bool =
      let e = SS.compress e in
      match e.n with
      | Tm_meta(e, _) -> aux must_check_ty vars e
      | Tm_ascribed(e, t, _) -> fst t, true

      | Tm_abs(bs, body, _) ->
        let scope, bs, must_check_ty = bs |> List.fold_left (fun (scope, bs, must_check_ty) (a, imp) ->
              let tb, must_check_ty =
                if must_check_ty
                then a, true
                else mk_binder scope a in
              let b = (tb, imp) in
              let bs = bs@[b] in
              let scope = scope@[b] in
              scope, bs, must_check_ty)
           (vars,[], must_check_ty) in

        let res, must_check_ty = aux must_check_ty scope body in
        let c = match res with
            | Inl t ->
              if Options.ml_ish()
              then U.ml_comp t r
              else S.mk_Total t //let rec without annotations default to Tot, except if --MLish
            | Inr c -> c in
        let t = U.arrow bs c in
        if debug env Options.High
        then BU.print3 "(%s) Using type %s .... must check = %s\n"
                (Range.string_of_range r) (Print.term_to_string t) (BU.string_of_bool must_check_ty);
        Inl t, must_check_ty

      | _ ->
        if must_check_ty
        then Inl S.tun, true
        else Inl (Rel.new_uvar r vars U.ktype0 |> fst), false
    in

    let t, b = aux false (t_binders env) e in
    let t = match t with
        | Inr c ->
	  if U.is_tot_or_gtot_comp c
	  then U.comp_result c
	  else raise (Error(BU.format1 "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
				       (Print.comp_to_string c),
                      rng))
        | Inl t -> t in
    [], t, b

  | _ ->
    let univ_vars, t = open_univ_vars univ_vars t in
    univ_vars, t, false

(************************************************************************)
(* Utilities on patterns  *)
(************************************************************************)

(*
  pat_as_exps allow_implicits env p:
    Turns a (possibly disjunctive) pattern p into a triple:
*)
let pat_as_exps allow_implicits env p
                        : (list<bv>          (* pattern-bound variables (which may appear in the branch of match) *)
                         * list<term>        (* expressions corresponding to each arm of the disjunct *)
                         * pat)   =          (* decorated pattern, with all the missing implicit args in p filled in *)

      let rec pat_as_arg_with_env allow_wc_dependence env (p:pat) :
                                    (list<bv>    //all pattern-bound vars including wild-cards, in proper order
                                    * list<bv>   //just the accessible vars, for the disjunctive pattern test
                                    * list<bv>   //just the wildcards
                                    * Env.env    //env extending with the pattern-bound variables
                                    * term       //the pattern as a term/typ
                                    * pat) =     //the elaborated pattern itself
        match p.v with
           | Pat_constant c ->
             let e = mk (Tm_constant c) None p.p in
             ([], [], [], env, e, p)

           | Pat_dot_term(x, _) ->
             let k, _ = U.type_u () in
             let t = new_uvar env k in
             let x = {x with sort=t} in
             let e, u = Rel.new_uvar p.p (Env.all_binders env) t in
             let p = {p with v=Pat_dot_term(x, e)} in
             ([], [], [], env, e, p)

           | Pat_wild x ->
             let t, _ = U.type_u() in
             let x = {x with sort=new_uvar env t} in
             let env = if allow_wc_dependence then Env.push_bv env x else env in
             let e = mk (Tm_name x) None p.p in
             ([x], [], [x], env, e, p)

           | Pat_var x ->
             let t, _ = U.type_u() in
             let x = {x with sort=new_uvar env t} in
             let env = Env.push_bv env x in
             let e = mk (Tm_name x) None p.p in
             ([x], [x], [], env, e, p)

           | Pat_cons(fv, pats) ->
               let (b, a, w, env, args, pats) = pats |> List.fold_left (fun (b, a, w, env, args, pats) (p, imp) ->
                   let (b', a', w', env, te, pat) = pat_as_arg_with_env allow_wc_dependence env p in
                   let arg = if imp then iarg te else as_arg te in
                   (b'::b, a'::a, w'::w, env, arg::args, (pat, imp)::pats))
                 ([], [], [], env, [], []) in
               let e = mk (Tm_meta(mk_Tm_app (Syntax.fv_to_tm fv) (args |> List.rev) None p.p, Meta_desugared Data_app)) None p.p in
               (List.rev b |> List.flatten,
                List.rev a |> List.flatten,
                List.rev w |> List.flatten,
                env,
                e,
                {p with v=Pat_cons(fv, List.rev pats)})

           | Pat_disj _ -> failwith "impossible" in

    let rec elaborate_pat env p = //Adds missing implicit patterns to constructor patterns
        let maybe_dot inaccessible a r =
            if allow_implicits && inaccessible
            then withinfo (Pat_dot_term(a, tun)) tun.n r
            else withinfo (Pat_var a) tun.n r in
        match p.v with
           | Pat_cons(fv, pats) ->
               let pats = List.map (fun (p, imp) -> elaborate_pat env p, imp) pats in
               let _, t = Env.lookup_datacon env fv.fv_name.v in
               let f, _ = U.arrow_formals t in
               let rec aux formals pats = match formals, pats with
                | [], [] -> []
                | [], _::_ -> raise (Error("Too many pattern arguments", range_of_lid fv.fv_name.v))
                | _::_, [] -> //fill the rest with dot patterns (if allowed), if all the remaining formals are implicit
                    formals |> List.map (fun (t, imp) -> match imp with
                        | Some (Implicit inaccessible) ->
                          let a = Syntax.new_bv (Some (Syntax.range_of_bv t)) tun in
                          let r = range_of_lid fv.fv_name.v in
                          maybe_dot inaccessible a r, true

                        | _ ->
                          raise (Error(BU.format1 "Insufficient pattern arguments (%s)" (Print.pat_to_string p), range_of_lid fv.fv_name.v)))

                | f::formals', (p, p_imp)::pats' ->
                    begin match f with
                        | (_, Some (Implicit _)) when p_imp ->
                            (p, true)::aux formals' pats'

                        | (_, Some (Implicit inaccessible)) ->
                            let a = Syntax.new_bv (Some p.p) tun in
                            let p = maybe_dot inaccessible a (range_of_lid fv.fv_name.v) in
                            (p, true)::aux formals' pats

                        | (_, imp) ->
                            (p, S.is_implicit imp)::aux formals' pats'
                    end in
               {p with v=Pat_cons(fv, aux f pats)}

        | _ -> p in

    let one_pat allow_wc_dependence env p =
        let p = elaborate_pat env p in
        let b, a, w, env, arg, p = pat_as_arg_with_env allow_wc_dependence env p in
        match b |> BU.find_dup bv_eq with
            | Some x -> raise (Error(Err.nonlinear_pattern_variable x, p.p))
            | _ -> b, a, w, arg, p in

   let top_level_pat_as_args env (p:pat) : (list<bv>                    (* pattern bound variables *)
                                            * list<arg>                 (* pattern sub-terms *)
                                            * pat)  =                   (* decorated pattern *)
        match p.v with
           | Pat_disj [] -> failwith "impossible"

           | Pat_disj (q::pats) ->
              let b, a, _, te, q = one_pat false env q in //in disjunctive patterns, the wildcards are not accessible even for typing
              let w, args, pats = List.fold_right (fun p (w, args, pats) ->
                  let b', a', w', arg, p = one_pat false env p in
                  if not (BU.multiset_equiv bv_eq a a')
                  then raise (Error(Err.disjunctive_pattern_vars a a', Env.get_range env))
                  else (w'@w, S.as_arg arg::args, p::pats))
                  pats ([], [], []) in
              b@w, S.as_arg te::args, {p with v=Pat_disj(q::pats)}

           | _ ->
             let b, _, _, arg, p = one_pat true env p in //in single pattersn, the wildcards are available, at least for typing
             b, [S.as_arg arg], p in

    let b, args, p = top_level_pat_as_args env p in
    let exps = args |> List.map fst in
    b, exps, p

let decorate_pattern env p exps =
    let qq = p in
    let rec aux p e : pat  =
        let pkg q t = withinfo q t p.p in
        let e = U.unmeta e in
        match p.v, e.n with
            | _, Tm_uinst(e, _) -> aux p e

            | Pat_constant _, Tm_constant _ ->
              pkg p.v (force_sort' e)

            | Pat_var x, Tm_name y ->
              if not (bv_eq x y)
              then failwith (BU.format2 "Expected pattern variable %s; got %s" (Print.bv_to_string x) (Print.bv_to_string y));
              if Env.debug env <| Options.Other "Pat"
              then BU.print2 "Pattern variable %s introduced at type %s\n" (Print.bv_to_string x) (Normalize.term_to_string env y.sort);
              let s = Normalize.normalize [Normalize.Beta] env y.sort in
              let x = {x with sort=s} in
              pkg (Pat_var x) s.n

            | Pat_wild x, Tm_name y ->
              if bv_eq x y |> not
              then failwith (BU.format2 "Expected pattern variable %s; got %s" (Print.bv_to_string x) (Print.bv_to_string y));
              let s = Normalize.normalize [Normalize.Beta] env y.sort in
              let x = {x with sort=s} in
              pkg (Pat_wild x) s.n

            | Pat_dot_term(x, _), _ ->
              let s = force_sort e in
              let x = {x with sort=s} in
              pkg (Pat_dot_term(x, e)) s.n

            | Pat_cons(fv, []), Tm_fvar fv' ->
              if not (Syntax.fv_eq fv fv')
              then failwith (BU.format2 "Expected pattern constructor %s; got %s" fv.fv_name.v.str fv'.fv_name.v.str);
              pkg (Pat_cons(fv', [])) (force_sort' e)

            | Pat_cons(fv, argpats), Tm_app({n=Tm_fvar(fv')}, args)
            | Pat_cons(fv, argpats), Tm_app({n=Tm_uinst({n=Tm_fvar(fv')}, _)}, args) ->

              if fv_eq fv fv' |> not
              then failwith (BU.format2 "Expected pattern constructor %s; got %s" fv.fv_name.v.str fv'.fv_name.v.str);

              let fv = fv' in
              let rec match_args matched_pats args argpats = match args, argpats with
                | [], [] -> pkg (Pat_cons(fv, List.rev matched_pats)) (force_sort' e)
                | arg::args, (argpat, _)::argpats ->
                  begin match arg, argpat.v with
                        | (e, Some (Implicit true)), Pat_dot_term _ ->
                          let x = Syntax.new_bv (Some p.p) (force_sort e) in
                          let q = withinfo (Pat_dot_term(x, e)) x.sort.n p.p in
                          match_args ((q, true)::matched_pats) args argpats

                        | (e, imp), _ ->
                          let pat = aux argpat e, S.is_implicit imp in
                          match_args (pat::matched_pats) args argpats
                 end

                | _ -> failwith (BU.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" (Print.pat_to_string p) (Print.term_to_string e)) in

              match_args [] args argpats

           | _ -> failwith (BU.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Range.string_of_range qq.p) (Print.pat_to_string qq)
                    (exps |> List.map Print.term_to_string |> String.concat "\n\t")) in

    match p.v, exps with
        | Pat_disj ps, _ when (List.length ps = List.length exps) ->
          let ps = List.map2 aux ps exps in
          withinfo (Pat_disj ps) tun.n p.p

        | _, [e] ->
          aux p e

        | _ -> failwith "Unexpected number of patterns"

 let rec decorated_pattern_as_term (pat:pat) : list<bv> * term =
    let topt = Some pat.ty in
    let mk f : term = mk f topt pat.p in

    let pat_as_arg (p, i) =
        let vars, te = decorated_pattern_as_term p in
        vars, (te, as_implicit i) in

    match pat.v with
        | Pat_disj _ -> failwith "Impossible" (* these are only on top-level patterns *)

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
let destruct_comp c : (universe * typ * typ) =
  let wp = match c.effect_args with
    | [(wp, _)] -> wp
    | _ -> failwith (BU.format2 "Impossible: Got a computation %s with effect args [%s]" c.effect_name.str
      (List.map (fun (x, _) -> Print.term_to_string x) c.effect_args |> String.concat ", ")) in
  List.hd c.comp_univs, c.result_typ, wp

let lift_comp c m lift =
  let u, _, wp = destruct_comp c in
  {comp_univs=[u];
   effect_name=m;
   result_typ=c.result_typ;
   effect_args=[as_arg (lift.mlift_wp c.result_typ wp)];
   flags=[]}

let join_effects env l1 l2 =
  let m, _, _ = Env.join env (norm_eff_name env l1) (norm_eff_name env l2) in
  m

let join_lcomp env c1 c2 =
  if U.is_total_lcomp c1
  && U.is_total_lcomp c2
  then Const.effect_Tot_lid
  else join_effects env c1.eff_name c2.eff_name

let lift_and_destruct env c1 c2 =
  let c1 = Env.unfold_effect_abbrev env c1 in
  let c2 = Env.unfold_effect_abbrev env c2 in
  let m, lift1, lift2 = Env.join env c1.effect_name c2.effect_name in
  let m1 = lift_comp c1 m lift1 in
  let m2 = lift_comp c2 m lift2 in
  let md = Env.get_effect_decl env m in
  let a, kwp = Env.wp_signature env md.mname in
  (md, a, kwp), destruct_comp m1, destruct_comp m2

let is_pure_effect env l =
  let l = norm_eff_name env l in
  lid_equals l Const.effect_PURE_lid

let is_pure_or_ghost_effect env l =
  let l = norm_eff_name env l in
  lid_equals l Const.effect_PURE_lid
  || lid_equals l Const.effect_GHOST_lid

let mk_comp_l mname u_result result wp flags =
  mk_Comp ({ comp_univs=[u_result];
             effect_name=mname;
             result_typ=result;
             effect_args=[S.as_arg wp];
             flags=flags})

let mk_comp md = mk_comp_l md.mname

let lax_mk_tot_or_comp_l mname u_result result flags =
    if Ident.lid_equals mname Const.effect_Tot_lid
    then S.mk_Total' result (Some u_result)
    else mk_comp_l mname u_result result S.tun flags

let subst_lcomp subst lc =
    {lc with res_typ=SS.subst subst lc.res_typ;
             comp=fun () -> SS.subst_comp subst (lc.comp())}

let is_function t = match (compress t).n with
    | Tm_arrow _ -> true
    | _ -> false

let return_value env t v =
  let c =
    if not <| Env.lid_exists env Const.effect_GTot_lid //we're still in prims, not yet having fully defined the primitive effects
    then mk_Total t
    else let m = Env.get_effect_decl env Const.effect_PURE_lid in //if Tot isn't fully defined in prims yet, then just return (Total t)
         let u_t = env.universe_of env t in
         let wp =
            if env.lax
            && Options.ml_ish() //NS: Disabling this optimization temporarily
            then S.tun
            else let a, kwp = Env.wp_signature env Const.effect_PURE_lid in
                 let k = SS.subst [NT(a, t)] kwp in
                 N.normalize [N.Beta] env (mk_Tm_app (inst_effect_fun_with [u_t] env m m.ret_wp) [S.as_arg t; S.as_arg v] (Some k.n) v.pos) in
         mk_comp m u_t t wp [RETURN] in
  if debug env <| Options.Other "Return"
  then BU.print3 "(%s) returning %s at comp type %s\n"
                    (Range.string_of_range v.pos)  (P.term_to_string v) (N.comp_to_string env c);
  c

let bind r1 env e1opt (lc1:lcomp) ((b, lc2):lcomp_with_binder) : lcomp =
  let lc1 = N.ghost_to_pure_lcomp env lc1 in //downgrade from ghost to pure, if possible
  let lc2 = N.ghost_to_pure_lcomp env lc2 in
  let joined_eff = join_lcomp env lc1 lc2 in
  if debug env Options.Extreme
  then
    (let bstr = match b with
      | None -> "none"
      | Some x -> Print.bv_to_string x in
    BU.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
        (match e1opt with | None -> "None" | Some e -> Print.term_to_string e)
        (Print.lcomp_to_string lc1) bstr (Print.lcomp_to_string lc2));
  let bind_it () =
      if env.lax
      && Options.ml_ish() //NS: disabling this optimization temporarily
      then
         let u_t = env.universe_of env lc2.res_typ in
         lax_mk_tot_or_comp_l joined_eff u_t lc2.res_typ []
      else begin
          let c1 = lc1.comp () in
          let c2 = lc2.comp () in
          if debug env Options.Extreme
          then BU.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n"
                (match b with
                  | None -> "none"
                  | Some x -> Print.bv_to_string x)
                (Print.lcomp_to_string lc1)
                (Print.comp_to_string c1)
                (Print.lcomp_to_string lc2)
                (Print.comp_to_string c2);
          let try_simplify () =
            let aux () =
                if U.is_trivial_wp c1
                then match b with
                        | None -> Some (c2, "trivial no binder")
                        | Some _ ->
                            if U.is_ml_comp c2 //|| not (U.is_free [Inr x] (U.freevars_comp c2))
                            then Some (c2, "trivial ml")
                            else None
                else if U.is_ml_comp c1 && U.is_ml_comp c2
                then Some (c2, "both ml")
                else None
            in
            let subst_c2 reason =
                match e1opt, b with
                    | Some e, Some x ->
                      Some (SS.subst_comp [NT(x,e)] c2, reason)
                    | _ -> aux()
            in
            if U.is_total_comp c1
            && U.is_total_comp c2
            then subst_c2 "both total"
            else if U.is_tot_or_gtot_comp c1
                 && U.is_tot_or_gtot_comp c2
            then Some (S.mk_GTotal (U.comp_result c2), "both gtot")
            else match e1opt, b with
                | Some e, Some x ->
                    if U.is_total_comp c1 && not (Syntax.is_null_bv x)
                    then subst_c2 "substituted e"
                    else aux ()
                | _ -> aux ()
          in
          match try_simplify () with
            | Some (c, reason) ->
              c
            | None ->
              let (md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2) = lift_and_destruct env c1 c2 in
              let bs = match b with
                | None -> [null_binder t1]
                | Some x -> [S.mk_binder x] in
              let mk_lam wp = U.abs bs wp (Some (Inr (Const.effect_Tot_lid, [TOTAL]))) in //we know it's total; let the normalizer reduce it
              let r1 = S.mk (S.Tm_constant (FStar.Const.Const_range r1)) None r1 in
              let wp_args = [S.as_arg r1; S.as_arg t1; S.as_arg t2; S.as_arg wp1; S.as_arg (mk_lam wp2)] in
              let k = SS.subst [NT(a, t2)] kwp in
              let wp = mk_Tm_app  (inst_effect_fun_with [u_t1;u_t2] env md md.bind_wp)  wp_args None t2.pos in
              let c = mk_comp md u_t2 t2 wp [] in
              c
        end
  in {eff_name=joined_eff;
      res_typ=lc2.res_typ;
      (* TODO : these cflags might be inconsistent with the one returned by bind_it  !!! *)
      cflags=[];
      comp=bind_it}

let label reason r f : term =
    mk (Tm_meta(f, Meta_labeled(reason, r, false))) None f.pos

let label_opt env reason r f = match reason with
    | None -> f
    | Some reason ->
        if not <| Env.should_verify env
        then f
        else label (reason()) r f

let label_guard r reason (g:guard_t) = match g.guard_f with
    | Trivial -> g
    | NonTrivial f -> {g with guard_f=NonTrivial (label reason r f)}

let weaken_guard g1 g2 = match g1, g2 with
    | NonTrivial f1, NonTrivial f2 ->
      let g = (U.mk_imp f1 f2) in
      NonTrivial g
    | _ -> g2

let weaken_precondition env lc (f:guard_formula) : lcomp =
  let weaken () =
      let c = lc.comp () in
      if env.lax
      && Options.ml_ish() //NS: Disabling this optimization temporarily
      then c
      else begin
         match f with
         | Trivial -> c
         | NonTrivial f ->
            if U.is_ml_comp c
            then c
            else let c = Env.unfold_effect_abbrev env c in
                 let u_res_t, res_t, wp = destruct_comp c in
                 let md = Env.get_effect_decl env c.effect_name in
                 let wp = mk_Tm_app (inst_effect_fun_with [u_res_t] env md md.assume_p)  [S.as_arg res_t; S.as_arg f; S.as_arg wp]  None wp.pos in
                 mk_comp md u_res_t res_t wp c.flags
      end
  in
  {lc with comp=weaken}

let strengthen_precondition (reason:option<(unit -> string)>) env (e:term) (lc:lcomp) (g0:guard_t) : lcomp * guard_t =
    if Rel.is_trivial g0
    then lc, g0
    else let _ = if Env.debug env <| Options.Extreme
                 then BU.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                                (N.term_to_string env e)
                                (Rel.guard_to_string env g0) in
         let flags = lc.cflags |> List.collect (function RETURN | PARTIAL_RETURN -> [PARTIAL_RETURN] | _ -> []) in
         let strengthen () =
            let c = lc.comp () in
            if env.lax
            then c
            else begin
                let g0 = Rel.simplify_guard env g0 in
                match guard_form g0 with
                    | Trivial -> c
                    | NonTrivial f ->
                    let c =
                        if (U.is_pure_or_ghost_comp c
                           && not (U.is_partial_return c))
                        then let x = S.gen_bv "strengthen_pre_x" None (U.comp_result c) in
                             let xret = U.comp_set_flags (return_value env x.sort (S.bv_to_name x)) [PARTIAL_RETURN] in
                             let lc = bind e.pos env (Some e) (U.lcomp_of_comp c) (Some x, U.lcomp_of_comp xret) in
                             lc.comp()
                        else c in

                    if Env.debug env <| Options.Extreme
                    then BU.print2 "-------------Strengthening pre-condition of term %s with guard %s\n"
                                    (N.term_to_string env e)
                                    (N.term_to_string env f);

                    let c = Env.unfold_effect_abbrev env c in
                    let u_res_t, res_t, wp = destruct_comp c in
                    let md = Env.get_effect_decl env c.effect_name in
                    let wp =  mk_Tm_app (inst_effect_fun_with [u_res_t] env md md.assert_p) [S.as_arg res_t; S.as_arg <| label_opt env reason (Env.get_range env) f; S.as_arg wp] None wp.pos in

                    if Env.debug env <| Options.Extreme
                    then BU.print1 "-------------Strengthened pre-condition is %s\n"
                                    (Print.term_to_string wp);

                    let c2 = mk_comp md u_res_t res_t wp flags in
                    c2
             end
       in
       {lc with eff_name=norm_eff_name env lc.eff_name;
                cflags=(if U.is_pure_lcomp lc && not <| U.is_function_typ lc.res_typ then flags else []);
                comp=strengthen},
       {g0 with guard_f=Trivial}

let add_equality_to_post_condition env (comp:comp) (res_t:typ) =
    let md_pure = Env.get_effect_decl env Const.effect_PURE_lid in
    let x = S.new_bv None res_t in
    let y = S.new_bv None res_t in
    let xexp, yexp = S.bv_to_name x, S.bv_to_name y in
    let u_res_t = env.universe_of env res_t in
    let yret =
        mk_Tm_app (inst_effect_fun_with [u_res_t] env md_pure md_pure.ret_wp)
                  [S.as_arg res_t; S.as_arg yexp] None res_t.pos in
    let x_eq_y_yret =
        mk_Tm_app (inst_effect_fun_with [u_res_t] env md_pure md_pure.assume_p)
                  [S.as_arg res_t;
                   S.as_arg <| U.mk_eq2 u_res_t res_t xexp yexp;
                   S.as_arg <| yret] None res_t.pos in
    let forall_y_x_eq_y_yret =
        mk_Tm_app (inst_effect_fun_with [u_res_t;u_res_t] env md_pure md_pure.close_wp)
                  [S.as_arg res_t;
                   S.as_arg res_t;
                   S.as_arg <| U.abs [mk_binder y] x_eq_y_yret (Some (Inr (Const.effect_Tot_lid, [TOTAL])))] //mark it as Tot for the normalizer
                   None res_t.pos in
    let lc2 = mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret [PARTIAL_RETURN] in
    let lc = bind (Env.get_range env) env None (U.lcomp_of_comp comp) (Some x, U.lcomp_of_comp lc2) in
    lc.comp()

let ite env (guard:formula) lcomp_then lcomp_else =
  let joined_eff = join_lcomp env lcomp_then lcomp_else in
  let comp () =
      if env.lax
      && Options.ml_ish() //NS: Disabling this optimization temporarily
      then
         let u_t = env.universe_of env lcomp_then.res_typ in
         lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.res_typ []
      else begin
          let (md, _, _), (u_res_t, res_t, wp_then), (_, _, wp_else) = lift_and_destruct env (lcomp_then.comp()) (lcomp_else.comp()) in
          let ifthenelse md res_t g wp_t wp_e = mk_Tm_app (inst_effect_fun_with [u_res_t] env md md.if_then_else) [S.as_arg res_t; S.as_arg g; S.as_arg wp_t; S.as_arg wp_e] None (Range.union_ranges wp_t.pos wp_e.pos) in
          let wp = ifthenelse md res_t guard wp_then wp_else in
          if (Options.split_cases()) > 0
          then let comp = mk_comp md u_res_t res_t wp [] in
               add_equality_to_post_condition env comp res_t
          else let wp = mk_Tm_app  (inst_effect_fun_with [u_res_t] env md md.ite_wp)  [S.as_arg res_t; S.as_arg wp] None wp.pos in
               mk_comp md u_res_t res_t wp []
      end
 in
 {eff_name=join_effects env lcomp_then.eff_name lcomp_else.eff_name;
  res_typ=lcomp_then.res_typ;
  cflags=[];
  comp=comp}

let fvar_const env lid =  S.fvar (Ident.set_lid_range lid (Env.get_range env)) Delta_constant None

let bind_cases env (res_t:typ) (lcases:list<(formula * lcomp)>) : lcomp =
    let eff = List.fold_left (fun eff (_, lc) -> join_effects env eff lc.eff_name) Const.effect_PURE_lid lcases in
    let bind_cases () =
        let u_res_t = env.universe_of env res_t in
        if env.lax
        && Options.ml_ish() //NS: Disabling this optimization temporarily
        then
             lax_mk_tot_or_comp_l eff u_res_t res_t []
        else begin
            let ifthenelse md res_t g wp_t wp_e =
                mk_Tm_app (inst_effect_fun_with [u_res_t] env md md.if_then_else) [S.as_arg res_t; S.as_arg g; S.as_arg wp_t; S.as_arg wp_e] None (Range.union_ranges wp_t.pos wp_e.pos) in
            let default_case =
                let post_k = U.arrow [null_binder res_t] (S.mk_Total U.ktype0) in
                let kwp    = U.arrow [null_binder post_k] (S.mk_Total U.ktype0) in
                let post   = S.new_bv None post_k in
                let wp     = U.abs [mk_binder post]
                                   (label Err.exhaustiveness_check (Env.get_range env) <| fvar_const env Const.false_lid)
                                   (Some (Inr (Const.effect_Tot_lid, [TOTAL]))) in
                let md     = Env.get_effect_decl env Const.effect_PURE_lid in
                mk_comp md u_res_t res_t wp [] in
            let comp = List.fold_right (fun (g, cthen) celse ->
                let (md, _, _), (_, _, wp_then), (_, _, wp_else) = lift_and_destruct env (cthen.comp()) celse in
                mk_comp md u_res_t res_t (ifthenelse md res_t g wp_then wp_else)  []) lcases default_case in
            if (Options.split_cases()) > 0
            then add_equality_to_post_condition env comp res_t
            else let comp = Env.comp_to_comp_typ env comp in
                 let md = Env.get_effect_decl env comp.effect_name in
                 let _, _, wp = destruct_comp comp in
                 let wp = mk_Tm_app  (inst_effect_fun_with [u_res_t] env md md.ite_wp)  [S.as_arg res_t; S.as_arg wp] None wp.pos in
                 mk_comp md u_res_t res_t wp []
        end
    in
    {eff_name=eff;
     res_typ=res_t;
     cflags=[];
     comp=bind_cases}

let close_comp env bvs (lc:lcomp) =
  let close () =
      let c = lc.comp() in
      if U.is_ml_comp c then c
      else
        if env.lax
	&& Options.ml_ish() //NS: disabling this optimization temporarily
        then
           c
        else begin
            let close_wp u_res md res_t bvs wp0 =
              List.fold_right (fun x wp ->
                  let bs = [mk_binder x] in
                  let us = u_res::[env.universe_of env x.sort] in
                  let wp = U.abs bs wp (Some (Inr (Const.effect_Tot_lid, [TOTAL]))) in
                  mk_Tm_app (inst_effect_fun_with us env md md.close_wp) [S.as_arg res_t; S.as_arg x.sort; S.as_arg wp] None wp0.pos)
              bvs wp0 in
            let c = Env.unfold_effect_abbrev env c in
            let u_res_t, res_t, wp = destruct_comp c in
            let md = Env.get_effect_decl env c.effect_name in
            let wp = close_wp u_res_t md res_t bvs wp in
            mk_comp md u_res_t c.result_typ wp c.flags
        end
  in
  {lc with comp=close}

let maybe_assume_result_eq_pure_term env (e:term) (lc:lcomp) : lcomp =
  let refine () =
      let c = lc.comp() in
      if not (is_pure_or_ghost_effect env lc.eff_name)
      || env.lax
      then c
      else if U.is_partial_return c then c
      else if U.is_tot_or_gtot_comp c
           && not (Env.lid_exists env Const.effect_GTot_lid)
      then failwith (BU.format2 "%s: %s\n" (Range.string_of_range e.pos) (Print.term_to_string e))
      else
           let c = Env.unfold_effect_abbrev env c in
           let t = c.result_typ in
           let c = mk_Comp c in
           let x = S.new_bv (Some t.pos) t in
           let xexp = S.bv_to_name x in
           let ret = U.lcomp_of_comp <| (U.comp_set_flags (return_value env t xexp) [PARTIAL_RETURN]) in
           let eq = U.mk_eq2 (env.universe_of env t) t xexp e in
           let eq_ret = weaken_precondition env ret (NonTrivial eq) in

           let c = U.comp_set_flags ((bind e.pos env None (U.lcomp_of_comp c) (Some x, eq_ret)).comp()) (PARTIAL_RETURN::U.comp_flags c) in
           c in

  let flags =
    if not (U.is_function_typ lc.res_typ)
    && U.is_pure_or_ghost_lcomp lc
    && not (U.is_lcomp_partial_return lc)
    then PARTIAL_RETURN::lc.cflags
    else lc.cflags in
  {lc with comp=refine; cflags=flags}

let check_comp env (e:term) (c:comp) (c':comp) : term * comp * guard_t =
  //printfn "Checking sub_comp:\n%s has type %s\n\t<:\n%s\n" (Print.exp_to_string e) (Print.comp_to_string c) (Print.comp_to_string c');
  match Rel.sub_comp env c c' with
    | None -> raise (Error(Err.computed_computation_type_does_not_match_annotation env e c c', Env.get_range env))
    | Some g -> e, c', g

let maybe_coerce_bool_to_type env (e:term) (lc:lcomp) (t:term) : term * lcomp =
    let is_type t =
        let t = N.unfold_whnf env t in
        match (SS.compress t).n with
        | Tm_type _ -> true
        | _ -> false
    in
    match (SS.compress lc.res_typ).n with
    | Tm_fvar fv
        when S.fv_eq_lid fv Const.bool_lid
          && is_type t ->
      let _ = Env.lookup_lid env Const.b2t_lid in  //check that we have Prims.b2t in the context
      let b2t = S.fvar (Ident.set_lid_range Const.b2t_lid e.pos) (Delta_defined_at_level 1) None in
      let lc = bind e.pos env (Some e) lc (None, U.lcomp_of_comp <| S.mk_Total (U.ktype0)) in
      let e = mk_Tm_app b2t [S.as_arg e] (Some U.ktype0.n) e.pos in
      e, lc
    | _ ->
      e, lc

let weaken_result_typ env (e:term) (lc:lcomp) (t:typ) : term * lcomp * guard_t =
  let use_eq =
    env.use_eq ||
    (match Env.effect_decl_opt env lc.eff_name with
     | Some (ed, qualifiers) -> qualifiers |> List.contains Reifiable
     | _ -> false) in
  let gopt = if use_eq //see issue #881 for why weakening result type of a reifiable computation is problematic
             then Rel.try_teq true env lc.res_typ t, false
             else Rel.try_subtype env lc.res_typ t, true in
  match gopt with
    | None, _ ->
      subtype_fail env e lc.res_typ t; //log a sub-typing error
      e, {lc with res_typ=t}, Rel.trivial_guard //and keep going to type-check the result of the program
    | Some g, apply_guard ->
      match guard_form g with
        | Trivial ->
          let lc = {lc with res_typ = t} in
          (e, lc, g)

        | NonTrivial f ->
          let g = {g with guard_f=Trivial} in
          let strengthen () =
              if env.lax
              && Options.ml_ish() //NS: disabling this optimization temporarily
              then
                lc.comp()
              else begin
                  //try to normalize one more time, since more unification variables may be resolved now
                  let f = N.normalize [N.Beta; N.Eager_unfolding; N.Simplify] env f in
                  match (SS.compress f).n with
                      | Tm_abs(_, {n=Tm_fvar fv}, _) when S.fv_eq_lid fv Const.true_lid ->
                        //it's trivial
                        let lc = {lc with res_typ=t} in
                        lc.comp()

                      | _ ->
                          let c = lc.comp() in
                          if Env.debug env <| Options.Extreme
                          then BU.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  (N.term_to_string env lc.res_typ)
                                  (N.term_to_string env t)
                                  (N.comp_to_string env c)
                                  (N.term_to_string env f);

                          let ct = Env.unfold_effect_abbrev env c in
                          let a, kwp = Env.wp_signature env Const.effect_PURE_lid in
                          let k = SS.subst [NT(a, t)] kwp in
                          let md = Env.get_effect_decl env ct.effect_name in
                          let x = S.new_bv (Some t.pos) t in
                          let xexp = S.bv_to_name x in
                          let u_t, _, _ = destruct_comp ct in
                          let wp = mk_Tm_app (inst_effect_fun_with [u_t] env md md.ret_wp)
                                             [S.as_arg t; S.as_arg xexp]
                                             (Some k.n) xexp.pos
                          in
                          let cret = U.lcomp_of_comp <| mk_comp md u_t t wp [RETURN] in
                          let guard = if apply_guard
                                      then mk_Tm_app f [S.as_arg xexp] (Some U.ktype0.n) f.pos
                                      else f
                          in
                          let eq_ret, _trivial_so_ok_to_discard =
                              strengthen_precondition (Some <| Err.subtyping_failed env lc.res_typ t)
                                                      (Env.set_range env e.pos) e cret
                                                      (guard_of_guard_formula <| NonTrivial guard)
                          in
                          let x = {x with sort=lc.res_typ} in
                          let c = bind e.pos env (Some e) (U.lcomp_of_comp <| mk_Comp ct) (Some x, eq_ret) in
                          let c = c.comp () in
                          if Env.debug env <| Options.Extreme
                          then BU.print1 "Strengthened to %s\n" (Normalize.comp_to_string env c);
                          c
                end
          in
          let flags = lc.cflags |> List.collect (function
                                                 | RETURN | PARTIAL_RETURN -> [PARTIAL_RETURN]
                                                 | CPS -> [CPS] // KM : Not exactly sure if it is necessary
                                                 | _ -> [])
          in
          let lc = {lc with res_typ=t; comp=strengthen; cflags=flags; eff_name=norm_eff_name env lc.eff_name} in
          let g = {g with guard_f=Trivial} in
          (e, lc, g)

let pure_or_ghost_pre_and_post env comp =
    let mk_post_type res_t ens =
        let x = S.new_bv None res_t in
        U.refine x (S.mk_Tm_app ens [S.as_arg (S.bv_to_name x)] None res_t.pos) in
    let norm t = Normalize.normalize [N.Beta;N.Eager_unfolding;N.EraseUniverses] env t in
    if U.is_tot_or_gtot_comp comp
    then None, U.comp_result comp
    else begin match comp.n with
            | GTotal _
            | Total _ -> failwith "Impossible"
            | Comp ct ->
              if lid_equals ct.effect_name Const.effect_Pure_lid
              || lid_equals ct.effect_name Const.effect_Ghost_lid
              then begin match ct.effect_args with
                      | (req, _)::(ens, _)::_ ->
                         Some (norm req), (norm <| mk_post_type ct.result_typ ens)
                      | _ ->
                        raise (Error (BU.format1 "Effect constructor is not fully applied; got %s" (Print.comp_to_string comp), comp.pos))
                   end
              else let ct = Env.unfold_effect_abbrev env comp in
                   begin match ct.effect_args with
                            | (wp, _)::_ ->
                              let us_r, _ = fst <| Env.lookup_lid env Const.as_requires in
                              let us_e, _ = fst <| Env.lookup_lid env Const.as_ensures in
                              let r = ct.result_typ.pos in
                              let as_req = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range Const.as_requires r) Delta_equational None) us_r in
                              let as_ens = S.mk_Tm_uinst (S.fvar (Ident.set_lid_range Const.as_ensures r) Delta_equational None) us_e in
                              let req = mk_Tm_app as_req [(ct.result_typ, Some S.imp_tag); S.as_arg wp] (Some U.ktype0.n) ct.result_typ.pos in
                              let ens = mk_Tm_app as_ens [(ct.result_typ, Some S.imp_tag); S.as_arg wp] None ct.result_typ.pos in
                              Some (norm req), norm (mk_post_type ct.result_typ ens)
                            | _ -> failwith "Impossible"
                  end

         end

(* [reify_body env t] assumes that [t] has a reifiable computation type *)
(* that is env |- t : M t' for some effect M and type t' where M is reifiable *)
(* and returns the result of reifying t *)
let reify_body (env:Env.env) (t:S.term) : S.term =
    let tm = U.mk_reify t in
    let tm' = N.normalize [N.Beta; N.Reify; N.Eager_unfolding; N.EraseUniverses; N.AllowUnboundUniverses] env tm in
    if Env.debug env <| Options.Other "SMTEncodingReify"
    then BU.print2 "Reified body %s \nto %s\n"
        (Print.term_to_string tm)
        (Print.term_to_string tm') ;
    tm'

let reify_body_with_arg (env:Env.env) (head:S.term) (arg:S.arg): S.term =
    let tm = S.mk (S.Tm_app(head, [arg])) None head.pos in
    let tm' = N.normalize [N.Beta; N.Reify; N.Eager_unfolding; N.EraseUniverses; N.AllowUnboundUniverses] env tm in
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
let maybe_instantiate (env:Env.env) e t =
  let torig = SS.compress t in
  if not env.instantiate_imp
  then e, torig, Rel.trivial_guard
  else let number_of_implicits t =
            let formals, _ = U.arrow_formals t in
            let n_implicits =
            match formals |> BU.prefix_until (fun (_, imp) -> imp=None || imp=Some Equality) with
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
             then raise (Error(BU.format3 "Expected a term with %s implicit arguments, but %s has only %s"
                                        (BU.string_of_int n_expected)
                                        (Print.term_to_string e)
                                        (BU.string_of_int n_available), Env.get_range env))
             else Some (n_available - n_expected)
        in
        let decr_inst = function
                | None -> None
                | Some i -> Some (i - 1)
        in
        begin match torig.n with
            | Tm_arrow(bs, c) ->
              let bs, c = SS.open_comp bs c in
              //instantiate at most inst_n implicit binders, when inst_n = Some n
              //otherwise, instantate all implicits
              //See issue #807 for why this is important
              let rec aux subst inst_n bs =
                  match inst_n, bs with
                  | Some 0, _ -> [], bs, subst, Rel.trivial_guard //no more instantiations to do
                  | _, (x, Some (Implicit dot))::rest ->
                      let t = SS.subst subst x.sort in
                      let v, _, g = new_implicit_var "Instantiation of implicit argument" e.pos env t in
                      let subst = NT(x, v)::subst in
                      let args, bs, subst, g' = aux subst (decr_inst inst_n) rest in
                      (v, Some (Implicit dot))::args, bs, subst, Rel.conj_guard g g'
                 | _, bs -> [], bs, subst, Rel.trivial_guard
              in
              let args, bs, subst, guard = aux [] (inst_n_binders t) bs in
              begin match args, bs with
                | [], _ -> //no implicits were instantiated
                  e, torig, guard

                | _, [] when not (U.is_total_comp c) ->
                  //don't instantiate implicitly, if it has an effect
                  e, torig, Rel.trivial_guard

                | _ ->

                  let t = match bs with
                    | [] -> U.comp_result c
                    | _ -> U.arrow bs c in
                  let t = SS.subst subst t in
                  let e = S.mk_Tm_app e args (Some t.n) e.pos in
                  e, t, guard
              end

            | _ -> e, t, Rel.trivial_guard
       end

(**************************************************************************************)
(* Generalizing types *)
(**************************************************************************************)
let string_of_univs univs =
  BU.set_elements univs
  |> List.map (fun u -> Unionfind.uvar_id u |> string_of_int) |> String.concat ", "

let gen_univs env (x:BU.set<universe_uvar>) : list<univ_name> =
    if BU.set_is_empty x then []
    else let s = BU.set_difference x (Env.univ_vars env) |> BU.set_elements in
         if Env.debug env <| Options.Other "Gen" then
         BU.print1 "univ_vars in env: %s\n" (string_of_univs (Env.univ_vars env));
         let r = Some (Env.get_range env) in
         let u_names = s |> List.map (fun u ->
            let u_name = Syntax.new_univ_name r in
            if Env.debug env <| Options.Other "Gen"
            then BU.print3 "Setting ?%s (%s) to %s\n" (string_of_int <| Unionfind.uvar_id u) (Print.univ_to_string (U_unif u)) (Print.univ_to_string (U_name u_name));
            Unionfind.change u (Some (U_name u_name));
            u_name) in
         u_names

let gather_free_univnames env t : list<univ_name> =
    let ctx_univnames = Env.univnames env in
    let tm_univnames = Free.univnames t in
    let univnames = BU.fifo_set_difference tm_univnames ctx_univnames |> BU.fifo_set_elements in
    // BU.print4 "Closing universe variables in term %s : %s in ctx, %s in tm, %s globally\n"
    //     (Print.term_to_string t)
    //     (Print.set_to_string Ident.text_of_id ctx_univnames)
    //     (Print.set_to_string Ident.text_of_id tm_univnames)
    //     (Print.list_to_string Ident.text_of_id univnames);
    univnames


let maybe_set_tk ts = function
    | None -> ts
    | Some t ->
      let t = S.mk t None Range.dummyRange in
      let t = SS.close_univ_vars (fst ts) t in
      (snd ts).tk := Some t.n;
      ts

let check_universe_generalization
  (explicit_univ_names : list<univ_name>)
  (generalized_univ_names : list<univ_name>)
  (t : term)
  : list<univ_name>
=
  match explicit_univ_names, generalized_univ_names with
  | [], _ -> generalized_univ_names
  | _, [] -> explicit_univ_names
  | _ -> raise (Error("Generalized universe in a term containing explicit universe annotation : "
                      ^ Print.term_to_string t, t.pos))

let generalize_universes (env:env) (t0:term) : tscheme =
    let t = N.normalize [N.NoFullNorm; N.Beta] env t0 in
    let univnames = gather_free_univnames env t in
    let univs = Free.univs t in
    if Env.debug env <| Options.Other "Gen"
    then BU.print1 "univs to gen : %s\n" (string_of_univs univs);
    let gen = gen_univs env univs in
    if Env.debug env <| Options.Other "Gen"
    then BU.print1 "After generalization: %s\n"  (Print.term_to_string t);
    let univs = check_universe_generalization univnames gen t0 in
    let ts = SS.close_univ_vars univs t in
    maybe_set_tk (univs, ts) (!t0.tk)

let gen env (ecs:list<(term * comp)>) : option<list<(list<univ_name> * term * comp)>> =
  if not <| (BU.for_all (fun (_, c) -> U.is_pure_or_ghost_comp c) ecs) //No value restriction in F*---generalize the types of pure computations
  then None
  else
     let norm c =
        if debug env Options.Medium
        then BU.print1 "Normalizing before generalizing:\n\t %s\n" (Print.comp_to_string c);
         let c = if Env.should_verify env
                 then Normalize.normalize_comp [N.Beta; N.Eager_unfolding; N.NoFullNorm] env c
                 else Normalize.normalize_comp [N.Beta; N.NoFullNorm] env c in
         if debug env Options.Medium then
            BU.print1 "Normalized to:\n\t %s\n" (Print.comp_to_string c);
         c in
     let env_uvars = Env.uvars_in_env env in
     let gen_uvars uvs = BU.set_difference uvs env_uvars |> BU.set_elements in
     let univs, uvars = ecs |> List.map (fun (e, c) ->
          let t = U.comp_result c |> SS.compress in
          let c = norm c in
          let t = U.comp_result c in
          let univs = Free.univs t in
          let uvt = Free.uvars t in
          let uvs = gen_uvars uvt in
         univs, (uvs, e, c)) |> List.unzip in

     let univs = List.fold_left BU.set_union S.no_universe_uvars univs in
     let gen_univs = gen_univs env univs in
     if debug env Options.Medium then gen_univs |> List.iter (fun x -> BU.print1 "Generalizing uvar %s\n" x.idText);

     let ecs = uvars |> List.map (fun (uvs, e, c) ->
          let tvars = uvs |> List.map (fun (u, k) ->
            match Unionfind.find u with
              | Fixed ({n=Tm_name a})
              | Fixed ({n=Tm_abs(_, {n=Tm_name a}, _)}) -> a, Some S.imp_tag
              | Fixed _ -> failwith "Unexpected instantiation of mutually recursive uvar"
              | _ ->
                  let k = N.normalize [N.Beta] env k in
                  let bs, kres = U.arrow_formals k in
                  let a = S.new_bv (Some <| Env.get_range env) kres in
                  let t = U.abs bs (S.bv_to_name a) (Some (Inl (U.lcomp_of_comp (S.mk_Total kres)))) in
                  U.set_uvar u t;//t clearly has a free variable; this is the one place we break the
                                 //invariant of a uvar always being resolved to a closed term ... need to be careful, see below
                  a, Some S.imp_tag) in

          let e, c = match tvars, gen_univs with
            | [], [] -> //nothing generalized
              e, c

            | [], _ ->
              //nothing generalized, or
              //only universes generalized, still need to compress out invariant-broken uvars
              let c = N.normalize_comp [N.Beta; N.NoDeltaSteps; N.NoFullNorm] env c in
              let e = N.normalize [N.Beta; N.NoDeltaSteps; N.NoFullNorm] env e in
              e, c

            | _ ->
              //before we manipulate the term further, we must normalize it to get rid of the invariant-broken uvars
              let e0, c0 = e, c in
              let c = N.normalize_comp [N.Beta; N.NoDeltaSteps; N.CompressUvars; N.NoFullNorm] env c in
              let e = N.normalize [N.Beta; N.NoDeltaSteps; N.CompressUvars; N.Exclude N.Zeta; N.Exclude N.Iota; N.NoFullNorm] env e in
              //now, with the uvars gone, we can close over the newly introduced type names
              let t = match (SS.compress (U.comp_result c)).n with
                    | Tm_arrow(bs, cod) ->
                      let bs, cod = SS.open_comp bs cod in
                      U.arrow (tvars@bs) cod

                    | _ ->
                      U.arrow tvars c in
              let e' = U.abs tvars e (Some (Inl (U.lcomp_of_comp c))) in
              e', S.mk_Total t in
          (gen_univs, e, c)) in
     Some ecs

let generalize env (lecs:list<(lbname*term*comp)>) : (list<(lbname*univ_names*term*comp)>) =
  if debug env Options.Low
  then BU.print1 "Generalizing: %s\n"
       (List.map (fun (lb, _, _) -> Print.lbname_to_string lb) lecs |> String.concat ", ");
  let univnames_lecs = List.map (fun (l, t, c) -> gather_free_univnames env t) lecs in
  let generalized_lecs =
      match gen env (lecs |> List.map (fun (_, e, c) -> (e, c))) with
          | None -> lecs |> List.map (fun (l,t,c) -> l,[],t,c)
          | Some ecs ->
              List.map2 (fun (l, _, _) (us, e, c) ->
                         if debug env Options.Medium
                         then BU.print4 "(%s) Generalized %s at type %s\n%s\n"
                                          (Range.string_of_range e.pos)
                                          (Print.lbname_to_string l)
                                          (Print.term_to_string (U.comp_result c))
                                          (Print.term_to_string e);
                         (l, us, e, c)) lecs ecs
   in
   List.map2 (fun univnames (l,generalized_univs, t, c) ->
              (l, check_universe_generalization univnames generalized_univs t, t, c))
             univnames_lecs
             generalized_lecs

(************************************************************************)
(* Convertibility *)
(************************************************************************)
//check_and_ascribe env e t1 t2
//checks is e:t1 is convertible to t2, subject to some guard.
//e is ascribed the type t2 and the guard is returned'
let check_and_ascribe env (e:term) (t1:typ) (t2:typ) : term * guard_t =
  let env = Env.set_range env e.pos in
  let check env t1 t2 =
    if env.use_eq
    then Rel.try_teq true env t1 t2
    else match Rel.try_subtype env t1 t2 with
            | None -> None
            | Some f -> Some <| apply_guard f e in
  let is_var e = match (SS.compress e).n with
    | Tm_name _ -> true
    | _ -> false in
  let decorate e t =
    let e = compress e in
    match e.n with
        | Tm_name x -> mk (Tm_name ({x with sort=t2})) (Some t2.n) e.pos
        | _ -> {e with tk=BU.mk_ref (Some t2.n)} in
  let env = {env with use_eq=env.use_eq || (env.is_pattern && is_var e)} in
  match check env t1 t2 with
    | None -> raise (Error(Err.expected_expression_of_type env t2 e t1, Env.get_range env))
    | Some g ->
        if debug env <| Options.Other "Rel"
        then BU.print1 "Applied guard is %s\n" <| guard_to_string env g;
        decorate e t2, g

/////////////////////////////////////////////////////////////////////////////////
let check_top_level env g lc : (bool * comp) =
  let discharge g =
    force_trivial_guard env g;
    U.is_pure_lcomp lc in
  let g = Rel.solve_deferred_constraints env g in
  if U.is_total_lcomp lc
  then discharge g, lc.comp()
  else let c = lc.comp() in
       let steps = [Normalize.Beta] in
       let c = Env.unfold_effect_abbrev env c
              |> S.mk_Comp
              |> Normalize.normalize_comp steps env
              |> Env.comp_to_comp_typ env in
       let md = Env.get_effect_decl env c.effect_name in
       let u_t, t, wp = destruct_comp c in
       let vc = mk_Tm_app (inst_effect_fun_with [u_t] env md md.trivial) [S.as_arg t; S.as_arg wp] (Some U.ktype0.n) (Env.get_range env) in
       if Env.debug env <| Options.Other "Simplification"
       then BU.print1 "top-level VC: %s\n" (Print.term_to_string vc);
       let g = Rel.conj_guard g (Rel.guard_of_guard_formula <| NonTrivial vc) in
       discharge g, mk_Comp c

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
        [(Const.op_And,  short_bin_op op_and_e);
         (Const.op_Or,   short_bin_op op_or_e);
         (Const.and_lid, short_bin_op op_and_t);
         (Const.or_lid,  short_bin_op op_or_t);
         (Const.imp_lid, short_bin_op op_imp_t);
         (Const.ite_lid, short_op_ite);] in

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
                   [Const.op_And;
                    Const.op_Or;
                    Const.and_lid;
                    Const.or_lid;
                    Const.imp_lid;
                    Const.ite_lid]
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
        | (hd, _)::_ -> S.range_of_bv hd
        | _ -> Env.get_range env in
    match bs with
        | (_, Some (Implicit _))::_ -> bs //bs begins with an implicit binder; don't add any
        | _ ->
          match Env.expected_typ env with
            | None -> bs
            | Some t ->
                match (SS.compress t).n with
                    | Tm_arrow(bs', _) ->
                      begin match BU.prefix_until (function (_, Some (Implicit _)) -> false | _ -> true) bs' with
                        | None -> bs
                        | Some ([], _, _) -> bs //no implicits
                        | Some (imps, _,  _) ->
                          if imps |> BU.for_all (fun (x, _) -> BU.starts_with x.ppname.idText "'")
                          then let r = pos bs in
                               let imps = imps |> List.map (fun (x, i) -> (S.set_range_of_bv x r, i)) in
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
    else mk (Tm_meta(e, Meta_monadic_lift(m1, m2, t))) !e.tk e.pos

let maybe_monadic env e c t =
    let m = Env.norm_eff_name env c in
    if is_pure_or_ghost_effect env m
    || Ident.lid_equals m Const.effect_Tot_lid
    || Ident.lid_equals m Const.effect_GTot_lid //for the cases in prims where Pure is not yet defined
    then e
    else mk (Tm_meta(e, Meta_monadic (m, t))) !e.tk e.pos

let d s = BU.print1 "\x1b[01;36m%s\x1b[00m\n" s

// Takes care of creating the [fv], generating the top-level let-binding, and
// return a term that's a suitable reference (a [Tm_fv]) to the definition
let mk_toplevel_definition (env: env_t) lident (def: term): sigelt * term =
  // Debug
  if Env.debug env (Options.Other "ED") then begin
    d (text_of_lid lident);
    BU.print2 "Registering top-level definition: %s\n%s\n" (text_of_lid lident) (Print.term_to_string def)
  end;
  // Allocate a new top-level name.
  let fv = S.lid_as_fv lident (U.incr_delta_qualifier def) None in
  let lbname: lbname = Inr fv in
  let lb: letbindings = false, [{
     lbname = lbname;
     lbunivs = [];
     lbtyp = S.tun;
     lbdef = def;
     lbeff = Const.effect_Tot_lid; //this will be recomputed correctly
  }] in
  // [Inline] triggers a "Impossible: locally nameless" error // FIXME: Doc?
  let sig_ctx = mk_sigelt (Sig_let (lb, [ lident ], [])) in
  {sig_ctx with sigquals=[ Unfold_for_unification_and_vcgen ]},
  mk (Tm_fvar fv) None Range.dummyRange


/////////////////////////////////////////////////////////////////////////////
//Checks that the qualifiers on this sigelt are legal for it
/////////////////////////////////////////////////////////////////////////////
let check_sigelt_quals (env:FStar.TypeChecker.Env.env) se =
    let visibility = function Private -> true | _ -> false in
    let reducibility = function
        | Abstract | Irreducible
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
          |> List.for_all (fun x -> x=q || x=Logic || inferred x || visibility x || assumption x || (env.is_iface && x=Inline_for_extraction))

        | New -> //no definition provided
          quals
          |> List.for_all (fun x -> x=q || inferred x || visibility x || assumption x)

        | Inline_for_extraction ->
          quals |> List.for_all (fun x -> x=q || x=Logic || visibility x || reducibility x
                                              || reification x || inferred x
                                              || (env.is_iface && x=Assumption))

        | Unfold_for_unification_and_vcgen
        | Visible_default
        | Irreducible
        | Abstract
        | Noeq
        | Unopteq ->
          quals
          |> List.for_all (fun x -> x=q || x=Logic || x=Abstract || x=Inline_for_extraction || has_eq x || inferred x || visibility x)

        | TotalEffect ->
          quals
          |> List.for_all (fun x -> x=q || inferred x || visibility x || reification x)

        | Logic ->
          quals
          |> List.for_all (fun x -> x=q || x=Assumption || inferred x || visibility x || reducibility x)

        | Reifiable
        | Reflectable _ ->
          quals
          |> List.for_all (fun x -> reification x || inferred x || visibility x || x=TotalEffect)

        | Private ->
          true //only about visibility; always legal in combination with others

        | _ -> //inferred
          true
    in
    let quals = U.quals_of_sigelt se in
    if quals |> BU.for_some (function OnlyName -> true | _ -> false) |> not
    then
      let r = U.range_of_sigelt se in
      let no_dup_quals = BU.remove_dups (fun x y -> x=y) quals in
      let err' msg =
          raise (Error(BU.format2
                          "The qualifier list \"[%s]\" is not permissible for this element%s"
                          (Print.quals_to_string quals) msg
                          , r)) in
      let err msg = err' (": " ^ msg) in
      let err' () = err' "" in
      if List.length quals <> List.length no_dup_quals
      then err "duplicate qualifiers";
      if not (quals |> List.for_all (quals_combo_ok quals))
      then err "ill-formed combination";
      match se.sigel with
      | Sig_let((is_rec, _), _, _) -> //let rec
        if is_rec && quals |> List.contains Unfold_for_unification_and_vcgen
        then err "recursive definitions cannot be marked inline";
        if quals |> BU.for_some (fun x -> assumption x || has_eq x)
        then err "definitions cannot be assumed or marked with equality qualifiers"
      | Sig_bundle _ ->
        if not (quals |> BU.for_all (fun x ->
              x=Abstract
              || inferred x
              || visibility x
              || has_eq x))
        then err' ()
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
      | Sig_new_effect_for_free _ ->
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



(******************************************************************************)
(*                                                                            *)
(*                Elaboration of the projectors                               *)
(*                                                                            *)
(******************************************************************************)



let mk_discriminator_and_indexed_projectors iquals                   (* Qualifiers of the envelopping bundle    *)
                                            (fvq:fv_qual)            (*                                         *)
                                            (refine_domain:bool)     (* If true, discriminates the projectee    *)
                                            env                      (*                                         *)
                                            (tc:lident)              (* Type constructor name                   *)
                                            (lid:lident)             (* Constructor name                        *)
                                            (uvs:univ_names)         (* Original universe names                 *)
                                            (inductive_tps:binders)  (* Type parameters of the type constructor *)
                                            (indices:binders)        (* Implicit type parameters                *)
                                            (fields:binders)         (* Fields of the constructor               *)
                                            : list<sigelt> =
    let p = range_of_lid lid in
    let pos q = Syntax.withinfo q tun.n p in
    let projectee ptyp = S.gen_bv "projectee" (Some p) ptyp in
    let inst_univs = List.map (fun u -> U_name u) uvs in
    let tps = inductive_tps in //List.map2 (fun (x,_) (_,imp) -> ({x,imp)) implicit_tps inductive_tps in
    let arg_typ =
        let inst_tc = S.mk (Tm_uinst (S.fv_to_tm (S.lid_as_fv tc Delta_constant None), inst_univs)) None p in
        let args = tps@indices |> List.map (fun (x, imp) -> S.bv_to_name x,imp) in
        S.mk_Tm_app inst_tc args None p
    in
    let unrefined_arg_binder = S.mk_binder (projectee arg_typ) in
    let arg_binder =
        if not refine_domain
        then unrefined_arg_binder //records have only one constructor; no point refining the domain
        else let disc_name = U.mk_discriminator lid in
             let x = S.new_bv (Some p) arg_typ in
             let sort =
                 let disc_fvar = S.fvar (Ident.set_lid_range disc_name p) Delta_equational None in
                 U.refine x (U.b2t (S.mk_Tm_app (S.mk_Tm_uinst disc_fvar inst_univs) [as_arg <| S.bv_to_name x] None p))
             in
             S.mk_binder ({projectee arg_typ with sort = sort})
    in


    let ntps = List.length tps in
    let all_params = List.map (fun (x, _) -> x, Some S.imp_tag) tps @ fields in

    let imp_binders = tps @ indices |> List.map (fun (x, _) -> x, Some S.imp_tag) in

    let discriminator_ses =
        if fvq <> Data_ctor
        then [] // We do not generate discriminators for record types
        else
            let discriminator_name = U.mk_discriminator lid in
            let no_decl = false in
            let only_decl =
                  lid_equals C.prims_lid  (Env.current_module env)
                  || Options.dont_gen_projectors (Env.current_module env).str
            in
            let quals =
                (* KM : What about Logic ? should it still be there even with an implementation *)
                S.Discriminator lid ::
                (if only_decl then [S.Logic] else []) @
                (if only_decl && (not <| env.is_iface || env.admit) then [S.Assumption] else []) @
                List.filter (function S.Abstract -> not only_decl | S.Private -> true | _ -> false ) iquals
            in

            (* Type of the discriminator *)
            let binders = imp_binders@[unrefined_arg_binder] in
            let t =
                let bool_typ = (S.mk_Total (S.fv_to_tm (S.lid_as_fv C.bool_lid Delta_constant None))) in
                SS.close_univ_vars uvs <| U.arrow binders bool_typ
            in
            let decl = { sigel = Sig_declare_typ(discriminator_name, uvs, t);
                         sigquals = quals;
                         sigrng = range_of_lid discriminator_name;
                         sigmeta = default_sigmeta  }  in
            if Env.debug env (Options.Other "LogTypes")
            then BU.print1 "Declaration of a discriminator %s\n"  (Print.sigelt_to_string decl);

            if only_decl
            then [decl]
            else
                (* Term of the discriminator *)
                let body =
                    if not refine_domain
                    then C.exp_true_bool   // If we have at most one constructor
                    else
                        let arg_pats = all_params |> List.mapi (fun j (x,imp) ->
                            let b = S.is_implicit imp in
                            if b && j < ntps
                            then pos (Pat_dot_term (S.gen_bv x.ppname.idText None tun, tun)), b
                            else pos (Pat_wild (S.gen_bv x.ppname.idText None tun)), b)
                        in
                        let pat_true = pos (S.Pat_cons (S.lid_as_fv lid Delta_constant (Some fvq), arg_pats)), None, C.exp_true_bool in
                        let pat_false = pos (Pat_wild (S.new_bv None tun)), None, C.exp_false_bool in
                        let arg_exp = S.bv_to_name (fst unrefined_arg_binder) in
                        mk (Tm_match(arg_exp, [U.branch pat_true ; U.branch pat_false])) None p
                in
                let dd =
                    if quals |> List.contains S.Abstract
                    then Delta_abstract Delta_equational
                    else Delta_equational
                in
                let imp = U.abs binders body None in
                let lbtyp = if no_decl then t else tun in
                let lb = {
                    lbname=Inr (S.lid_as_fv discriminator_name dd None);
                    lbunivs=uvs;
                    lbtyp=lbtyp;
                    lbeff=C.effect_Tot_lid;
                    lbdef=SS.close_univ_vars uvs imp
                } in
                let impl = { sigel = Sig_let((false, [lb]), [lb.lbname |> right |> (fun fv -> fv.fv_name.v)], []);
                             sigquals = quals;
                             sigrng = p;
                             sigmeta = default_sigmeta  } in
                if Env.debug env (Options.Other "LogTypes")
                then BU.print1 "Implementation of a discriminator %s\n"  (Print.sigelt_to_string impl);
                (* TODO : Are there some cases where we don't want one of these ? *)
                (* If not the declaration is useless, isn't it ?*)
                [decl ; impl]
    in


    let arg_exp = S.bv_to_name (fst arg_binder) in
    let binders = imp_binders@[arg_binder] in
    let arg = U.arg_of_non_null_binder arg_binder in

    let subst = fields |> List.mapi (fun i (a, _) ->
            let field_name, _ = U.mk_field_projector_name lid a i in
            let field_proj_tm = mk_Tm_uinst (S.fv_to_tm (S.lid_as_fv field_name Delta_equational None)) inst_univs in
            let proj = mk_Tm_app field_proj_tm [arg] None p in
            NT(a, proj))
    in

    let projectors_ses =
      fields |> List.mapi (fun i (x, _) ->
          let p = S.range_of_bv x in
          let field_name, _ = U.mk_field_projector_name lid x i in
          let t = SS.close_univ_vars uvs <| U.arrow binders (S.mk_Total (Subst.subst subst x.sort)) in
          let only_decl =
              lid_equals C.prims_lid  (Env.current_module env)
              || fvq<>Data_ctor
              || Options.dont_gen_projectors (Env.current_module env).str
          in
          (* KM : Why would we want to prevent a declaration only in this particular case ? *)
          (* TODO : If we don't want the declaration then we need to propagate the right types in the patterns *)
          let no_decl = false (* Syntax.is_type x.sort *) in
          let quals q =
              if only_decl
              then S.Assumption::List.filter (function S.Abstract -> false | _ -> true) q
              else q
          in
          let quals =
              let iquals = iquals |> List.filter (function
                  | S.Abstract
                  | S.Private -> true
                  | _ -> false)
              in
              quals (S.Projector(lid, x.ppname)::iquals) in
          let decl = { sigel = Sig_declare_typ(field_name, uvs, t);
                       sigquals = quals;
                       sigrng = range_of_lid field_name;
                       sigmeta = default_sigmeta  } in
          if Env.debug env (Options.Other "LogTypes")
          then BU.print1 "Declaration of a projector %s\n"  (Print.sigelt_to_string decl);
          if only_decl
          then [decl] //only the signature
          else
              let projection = S.gen_bv x.ppname.idText None tun in
              let arg_pats = all_params |> List.mapi (fun j (x,imp) ->
                  let b = S.is_implicit imp in
                  if i+ntps=j  //this is the one to project
                  then pos (Pat_var projection), b
                  else if b && j < ntps
                  then pos (Pat_dot_term (S.gen_bv x.ppname.idText None tun, tun)), b
                  else pos (Pat_wild (S.gen_bv x.ppname.idText None tun)), b)
              in
              let pat = pos (S.Pat_cons (S.lid_as_fv lid Delta_constant (Some fvq), arg_pats)), None, S.bv_to_name projection in
              let body = mk (Tm_match(arg_exp, [U.branch pat])) None p in
              let imp = U.abs binders body None in
              let dd =
                  if quals |> List.contains S.Abstract
                  then Delta_abstract Delta_equational
                  else Delta_equational
              in
              let lbtyp = if no_decl then t else tun in
              let lb = {
                  lbname=Inr (S.lid_as_fv field_name dd None);
                  lbunivs=uvs;
                  lbtyp=lbtyp;
                  lbeff=C.effect_Tot_lid;
                  lbdef=SS.close_univ_vars uvs imp
              } in
              let impl = { sigel = Sig_let((false, [lb]), [lb.lbname |> right |> (fun fv -> fv.fv_name.v)], []);
                           sigquals = quals;
                           sigrng = p;
                           sigmeta = default_sigmeta  } in
              if Env.debug env (Options.Other "LogTypes")
              then BU.print1 "Implementation of a projector %s\n"  (Print.sigelt_to_string impl);
              if no_decl then [impl] else [decl;impl]) |> List.flatten
    in
    discriminator_ses @ projectors_ses

let mk_data_operations iquals env tcs se =
  match se.sigel with
  | Sig_datacon(constr_lid, uvs, t, typ_lid, n_typars, _) when not (lid_equals constr_lid C.lexcons_lid) ->

    let univ_opening, uvs = SS.univ_var_opening uvs in
    let t = SS.subst univ_opening t in
    let formals, _ = U.arrow_formals t in

    let inductive_tps, typ0, should_refine =
        let tps_opt = BU.find_map tcs (fun se ->
            if lid_equals typ_lid (must (U.lid_of_sigelt se))
            then match se.sigel with
                  | Sig_inductive_typ(_, uvs', tps, typ0, _, constrs) ->
                      assert (List.length uvs = List.length uvs') ;
                      Some (tps, typ0, List.length constrs > 1)
                  | _ -> failwith "Impossible"
            else None)
        in
        match tps_opt with
            | Some x -> x
            | None ->
                if lid_equals typ_lid Const.exn_lid
                then [], U.ktype0, true
                else raise (Error("Unexpected data constructor", se.sigrng))
    in

    let inductive_tps = SS.subst_binders univ_opening inductive_tps in
    let typ0 = SS.subst univ_opening typ0 in
    let indices, _ = U.arrow_formals typ0 in

    let refine_domain =
        if se.sigquals |> BU.for_some (function RecordConstructor _ -> true | _ -> false)
        then false
        else should_refine
    in

    let fv_qual =
        let filter_records = function
            | RecordConstructor (_, fns) -> Some (Record_ctor(constr_lid, fns))
            | _ -> None
        in match BU.find_map se.sigquals filter_records with
            | None -> Data_ctor
            | Some q -> q
    in

    let iquals =
        if List.contains S.Abstract iquals
        then S.Private::iquals
        else iquals
    in

    let fields =
        let imp_tps, fields = BU.first_N n_typars formals in
        let rename = List.map2 (fun (x, _) (x', _) -> S.NT(x, S.bv_to_name x')) imp_tps inductive_tps in
        SS.subst_binders rename fields
    in
    mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields

  | _ -> []
