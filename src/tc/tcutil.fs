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

module FStar.Tc.Util

open FStar
open FStar.Tc
open FStar.Absyn
open FStar.Absyn.Util
open FStar.Util
open FStar.Tc.Env
open FStar.Tc.Normalize
open FStar.Tc.Rel
open FStar.Absyn.Syntax

(**************************************************************************************)
(* Calling the solver *)
(**************************************************************************************)
let try_solve env f = env.solver.solve env f
let report env errs =
    Tc.Errors.report (Tc.Env.get_range env)
                     (Tc.Errors.failed_to_prove_specification errs)

let discharge_guard env (g:guard_t) = Rel.try_discharge_guard env g

let force_trivial env g = discharge_guard env g

(**************************************************************************************)
let syn' env k = syn (Tc.Env.get_range env) k

let is_xvar_free (x:bvvdef) t =
  let f = Util.freevars_typ t in
  Util.set_mem (bvd_to_bvar_s x tun) f.fxvs

let is_tvar_free (a:btvdef) t =
  let f = Util.freevars_typ t in
  Util.set_mem (bvd_to_bvar_s a kun) f.ftvs

let check_and_ascribe env (e:exp) (t1:typ) (t2:typ) : exp * guard_t =
  let env = Env.set_range env e.pos in
  let check env t1 t2 =
    if env.use_eq
    then Rel.try_teq env t1 t2
    else match Rel.try_subtype env t1 t2 with
            | None -> None
            | Some f -> Some <| apply_guard f e in
  if env.is_pattern && false
  then match Rel.try_teq env t1 t2 with
        | None -> raise (Error(Tc.Errors.expected_pattern_of_type env t2 e t1, Tc.Env.get_range env))
        | Some g -> e, g
  else match check env t1 t2 with
        | None ->
          raise (Error(Tc.Errors.expected_expression_of_type env t2 e t1, Tc.Env.get_range env))
        | Some g ->
           if debug env <| Options.Other "Rel"
           then Util.print1 "Applied guard is %s\n" <| guard_to_string env g;
           let e = Util.compress_exp e in
           let e = match e.n with
               | Exp_bvar x -> mk_Exp_bvar (Util.bvd_to_bvar_s x.v t2) (Some t2) e.pos
               | _ -> {e with tk=Util.mk_ref (Some t2)} in
           e, g

let env_binders env =
    if !Options.full_context_dependency
    then Env.binders env
    else Env.t_binders env

let as_uvar_e = function
    | {n=Exp_uvar(uv, _)} -> uv
    | _ -> failwith "Impossible"
let as_uvar_t (t:typ) = match t with
    | {n=Typ_uvar(uv, _)} -> uv
    | _ -> failwith "Impossible"
let new_kvar env   = Rel.new_kvar (Env.get_range env) (env_binders env)   |> fst
let new_tvar env k = Rel.new_tvar (Env.get_range env) (env_binders env) k |> fst
let new_evar env t = Rel.new_evar (Env.get_range env) (env_binders env) t |> fst
let new_implicit_tvar env k =
    let t, u = Rel.new_tvar (Env.get_range env) (env_binders env) k in
    t, (as_uvar_t u, u.pos)
let new_implicit_evar env t =
    let e, u = Rel.new_evar (Env.get_range env) (env_binders env) t in
    e, (as_uvar_e u, u.pos)
let force_tk s = match !s.tk with
    | None -> failwith (Util.format1 "Impossible: Forced tk not present (%s)" (Range.string_of_range s.pos))
    | Some tk -> tk
let tks_of_args (args:args) =
    args |> List.map (function
        | Inl t, imp -> Inl (force_tk t), imp
        | Inr v, imp -> Inr (force_tk v), imp)

let is_implicit = function Some Implicit -> true | _ -> false
let destruct_arrow_kind env tt k (args:args) : (Syntax.args * binders * knd) =
    let ktop = compress_kind k |> Normalize.norm_kind [WHNF; Beta; Eta] env in
    let r = Env.get_range env in
    let rec aux k = match k.n with
        | Kind_arrow(bs, k') ->
          let imp_follows = match args with
            | (_, qual)::_ -> is_implicit qual
            | _ -> false in
          let rec mk_implicits vars subst bs = match bs with
            | b::brest ->
              if snd b |> is_implicit
              then let imp_arg = match fst b with
                    | Inl a -> Tc.Rel.new_tvar r vars (Util.subst_kind subst a.sort) |> fst |> (fun x -> Inl x, as_implicit true) //set the implicit flag
                    | Inr x -> Tc.Rel.new_evar r vars (Util.subst_typ subst x.sort) |> fst |>  (fun x -> Inr x, as_implicit true) in
                   let subst = if is_null_binder b then subst else  (subst_formal b imp_arg)::subst in
                   let imp_args, bs = mk_implicits vars subst brest in
                   imp_arg::imp_args, bs
              else [], subst_binders subst bs
            | _ -> [], subst_binders subst bs in
          if imp_follows
          then [], bs, k'
          else let imps, bs = mk_implicits (Tc.Env.binders env) [] bs in
               imps, bs, k'

       | Kind_abbrev(_, k) -> aux k

       | Kind_uvar _ ->
         let fvs = Util.freevars_kind k in
         let binders = Util.binders_of_freevars fvs in
         let kres = Tc.Rel.new_kvar r binders |> fst in
         let bs = null_binders_of_tks (tks_of_args args) in
         let kar = mk_Kind_arrow(bs, kres) r in
         force_trivial env <| keq env None k kar;
         [], bs, kres

       | _ -> raise (Error(Tc.Errors.expected_tcon_kind env tt ktop, r)) in

    aux ktop

let as_imp = function
    | Some Implicit -> true
    | _ -> false
(*
    Turns a disjunctive pattern p into a quadruple:
 *)
let pat_as_exps allow_implicits env p
                        : (list<binding>     (* pattern-bound variables (which may appear in the branch of match) *)
                         * list<exp>        (* expressions corresponding to each arm of the disjunct *)
                         * pat)   =          (* decorated pattern, with all the missing implicit args in p filled in *)
     let pvar_eq x y = match x, y with
          | Env.Binding_var(x, _), Env.Binding_var(y, _) -> bvd_eq x y
          | Env.Binding_typ(x, _), Env.Binding_typ(y, _) -> bvd_eq x y
          | _ -> false in

     let vars_of_bindings bs =
        bs |> List.map (function
           | Env.Binding_var(x, _) -> Inr x
           | Env.Binding_typ(x, _) -> Inl x
           | _ -> failwith "impos") in


      let rec pat_as_arg_with_env allow_wc_dependence env (p:pat) :
                                    (list<Env.binding>    //all pattern-bound vars including wild-cards, in proper order
                                    * list<Env.binding>   //just the accessible vars, for the disjunctive pattern test
                                    * list<Env.binding>   //just the wildcards
                                    * Env.env             //env extending with the pattern-bound variables
                                    * either<typ,exp>      //the pattern as a term/typ
                                    * pat) =              //the elaborated pattern itself
        match p.v with
           | Pat_dot_term(x, _) ->
             let t = new_tvar env ktype in
             let e, u = Rel.new_evar p.p [] t in //TODO: why empty vars?
             let p = {p with v=Pat_dot_term(x, e)} in
             ([], [], [], env, Inr e, p)

           | Pat_dot_typ (a, _) ->
             let k = new_kvar env in
             let t, u = Rel.new_tvar p.p (Env.binders env) k in
             let p = {p with v=Pat_dot_typ(a, t)} in
             ([], [], [], env, Inl t, p)

           | Pat_constant c ->
             let e = mk_Exp_constant c None p.p in
             ([], [], [], env, Inr e, p)

           | Pat_wild x ->
             let w = Env.Binding_var(x.v, new_tvar env ktype) in
             let env = if allow_wc_dependence then Env.push_local_binding env w else env in
             let e = mk_Exp_bvar x None p.p in
             ([w], [], [w], env, Inr e, p)

           | Pat_var x ->
             let b = Env.Binding_var(x.v, new_tvar env ktype) in
             let env = Env.push_local_binding env b in
             let e = mk_Exp_bvar x None p.p in
             ([b], [b], [], env, Inr e, p)

           | Pat_twild a ->
             let w = Env.Binding_typ(a.v, new_kvar env) in
             let env = if allow_wc_dependence then Env.push_local_binding env w else env in
             let t = mk_Typ_btvar a None p.p in
             ([w], [], [w], env, Inl t, p)

           | Pat_tvar a ->
             let b = Env.Binding_typ(a.v, new_kvar env) in
             let env = Env.push_local_binding env b in
             let t = mk_Typ_btvar a None p.p in
             ([b], [b], [], env, Inl t, p)


           | Pat_cons(fv, q, pats) ->
               let (b, a, w, env, args, pats) = pats |> List.fold_left (fun (b, a, w, env, args, pats) (p, imp) ->
                   let (b', a', w', env, te, pat) = pat_as_arg_with_env allow_wc_dependence env p in
                   let arg = match te with
                    | Inl t -> if imp then itarg t else targ t
                    | Inr e -> if imp then ivarg e else varg e in
                    (b'::b, a'::a, w'::w, env, arg::args, (pat, imp)::pats))  ([], [], [], env, [], []) in
               let e = mk_Exp_meta(Meta_desugared(mk_Exp_app'(Util.fvar (Some Data_ctor) fv.v fv.p, args |> List.rev) None p.p, Data_app)) in
               (List.rev b |> List.flatten,
                List.rev a |> List.flatten,
                List.rev w |> List.flatten,
                env,
                Inr e,
                {p with v=Pat_cons(fv, q, List.rev pats)})

           | Pat_disj _ -> failwith "impossible" in
    let rec elaborate_pat env p = //Adds missing implicit patterns to constructor patterns
        match p.v with
           | Pat_cons(fv, q, pats) ->
               let pats = List.map (fun (p, imp) -> elaborate_pat env p, imp) pats in
               let t = Tc.Env.lookup_datacon env fv.v in
               let pats = match Util.function_formals t with
                    | None ->
                        begin match pats with
                            | [] -> []
                            | _ -> raise (Error("Too many pattern arguments", range_of_lid fv.v))
                        end
                    | Some(f, _) ->
                      let rec aux formals pats = match formals, pats with
                        | [], [] -> []
                        | [], _::_ -> raise (Error("Too many pattern arguments", range_of_lid fv.v))
                        | _::_, [] -> //fill the rest with dot patterns (if allowed), if all the remaining formals are implicit
                          formals |> List.map (fun f -> match f with
                            | Inl t, imp -> //type arguments are implicit by default
                              let a = Util.bvd_to_bvar_s (Util.new_bvd None) kun in
                              if allow_implicits
                              then withinfo (Pat_dot_typ (a, tun)) None  (Syntax.range_of_lid fv.v), as_imp imp
                              else withinfo (Pat_tvar a) None (Syntax.range_of_lid fv.v), as_imp imp

                            | Inr _, Some Implicit ->
                              let a = Util.gen_bvar tun in
                              withinfo (Pat_var a) None (*Inr tun*) (Syntax.range_of_lid fv.v), true

                            | _ -> raise (Error(Util.format1 "Insufficient pattern arguments (%s)" (Print.pat_to_string p), range_of_lid fv.v)))

                        | f::formals', (p, p_imp)::pats' ->
                            begin match f, p.v with
                                | (Inl _, imp), Pat_tvar _
                                | (Inl _, imp), Pat_twild _ -> (p, as_imp imp)::aux formals' pats'
                                | (Inl _, imp), Pat_dot_typ _ when allow_implicits -> (p, as_imp imp)::aux formals' pats'
                                | (Inl _, imp), _ ->
                                    let a = Util.bvd_to_bvar_s (Util.new_bvd None) kun in
                                    let p1 =
                                        if allow_implicits
                                        then withinfo (Pat_dot_typ (a, tun)) None (Syntax.range_of_lid fv.v)
                                        else withinfo (Pat_tvar a) None (Syntax.range_of_lid fv.v) in
                                    let pats' = match p.v with
                                        | Pat_dot_typ _ -> pats'
                                        | _ -> pats in
                                    (p1, as_imp imp)::aux formals' pats'
                                | (Inr _, Some Implicit), _ when p_imp ->
                                    (p, true)::aux formals' pats'
                                | (Inr _, Some Implicit), _ ->
                                    let a = Util.gen_bvar tun in
                                    let p = withinfo (Pat_var a) None (Syntax.range_of_lid fv.v) in
                                    (p, true)::aux formals' pats
                                | (Inr _, imp), _ ->
                                  (p, as_imp imp)::aux formals' pats'
                            end in
                      aux f pats in
               {p with v=Pat_cons(fv, q, pats)}

        | _ -> p in

    let one_pat allow_wc_dependence env p =
        let p = elaborate_pat env p in

//        let b, a, w, env = pat_env allow_wc_dependence env p in
//        let arg, p, uvars = pat_as_arg env p in

//        let b, a, w, env = pat_env allow_wc_dependence env p in
        let b, a, w, env, arg, p = pat_as_arg_with_env allow_wc_dependence env p in

        match b |> Util.find_dup pvar_eq with
            | Some (Env.Binding_var(x, _)) -> raise (Error(Tc.Errors.nonlinear_pattern_variable (Inr x), p.p))
            | Some (Env.Binding_typ(x, _)) -> raise (Error(Tc.Errors.nonlinear_pattern_variable (Inl x), p.p))
            | _ -> b, a, w, arg, p in

   let as_arg = function
    | Inl t -> failwith "Impossible"
    | Inr e -> varg e in
   let top_level_pat_as_args env (p:pat) : (list<Env.binding>                    (* pattern bound variables *)
                                            * list<arg>                          (* pattern sub-terms *)
                                            * pat)  =                            (* decorated pattern *)
        match p.v with
           | Pat_disj [] -> failwith "impossible"

           | Pat_disj (q::pats) ->
              let b, a, _, te, q = one_pat false env q in //in disjunctive patterns, the wildcards are not accessible even for typing
              let w, args, pats = List.fold_right (fun p (w, args, pats) ->
                  let b', a', w', arg, p = one_pat false env p in
                  if not (Util.multiset_equiv pvar_eq a a')
                  then raise (Error(Tc.Errors.disjunctive_pattern_vars (vars_of_bindings a) (vars_of_bindings a'), Tc.Env.get_range env))
                  else (w'@w, as_arg arg::args, p::pats))
                  pats ([], [], []) in
              b@w, as_arg te::args, {p with v=Pat_disj(q::pats)}

           | _ ->
             let b, _, _, arg, p = one_pat true env p in //in single pattersn, the wildcards are available, at least for typing
             b, [as_arg arg], p in

    let b, args, p = top_level_pat_as_args env p in
    let exps = args |> List.map (function
        | Inl _, _ -> failwith "Impossible: top-level pattern must be an expression"
        | Inr e, _ -> e) in
    b, exps, p

let decorate_pattern env p exps =
    let qq = p in
    let rec aux p e : pat  =
        let pkg q t = withinfo q (Some <| Inr t) p.p in
        let e = Util.unmeta_exp e in
        match p.v, e.n with
            | Pat_constant _, Exp_constant _ -> pkg p.v (force_tk e)

            | Pat_var x, Exp_bvar y ->
              if Util.bvar_eq x y |> not
              then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd x.v) (Print.strBvd y.v));
              if Env.debug env <| Options.Other "Pat"
              then Util.print2 "Pattern variable %s introduced at type %s\n" (Print.strBvd x.v) (Normalize.typ_norm_to_string env y.sort);
              let s = Normalize.norm_typ [Normalize.Beta] env y.sort in
              let x = {x with sort=s} in
              pkg (Pat_var x) (force_tk e)

            | Pat_wild x, Exp_bvar y ->
              if Util.bvar_eq x y |> not
              then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd x.v) (Print.strBvd y.v));
              let x = {x with sort=force_tk e} in
              pkg (Pat_wild x) x.sort

            | Pat_dot_term(x, _), _ ->
              let x = {x with sort=force_tk e} in
              pkg (Pat_dot_term(x, e)) x.sort

            | Pat_cons(fv, q, []), Exp_fvar (fv',_) ->
              if Util.fvar_eq fv fv' |> not
              then failwith (Util.format2 "Expected pattern constructor %s; got %s" fv.v.str fv'.v.str);
              pkg (Pat_cons(fv', q, [])) fv'.sort

            | Pat_cons(fv, q, argpats), Exp_app({n=Exp_fvar(fv', _)}, args) ->
              if Util.fvar_eq fv fv' |> not
              then failwith (Util.format2 "Expected pattern constructor %s; got %s" fv.v.str fv'.v.str);
              let fv = fv' in

              let rec match_args matched_pats args argpats = match args, argpats with
                | [], [] -> pkg (Pat_cons(fv, q, List.rev matched_pats)) (force_tk e)
                | arg::args, (argpat, _)::argpats ->
                  begin match arg, argpat.v with
                        | (Inl t, Some Implicit), Pat_dot_typ _ -> (* implicit type argument *)
                          let x = Util.gen_bvar_p p.p (force_tk t) in
                          let q = withinfo (Pat_dot_typ(x, t)) (Some<| Inl x.sort) p.p in
                          match_args ((q, true)::matched_pats) args argpats

                        | (Inr e, Some Implicit), Pat_dot_term _ -> (* implicit value argument *)
                          let x = Util.gen_bvar_p p.p (force_tk e) in
                          let q = withinfo (Pat_dot_term(x, e)) (Some <| Inr x.sort) p.p in
                          match_args ((q, true)::matched_pats) args argpats

                        | (Inl t, imp), _ ->
                          let pat = aux_t argpat t in
                          match_args ((pat, as_imp imp)::matched_pats) args argpats

                        | (Inr e, imp), _ ->
                          let pat = aux argpat e, as_imp imp in
                          match_args (pat::matched_pats) args argpats
                 end

                | _ -> failwith (Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" (Print.pat_to_string p) (Print.exp_to_string e)) in

              match_args [] args argpats

           | _ -> failwith (Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Range.string_of_range qq.p) (Print.pat_to_string qq)
                    (exps |> List.map Print.exp_to_string |> String.concat "\n\t"))

    and aux_t p t0 =
       let pkg q k = withinfo q (Some <| Inl k) p.p in
       let t = Util.compress_typ t0 in
       match p.v, t.n with
         | Pat_twild a, Typ_btvar b ->
            if Util.bvar_eq a b |> not
            then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd a.v) (Print.strBvd b.v));
            pkg (Pat_twild b) b.sort

         | Pat_tvar a, Typ_btvar b ->
            if Util.bvar_eq a b |> not
            then failwith (Util.format2 "Expected pattern variable %s; got %s" (Print.strBvd a.v) (Print.strBvd b.v));
            pkg (Pat_tvar b) b.sort

         | Pat_dot_typ(a, _), _ ->
            let k0 = force_tk t0 in
            let a = {a with sort=k0} in
            pkg (Pat_dot_typ(a, t)) a.sort

         | _ -> failwith (Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Range.string_of_range p.p) (Print.pat_to_string p) (Print.typ_to_string t)) in

    match p.v, exps with
        | Pat_disj ps, _ when (List.length ps = List.length exps) ->
          let ps = List.map2 aux ps exps in
          withinfo (Pat_disj ps) (Some <| Inr tun) p.p

        | _, [e] ->
          aux p e

        | _ -> failwith "Unexpected number of patterns"

 let rec decorated_pattern_as_exp (pat:pat) : list<either_var> * exp =
    let topt = match pat.sort with
        | (Some (Inr t)) -> Some t
        | None -> None
        | _ -> failwith "top-level pattern should be decorated with a type" in

    let pkg f = f topt pat.p in

    let pat_as_arg (p, i) =
        let vars, te = decorated_pattern_as_either p in
        vars, (te, as_implicit i) in

    match pat.v with
        | Pat_disj _ -> failwith "Impossible" (* these are only on top-level patterns *)

        | Pat_constant c ->
            [], mk_Exp_constant c |> pkg

        | Pat_wild x
        | Pat_var x  ->
            [Inr x], mk_Exp_bvar x |> pkg

        | Pat_cons(fv, q, pats) ->
            let vars, args = pats |> List.map pat_as_arg |> List.unzip in
            let vars = List.flatten vars in
            vars,  mk_Exp_app'(mk_Exp_fvar(fv, q) (Some fv.sort) fv.p, args) |> pkg

        | Pat_dot_term(x, e) ->
            [], e

        | Pat_twild _
        | Pat_tvar _
        | Pat_dot_typ _ -> failwith "Impossible: expected a term pattern"

and decorated_pattern_as_typ (p:pat) : list<either_var> * typ = match p.v with
    | Pat_twild a
    | Pat_tvar a ->
        [Inl a], mk_Typ_btvar a (Some a.sort) p.p

    | Pat_dot_typ(a, t) ->
        [], t

    | _ -> failwith "Expected a type pattern"

and decorated_pattern_as_either (p:pat) =
    match p.v with
        | Pat_twild _
        | Pat_tvar _
        | Pat_dot_typ _ ->
            let vars, t = decorated_pattern_as_typ p in
            vars, Inl t

        | _ ->
            let vars, e = decorated_pattern_as_exp p in
            vars, Inr e


//DTuple u1 (\_:u1. u2) (\_:u1 u2. u3) ...
// where ui:Type
let mk_basic_dtuple_type env n =
  let r = Tc.Env.get_range env in
  let l = Util.mk_dtuple_lid n r in
  let k = Tc.Env.lookup_typ_lid env l in
  let t = Util.ftv l k in
  let vars = Env.binders env in
  match k.n with
    | Kind_arrow(bs, {n=Kind_type}) ->
      let args, _ = bs |> List.fold_left (fun (out, subst) (b, _) -> match b with
        | Inr _ -> failwith "impossible"
        | Inl a ->
          let k = Util.subst_kind subst a.sort in
          let arg = match k.n with
            | Kind_type ->
              Rel.new_tvar r vars ktype |> fst
            | Kind_arrow(bs, k) ->
              mk_Typ_lam(bs, Rel.new_tvar r vars ktype |> fst) (Some k) r
            | _ -> failwith "Impossible" in
          let subst = (Inl(a.v, arg))::subst in
          (targ arg::out, subst)) ([], []) in
      mk_Typ_app(t, List.rev args) (Some ktype) r

    | _ -> failwith "Impossible"

let extract_lb_annotation env t e = match t.n with
  | Typ_unknown ->
    let r = Env.get_range env in
    let mk_t_binder scope a = match a.sort.n with
        | Kind_unknown ->
          let k =  Rel.new_kvar e.pos scope |> fst in
          {a with sort=k}, false
        | _ -> a, true in

    let mk_v_binder scope x = match x.sort.n with
        | Typ_unknown ->
          let t = Rel.new_tvar e.pos scope ktype |> fst in
          begin match Syntax.null_v_binder t with
            | Inr x, _ -> x, false
            | _ -> failwith "impos"
          end

        | _ ->
          begin match Syntax.null_v_binder x.sort with
            | Inr x, _ -> x, true
            | _ -> failwith "impos"
          end in


    let rec aux vars e : exp * typ * bool = match e.n with
      | Exp_meta(Meta_desugared(e, _)) -> aux vars e
      | Exp_ascribed(e, t, _) -> e, t, true

      | Exp_abs(bs, body) ->
        let scope, bs, check = bs |> List.fold_left (fun (scope, bs, check) b -> match fst b with
            | Inl a ->
              let tb, c = mk_t_binder scope a in
              let b = (Inl tb, snd b) in
              let bs = bs@[b] in
              let scope = scope@[b] in
              scope, bs, c || check
            | Inr x ->
              let vb, c = mk_v_binder scope x in
              let b = (Inr vb, snd b) in //Note, the default annotation for a let-rec bound function is non-dependent on the values; important for efficiency
              scope, bs@[b], c || check) (vars,[],false) in

        let body, res, check_res = aux scope body in
        let c = Util.ml_comp res r in
        let t = mk_Typ_fun(bs, c) (Some ktype) e.pos in
        if debug env Options.High then Util.print2 "(%s) Using type %s\n" (Range.string_of_range r) (Print.typ_to_string t);
        let e = mk_Exp_abs(bs, body) None e.pos in
        e, t, check_res || check

      | _ -> e, Rel.new_tvar r vars ktype |> fst, false in

     aux (Env.t_binders env)  e

  | _ -> e, t, false

(*********************************************************************************************)
(* Utils related to monadic computations *)
(*********************************************************************************************)
type lcomp_with_binder = option<Env.binding> * lcomp

let destruct_comp c : (typ * typ * typ) =
  let wp, wlp = match c.effect_args with
    | [(Inl wp, _); (Inl wlp, _)] -> wp, wlp
    | _ -> failwith (Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.effect_name.str
      (List.map Print.arg_to_string c.effect_args |> String.concat ", ")) in
  c.result_typ, wp, wlp

let lift_comp c m lift =
  let _, wp, wlp = destruct_comp c in
  {effect_name=m;
   result_typ=c.result_typ;
   effect_args=[targ (lift c.result_typ wp); targ (lift c.result_typ wlp)];
   flags=[]}

let norm_eff_name =
   let cache = Util.smap_create 20 in
   fun env (l:lident) ->
       let rec find l =
           match Tc.Env.lookup_effect_abbrev env l with
            | None -> None
            | Some (_, c) ->
                let l = (Util.comp_to_comp_typ c).effect_name in
                match find l with
                    | None -> Some l
                    | Some l' -> Some l' in
       let res = match Util.smap_try_find cache l.str with
            | Some l -> l
            | None ->
              begin match find l with
                        | None -> l
                        | Some m -> Util.smap_add cache l.str m;
                                    m
              end in
       res


let join_effects env l1 l2 =
  let m, _, _ = Tc.Env.join env (norm_eff_name env l1) (norm_eff_name env l2) in
  m
let join_lcomp env c1 c2 =
  if lid_equals c1.eff_name Const.effect_Tot_lid
  && lid_equals c2.eff_name Const.effect_Tot_lid
  then Const.effect_Tot_lid
  else join_effects env c1.eff_name c2.eff_name

let lift_and_destruct env c1 c2 =
  let c1 = Tc.Normalize.weak_norm_comp env c1 in
  let c2 = Tc.Normalize.weak_norm_comp env c2 in
  let m, lift1, lift2 = Tc.Env.join env c1.effect_name c2.effect_name in
  let m1 = lift_comp c1 m lift1 in
  let m2 = lift_comp c2 m lift2 in
  let md = Tc.Env.get_effect_decl env m in
  let a, kwp = Tc.Env.wp_signature env md.mname in
  (md, a, kwp), (destruct_comp m1), destruct_comp m2

let is_pure_effect env l =
  let l = norm_eff_name env l in
  lid_equals l Const.effect_PURE_lid

let is_pure_or_ghost_effect env l =
  let l = norm_eff_name env l in
  lid_equals l Const.effect_PURE_lid
  || lid_equals l Const.effect_GHOST_lid

let mk_comp md result wp wlp flags =
  mk_Comp ({effect_name=md.mname;
             result_typ=result;
             effect_args=[targ wp; targ wlp];
             flags=flags})

let lcomp_of_comp c0 =
    let c = Util.comp_to_comp_typ c0 in
    {eff_name = c.effect_name;
     res_typ = c.result_typ;
     cflags = c.flags;
     comp = fun() -> c0}

let subst_lcomp subst lc =
    {lc with res_typ=Util.subst_typ subst lc.res_typ;
             comp=fun () -> Util.subst_comp subst (lc.comp())}

let is_function t = match (compress_typ t).n with
    | Typ_fun _ -> true
    | _ -> false

let return_value env t v =
//  if is_function t then failwith (Util.format1 "(%s): Returning a function!" (Range.string_of_range (Env.get_range env)));
  let c = match Tc.Env.effect_decl_opt env Const.effect_PURE_lid with
    | None -> mk_Total t
    | Some m ->
       let a, kwp = Env.wp_signature env Const.effect_PURE_lid in
       let k = Util.subst_kind [Inl(a.v, t)] kwp in
       let wp = Tc.Normalize.norm_typ [Beta] env <| mk_Typ_app(m.ret, [targ t; varg v]) (Some k) v.pos in
       let wlp = wp in
       mk_comp m t wp wlp [RETURN] in
  if debug env Options.High
  then Util.print3 "(%s) returning %s at comp type %s\n" (Range.string_of_range v.pos)  (Print.exp_to_string v) (Normalize.comp_typ_norm_to_string env c);
  c

let bind env e1opt (lc1:lcomp) ((b, lc2):lcomp_with_binder) : lcomp =
  if debug env Options.Extreme
  then
    (let bstr = match b with
      | None -> "none"
      | Some (Env.Binding_var(x, _)) -> Print.strBvd x
      | _ -> "??" in
    Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" (Print.lcomp_typ_to_string lc1) bstr (Print.lcomp_typ_to_string lc2));
  let bind_it () =
      let c1 = lc1.comp () in
      let c2 = lc2.comp () in
      let try_simplify () =
        let aux () =
            if Util.is_trivial_wp c1
            then match b with
                    | None -> Some c2
                    | Some (Env.Binding_lid _) -> Some c2
                    | Some (Env.Binding_var _) ->
                        if Util.is_ml_comp c2 //|| not (Util.is_free [Inr x] (Util.freevars_comp c2))
                        then Some c2
                        else None
                    | _ -> None
            else if Util.is_ml_comp c1 && Util.is_ml_comp c2
            then Some c2
            else None in
        match e1opt, b with
            | Some e, Some (Env.Binding_var(x,_)) ->
                if Util.is_tot_or_gtot_comp c1 && not (Syntax.is_null_bvd x)
                then Some <| Util.subst_comp [Inr(x, e)] c2
                else aux ()
            | _ -> aux () in
      match try_simplify () with
        | Some c ->
          if Tc.Env.debug env <| Options.Other "bind"
          then Util.print4 "bind (%s) %s and %s simplified to %s\n"
              (match b with
                 | None -> "None"
                 | Some (Env.Binding_var(x, _)) -> Print.strBvd x
                 | Some (Env.Binding_lid(l, _)) -> Print.sli l
                 | _ -> "Something else")
            (Print.comp_typ_to_string c1) (Print.comp_typ_to_string c2) (Print.comp_typ_to_string c);
          c
        | None ->
          let (md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2) = lift_and_destruct env c1 c2 in
          let bs = match b with
            | None -> [null_v_binder t1]
            | Some (Env.Binding_var(x, t1)) -> [v_binder (bvd_to_bvar_s x t1)]
            | Some (Env.Binding_lid(l, t1)) -> [null_v_binder t1]
            | _ -> failwith "Unexpected type-variable binding" in
          let mk_lam wp = mk_Typ_lam(bs, wp) None wp.pos in
          let wp_args = [targ t1; targ t2; targ wp1; targ wlp1; targ (mk_lam wp2); targ (mk_lam wlp2)] in
          let wlp_args = [targ t1; targ t2; targ wlp1; targ (mk_lam wlp2)] in
          let k = Util.subst_kind [Inl(a.v, t2)] kwp in
          let wp = mk_Typ_app(md.bind_wp, wp_args) None t2.pos in
          let wlp = mk_Typ_app(md.bind_wlp, wlp_args) None t2.pos in
          let c = mk_comp md t2 wp wlp [] in
          c in
    {eff_name=join_lcomp env lc1 lc2;
     res_typ=lc2.res_typ;
     cflags=[];
     comp=bind_it}

let lift_formula env t mk_wp mk_wlp f =
  let md_pure = Tc.Env.get_effect_decl env Const.effect_PURE_lid in
  let a, kwp = Tc.Env.wp_signature env md_pure.mname in
  let k = Util.subst_kind [Inl(a.v, t)] kwp in
  let wp = mk_Typ_app(mk_wp, [targ t; targ f]) (Some k) f.pos in
  let wlp = mk_Typ_app(mk_wlp, [targ t; targ f]) (Some k) f.pos in
  mk_comp md_pure Recheck.t_unit wp wlp []

let unlabel t = mk_Typ_meta(Meta_refresh_label(t, None, t.pos))

let refresh_comp_label env (b:bool) lc =
    let refresh () =
        let c = lc.comp () in
        if Util.is_ml_comp c then c
        else match c.n with
        | Total _ -> c
        | Comp ct ->
          if Tc.Env.debug env Options.Low
          then (Util.print1 "Refreshing label at %s\n" (Range.string_of_range <| Env.get_range env));
          let c' = Tc.Normalize.weak_norm_comp env c in
          if not <| lid_equals ct.effect_name c'.effect_name && Tc.Env.debug env Options.Low
          then Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" (Print.comp_typ_to_string c) (Print.comp_typ_to_string <| mk_Comp c');
          let t, wp, wlp = destruct_comp c' in
          let wp = mk_Typ_meta(Meta_refresh_label(wp, Some b, Env.get_range env)) in
          let wlp = mk_Typ_meta(Meta_refresh_label(wlp, Some b, Env.get_range env)) in
          Syntax.mk_Comp ({c' with effect_args=[targ wp; targ wlp]; flags=c'.flags}) in
    {lc with comp=refresh}

let label reason r f =
    Syntax.mk_Typ_meta(Meta_labeled(f, reason, r, true))
let label_opt env reason r f = match reason with
    | None -> f
    | Some reason ->
        if not <| Options.should_verify env.curmodule.str
        then f
        else label (reason()) r f

let label_guard reason r g = match g with
    | Rel.Trivial -> g
    | Rel.NonTrivial f -> Rel.NonTrivial (label reason r f)

let weaken_guard g1 g2 = match g1, g2 with
    | Rel.NonTrivial f1, Rel.NonTrivial f2 ->
      let g = (Util.mk_imp f1 f2) in
      Rel.NonTrivial g
    | _ -> g2

let weaken_precondition env lc (f:guard_formula) : lcomp =
  let weaken () =
      let c = lc.comp () in
      match f with
      | Rel.Trivial -> c
      | Rel.NonTrivial f ->
        if Util.is_ml_comp c
        then c
        else let c = Tc.Normalize.weak_norm_comp env c in
             let res_t, wp, wlp = destruct_comp c in
             let md = Tc.Env.get_effect_decl env c.effect_name in
             let wp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wp]) None wp.pos in
             let wlp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wlp]) None wlp.pos in
             mk_comp md res_t wp wlp c.flags in
  {lc with comp=weaken}

let strengthen_precondition (reason:option<(unit -> string)>) env (e:exp) (lc:lcomp) (g0:guard_t) : lcomp * guard_t =
    if Rel.is_trivial g0 then lc, g0
    else
        let flags = lc.cflags |> List.collect (function RETURN | PARTIAL_RETURN -> [PARTIAL_RETURN] | _ -> []) in
        let strengthen () =
            let c = lc.comp () in
            let g0 = Rel.simplify_guard env g0 in
            match guard_form g0 with
                | Rel.Trivial -> c
                | Rel.NonTrivial f ->
                let c =
                    if Util.is_pure_or_ghost_comp c
                    && not (is_function (Util.comp_result c))
                    && not (Util.is_partial_return c)
                    then let x = Util.gen_bvar (Util.comp_result c) in
                         let xret = return_value env x.sort (Util.bvar_to_exp x) in
                         let xbinding = Env.Binding_var(x.v, x.sort) in
                         let lc = bind env (Some e) (lcomp_of_comp c) (Some xbinding, lcomp_of_comp xret) in
                         lc.comp()
                    else c in
                let c = Tc.Normalize.weak_norm_comp env c in
                let res_t, wp, wlp = destruct_comp c in
                let md = Tc.Env.get_effect_decl env c.effect_name in
                let wp = mk_Typ_app(md.assert_p, [targ res_t; targ <| label_opt env reason (Env.get_range env) f; targ wp]) None wp.pos in
                let wlp = mk_Typ_app(md.assume_p, [targ res_t; targ f; targ wlp]) None wlp.pos in
                let c2 = mk_comp md res_t wp wlp flags in
                c2 in
       {lc with eff_name=norm_eff_name env lc.eff_name;
                cflags=(if Util.is_pure_lcomp lc && not <| Util.is_function_typ lc.res_typ then flags else []);
                comp=strengthen},
       {g0 with Rel.guard_f=Rel.Trivial}

let add_equality_to_post_condition env (comp:comp) (res_t:typ) =
    let md_pure = Tc.Env.get_effect_decl env Const.effect_PURE_lid in
    let x = Util.gen_bvar res_t in
    let y = Util.gen_bvar res_t in
    let xexp, yexp = Util.bvar_to_exp x, Util.bvar_to_exp y in
    let yret = mk_Typ_app(md_pure.ret, [targ res_t; varg yexp]) None res_t.pos in
    let x_eq_y_yret = mk_Typ_app(md_pure.assume_p, [targ res_t; targ <| Util.mk_eq res_t res_t xexp yexp; targ <| yret]) None res_t.pos in
    let forall_y_x_eq_y_yret = mk_Typ_app(md_pure.close_wp, [targ res_t; targ res_t; targ <| mk_Typ_lam([v_binder y], x_eq_y_yret) None res_t.pos]) None res_t.pos in
    let lc2 = mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret [RETURN] in
    let lc = bind env None (lcomp_of_comp comp) (Some (Env.Binding_var(x.v, x.sort)), lcomp_of_comp lc2) in
    lc.comp()

let ite env (guard:formula) lcomp_then lcomp_else =
  let comp () =
      let (md, _, _), (res_t, wp_then, wlp_then), (_, wp_else, wlp_else) = lift_and_destruct env (lcomp_then.comp()) (lcomp_else.comp()) in
      let ifthenelse md res_t g wp_t wp_e = mk_Typ_app(md.if_then_else, [targ res_t; targ g; targ wp_t; targ wp_e]) None (Range.union_ranges wp_t.pos wp_e.pos) in
      let wp = ifthenelse md res_t guard wp_then wp_else in
      let wlp = ifthenelse md res_t guard wlp_then wlp_else in
      if !Options.split_cases > 0
      then let comp = mk_comp md res_t wp wlp [] in
           add_equality_to_post_condition env comp res_t
      else let wp = mk_Typ_app(md.ite_wp, [targ res_t; targ wlp; targ wp]) None wp.pos in
           let wlp = mk_Typ_app(md.ite_wlp, [targ res_t; targ wlp]) None wlp.pos in
           mk_comp md res_t wp wlp [] in
    {eff_name=join_effects env lcomp_then.eff_name lcomp_else.eff_name;
     res_typ=lcomp_then.res_typ;
     cflags=[];
     comp=comp}

let bind_cases env (res_t:typ) (lcases:list<(formula * lcomp)>) : lcomp =
    let eff = match lcases with
        | [] -> failwith "Empty cases!"
        | hd::tl -> List.fold_left (fun eff (_, lc) -> join_effects env eff lc.eff_name) (snd hd).eff_name tl in
    let bind_cases () =
        let ifthenelse md res_t g wp_t wp_e = mk_Typ_app(md.if_then_else, [targ res_t; targ g; targ wp_t; targ wp_e]) None (Range.union_ranges wp_t.pos wp_e.pos) in
        let default_case =
            let post_k = mk_Kind_arrow([null_v_binder res_t], ktype) res_t.pos in
            let kwp = mk_Kind_arrow([null_t_binder post_k], ktype) res_t.pos in
            let post = Util.bvd_to_bvar_s (Util.new_bvd None) post_k in
            let wp = mk_Typ_lam([t_binder post], label Errors.exhaustiveness_check (Env.get_range env) <| Util.ftv Const.false_lid ktype) (Some kwp) res_t.pos in
            let wlp = mk_Typ_lam([t_binder post], Util.ftv Const.true_lid ktype) (Some kwp) res_t.pos in
            let md = Tc.Env.get_effect_decl env Const.effect_PURE_lid in
            mk_comp md res_t wp wlp [] in
        let comp = List.fold_right (fun (g, cthen) celse ->
            let (md, _, _), (_, wp_then, wlp_then), (_, wp_else, wlp_else) = lift_and_destruct env (cthen.comp()) celse in
            mk_comp md res_t (ifthenelse md res_t g wp_then wp_else) (ifthenelse md res_t g wlp_then wlp_else) []) lcases default_case in
        if !Options.split_cases > 0
        then add_equality_to_post_condition env comp res_t
        else let comp = comp_to_comp_typ comp in
             let md = Tc.Env.get_effect_decl env comp.effect_name in
             let _, wp, wlp = destruct_comp comp in
             let wp = mk_Typ_app(md.ite_wp, [targ res_t; targ wlp; targ wp]) None wp.pos in
             let wlp = mk_Typ_app(md.ite_wlp, [targ res_t; targ wlp]) None wlp.pos in
             mk_comp md res_t wp wlp [] in
    {eff_name=eff;
     res_typ=res_t;
     cflags=[];
     comp=bind_cases}

let close_comp env bindings (lc:lcomp) =
  let close () =
      let c = lc.comp() in
      if Util.is_ml_comp c then c
      else
        let close_wp md res_t bindings wp0 =
          List.fold_right (fun b wp -> match b with
            | Env.Binding_var(x, t) ->
              let bs = [v_binder <| bvd_to_bvar_s x t] in
              let wp = mk_Typ_lam(bs, wp) None wp.pos in
              mk_Typ_app(md.close_wp, [targ res_t; targ t; targ wp]) None wp0.pos

            | Env.Binding_typ(a, k) -> //A bit sloppy here: close_wp_t is only for Type; overloading it here for all kinds
              let bs = [t_binder <| bvd_to_bvar_s a k] in
              let wp = mk_Typ_lam(bs, wp) None wp.pos in
              mk_Typ_app(md.close_wp_t, [targ res_t; targ wp]) None wp0.pos

            | Env.Binding_lid(l, t) ->
              (* TODO: replace every occurrence of l in wp with a fresh bound var, abstract over the bound var and then close it.
                       Except that it is highly unlikely for the wp to actually contain such a free occurrence of l *)
              wp
            | Env.Binding_sig s -> failwith "impos") bindings wp0 in //(Printf.sprintf "NYI close_comp_typ with binding %A" b))
        let c = Tc.Normalize.weak_norm_comp env c in
        let t, wp, wlp = destruct_comp c in
        let md = Tc.Env.get_effect_decl env c.effect_name in
        let wp = close_wp md c.result_typ bindings wp in
        let wlp = close_wp md c.result_typ bindings wlp in
        mk_comp md c.result_typ wp wlp c.flags in
  {lc with comp=close}

let maybe_assume_result_eq_pure_term env (e:exp) (lc:lcomp) : lcomp =
  let refine () =
      let c = lc.comp() in
      if not (is_pure_or_ghost_effect env lc.eff_name)
      then c
      else if Util.is_partial_return c then c
      else
           let c = Tc.Normalize.weak_norm_comp env c in
           let t = c.result_typ in
           let c = mk_Comp c in
           let x = Util.new_bvd None in
           let xexp = Util.bvd_to_exp x t in
           let ret = lcomp_of_comp <| return_value env t xexp in
           let eq_ret = weaken_precondition env ret (Rel.NonTrivial (Util.mk_eq t t xexp e)) in
           comp_set_flags ((bind env None (lcomp_of_comp c) (Some (Env.Binding_var(x, t)), eq_ret)).comp()) (PARTIAL_RETURN::comp_flags c) in
  let flags =
    if not (Util.is_function_typ lc.res_typ)
    && Util.is_pure_or_ghost_lcomp lc
    && not (Util.is_lcomp_partial_return lc)
    then PARTIAL_RETURN::lc.cflags
    else lc.cflags in
  {lc with comp=refine; cflags=flags}

let check_comp env (e:exp) (c:comp) (c':comp) : exp * comp * guard_t =
  //printfn "Checking sub_comp:\n%s has type %s\n\t<:\n%s\n" (Print.exp_to_string e) (Print.comp_typ_to_string c) (Print.comp_typ_to_string c');
  match Tc.Rel.sub_comp env c c' with
    | None -> raise (Error(Tc.Errors.computed_computation_type_does_not_match_annotation env e c c', Tc.Env.get_range env))
    | Some g -> e, c', g

let maybe_instantiate_typ env t k =
  let k = compress_kind k in
  if not (env.instantiate_targs && env.instantiate_vargs) then t, k, [] else
  match k.n with
    | Kind_arrow(bs, k) ->
      let rec aux subst = function
        | (Inl a, Some Implicit)::rest ->
          let k = Util.subst_kind subst a.sort in
          let t, u = new_implicit_tvar env k in
          let subst = (Inl(a.v, t))::subst in
          let args, bs, subst, us = aux subst rest in
          (Inl t, Some Implicit)::args, bs, subst, Inl u::us

        | (Inr x, Some Implicit)::rest ->
          let t = Util.subst_typ subst x.sort in
          let v, u = new_implicit_evar env t in
          let subst = (Inr(x.v, v))::subst in
          let args, bs, subst, us = aux subst rest in
          (Inr v, Some Implicit)::args, bs, subst, Inr u::us

        | bs -> [], bs, subst, [] in
     let args, bs, subst, implicits = aux [] bs in
     let k = mk_Kind_arrow'(bs, k) t.pos in
     let k = Util.subst_kind subst k in
     Syntax.mk_Typ_app'(t, args) (Some k) t.pos, k, implicits

  | _ -> t, k, []

let maybe_instantiate env e t =
  let t = compress_typ t in
  if not (env.instantiate_targs && env.instantiate_vargs) then e, t, [] else
  match t.n with
    | Typ_fun(bs, c) ->
      let rec aux subst = function
        | (Inl a, _)::rest ->
          let k = Util.subst_kind subst a.sort in
          let t, u = new_implicit_tvar env k in
          let subst = (Inl(a.v, t))::subst in
          let args, bs, subst, us = aux subst rest in
          (Inl t, Some Implicit)::args, bs, subst, Inl u::us

        | (Inr x, Some Implicit)::rest ->
          let t = Util.subst_typ subst x.sort in
          let v, u = new_implicit_evar env t in
          let subst = (Inr(x.v, v))::subst in
          let args, bs, subst, us = aux subst rest in
          (Inr v, Some Implicit)::args, bs, subst, Inr u::us

        | bs -> [], bs, subst, [] in
     let args, bs, subst, implicits = aux [] bs in
     let mk_exp_app e args t = match args with
        | [] -> e
        | _ -> mk_Exp_app(e, args) t e.pos in
     begin match bs with
        | [] ->
            if Util.is_total_comp c
            then let t = Util.subst_typ subst (Util.comp_result c) in
                 mk_exp_app e args (Some t), t, implicits
            else e, t, [] //don't instantiate implicitly, if it has an effect
        | _ ->
            let t = mk_Typ_fun(bs, c) (Some ktype) e.pos |> Util.subst_typ subst in
            mk_exp_app e args (Some t), t, implicits
     end

  | _ -> e, t, []

let weaken_result_typ env (e:exp) (lc:lcomp) (t:typ) : exp * lcomp * guard_t =
  let gopt = if //env.is_pattern ||
                env.use_eq
             then Tc.Rel.try_teq env lc.res_typ t, false
             else Tc.Rel.try_subtype env lc.res_typ t, true in
  match gopt with
    | None, _ -> subtype_fail env lc.res_typ t
    | Some g, apply_guard ->
      let g = Rel.simplify_guard env g in
      match guard_form g with
        | Rel.Trivial ->
          let lc = {lc with res_typ = t} in
          (e, lc, g)
        | Rel.NonTrivial f ->
          let g = {g with Rel.guard_f=Rel.Trivial} in
          let strengthen () =
            let c = lc.comp() in

            if Tc.Env.debug env <| Options.Extreme
            then Util.print2 "Strengthening %s with guard %s\n" (Normalize.comp_typ_norm_to_string env c) (Normalize.typ_norm_to_string env f);

            let ct = Tc.Normalize.weak_norm_comp env c in
            let a, kwp = Env.wp_signature env Const.effect_PURE_lid in
            let k = Util.subst_kind [Inl(a.v, t)] kwp in
            let md = Tc.Env.get_effect_decl env ct.effect_name in
            let x = new_bvd None in
            let xexp = Util.bvd_to_exp x t in
            let wp = mk_Typ_app(md.ret, [targ t; varg xexp]) (Some k) xexp.pos in
            let cret = lcomp_of_comp <| mk_comp md t wp wp [RETURN] in
            let guard = if apply_guard then mk_Typ_app(f, [varg xexp]) (Some ktype) f.pos else f in
            let eq_ret, _trivial_so_ok_to_discard =
            strengthen_precondition (Some <| Errors.subtyping_failed env lc.res_typ t) (Env.set_range env e.pos) e cret
                                    (guard_of_guard_formula <| Rel.NonTrivial guard) in
//            let eq_ret =
//                if Util.is_pure_or_ghost_comp c
//                then weaken_precondition env eq_ret (Rel.NonTrivial (Util.mk_eq t t xexp e))
//                else eq_ret in
            let c = bind env (Some e) (lcomp_of_comp <| mk_Comp ct) (Some(Env.Binding_var(x, lc.res_typ)), eq_ret) in
            let c = c.comp () in
            if Tc.Env.debug env <| Options.Extreme
            then Util.print1 "Strengthened to %s\n" (Normalize.comp_typ_norm_to_string env c);
            c in
          let flags = lc.cflags |> List.collect (function RETURN | PARTIAL_RETURN -> [PARTIAL_RETURN] | _ -> []) in
          let lc = {lc with res_typ=t; comp=strengthen; cflags=flags; eff_name=norm_eff_name env lc.eff_name} in
          (e, lc, g)


(**************************************************************************************)
(* Generalizing types *)
(**************************************************************************************)
let check_uvars r t =
  let uvt = Util.uvars_in_typ t in
  if Util.set_count uvt.uvars_e +
     Util.set_count uvt.uvars_t +
     Util.set_count uvt.uvars_k > 0
  then
    let ue = List.map Print.uvar_e_to_string (Util.set_elements uvt.uvars_e) in
    let ut = List.map Print.uvar_t_to_string (Util.set_elements uvt.uvars_t) in
    let uk = List.map Print.uvar_k_to_string (Util.set_elements uvt.uvars_k) in
    let union = String.concat ","  (ue @ ut @ uk) in
    (* ignoring the hide_uvar_nums and print_implicits flags here *)
    let hide_uvar_nums_saved = !Options.hide_uvar_nums in
    let print_implicits_saved = !Options.print_implicits in
    Options.hide_uvar_nums := false;
    Options.print_implicits := true;
    Tc.Errors.report r
      (format2 "Unconstrained unification variables %s in type signature %s; \
       please add an annotation" union (Print.typ_to_string t));
    Options.hide_uvar_nums := hide_uvar_nums_saved;
    Options.print_implicits := print_implicits_saved

let gen verify env (ecs:list<(exp * comp)>) : option<list<(exp * comp)>> =
  if not <| (Util.for_all (fun (_, c) -> Util.is_pure_comp c) ecs) //No value restriction in F*---generalize the types of pure computations
  then None
  else
     let norm c =
        if debug env Options.Medium then Util.print1 "Normalizing before generalizing:\n\t %s" (Print.comp_typ_to_string c);
         let steps = [Eta;Delta;Beta;SNComp] in
         let c = if Options.should_verify env.curmodule.str
                 then Normalize.norm_comp steps env c
                 else Normalize.norm_comp [Beta; Delta] env c
         in
        if debug env Options.Medium then Util.print1 "Normalized to:\n\t %s" (Print.comp_typ_to_string c);
        c in
     let env_uvars = Env.uvars_in_env env in
     let gen_uvars uvs = Util.set_difference uvs env_uvars.uvars_t |> Util.set_elements in
     let should_gen t = match t.n with
        | Typ_fun(bs, _) ->
            if bs |> Util.for_some (function (Inl _, _) -> true | _ -> false)
            then false (* contains an explicit type abstraction; don't generalize further *)
            else true
        | _ -> true in

     let uvars = ecs |> List.map (fun (e, c) ->
          let t = Util.comp_result c |> Util.compress_typ in
          if not <| should_gen t
          then ([], e, c)
          else let c = norm c in
               let ct = comp_to_comp_typ c in
               let t = ct.result_typ in
               let uvt = Util.uvars_in_typ t in
               let uvs = gen_uvars uvt.uvars_t in
               if Options.should_verify env.curmodule.str
               && verify
               && not <| Util.is_total_comp c
               then begin
                  let _, wp, _ = destruct_comp ct in
                  let binder = [null_v_binder t] in
                  let post = mk_Typ_lam(binder, Util.ftv Const.true_lid ktype) (Some (mk_Kind_arrow(binder, ktype) t.pos)) t.pos in
                  let vc = Normalize.norm_typ [Delta; Beta] env (syn wp.pos (Some ktype) <| mk_Typ_app(wp, [targ post])) in
                  discharge_guard env (Rel.guard_of_guard_formula <| Rel.NonTrivial vc)
               end;
               uvs, e, c) in

     let ecs = uvars |> List.map (fun (uvs, e, c) ->
          let tvars = uvs |> List.map (fun (u, k) ->
            let a = match Unionfind.find u with
              | Fixed ({n=Typ_btvar a})
              | Fixed ({n=Typ_lam(_, {n=Typ_btvar a})}) -> Util.bvd_to_bvar_s a.v k
              | Fixed _ -> failwith "Unexpected instantiation of mutually recursive uvar"
              | _ ->
                  let a = Util.new_bvd (Some <| Tc.Env.get_range env) in
                  let t = Util.close_for_kind (Util.bvd_to_typ a ktype) k in
                  //let t = Util.bvd_to_typ a k in
                  unchecked_unify u t;
                  Util.bvd_to_bvar_s a ktype in
            Inl a, Some Implicit) in

          let t = match Util.comp_result c |> Util.function_formals with
            | Some (bs, cod) -> mk_Typ_fun(tvars@bs, cod) (Some ktype) c.pos
            | None -> match tvars with [] -> Util.comp_result c | _ -> mk_Typ_fun(tvars, c) (Some ktype) c.pos in

          let e = match tvars with
            | [] -> e
            | _ -> mk_Exp_abs'(tvars, e) (Some t) e.pos in
          e, mk_Total t) in
     Some ecs

let generalize verify env (lecs:list<(lbname*exp*comp)>) : (list<(lbname*exp*comp)>) =
  if debug env Options.Low then Util.print1 "Generalizing: %s" (List.map (fun (lb, _, _) -> Print.lbname_to_string lb) lecs |> String.concat ", ");
  match gen verify env (lecs |> List.map (fun (_, e, c) -> (e, c))) with
    | None -> lecs
    | Some ecs ->
      List.map2 (fun (l, _, _) (e, c) ->
         if debug env Options.Medium then Util.print3 "(%s) Generalized %s to %s" (Range.string_of_range e.pos) (Print.lbname_to_string l) (Print.typ_to_string (Util.comp_result c));
      (l, e, c)) lecs ecs

let unresolved u = match Unionfind.find u with
    | Uvar -> true
    | _ -> false

let check_top_level env g lc : (bool * comp) =
  let discharge g =
    try_discharge_guard env g;
    begin match g.implicits |> List.tryFind (function Inl u -> false | Inr (u, _) -> unresolved u) with
        | Some (Inr(_, r)) -> raise (Error("Unresolved implicit argument", r))
        | _ -> ()
    end;
    Util.is_pure_lcomp lc in
  let g = Rel.solve_deferred_constraints env g in
  if Util.is_total_lcomp lc
  then discharge g, lc.comp()
  else let c = lc.comp() in
       let steps = [Normalize.Beta; Normalize.SNComp; Normalize.DeltaComp] in
       let c = Tc.Normalize.norm_comp steps env c |> Util.comp_to_comp_typ in
       let md = Tc.Env.get_effect_decl env c.effect_name in
       let t, wp, _ = destruct_comp c in
       let vc = mk_Typ_app(md.trivial, [targ t; targ wp]) (Some ktype) (Env.get_range env) in
       let g = Rel.conj_guard g (Rel.guard_of_guard_formula <| Rel.NonTrivial vc) in
       discharge g, mk_Comp c

(* Having already seen_args to head (from right to left),
   compute the guard, if any, for the next argument,
   if head is a short-circuiting operator *)
let short_circuit_exp (head:exp) (seen_args:args) : option<(formula * exp)> =
    let short_bin_op_e f : args -> option<(formula * exp)> = function
        | [] -> (* no args seen yet *) None
        | [(Inr fst, _)] -> f fst |> Some
        | _ -> failwith "Unexpexted args to binary operator" in

    let table =
       let op_and_e e = Util.b2t e, Const.exp_false_bool in
       let op_or_e e  = Util.mk_neg (Util.b2t e), Const.exp_true_bool  in
       [(Const.op_And,  short_bin_op_e op_and_e);
        (Const.op_Or,   short_bin_op_e op_or_e)]  in

    match head.n with
        | Exp_fvar(fv, _) ->
          let lid = fv.v in
          begin match Util.find_map table (fun (x, mk) -> if lid_equals x lid then Some (mk seen_args) else None) with
            | None -> None
            | Some g -> g
          end
        | _ -> None


(* Having already seen_args to head (from right to left),
   compute the guard, if any, for the next argument,
   if head is a short-circuiting operator *)
let short_circuit_typ (head:either<typ,exp>) (seen_args:args) : guard_formula =
    let short_bin_op_t f : args -> guard_formula = function
        | [] -> (* no args seen yet *) Rel.Trivial
        | [(Inl fst, _)] -> f fst
        | _ -> failwith "Unexpexted args to binary operator" in

    let op_and_t t = unlabel t |> Rel.NonTrivial in
    let op_or_t t  =  unlabel t |> Util.mk_neg |> Rel.NonTrivial in
    let op_imp_t t = unlabel t |> Rel.NonTrivial in
    let short_op_ite : args -> guard_formula = function
        | [] -> Rel.Trivial
        | [(Inl guard, _)] -> Rel.NonTrivial guard
        | [_then;(Inl guard, _)] -> Util.mk_neg guard |> Rel.NonTrivial
        | _ -> failwith "Unexpected args to ITE" in
    let table =
        [(Const.and_lid, short_bin_op_t op_and_t);
         (Const.or_lid,  short_bin_op_t op_or_t);
         (Const.imp_lid, short_bin_op_t op_imp_t);
         (Const.ite_lid, short_op_ite);] in

     match head with
        | Inr head ->
          begin match short_circuit_exp head seen_args with
            | None -> Rel.Trivial
            | Some (g, _) -> Rel.NonTrivial g
          end
        | Inl ({n=Typ_const fv}) ->
          let lid = fv.v in
          begin match Util.find_map table (fun (x, mk) -> if lid_equals x lid then Some (mk seen_args) else None) with
            | None ->   Rel.Trivial
            | Some g -> g
          end
        | _ -> Rel.Trivial

let pure_or_ghost_pre_and_post env comp =
    let mk_post_type res_t ens =
        let x = Util.gen_bvar res_t in
        mk_Typ_refine(x, mk_Typ_app(ens, [varg (Util.bvar_to_exp x)]) (Some mk_Kind_type) res_t.pos) (Some mk_Kind_type) res_t.pos in
    let norm t = Normalize.norm_typ [Beta;Delta;Unlabel] env t in
    if Util.is_tot_or_gtot_comp comp
    then None, Util.comp_result comp
    else begin match comp.n with
            | Total _ -> failwith "Impossible"
            | Comp ct ->
              if lid_equals ct.effect_name Const.effect_Pure_lid
              || lid_equals ct.effect_name Const.effect_Ghost_lid
              then begin match ct.effect_args with
                      | (Inl req, _)::(Inl ens, _)::_ ->
                         Some (norm req), (norm <| mk_post_type ct.result_typ ens)
                      | _ -> failwith "Impossible"
                   end
              else let comp = Normalize.norm_comp [Normalize.DeltaComp] env comp in
                   begin match comp.n with
                    | Total _ -> failwith "Impossible"
                    | Comp ct ->
                        begin match ct.effect_args with
                            | (Inl wp, _)::(Inl wlp, _)::_ ->
                              let as_req, as_ens = match Tc.Env.lookup_typ_abbrev env Const.as_requires, Tc.Env.lookup_typ_abbrev env Const.as_ensures with
                                | Some x, Some y -> x, y
                                | _ -> failwith "Impossible" in
                              let req = mk_Typ_app(as_req, [(Inl ct.result_typ, Some Implicit); targ wp]) (Some mk_Kind_type) ct.result_typ.pos in
                              let ens = mk_Typ_app(as_ens, [(Inl ct.result_typ, Some Implicit); targ wlp]) None ct.result_typ.pos in
                              Some (norm req), norm (mk_post_type ct.result_typ ens)
                            | _ -> failwith "Impossible"
                        end
                    end
         end