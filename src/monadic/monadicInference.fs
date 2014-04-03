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
module Microsoft.FStar.MonadicInference

open Util
open Absyn
open MonadicPretty
open MonadicUtils
open Profiling
open KindAbbrevs

#if MONO
 module Z3Enc = Z3Exe.Query
#else
 module Z3Enc = Z3Encoding.Query
#endif

type tidmap = HashMultiMap<int, typ>
let tids = Hashtbl.create 100

let instantiate_type_scheme (env:Tcenv.env) (e:exp) : exp =
  let sigma = e.sort in  
  let constraints, t, alpha_bindings = TypeRelations.instantiate_typ_gen_constraints env sigma in
  let _ = match constraints with [] -> () | _ -> raise (Err "Unexpected constraints in type") in 
  let targs = alpha_bindings |> List.map snd in 
  List.fold_left (fun e targ -> 
                     let t = open_typ_with_typ e.sort targ in 
                     ewithinfo (Exp_tapp(e, targ)) t targ.p) 
                   e targs 

let try_unify = MonadicUtils.unify

let unify (env:Tcenv.env) msig (t1:typ) (t2:typ) : unit =
  if try_unify env msig  t1 t2 
  then ()
  else 
    let msg = (spr "Expected type \n%s; \ngot type\n%s\n" (typ2string t2 "") (typ2string t1 "")) in
      raise (Error(msg, t1.p))

let rec infer_val_typ (msig:monadsig) (env:Tcenv.env) (top_v:exp) : list<pred> * exp =
  let fail_var sigma = 
    raise (Error(spr "Instantiation of type arguments is supported only for \
                             data constructors and function applications\n \
                             Got var %s with type\n %s" (Pretty.strExp top_v) (sigma.ToString()), top_v.p)) in

    match top_v.v with
      | Exp_bvar x ->
          let sigma = alpha_fresh_labels top_v.p (Tcenv.lookup_bvar env x) in
            [], ewithinfo (Exp_bvar (setsort x sigma)) sigma top_v.p
            (* if mono_type env sigma  *)
            (* then [], ewithinfo (Exp_bvar (setsort x sigma)) sigma top_v.p *)
            (* else fail_var sigma *)
              
      | Exp_fvar(fv, optr) -> 
          let sigma = alpha_fresh_labels top_v.p (Tcenv.lookup_lid env fv.v) in
            [], ewithinfo (Exp_fvar (setsort fv sigma, optr)) sigma top_v.p
            (* if mono_type env sigma  *)
            (* then [], ewithinfo (Exp_fvar (setsort fv sigma, optr)) sigma top_v.p *)
            (* else fail_var sigma *)
              
      | Exp_constant c ->
          let t = Tcutil.typing_const env c in 
            [], setsort top_v t

      | Exp_constr_app(cname, targs, [], vargs) -> (* Type this just as a pure function application *)
        let constr = ewithpos (Exp_fvar(cname, None)) cname.p in 
        let preds1, cexp = infer_val_typ_insts msig env (List.fold_left (fun cexp t -> ewithpos (Exp_tapp(cexp, t)) top_v.p) constr targs) in 
        let cname, targs = match AbsynUtils.flattenExpTapps cexp with 
          | {v=Exp_fvar(cname, _)}, targs -> cname, targs 
          | _ -> raise Impos in 
        begin match unFunType env msig cexp.sort with 
          | Inl _ -> raise Impos
          | Inr purefun -> 
            let preds2, out = checkArgs top_v cname.p msig env vargs purefun.formals in 
            let formals, vargs, guards = List.unzip3 out in (* guards are refinement properties of the arguments *)
            let subs = List.zip formals vargs in 
            let preds3 = List.map (fun t -> substitute_exp_l t subs) purefun.preconditions in 
            let guards = List.flatten guards in
            let purefun = {purefun with typ=substitute_exp_l purefun.typ subs} in
            let purefun = guard_purefun purefun guards in (* Add the arg properties to the result refinement. why? *)
            let result_e = ewithinfo (Exp_constr_app(cname, targs, [], vargs)) purefun.typ top_v.p in 
            let result_refinement = 
              twithsort (Typ_refine(purefun.refname, 
                                    purefun.typ, 
                                    (mkAnd
                                       (substitute_exp_l purefun.refinement subs)
                                       (mkEq env purefun.typ (* Why do we need this equality refinement? *)
                                          (bvd_to_exp purefun.refname purefun.typ)
                                          result_e)), 
                                    true)) purefun.typ.sort in 
            (preds1@preds2@preds3), {result_e with sort=result_refinement}
        end

      | Exp_recd(_, _, _, ((fn,_)::_ as fn_e_l)) -> 
          let recd_lident, tabbrv, tps, expected_record_typ = 
            (try Tcenv.lookup_record_typ env fn 
             with Tcenv.Not_found_binding _ -> 
               let msg = spr "%s is not a valid field name" (Sugar.text_of_lid fn) in
                 raise (Error(msg, top_v.p))) in             

          let subst = 
            if tps |> List.exists (function (Tparam_term _) -> true | _ -> false)
            then 
              let env, topt = Tcenv.clear_expected_typ env in
                match topt with 
                  | None -> raise (Error("Monadic inference for dependent record types requires an annotation", top_v.p))
                  | Some t -> 
                      let fail s = raise (Error(spr "Expected an instance of record %s\n got %s\n" s (Pretty.sli recd_lident), top_v.p)) in 
                      match AbsynUtils.flattenTypAppsAndDeps t with 
                        | {v=Typ_const(fv,_)}, args ->
                            if not (Sugar.lid_equals fv.v recd_lident) || List.length args <> List.length tps then fail (Pretty.sli fv.v);
                            List.map2 (fun tp arg -> match tp, arg with 
                                         | Tparam_typ(bvd, k), Inl t -> Inl(bvd,t)
                                         | Tparam_term(bvd, t), Inr v -> Inr(bvd,v)
                                         | _ -> fail (Pretty.sli fv.v)) tps args 
                        | _ -> fail ""
            else
              tps |> List.map (function 
                                 | Tparam_term (bvd, t) -> raise Impos
                                 | Tparam_typ (bvd, k) -> Inl(bvd, TypeRelations.new_uvar env k top_v.p)) in 
          let {v=Typ_record(fn_t_l, _)} = substitute_l_typ_or_exp expected_record_typ subst in 
            
          let preds, fn_e_l = List.unzip <| List.map2 (fun (fn, e) (fn', t) -> 
                                                         if not (Sugar.lid_equals fn fn') then raise Impos;
                                                         let preds, e = check_val_typ msig env e t in 
                                                           (preds, (fn, e))) fn_e_l fn_t_l in 
          let targs,vargs = List.partition (function Inl _ -> true | Inr _ -> false) subst in 
          let targs = List.map (function (Inl(_,t)) -> t) targs in 
          let vargs = List.map (function (Inr(_,t)) -> t) vargs in 
          let result_ty = List.fold_left mkDep (List.fold_left mkTapp tabbrv targs) vargs in 
            List.flatten preds, ewithinfo (Exp_recd(Some recd_lident, targs, vargs, fn_e_l)) result_ty top_v.p 
              
                  
      | Exp_proj(e, fn) -> 
          let preds, e = infer_val_typ msig env e in 
          let fieldTyp = Tcutil.lookup_field_in_record_typ top_v.p env fn e.sort in
            preds, ewithinfo (Exp_proj(e, fn)) fieldTyp top_v.p

      | Exp_ascribed(v, t, ev) -> 
          let t = check_kind msig env t Kind_star in 
            check_val_typ msig env v t 
              
      | Exp_tabs _ 
      | Exp_abs _ -> 
          (* For (fun x1 ... xn -> e), we compute the type x1:t1 -> .. -> xn:tn -> M t Tx
           * Note, however, the sort of e is just t, not M t tx
           *)
          let rec process_abs (env:Tcenv.env) (formals_rev:list<either<btvdef*kind, bvvdef*typ>>) (f:exp) : exp = 
            match f.v with
              | Exp_abs (x, tformal, body) ->
                  let tformal = match tformal.v with 
                    | Typ_unknown -> TypeRelations.new_uvar env Kind_star f.p
                    | _ -> 
                        let t = check_kind msig env tformal Kind_star in 
                          t (* TODO: Check that the annotated type is uniform *)

                  (* if (not (small_type env t))  *)
                  (* then raise (Error("Currently, monadic inference only supports first-order parameters", top_v.p)) *)
                  (* else t in  *) in
                  let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name x, tformal)) in 
                    process_abs env (Inr(x, tformal)::formals_rev) body

              | Exp_tabs(a, k, [], body) -> 
                  let k = Tc.well_formed_kind f.p env k in 
                  let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(real_name a, k)) in 
                    process_abs env (Inl(a, k)::formals_rev) body

              | _ ->
                  let postvar, post = fresh_postcondition msig env f.p in 
                  let pre, body = infer_exp_typ msig env f post in 
                    
                  let pk = (post_kind msig body.sort) in
                    (* let _ = pr "(abs) pre k1 = %s\n k2=%s\n" (Pretty.strKind post.sort) (Pretty.strKind pk) in  *)
                  let _ = fix_post_kind body.p env post.sort pk in 
                    (* let _ = pr "(abs) k1 = %s\n k2=%s\n" (Pretty.strKind post.sort) (Pretty.strKind pk) in  *)

                  let tx = mkTyp_tlam postvar post.sort pre in 
                  let mtyp = mk_monad msig body.sort tx in 
                  let _, abs = 
                    formals_rev |> List.fold_left 
                        (fun (out_t, out_e) formal -> 
                           match formal with 
                             | Inr (x, tformal) -> 
                                 let range = Range.union_ranges (range_of_bvd x) out_e.p in 
                                 let out_t = twithinfo (Typ_fun(Some x, tformal, out_t)) Kind_star range in
                                 let out_e = ewithinfo (Exp_abs(x, tformal, out_e)) out_t range in 
                                   (out_t, out_e)
                             | Inl (a, k) -> 
                                 let range = Range.union_ranges (range_of_bvd a) out_e.p in 
                                 let out_t = twithinfo (Typ_univ(a, k, [], out_t)) Kind_star range in
                                 let out_e = ewithinfo (Exp_tabs(a, k, [], out_e)) out_t range in 
                                   (out_t, out_e))
                        (mtyp, f) in 
                    abs in
            [], process_abs env [] top_v
              
      | _ -> failwith (spr "unexpected value %s" (Pretty.strExp top_v))
          
(* Returned expression may not be a value---type applications may be inserted *)
and infer_val_typ_insts msig (env:Tcenv.env) (top_v:exp) : list<pred> * exp = 
  let aux v = match v.v with 
    | Exp_bvar x ->
        let sigma = alpha_fresh_labels v.p (Tcenv.lookup_bvar env x) in
        let sv = ewithinfo (Exp_bvar (setsort x sigma)) sigma top_v.p in
          sv
            
    | Exp_fvar(fv, optr) -> 
        let sigma = alpha_fresh_labels v.p (Tcenv.lookup_lid env fv.v) in
        let sv = ewithinfo (Exp_fvar (setsort fv sigma, optr)) sigma top_v.p in 
          sv
            
    | _ -> raise (Error("Expected a name", v.p)) in
    
    match top_v.v with
      | Exp_bvar _ 
      | Exp_fvar _ -> [], instantiate_type_scheme env (aux top_v)    
      | Exp_tapp _ -> 
          let v, targs = AbsynUtils.flattenExpTapps top_v in 
          let sv = aux v in 
          let result = targs |> List.fold_left 
              (fun v t ->
                 let rename t' = match t.v with 
                   | Typ_meta(Meta_named(s, _)) -> twithinfo (Typ_meta(Meta_named(s, t'))) t'.sort t.p
                   | _ -> t' in 
                 let t = match unname_typ t, v.sort.v with 
                   | {v=Typ_meta(Meta_tid i)}, Typ_univ(_, k, _, _) ->
                       (match Hashtbl.tryfind tids i with 
                          | None -> let t' = TypeRelations.new_uvar env k t.p in 
                              Hashtbl.add tids i t';
                              rename t'
                          | Some t -> 
                              rename (twithinfo (Typ_meta(Meta_alpha t)) t.sort t.p))
                              (* (match TypeRelations.force_kind_convertible_ev env t.sort k with  *)
                              (*    | None -> raise (Error(spr "Expected a type argument of kind %s\n got %s\n" *)
                              (*                                    (Pretty.strKind k) (Pretty.strKind t.sort), v.p)) *)
                              (*    | Some _ -> rename (twithinfo (Typ_meta(Meta_alpha t)) t.sort t.p))) *)
                              
                              
                   | {v=Typ_unknown}, Typ_univ(_, k, _, _) -> rename (TypeRelations.new_uvar env k t.p)
                   | t, Typ_univ(_, k, _, _) -> 
                       (match t.sort with 
                          | Kind_unknown -> rename (fst (Tc.kinding (Tcenv.set_expected_kind (enableSolver msig env) k) t))
                          | _ -> 
                              (* let _ = pr "At location %s\n Got type arg of kind %s\n type=%s\n"  *)
                              (*   (Range.string_of_range t.p) *)
                              (*   (Pretty.strKind t.sort) *)
                              (*   (Pretty.strTyp t) in  *)
                                (match TypeRelations.force_kind_convertible_ev env t.sort k with 
                                   | None -> raise (Error(spr "Expected a type argument of kind %s\n got %s\n"
                                                                   (Pretty.strKind k) (Pretty.strKind t.sort), v.p))
                                   | Some _ -> rename t))
                   | _ -> raise (Error(spr "Expected a term with a type scheme; got %s\n\t of type %s"
                                                (exp2string v "") (typ2string v.sort ""), v.p)) in 
                 let v' = Exp_tapp(v, t) in 
                 let s = open_typ_with_typ v.sort t in 
                   ewithinfo v' s v.p) 
              sv in 
            [], result
      | _ -> infer_val_typ msig env top_v
          
and check_val_typ msig (env:Tcenv.env) (top_v:exp) (expected_t:typ) : list<pred> * exp = 
  let preds, e = infer_val_typ msig env top_v in
    if !Options.monadic_subtyping
    then 
      let pred = check_subtype e e.p msig (Tcenv.set_current_value env e) e.sort expected_t in
        (pred::preds), setsort e expected_t
    else
      (check_subtype_old e e.p msig (Tcenv.set_current_value env e) e.sort expected_t;
       preds, setsort e expected_t)
      
and check_subtype err_e p msig env got_t expected_t : pred = 
  let t = canonicalizePST msig env (AbsynUtils.unrefine got_t) in
  is_convertible msig err_e p env t expected_t

and check_subtype_old err_e p msig env got_t expected_t = 
  let fail t =
    raise (Error(spr "\nInferred type for %s : %s not compatible with annotated type %s\n"
                          (Pretty.strExp err_e) 
                          (Pretty.strTyp t) 
                          (Pretty.strTyp expected_t),
                        p)) in
  let t = canonicalizePST msig env (AbsynUtils.unrefine got_t) in
    if try_unify env msig t expected_t 
    then ()
    else 
      match msig.solver with
        | None -> fail t
        | Some s -> 
            (let env = Tcenv.set_solver env s in
               match TypeRelations.convertible_ev env got_t expected_t with
                 | Some(subst, _) ->
                     Tcutil.unify_subst_vars subst; ()
                 | _ -> fail t)
                        
(* Returns the pre-condition and the expression with its computed typ *)
and infer_exp_typ msig (env:Tcenv.env) (top_e:exp) (post:pred) : pred * exp =
  match top_e.v with 
    | _  when AbsynUtils.is_value top_e -> (* monadic return *)
        let preds, v = infer_val_typ msig env top_e in
        let pre = mk_return_pre msig v post in 
        let t, pre = match AbsynUtils.normalizeRefinement v.sort with 
          | {v=Typ_refine(x, t, phi, _)} -> 
              t, guard_precondition msig env pre (substitute_exp_l phi [(x,v)])
          | t -> t, pre in 
        let pre = strengthen_precondition pre preds in 
        let _ = check_post_kind msig env post t in
          (pre, setsort v t)

    | Exp_let(true, _, _) -> raise (Error("Monadic mode: nested let rec is not yet supported", top_e.p))

    | Exp_let(false, [(x,tannot,e)], body) when not(AbsynUtils.is_value e) -> (* monadic bind *)
        let postvar1, post1 = fresh_postcondition msig env e.p in 
        let e = match tannot.v with 
          | Typ_unknown -> e
          | _ -> unascribe e in 
        let pre1, e = infer_exp_typ msig env e post1 in 
        let e = setsort e (canonicalizePST msig env e.sort) in 
        let tx1 = mkTyp_tlam postvar1 post1.sort pre1 in 
        let tannot, guard = match tannot.v with 
          | Typ_unknown -> e.sort, []
          | _ -> 
              let tannot = check_kind msig env tannot Kind_star in 
              let guard = match AbsynUtils.normalizeRefinement tannot with 
                | {v=Typ_refine(y, t, phi, _)} as tt -> 
                    (* let _ = pr "Checking annotation for type %s\n" (Pretty.strTyp tt) in  *)
                    check_subtype e e.p msig env e.sort t;
                    [(substitute_exp_l phi [y,bvd_to_exp x e.sort])]
                | t -> 
                    (* let _ = pr "Checking annotation for type %s\n" (Pretty.strTyp t) in  *)
                    check_subtype e e.p msig env e.sort t;
                    [] in 
                tannot, guard in 
        let postvar2, post2 = fresh_postcondition msig env body.p in 
        let env_body = 
          (* let _ = pr "Pushing %s at type %s\n" (Pretty.strBvd x) (Pretty.strTyp tannot) in  *)
          Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, tannot)) in
        let pre2, body = infer_exp_typ msig env_body body post2 in
        let pre2 = strengthen_precondition pre2 guard in
        let body = setsort body (close_typ msig env body.sort [(x.realname, e.sort)]) in 
          
        let pk = (post_kind msig body.sort) in
        let tx2 = mkTyp_tlam postvar2 post2.sort pre2 in 
          
        let pre = (compose_tx msig env
                     x
                     e.sort
                     tx1
                     body.sort
                     (mkLam x e.sort tx2)
                     post) in 
        let e = ewithinfo (Exp_let(false, [(x, e.sort, e)], body)) body.sort top_e.p in 
          pre, e
            
    | Exp_let(false, [(x,t,v)], body) when AbsynUtils.is_value v ->
        let preds, v = match t.v with
          | Typ_unknown -> infer_val_typ msig env v
          | _ ->
              let t = check_kind msig env t Kind_star in
              let _ = pr "Checking let-bound variable %s\n" x.ppname.idText in 
                check_val_typ msig env v t in

        (* Not generalizing inner lets, for now *)
        (* let _, sigma, v = Tcutil.generalize_with_constraints env [] v.sort v in  *)
        let sigma = v.sort in 
        let env_body = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, sigma)) in
        let tt = canonicalizePST msig env (AbsynUtils.unrefine sigma) in
        (* let env_body = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, tt)) in *)
        let guard_pre, env_body = match AbsynUtils.normalizeRefinement (Tcutil.reduce_typ_delta_beta env sigma) with 
          | {v=Typ_refine(y, t, phi, _)} -> 
              let phi = substitute_exp_l phi [y, bvd_to_exp x t] in 
                (* let id = genident None in *)
                (* let y = ident(spr "%s_refinment" x.realname.idText, dummyRange) in *)
                (* let _ = pr "Pushing assumption %s : %s\n" y.idText (Pretty.strTyp phi) in *)
                (* let env_body = Tcenv.push_local_binding_fast env_body (Tcenv.Binding_var(id, twithsort (Typ_refine(mkbvd (y,y), Const.unit_typ, phi, true)) Kind_star)) in *)
                (fun pre -> guard_precondition msig env pre phi), env_body
          |  t -> (fun t -> t), env_body in 
        let pre, body = infer_exp_typ msig env_body body post in
        let pre = strengthen_precondition (guard_pre pre) preds in 
        let pre, t = 
          if small_type env sigma 
          then 
            let pre, t = substitute_exp_l pre [x, v], substitute_exp_l body.sort [x,v] in 
            let pre = guard_precondition msig env pre (mkTypeOf env v sigma) in 
              pre, t
          else close_precondition msig env pre [(x, sigma)], close_typ msig env body.sort [(x,v)] in 
          
        let e = ewithinfo (Exp_let(false, [(x, sigma, v)], body)) t top_e.p in
          pre, e
            
    | Exp_app _ ->
        let builder e args =
          List.fold_left
            (fun f arg ->
               let sort = open_typ_with_exp f.sort arg in
                 ewithinfo (Exp_app(f, arg)) sort arg.p)
            e args in

        let pre, e = infer_app_typ msig env top_e post builder in
        let _ = check_post_kind msig env post e.sort in
          pre, e
            
    | Exp_primop(op, vargs) ->
        begin match Tcenv.lookup_operator env op with
          | None -> raise (Error("Unknown operator: "^op.idText, top_e.p))
          | Some t ->
              let op_name = new_bvd (Some top_e.p) in
              let op_exp = bvd_to_exp op_name t in
              let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name op_name, t)) in
              let exp = List.fold_left (fun op arg -> ewithpos (Exp_app(op, arg)) op.p) op_exp vargs in
              let builder e args =
                match AbsynUtils.flattenExpTapps e with
                  | _, [] -> (* This seems to insist on primops being monomorphic? What about equality? *)
                      let sort = List.fold_left open_typ_with_exp e.sort args in
                        ewithinfo (Exp_primop(op, args)) sort e.p
                  | _ -> pr "(%s): Builder failed on %s\n" (Range.string_of_range e.p) (Pretty.strExp e); raise Impos in
              let pre, e = infer_app_typ msig env exp post builder in
              let _ = check_post_kind msig env post e.sort in
                (* let _ = pr "Inferred pre %s \n of kind %s\n for expression %s\n" (Pretty.strTyp pre) (Pretty.strKind pre.sort) (Pretty.strExp e) in  *)
                pre, e
        end

    | Exp_match(v, pats, edef) ->
        let preds, v = infer_val_typ msig env v in
          
        (* Ignore edef if it's bot, as with unpacking tuples. *)
        let predef, edef = match edef.v with
          | Exp_bot ->
              let t = TypeRelations.new_uvar env Kind_star edef.p in
              let edef = setsort edef t in 
                trivial_pre msig t, edef
          | _ -> infer_exp_typ msig env edef post in 

        let infer_branch env (pat, branch) : formula * (pat * list<either<(btvdef*kind), (bvvdef*typ)>> * exp * list<pred> * exp) =
          let patpos = top_e.p in 
          let vpat, binders, env = patternBindings patpos env pat in 
          let preds, vpat = infer_val_typ msig env vpat in 
          let p = check_subtype vpat vpat.p msig (Tcenv.set_current_value env vpat) (AbsynUtils.unrefine vpat.sort) (AbsynUtils.unrefine v.sort) in
          let preds = p::preds in 
          let pre, branch = infer_exp_typ msig env branch post in 
          let pre = strengthen_precondition (guard_precondition msig env pre (mkEq env v.sort v vpat)) preds in 
          let pre = close_precondition_with_types msig env pre binders in 
          pre, (pat, binders, vpat, preds, setsort branch (close_typ msig env branch.sort binders)) in 
        
        let pres, pats = List.map (infer_branch env) pats |> List.unzip in
        let mk_lproj = mk_lproj env in 
        let mk_rproj = mk_rproj env in 
        let cross = 
          if !Options.relational && not !Options.double_only
          then
            let crosscases = pats |> List.collect 
                (fun ((pat0,binders0,vpat0,preds0,e0) as ee0) -> 
                  pats |> List.collect 
                      (fun ((pat1,binders1,vpat1,preds1,e1) as ee1) -> 
                        if ee0 === ee1
                        then (* default case *)
                          match edef.v with 
                            | Exp_bot -> []
                            | _ -> 
                              [(mkEq env v.sort (mk_lproj v) (mk_lproj vpat0), preds0, (binders0,e0), ([],edef));
                               (mkEq env v.sort (mk_rproj v) (mk_rproj vpat0), preds0, ([],edef), (binders0,e0))]
                        else 
                          [(mkAnd 
                              (mkEq env v.sort (mk_lproj v) (mk_lproj vpat0))
                              (mkEq env v.sort (mk_rproj v) (mk_rproj vpat1)),
                            preds0@preds1, (binders0,e0), (binders1,e1))])) in 

            crosscases |> List.map 
                (fun ((guard, strength, (b0,e0), (b1,e1))) -> 
                  let env = b0@b1 |> (env |> List.fold_left (fun env b -> 
                    match b with 
                      | Inl (a,k) -> Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(real_name a,k))
                      | Inr (x,t) -> Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name x,t)))) in
                  let t, pre = infer_exp_reltyp msig env e0 e1 post in 
                  let pre = strengthen_precondition (guard_singlesided_precondition msig env pre guard) strength in
                  close_precondition_with_types msig env pre (b0@b1))
          else [] in 
        let pre = mk_cases msig env (pres@cross@[predef]) in 
        let t = join_types msig env (List.map (fun (_, _, _, _, e) -> e.sort) pats) top_e.p in (* TODO: types from cross cases? *)
        let e = ewithsort (Exp_match(v, pats |> List.map (fun (p, _, _, _, b) -> (p,b)), edef)) t in 
        strengthen_precondition pre preds, e
          
    | Exp_cond (({v=Exp_bvar x} as v), e1, e2) ->
      let preds, v = check_val_typ msig env v Const.bool_typ in

      let pre1, e1 = 
        let t, x = AbsynUtils.mkRefinedUnit (mkEq env Const.bool_typ v Const.exp_true_bool) in 
        let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x, t)) in 
          infer_exp_typ msig env e1 post in 
        
      let pre2, e2 = 
        let t, x = AbsynUtils.mkRefinedUnit (mkEq env Const.bool_typ v Const.exp_false_bool) in 
        let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x, t)) in 
          infer_exp_typ msig env e2 post in
        
      let pre1 =
        guard_precondition msig env pre1
          (mkEq env Const.bool_typ v Const.exp_true_bool) in 
      let pre2 =
        guard_precondition msig env pre2
          (mkEq env Const.bool_typ v Const.exp_false_bool) in 
      let cross = 
        if !Options.relational && not !Options.double_only
        then 
          let _, pre3 = infer_exp_reltyp msig env e1 e2 post in 
          let guard3 = (mkAnd (mkEq env Const.bool_typ (mk_lproj env v) Const.exp_true_bool)
                          (mkEq env Const.bool_typ (mk_rproj env v) Const.exp_false_bool)) in 
          let pre3 = guard_singlesided_precondition msig env pre3 guard3 in 
          let _, pre4 = infer_exp_reltyp msig env e2 e1 post in 
          let guard4 = (mkAnd (mkEq env Const.bool_typ (mk_lproj env v) Const.exp_false_bool)
                          (mkEq env Const.bool_typ (mk_rproj env v) Const.exp_true_bool)) in 
          let pre4 = guard_singlesided_precondition msig env pre4 guard4 in 
          [pre3;pre4]
        else [] in 
      let pre = mk_cases msig env ([pre1;pre2]@cross) in 
      let t = join_types msig env [e1.sort; e2.sort] top_e.p in 
      let _ = check_post_kind msig env post t in 
      let result = ewithinfo (Exp_cond(v, e1, e2)) t top_e.p in
      strengthen_precondition pre preds, result
            
    | Exp_tapp(e, t) ->
        raise (Error("Explicit type applications not supported in expression position", top_e.p))
          
    | Exp_ascribed(e, t, []) ->
        let t = check_kind msig env t Kind_star in
          check_exp_typ msig env e t post
            
    | _ -> raise (Error(spr "Monadic mode: unsupported expression form %s" (Pretty.strExp top_e), top_e.p))

and infer_exp_reltyp msig env e0 e1 post : (typ * pred) = 
  let mk_lproj = mk_lproj env in 
  let mk_rproj = mk_rproj env in 
  let false_pre () = 
    pr "Warning (%s,%s): Failed to compute a non-trivial single-sided derivation; trying to prove cross-cases unreachable\n" 
      (Range.string_of_range e0.p) (Range.string_of_range e1.p);
    pr "\n\te0=%s\n\te1=%s\n" (Pretty.strExp e0) (Pretty.strExp e1);
    (TypeRelations.new_uvar env Kind_star e0.p, prop_as_pre msig Const.false_typ) in
  if  (AbsynUtils.is_value e0 && AbsynUtils.is_value e1) 
  then 
    let v0, v1 = e0, e1 in 
    match infer_val_reltyp msig env v0 v1 with 
    | None -> false_pre ()
    | Some t -> 
      let x = gen_bvar_p (Range.union_ranges v0.p v1.p) t in
      let xexp = ewithsort (Exp_bvar x) t in 
      let pre = mk_return_pre msig xexp post in 
      let pre = Krivine.strong_normalize env pre in
      let pre = AbsynUtils.substitute_proj_l pre [(mk_lproj xexp, mk_lproj v0); 
                                       (mk_rproj xexp, mk_rproj v1)] in 
      t, pre
  else match e0.v, e1.v with 
    | Exp_app _, Exp_app _ -> 
      let (v0, args0), (v1, args1) = AbsynUtils.flattenApps e0, AbsynUtils.flattenApps e1 in 
      begin match infer_val_reltyp msig env v0 v1 with 
        | Some tfun -> 
          begin match unFunType env msig tfun with 
            | Inr purefun -> raise (NYI "pure function application (single-sided)")
            | Inl mfun -> 
              if (List.length args0 <> List.length args1) ||
                 (List.length args0 <> List.length mfun.formals)
              then raise (Error("Wrong number of arguments", e0.p));
              let subst = mfun.formals |> (List.zip args0 args1 |> (Some ([],[]) |> List.fold2
                  (fun out (a0, a1) (y,tformal) -> 
                    match out with 
                      | None -> None
                      | Some (preds, subst) -> 
                        match infer_val_reltyp msig env a0 a1 with 
                          | Some tt -> 
                            let x = gen_bvar_p (Range.union_ranges v0.p v1.p) tt in 
                            let xexp = ewithsort (Exp_bvar x) tt in 
                            let tt = twithsort (Typ_refine(x.v, tt, (mkAnd (mkEq env tt (mk_lproj xexp) a0) 
                                                                       (mkEq env tt (mk_rproj xexp) a1)), true)) tt.sort in 
                            let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name x.v, tt)) in 
                            let p = mkForall x.v tt (check_subtype xexp xexp.p msig (Tcenv.set_current_value env xexp) tt tformal) in
                            let yexp = ewithsort (Exp_bvar (bvd_to_bvar_s y tformal)) tformal in 
                            Some (p::preds, 
                                  (mk_lproj yexp, mk_lproj a0)::(mk_rproj yexp, mk_rproj a1)::subst)
                          | None -> None))) in 
              match subst with 
                | None -> false_pre ()
                | Some (preds, s) -> 
                  let t = AbsynUtils.substitute_proj_l mfun.typ s in 
                  let wp = AbsynUtils.substitute_proj_l (Krivine.strong_normalize env mfun.transformer) s in 
                  t, strengthen_precondition (mkTapp wp post) preds
           end
        | _ -> false_pre ()
      end
        
    | (Exp_let(false, [(x0,_,e0)], e0'), 
       Exp_let(false, [(x1,_,e1)], e1')) -> 
      let ppvar, pp = fresh_postcondition msig env e0.p in 
      let t, pre = infer_exp_reltyp msig env e0 e1 pp in 
      let wp = mkTyp_tlam ppvar pp.sort pre in

      let e1' = 
        if bvd_eq x0 x1 then e1'
        else substitute_exp_typ_or_exp_l e1' [Inr(x1, bvd_to_exp x0 t)] in 
      let env = Tcenv.push_local_binding env (Tcenv.Binding_var(real_name x0, t)) in
      let ppvar', pp' = fresh_postcondition msig env e0'.p in 
      let tres, pre' = infer_exp_reltyp msig env e0' e1' pp' in 
      let wp' = mkTyp_tlam ppvar' pp'.sort pre' in 
      
      let pre = compose_tx msig env x0 t wp tres (mkLam x0 t wp') post in 
      tres, pre

    | Exp_let(false, [(x0, _, _)], _), _ -> 
        let ty = TypeRelations.new_uvar env Kind_star e1.p in
        let y = new_bvd (Some e1.p) in 
        let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name y, ty)) in 
        let e1 = ewithsort (Exp_let(false, [(x0, ty, bvd_to_exp y ty)], e1)) e1.sort in 
        let t, pre = infer_exp_reltyp msig env e0 e1 post in 
        let pre = close_precondition_with_types msig env pre [Inr(y,ty)] in 
          t, pre
        
    | _, Exp_let(false, [(x1, _, _)], _)  -> 
        let ty = TypeRelations.new_uvar env Kind_star e0.p in
        let y = new_bvd (Some e0.p) in 
        let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name y, ty)) in 
        let e0 = ewithsort (Exp_let(false, [(x1, ty, bvd_to_exp y ty)], e0)) e0.sort in 
        let t, pre = infer_exp_reltyp msig env e0 e1 post in 
        let pre = close_precondition_with_types msig env pre [Inr(y,ty)] in 
          t, pre
        
    | Exp_match(v, pats, def), _ -> 
      let _, t = infer_val_typ msig env v in (* a bit funky, since this is single sided *)
      let pres = pats |> List.map (fun (pat, branch) ->
        let vpat, binders, env = patternBindings e0.p env pat in 
        let tbranch, prebranch = infer_exp_reltyp msig env branch e1 post in 
        let guard = mkEq env v.sort (mk_lproj v) (mk_lproj vpat) in 
        let pre = guard_singlesided_precondition msig env prebranch guard in 
        (tbranch, close_precondition_with_types msig env prebranch binders)) in 
      let pres = match def.v with 
        | Exp_bot -> pres 
        | _ -> pres@[infer_exp_reltyp msig env def e1 post] in 
      let t = join_types msig env (List.map fst pres) e0.p in 
      let pre = mk_cases msig env (List.map snd pres) in 
      t,pre

    | _, Exp_match(v, pats, def) -> 
      let _, t = infer_val_typ msig env v in (* a bit funky, since this is single sided *)
      let pres = pats |> List.map (fun (pat, branch) ->
        let vpat, binders, env = patternBindings e1.p env pat in 
        let tbranch, prebranch = infer_exp_reltyp msig env e0 branch post in 
        let guard = mkEq env v.sort (mk_rproj v) (mk_rproj vpat) in 
        let pre = guard_singlesided_precondition msig env prebranch guard in 
        (tbranch, close_precondition_with_types msig env prebranch binders)) in 
      let pres = match def.v with 
        | Exp_bot -> pres 
        | _ -> pres@[infer_exp_reltyp msig env e0 def post] in 
      let t = join_types msig env (List.map fst pres) e1.p in 
      let pre = mk_cases msig env (List.map snd pres) in 
      t,pre

    | Exp_cond(v, e0, e0'), _ -> 
      let _, t = infer_val_typ msig env v in (* a bit funky, since this is single sided, but its just an unrefined bool value *)

      let t1, pre1 = infer_exp_reltyp msig env e0 e1 post in 
      let guard1 = mkEq env v.sort (mk_lproj v) Const.exp_true_bool in
      let pre1 = guard_singlesided_precondition msig env pre1 guard1 in 

      let t2, pre2 = infer_exp_reltyp msig env e0' e1 post in 
      let guard2 = mkEq env v.sort (mk_lproj v) Const.exp_false_bool in
      let pre2 = guard_singlesided_precondition msig env pre2 guard2 in 
      
      let t = join_types msig env [t1;t2] e1.p in 
      let pre = mk_cases msig env [pre1;pre2] in 
      t, pre

      
    | _, Exp_cond(v,e1,e1') -> 
      let _, t = infer_val_typ msig env v in  (* a bit funky, since this is single sided, but its just an unrefined bool value *)

      let t1, pre1 = infer_exp_reltyp msig env e0 e1 post in 
      let guard1 = mkEq env v.sort (mk_rproj v) Const.exp_true_bool in
      let pre1 = guard_singlesided_precondition msig env pre1 guard1 in 

      let t2, pre2 = infer_exp_reltyp msig env e0 e1' post in 
      let guard2 = mkEq env v.sort (mk_rproj v) Const.exp_false_bool in
      let pre2 = guard_singlesided_precondition msig env pre2 guard2 in 
      
      let t = join_types msig env [t1;t2] e1.p in 
      let pre = mk_cases msig env [pre1;pre2] in 
      t, pre

    | _ -> 
        let pre0, e0 = infer_exp_typ msig env e0 post in
        let pre1, e1 = infer_exp_typ msig env e1 post in
        let pre0 = whnf pre0 in 
        let pre1 = whnf pre1 in 
        (* let _ = pr "Got pres:\n\t%s\n\t%s\n" (Pretty.strTyp pre0) (Pretty.strTyp pre1) in  *)
          match pre0.v, pre1.v with 
            | Typ_app(c0, post0),  Typ_app(c1, post1) 
                when (try_unify env msig post0 post1) 
                  && (try_unify env msig post0 post) -> 
                begin match (Tcenv.expand_typ_until env c0 Const.composeClassic_lid,
                             Tcenv.expand_typ_until env c1 Const.composeClassic_lid) with
                  | Some c0, Some c1 -> 
                      begin match (AbsynUtils.destruct c0 Const.composeClassic_lid, 
                                   AbsynUtils.destruct c1 Const.composeClassic_lid) with 
                        | Some [Inl tret0; Inl wp0; Inl _], Some [Inl tret1; Inl _; Inl wp1] when try_unify env msig tret0 tret1 -> 
                            let wp = composeClassic env tret0 wp0 wp1 in 
                              tret0, mkTapp wp post
                        | _ -> raise Impos
                      end
                  | _ -> false_pre ()
                end
            | _ -> false_pre ()


and infer_val_reltyp msig env v0 v1 : option<typ> = match v0.v, v1.v with 
  | Exp_bvar x0, Exp_bvar x1 when bvar_eq x0 x1 ->  
    let _, v0' = infer_val_typ msig env v0 in 
    Some (v0'.sort)
    
  | Exp_fvar(x0,None), Exp_fvar(x1,None) when Sugar.lid_equals x0.v x1.v ->
    let _, v0' = infer_val_typ msig env v0 in 
    Some (v0'.sort)

  | Exp_tapp _, Exp_tapp _ -> 
      let v0, ts0 = AbsynUtils.flattenExpTapps v0 in
      let v1, ts1 = AbsynUtils.flattenExpTapps v1 in
      begin match infer_val_reltyp msig env v0 v1 with
        | None -> None
        | Some t -> 
            if List.length ts0 = List.length ts1 
            && List.forall2 (try_unify env msig) ts0 ts1
            then Some (List.fold_left open_typ_with_typ t ts0)
            else None
      end

  | Exp_constr_app _, Exp_constr_app _  -> 
    let _, {sort=t0} = infer_val_typ msig env v0 in 
    let _, {sort=t1} = infer_val_typ msig env v1 in 
    if try_unify env msig t0 t1
    then Some t0
    else None
      (* raise (Error(spr "(%s) Unable to relate values at types %s and %s" (Range.string_of_range v1.p) (Pretty.strTyp t0) (Pretty.strTyp t1),  *)
      (*                        v0.p)) *)
    

  | Exp_abs(x0, t0, e0), Exp_abs(x1, t1, e1) -> 
    if not (try_unify env msig t0 t1)
    then None
    else (* raise (Error(spr "(%s) Unable to relate functions with different formal params at types %s and %s" (Range.string_of_range v1.p) (Pretty.strTyp t0) (Pretty.strTyp t1),  *)
               (*               v0.p)); *)

    let e1 = 
      if bvd_eq x0 x1 then e1
      else substitute_exp_typ_or_exp_l e1 [Inr(x1, bvd_to_exp x0 t0)] in 
    let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(real_name x0, t0)) in
    let postvar, post = fresh_postcondition msig env (Range.union_ranges e0.p e1.p) in
    let tbody, pre = infer_exp_reltyp msig env e0 e1 post in 
    let pk = post_kind msig tbody in
    let _ = fix_post_kind e0.p env post.sort pk in 
    let wp = mkTyp_tlam postvar post.sort pre in 
    let mtyp = mk_monad msig tbody wp in 
    Some (twithinfo (Typ_fun(Some x0, t0, mtyp)) Kind_star (Range.union_ranges e0.p e1.p))

  | _ -> 
    let _, {sort=t0} = infer_val_typ msig env v0 in 
    let _, {sort=t1} = infer_val_typ msig env v1 in  (* todo ... check that t0/t1 are classical *)
    if try_unify env msig t0 t1
    then Some t0
    else None
    
and checkArgs err_e p msig (env:Tcenv.env) (args:list<exp>) formals : (list<pred> * list<bvvdef * exp * list<formula>>) = 
  if List.length args <> List.length formals
  then raise (Error (spr "In %s\nExpected %d arguments; got %d\n" (Pretty.strExp err_e) (List.length formals) (List.length args), p));
  let rec aux (subst, preds, out) args formals = match args, formals with
    | [], [] -> List.flatten preds, List.rev out
    | arg::args, (x,tformal)::formals -> 
      let tformal, (preds', arg) = 
        if !Options.monadic_subtyping 
        then 
          let tformal = substitute_l_typ_or_exp tformal subst in 
            tformal, infer_val_typ msig (Tcenv.set_expected_typ env tformal) arg
        else tformal, infer_val_typ msig env arg in
      let t, refinement = match AbsynUtils.normalizeRefinement arg.sort with
          | {v=Typ_refine(y, t, phi, _)} ->
              let phi = (* removing any equality refinements. 
                           why not just not add them in the first place? see line 77 *)
                match AbsynUtils.flattenTypAppsAndDeps phi with
                  | {v=Typ_const(tc,_)}, [Inl t1; Inl t2]
                      when ((Sugar.lid_equals tc.v Const.and_lid) &&
                              AbsynUtils.is_constructed_typ t2 Const.eq_lid) ->
                      [(mkDep (mkLam y t t1) (bvd_to_exp x tformal))]
                        
                  | {v=Typ_const(tc,_)}, _
                      when ((Sugar.lid_equals tc.v Const.eq_lid) ||
                              (Sugar.lid_equals tc.v Const.true_lid)) -> []
                      
                  | _ ->
                      [(mkDep (mkLam y t phi) (bvd_to_exp x tformal))] in
                
                t, phi
                  
          | t -> t, [] in
      let preds'' = 
        if !Options.monadic_subtyping 
        then [check_subtype arg arg.p msig (Tcenv.set_current_value env arg) t tformal]
        else
          let tformal = substitute_l_typ_or_exp tformal subst in 
          let preds'', tformal = match AbsynUtils.normalizeRefinement tformal with 
            | {v=Typ_refine(x,t,phi,_)} -> [substitute_exp_l phi [(x, arg)]], t
            | tformal -> [], tformal in
          let p = check_subtype arg arg.p msig (Tcenv.set_current_value env arg) t tformal in
          p::preds'' in
      let out = (x,arg,refinement)::out in 
      let subst = (Inr(x,arg))::subst in 
          aux (subst,preds''::preds'::preds,out) args formals in 
    aux ([],[],[]) args formals
    
    
  (* formals |> (args |> List.map2  *)
  (*                 (fun arg (x, tformal) -> *)
  (*                    let arg = infer_val_typ msig env arg in *)
  (*                    let t, refinement = match AbsynUtils.normalizeRefinement arg.sort with *)
  (*                      | {v=Typ_refine(y, t, phi, _)} -> *)
  (*                          let phi = (\* removing any equality refinements.  *)
  (*                                       why not just not add them in the first place? see line 77 *\) *)
  (*                            match AbsynUtils.flattenTypAppsAndDeps phi with *)
  (*                              | {v=Typ_const(tc,_)}, [Inl t1; Inl t2] *)
  (*                                  when ((Sugar.lid_equals tc.v Const.and_lid) && *)
  (*                                          AbsynUtils.is_constructed_typ t2 Const.eq_lid) -> *)
  (*                                  [(mkDep (mkLam y t t1) (bvd_to_exp x tformal))] *)
                                     
  (*                              | {v=Typ_const(tc,_)}, _ *)
  (*                                  when ((Sugar.lid_equals tc.v Const.eq_lid) || *)
  (*                                          (Sugar.lid_equals tc.v Const.true_lid)) -> [] *)
                                   
  (*                              | _ -> *)
  (*                                  [(mkDep (mkLam y t phi) (bvd_to_exp x tformal))] in *)
                             
  (*                            t, phi *)
                               
  (*                      | t -> t, [] in *)
                       
  (*                    let _ = check_typ msig env t tformal in *)
  (*                      (x,arg,refinement))) in  *)
    
      

and infer_app_typ msig (env:Tcenv.env) (top_e:exp) (post:typ) (buildApp:exp -> list<exp> -> exp)
    : (typ * exp) =

  let rec aux in_e (args:list<exp>) =
    match in_e.v with
      | Exp_app (e, v) -> aux e (v::args)
      | _ ->
          let preds1, in_e = infer_val_typ_insts msig env in_e in  (* we allow type instantiation here *)
            match unFunType env msig in_e.sort with
              | Inl mfun ->
                  let preds2, subs = checkArgs top_e top_e.p msig env args mfun.formals in
                  let formals, (args : list<exp>), guards  = List.unzip3 subs in
                  let guards = List.flatten guards in
                  let mfun = guard_mfun msig env in_e.p mfun guards in
                  let result_e = buildApp (setsort in_e (mkMFun msig mfun)) args in
                    begin match destruct_monad env msig result_e.sort with 
                      | None -> raise Impos
                      | Some (t, tx) -> 
                          strengthen_precondition (mkTapp tx post) (preds1@preds2), setsort result_e t
                    end
              | Inr purefun ->
                  let preds2, out = checkArgs top_e top_e.p msig env args purefun.formals in
                  let formals, args, guards = List.unzip3 out in
                  let subst = List.zip formals args in 
                  let preds3 = List.map (fun t -> substitute_exp_l t subst) purefun.preconditions in 
                  let guards = List.flatten guards in
                  let result_e = buildApp (setsort in_e (mkPureFun (guard_purefun purefun guards))) args in
                  let t = unrefine_typ env result_e.sort in 
                  let xbvd = new_bvd None in 
                  let xexp = bvd_to_exp xbvd t in 
                  let pre = mk_return_pre msig xexp post in 
                  let pre = match AbsynUtils.normalizeRefinement result_e.sort with 
                    | {v=Typ_refine(y, t, phi, _)} -> 
                        guard_precondition msig env pre (substitute_exp_l phi [y,xexp])
                    | _ -> pre in 
                  let pre = close_precondition msig env pre [(xbvd, t)] in 
                    strengthen_precondition pre (preds1@preds2@preds3), setsort result_e t
  in
    aux top_e []
       
and check_exp_typ msig (env:Tcenv.env) (top_e:exp) (top_t:typ) (post:pred) : (typ * exp) =
  let pre, e = infer_exp_typ msig env top_e post in
  let _ = unify env msig e.sort top_t in
    pre, e

and check_kind msig (env:Tcenv.env) (t:typ) (k:kind) : typ = 
  let env = Tcenv.set_expected_kind env k in 
    try 
      let t, _ = Tc.kinding env t in 
        t
    with Error _ as e -> 
      match msig.solver with 
        | None -> raise e
        | Some s -> let env = Tcenv.set_solver env s in 
            fst (Tc.kinding env t)

and check_post_kind msig env post t' = 
  let expect = post_kind msig t' in 
    match expect, post.sort with 
      | Kind_dcon(_, t', _), Kind_dcon(_, t, _) -> unify env msig t t'; post
      | _ -> raise Impos
           
(*****************************************************************************)
(*                     Top-level                                             *)
(*****************************************************************************)

let infer_letbinding_typ msig (env:Tcenv.env) (lb,r) : (letbinding * bool) =
  let lb_rev = List.fold_left 
    (fun out (x, _, e) -> 
       if not (AbsynUtils.is_value e)
       then raise (Error(spr "At the moment, top-level let statments may only bind function-typed values. %s = %s is a not a function value" (x.ppname.idText) (Pretty.strExp e), 
                                (range_of_bvd x)));
       (* let _ = pr "\n******Inferring type for top-level let: %s\n" (x.ppname.idText) in *)
       let preds, e' = infer_val_typ msig env e in 
         match preds with 
           | [] -> 
               let e' = 
                 if !Options.generalize_monadic_types then 
                   let _, sigma, e' = Tcutil.generalize_with_constraints env [] e'.sort e' in         
                     e'
                 else e' in
               (x, e'.sort, e')::out
           | _ -> failwith "Unexpected preds")
    [] lb in 
    (List.rev lb_rev, r)
      
