#light "off"
module Microsoft.FStar.Backends.ML.ExtractExp
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar.Backends.ML.Util

let eff_to_string = function
    | MayErase -> "MayErase"
    | Keep -> "Keep"

let fail r msg = 
    Util.print_string <| Print.format_error r msg;
    exit 1 

let err_uninst e = 
    fail e.pos (Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" (Print.exp_to_string e))

let err_ill_typed_application e args t =
    fail e.pos ("Ill-typed application")

let err_value_restriction e =
    fail e.pos ("Refusing to generalize because of the value restriction")
    
let err_unexpected_eff e f0 f1 =
    fail e.pos (Util.format2 "Expected effect %s; got effect %s" (eff_to_string f0) (eff_to_string f1))
    
let is_constructor e = match (Util.compress_exp e).n with 
    | Exp_fvar(_, b) -> b
    | _ -> false

let rec is_value (e:exp) = match (Util.compress_exp e).n with 
    | Exp_bvar _
    | Exp_fvar _ 
    | Exp_abs _  -> true
    | Exp_app(head, args) -> is_constructor head && args |> List.for_all (fun (te, _) -> 
        match te with 
            | Inl _ -> true
            | Inr e -> is_value e)
    | _ -> false

let translate_typ (g:env) (t:typ) : mlty = ExtractTyp.extractTyp g t

let instantiate (s:mltyscheme) (args:list<mlty>) : mlty = Util.subst s args

let ml_unit = MLE_Const MLC_Unit
let ml_unit_ty = MLTY_Named ([], ([], "unit")) 
let ml_bool_ty = MLTY_Named ([], ([], "bool")) 

let erasable (g:env) (t:mlty) = 
    if t = ml_unit_ty then true
    else match t with 
        | MLTY_Named (_, (["Ghost"], "erased")) -> true
        | _ -> false //what about types that reduce/unfold to unit/erased t?


let erase (g:env) (e:mlexpr) (f:e_tag) (t:mlty) = 
    if f = MayErase && erasable g t
    then ml_unit
    else e

let coerce (g:env) (e:mlexpr) (t:mlty) (t':mlty) = 
    if equiv g t t' 
    then e
    else MLE_Coerce (e, t, t')

let eff_leq f f' = match f, f' with 
    | MayErase, _ 
    | _, Keep -> true
    | _ -> false

let join f f' = match f, f' with 
    | Keep, _
    | _ , Keep -> Keep
    | _ -> MayErase

let join_l fs = List.fold_left join MayErase fs

let unit_binder = 
    let x = Util.gen_bvar Tc.Recheck.t_unit in
    v_binder x

let is_type_abstraction = function 
    | (Inl _, _)::_ -> true
    | _ -> false

let rec extract_pat (g:env) p : (env * list<mlpattern>) = match p.v with
  | Pat_disj [] -> failwith "Impossible"

  | Pat_disj (p::pats)      ->
    let g, p = extract_pat g p in
    g, [MLP_Branch (List.collect (fun x -> snd (extract_pat g x)) pats)]

  | Pat_constant s     -> 
    g, [MLP_Const (mlconst_of_const s)]

  | Pat_cons (f, pats) -> 
    let d, _ = Env.lookup_fv g f in
    let g, pats = Util.fold_map extract_pat g pats in
    g, [MLP_CTor (d, List.flatten pats)]

  | Pat_var(x, _) ->
    let mlty = translate_typ g x.sort in 
    let g = Env.extend_bv g x ([], mlty) in
    g, [MLP_Var (as_mlident x.v)]

  | Pat_wild _ 
  | Pat_dot_term _ -> 
    g, [MLP_Wild]

  | Pat_dot_typ _
  | Pat_twild _
  | Pat_tvar _ ->
    g, []
  
let rec check_exp (g:env) (e:exp) (f:e_tag) (t:mlty) : mlexpr = 
    erase g (check_exp' g e f t) f t

and check_exp' (g:env) (e:exp) (f:e_tag) (t:mlty) : mlexpr = 
    match (Util.compress_exp e).n with 
      | Exp_match(scrutinee, pats) -> 
        let e, f_e, t_e = synth_exp g scrutinee in 
        let mlbranches = pats |> List.map (fun (pat, when_opt, branch) -> 
            let env, p = extract_pat g pat in 
            let when_opt = match when_opt with 
                | None -> None
                | Some w -> Some (check_exp env w MayErase ml_bool_ty) in //when clauses are Pure in F*
            let branch = check_exp env branch f t in
            List.hd p, when_opt, branch) in
        if eff_leq f_e f
        then MLE_Match(e, mlbranches)
        else err_unexpected_eff scrutinee f_e f

     | _ -> 
       let e0, f0, t0 = synth_exp g e in
       if eff_leq f0 f
       then coerce g e0 t0 t
       else err_unexpected_eff e f0 f
      
and synth_exp (g:env) (e:exp) : (mlexpr * e_tag * mlty) = 
    let e, f, t = synth_exp' g e in
    erase g e f t, f, t

and synth_exp' (g:env) (e:exp) : (mlexpr * e_tag * mlty) = 
    match (Util.compress_exp e).n with 
        | Exp_constant c ->
          let t = Tc.Recheck.typing_const e.pos c in
          MLE_Const <| mlconst_of_const c, MayErase, translate_typ g t
 
        | Exp_ascribed(e, t) ->
          let t = translate_typ g t in 
          let e, f, t' = synth_exp g e in
          coerce g e t' t, f, t

        | Exp_bvar _
        | Exp_fvar _ -> 
          let x, s = lookup_var g e in 
          begin match s with 
            | ([], t) -> x, MayErase, t
            | _ -> err_uninst e
          end

        | Exp_app(head, args) -> 
          let rec synth_app (head, args') (f, t) args = //if partially applied and head is a datacon, it needs to be eta-expanded
            match args, t with 
                | [], _ -> MLE_App(head, List.rev args'), f, t

                | (Inl _, _)::rest, MLTY_Fun (tunit, f', t) -> //non-prefix type app; this type argument gets erased to unit
                  if equiv g tunit ml_unit_ty
                  then synth_app (head, ml_unit::args') (join f f', t) rest
                  else failwith "Impossible: ill-typed application" //ill-typed; should be impossible

                | (Inr e0, _)::rest, MLTY_Fun(t0, f', t) -> 
                  let e0, f0, t0' = synth_exp g e0 in 
                  let e0 = coerce g e0 t0' t0 in 
                  synth_app (head, e0::args') (join_l [f;f';f0], t) rest
                  
                | _ -> err_ill_typed_application e args t in
                  
          let head = Util.compress_exp head in
          begin match head.n with 
            | Exp_bvar _ 
            | Exp_fvar _ -> 
              let head, (vars, t) = lookup_var g e in
              let n = List.length vars in
              if n <= List.length args
              then let prefix, rest = Util.first_N (List.length vars) args in
                   let tys = prefix |> List.map (function 
                    | (Inl t, _) ->  translate_typ g t
                    | _ -> err_uninst e) in
                   let t = instantiate (vars, t) tys in
                   match rest with 
                    | [] -> head, MayErase, t
                    | _ -> synth_app (head, []) (MayErase, t) rest 
              else err_uninst e

            | _ -> 
              let head, f, t = synth_exp g head in
              synth_app (head, []) (f, t) args               
          end

        | Exp_abs(bs, e) -> 
            let ml_bs, env = List.fold_left (fun (ml_bs, env) (b, _) -> match b with 
                | Inl a -> //no first-class polymorphism; so type-binders get wiped out
                  let env = Env.extend_ty env a (Some MLTY_Top) in 
                  let ml_b = (as_mlident a.v, Some <| ml_unit_ty) in
                  ml_b::ml_bs, env 
              
                | Inr x -> 
                  let t = translate_typ env x.sort in
                  let env = Env.extend_bv env x ([], t) in
                  let ml_b = (as_mlident x.v, Some t) in
                  ml_b::ml_bs, env) ([], g) bs in
            let bs = List.rev ml_bs in
            let e, f, t = synth_exp env e in
            let f, tfun = List.fold_right 
                (fun (_, targ) (f, t) -> MayErase, MLTY_Fun (must targ, f, t))
                ml_bs (f, t) in
            MLE_Fun(bs, e), f, tfun
    
        | Exp_let((is_rec, lbs), e') -> 
          let maybe_generalize {lbname=lbname; lbeff=lbeff; lbtyp=t; lbdef=e} = 
              let f_e = ExtractTyp.translate_eff g lbeff in
              let t = Util.compress_typ t in
              match t.n with 
                | Typ_fun(bs, c) when is_type_abstraction bs -> 
                  //need to generalize, but will erase all the type abstractions; 
                  //so, always add an extra unit arg. to preserve order of evaluation/generativity 
                  //and to circumvent the value restriction
                   let tbinders, tbody = 
                        match Util.prefix_until (function (Inr _, _) -> true | _ -> false) bs with 
                            | None -> bs, Util.comp_result c
                            | Some (bs, b, rest) -> bs, mk_Typ_fun(unit_binder::b::rest, c) None c.pos in

                   let n = List.length tbinders in
                   begin match (Util.compress_exp e).n with 
                      | Exp_abs(bs, body) -> 
                        if n <= List.length bs
                        then let targs, rest_args = Util.first_N n bs in 
                             let expected_t = match Util.mk_subst_binder tbinders targs with 
                                | None -> failwith "Not enough type binders"
                                | Some s -> Util.subst_typ s tbody in
                             let targs = targs |> List.map (function (Inl a, _) -> a | _ -> failwith "Impossible") in
                             let env = List.fold_left (fun env a -> Env.extend_ty env a None) g targs in
                             let expected_t = translate_typ env expected_t in
                             let polytype = targs |> List.map (fun a -> as_mlident a.v), expected_t in
                             let body = mk_Exp_abs(unit_binder::rest_args, body) None e.pos in
                             (lbname, f_e, (t, (targs, polytype)), body)

                        else (* fails to handle:
                                let f : a:Type -> b:Type -> a -> b -> Tot (nat * a * b) = 
                                    fun (a:Type) -> 
                                      let x = 0 in 
                                      fun (b:Type) (y:a) (z:b) -> (x, y, z)
                                
                                Could eta-expand; but with effects this is problem; see ETA-EXPANSION and NO GENERALIZATION below
                             *)
                             failwith "Not enough type binders" //TODO: better error message
                     | _ -> 
                        //ETA-EXPANSION?
                        //An alternative here could be to eta expand the body, but with effects, that's quite dodgy
                        // Consider:
                        //    let f : ML ((a:Type) -> a -> Tot a) = x := 17; (fun (a:Type) (x:a) -> x) 
                        // Eta-expanding this would break the assignment; so, unless we hoist the assignment, we must reject this program
                        // One possibility is to restrict F* so that the effect of f must be Pure 
                        // In that case, an eta-expansion would be semantically ok, but consider this:
                        //    let g : Tot ((a:Type) -> a -> Tot (a * nat)) = let z = expensive_pure_comp x in fun (a:Type) (x:a) -> (x,z))
                        // The eta expansion would cause the expensive_pure_comp to be run each time g is instantiated (this is what Coq does, FYI)
                        // It may be better to hoist expensive_pure_comp again.
                        //NO GENERALIZATION:
                        //Another alternative could be to not generalize the type t, inserting MLTY_Top for the type variables
                        err_value_restriction e
                   end

                | _ ->  (* no generalizations; TODO: normalize and retry? *)
                  let expected_t = translate_typ g t in
                  (lbname, f_e, (t, ([], ([],expected_t))), e) in
         
          let check_lb env (nm, (lbname, f, (t, (targs, polytype)), e)) =
              let env = List.fold_left (fun env a -> Env.extend_ty env a None) env targs in
              let e = check_exp env e f (snd polytype) in
              f, (nm, Some polytype, [], e) in

          let lbs = lbs |> List.map maybe_generalize in 
        
          let env_body, lbs = List.fold_right (fun lb (env, lbs) ->
              let (lbname, _, (t, (_, polytype)), _) = lb in
              let env, nm = Env.extend_lb env lbname t polytype in
              env, (nm,lb)::lbs) lbs (g, []) in 

          let env_def = if is_rec then env_body else g in 

          let lbs = lbs |> List.map (check_lb env_def)  in

          let e', f', t' = synth_exp env_body e' in
          
          let f = join_l (f'::List.map fst lbs) in

          MLE_Let((is_rec, List.map snd lbs), e'), f', t'
   

      | Exp_match(e, pats) -> 
        failwith "Matches must be checked; missing a compiler-provided annotation" //matches must be checked, not synth'd

      | Exp_meta(Meta_desugared(e, _)) -> synth_exp g e //TODO: handle the re-sugaring
      
      | Exp_uvar _ 
      | Exp_delayed _ -> failwith "Unexpected expression"