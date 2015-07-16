#light "off"
module Microsoft.FStar.Backends.ML.ExtractExp
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar.Backends.ML.Util

let fail r msg = 
    Util.print_string <| Print.format_error r msg;
    exit 1 

let err_uninst e = 
    fail e.pos (Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" (Print.exp_to_string e))

let err_ill_typed_application e args t =
    fail e.pos ("Ill-typed application")

let err_value_restriction e =
    fail e.pos ("Refusing to generalize because of the value restriction")
    
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

let translate_typ (g:env) (t:typ) : mlty = failwith "NYI"
let translate_eff (g:env) (l:lident) : e_tag = failwith "NYI"
let instantiate (s:mltyscheme) (args:list<mlty>) : mlty = failwith "NYI"

let equiv (g:env) (t:mlty) (t':mlty) : bool = failwith "NYI"

let ml_unit = MLE_Const MLC_Unit
let ml_unit_ty = MLTY_Named ([], ([], "unit")) 

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

let join f f' = match f, f' with 
    | Keep, _
    | _ , Keep -> Keep
    | _ -> MayErase

let join_l fs = List.fold_left join MayErase fs

let rec check_exp (g:env) (e:exp) (f:e_tag) (t:mlty) : mlexpr = 
    erase g (check_exp' g e f t) f t

and synth_exp (g:env) (e:exp) : (mlexpr * e_tag * mlty) = 
    let e, f, t = synth_exp' g e in
    erase g e f t, f, t

and check_exp' (g:env) (e:exp) (f:e_tag) (t:mlty) : mlexpr = failwith "NYI"

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
                  let ml_b = (Util.as_mlident a.v, Some <| ml_unit_ty) in
                  ml_b::ml_bs, env 
              
                | Inr x -> 
                  let t = translate_typ env x.sort in
                  let env = Env.extend_bv env x ([], t) in
                  let ml_b = (Util.as_mlident x.v, Some t) in
                  ml_b::ml_bs, env) ([], g) bs in
            let bs = List.rev ml_bs in
            let e, f, t = synth_exp env e in
            let f, tfun = List.fold_right 
                (fun (_, targ) (f, t) -> MayErase, MLTY_Fun (must targ, f, t))
                ml_bs (f, t) in
            MLE_Fun(bs, e), f, tfun
    
        | Exp_let((false, [{lbname=lbname; lbeff=eff; lbtyp=t; lbdef=e}]), e') -> 
          let t = Util.compress_typ t in
          begin match t.n with 
             | Typ_fun(bs, c) -> 
                 begin match bs with 
                    | (Inl _,_)::_ -> //need to generalize
                       let tbinders, tbody = 
                           match Util.prefix_until (function (Inr _, _) -> true | _ -> false) bs with 
                            | None -> bs, Util.comp_result c
                            | Some (bs, b, rest) -> bs, mk_Typ_fun(b::rest, c) None c.pos in

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
                                let expected_e = translate_eff env eff in
                                let body = match rest_args with 
                                    | [] -> 
                                      if is_value body 
                                      then body
                                      else err_value_restriction body
                                    | _ -> mk_Exp_abs(rest_args, body) None e.pos in
                                let body = check_exp env body expected_e expected_t in
                                let polytype = (targs |> List.map (fun a -> as_mlident a.v), expected_t) in
                                let env, nm = Env.extend_lb g lbname t polytype in
                                let e', f, t = synth_exp env e' in
                                MLE_Let(false, [(nm, (Some polytype), [], body)], e'), f, t

                            else failwith "Not enough type binders"
                          
                          | _ -> err_value_restriction e
                        end

                    | _ -> //no generalization 
                      failwith "NYI"
                 end
               
           | _ -> (* normalize and retry? *)
                failwith "NYI"

        end


//      | Exp_let((true, lbs), e') -> 
//  
//      | Exp_match(e, pats) 
//        -> failwith "NYI"
        
//      | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
//      | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
//      
      | Exp_uvar _ 
      | Exp_delayed _ -> failwith "Unexpected expression"