#light "off"
module Microsoft.FStar.Backends.ML.ExtractExp
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML.Env

let fail r msg = 
    Util.print_string <| Print.format_error r msg;
    exit 1 

let err_uninst e = 
    fail e.pos (Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" (Print.exp_to_string e))

let err_ill_typed_application e args t =
    fail e.pos ("Ill-typed application")
    
let translate_typ (g:env) (t:typ) : mlty = failwith "NYI"

let instantiate (s:mltyscheme) (args:list<mlty>) : mlty = failwith "NYI"

let equiv (g:env) (t:mlty) (t':mlty) : bool = failwith "NYI"

let ml_unit = MLE_Const MLC_Unit
let ml_tunit = MLTY_Named ([], ([], "unit")) 

let erasable (g:env) (t:mlty) = 
    if t = ml_tunit then true
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

let mlconst_of_const p c = failwith ""

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
          mlconst_of_const e.pos c, MayErase, translate_typ g t
 
        | Exp_ascribed(e, t) ->
          let t = translate_typ g t in 
          let e, f, t' = synth_exp g e in
          coerce g e t' t, f, t

        | Exp_bvar _
        | Exp_fvar _ -> 
          let x, s = must <| lookup_var g e in 
          begin match s with 
            | ([], t) -> x, MayErase, t
            | _ -> err_uninst e
          end

        | Exp_app(head, args) -> 
          let rec synth_app (head, args') (f, t) args = //if partially applied and head is a datacon, it needs to be eta-expanded
            match args, t with 
                | [], _ -> MLE_App(head, List.rev args'), f, t

                | (Inl _, _)::rest, MLTY_Fun (tunit, f', t) -> //non-prefix type app; this type argument gets erased to unit
                  if equiv g tunit ml_tunit
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
              let head, (vars, t) = must <| lookup_var g e in
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
        
        failwith "NYI" 
      
      | Exp_match(e, pats) 
        -> failwith "NYI"
      
//      
//      | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
//      | Exp_meta       of meta_e                                     (* No longer tag every expression with info, only selectively *)
//      
//      | Exp_uvar       of uvar_e * typ                               (* not present after 1st round tc *)
//      | Exp_delayed    of exp * subst_t * memo<exp>                  (* A delayed substitution --- always force it before inspecting the first arg *)
//  