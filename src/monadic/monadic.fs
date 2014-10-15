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
module Microsoft.FStar.Monadic

open Util
open Absyn
open MonadicPretty
open MonadicUtils
open MonadicInference
open Profiling

#if MONO
 module Z3Enc = Z3Exe.Query
#else
 module Z3Enc = Z3Encoding.Query
#endif

let normalize_tparam env (tp:tparam) : tparam =
  match tp with
    | Tparam_typ (id, k) -> 
        if kind_contains_refinement env k
        then failwith "Type constructor kinds may not contain refinements."
        else tp
    | Tparam_term (id, t) -> 
        if typ_contains_refinement env t
        then failwith "Type constructor kinds may not contain refinements."
        else tp

let check_kind_contains_refinement env k = 
  if kind_contains_refinement env k 
  then failwith "In monadic mode, kinds may not contain refinements."
  else ()

let rec normalize_sigelt msig (env:Tcenv.env) (s:sigelt) : sigelt =
  match s with
    | Sig_tycon_kind (id, tl, k, b, muts, tags) ->
        let tl' = List.map (normalize_tparam env) tl in
          check_kind_contains_refinement env k;
          Sig_tycon_kind (id, tl', k, b, muts, tags)

    | Sig_typ_abbrev (id, tl, k, t) -> 
        let tl = List.map (normalize_tparam env) tl in
        let _ = pr "Normalizing refinement type of %s ... %s\n" (Sugar.text_of_lid id) (Pretty.strTyp t) in 
        let t = normalize_refinements id msig env t in
          check_kind_contains_refinement env k;
          Sig_typ_abbrev(id, tl, k, t)

    | Sig_record_typ (id, tl, k, t, b) ->
        let tl' = List.map (normalize_tparam env) tl in
          check_kind_contains_refinement env k;
          if typ_contains_refinement env t
          then failwith "Record signature types may not contain refinements."
          else Sig_record_typ (id, tl', k, t, b)

    | Sig_datacon_typ (id, tl, t, b, a, o1, o2, flist) -> 
        let tl' = List.map (normalize_tparam env) tl in
          Sig_datacon_typ (id, tl', t, b, a, o1, o2, flist)

    | Sig_value_decl (id, t) ->
        let t' = normalize_refinements id msig env t in
          Sig_value_decl (id, t')
            
    | Sig_extern_value (eref, id, t) ->
        let t' = normalize_refinements id msig env t in
          Sig_extern_value (eref, id, t')

    | Sig_extern_typ (eref, s') ->
        let s' = normalize_sigelt msig env s' in
          Sig_extern_typ (eref, s')

    | Sig_query _
    | Sig_ghost_assume _ 
    | Sig_logic_function _ -> s

let find_annot annots (x:bvvdef) : option<typ> = 
  match annots |> Util.findOpt (function 
                                  | Sig_value_decl(lid, t) -> 
                                      let _, name = Util.pfx lid.lid in 
                                        name.idText = (pp_name x).idText
                                  | _ -> false) with 
    | Some (Sig_value_decl(lid, t)) -> Some t 
    | _ -> None
   

let infer_and_check_letbinding msig env lbr annots 
    : (Tcenv.env * (letbinding * bool)) = 
  let solver = Tcenv.get_solver env in 
  let msig = {msig with solver=solver} in 
  let ienv = Tcenv.clear_solver env in
  let ienv = (if snd lbr (* it's recursive, so push the annots *)
              then fst lbr |> List.fold_left 
                  (fun ienv (x, _, e) -> 
                     match AbsynUtils.findValDecl annots x with 
                       | Some (Sig_value_decl(_, t)) -> Tcenv.push_local_binding_fast ienv (Tcenv.Binding_var(x.realname, t))
                       | _ -> ienv)
                  ienv
              else ienv) in 
  let lbr = "infer_letbinding_typ" ^^ lazy infer_letbinding_typ msig ienv lbr in

  let monadic_conv (tenv:Tcenv.env) inferred_t annot_t = 
    (* let _ = pr "Inferred type for ... %s\n" (Pretty.strTyp inferred_t) in  *)
    if !Options.__unsafe 
    then (pr "Unsafe mode! Skipping proof obligation\n"; true)
    else
      (*   (match tenv.annot with None -> "" | Some s -> "for " ^s) *)
      (*   (Pretty.strTyp inferred_t) *)
      (*   (Pretty.strTyp annot_t) in *)
      (* let _ = pr "Inferred type %s ... checking for convertibility with annotation\n" *)
      (*   (match tenv.annot with None -> "" | Some s -> "for " ^s) in *)
      let destruct tenv typ lid = 
        match AbsynUtils.flattenTypAppsAndDeps (unascribe_typ typ) with
          | {v=Typ_const(tc,_)}, args when Sugar.lid_equals tc.v lid -> Some args
          | _ -> None in
      let fallback () = 
        match TypeRelations.convertible_ev env inferred_t annot_t with 
          | Some(subst, _) -> Tcutil.unify_subst_vars subst; true
          | _ -> false in 
        if not !Options.monadic_conv then fallback ()
        else
          match inferred_t.v, annot_t.v with
            | Typ_fun(_, u1, dst1), Typ_fun(_, u2, dst2) 
                when (AbsynUtils.is_constructor u1 Const.unit_lid &&
                        AbsynUtils.is_constructor u2 Const.unit_lid) -> 
                (match destruct tenv dst1 Const.DST_lid, destruct tenv dst2 Const.DST_lid with 
                   | Some ([Inl d1; Inl tx1]), Some ([Inl d2; Inl tx2]) 
                       when (AbsynUtils.is_constructor d1 Const.dyn_lid &&
                               AbsynUtils.is_constructor d2 Const.dyn_lid) -> 
                       (match tx2.v with 
                          | Typ_tlam(post, post_k, {v=Typ_lam(h, heap_t, pre); sort=s}) -> 
                              let inferred_pre = twithsort (Typ_dep((twithsort (Typ_app(tx1, bvd_to_typ post post_k)) s), 
                                                                    bvd_to_exp h heap_t)) pre.sort in 
                              let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(post.realname, post_k)) in 
                              let env = Tcenv.push_local_binding_fast env (Tcenv.Binding_var(h.realname, twithsort (Typ_refine(h, heap_t, pre, true)) Kind_star)) in 
                              (* let _ = pr "Starting KNL\n" in  *)
                              let inferred_pre = Krivine.strong_normalize env inferred_pre in
                                (* let _ = pr "Normalized type: %s\n" (Pretty.strTyp inferred_pre) in  *)
                              (* let _ = pr "Calling Z3 to check inferred type ... \n" in *)
                                Z3Enc.query env inferred_pre
                          | _ -> fallback ())
                   | _ -> fallback ())
            | _ -> fallback () in 
    
  let env = fst lbr |> 
      List.fold_left (fun env (x, inferred_t, _) -> 
                          match find_annot annots x with 
                            | None -> 
                                Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, inferred_t))
                            | Some annot_t -> 
                                let _ = pr "Checking top-level let-binding %s\n" (x.ppname.idText) in
                                  if !Options.monadic_subtyping 
                                  then 
                                    match MonadicUtils.monadic_conv msig env [] inferred_t annot_t with
                                      | NonMonadic 
                                      | Failure -> 
                                          raise (Error(spr "\nInferred type for %s is\n%s\n\nnot compatible with annotated type\n%s\n" 
                                                         (x.ppname.idText)
                                                         (Pretty.strTyp inferred_t)
                                                         (Pretty.strTyp annot_t),
                                                       range_of_bvd x))
                                      | Success -> 
                                          Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, annot_t))
                                  else
                                    (* let _ = pr "Inferred type is %s\n" (Pretty.strTyp inferred_t) in  *)
                                    let inferred_t = if !Options.relational then inferred_t else (Krivine.strong_normalize env inferred_t) in
                                    if monadic_conv {env with annot=Some (x.ppname.idText)} inferred_t annot_t 
                                    then Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, annot_t))
                                    else raise (Error(spr "\nInferred type for %s : %s not compatible with annotated type %s\n" 
                                                        (x.ppname.idText)
                                                        (Pretty.strTyp inferred_t)
                                                        (Pretty.strTyp annot_t),
                                                      range_of_bvd x)))


      (* if monadic_conv {env with annot=Some (x.ppname.idText)} (Krivine.strong_normalize env inferred_t) annot_t  *)
      (* then Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, annot_t)) *)
      (* else raise (Error(spr "\nInferred type for %s : %s not compatible with annotated type %s\n"  *)
      (*                            (x.ppname.idText) *)
      (*                            (Pretty.strTyp inferred_t) *)
      (*                            (Pretty.strTyp annot_t), *)
      (*                          range_of_bvd x))) *)
      (* raise (Tcutil.Error(spr "\nInferred type for %s:\n%s\n\nNot compatible with annotated type:\n%s\n"  *)
      (*                       (x.ppname.idText) (Pretty.strTyp inferred_t) (Pretty.strTyp annot_t),  *)
      (*                     range_of_bvd x))) *)
      env in 
  let env = annots |> List.fold_left Tcenv.push_sigelt env in 
    env, lbr

let check_sigelt env se = 
  try Tc.check_sigelt env se
  with Error(msg, p) ->
    let msg = spr "Failed to check signature element: %s\n%s\n" (Pretty.sli (lid_of_sigelt se)) msg in 
      raise (Error(msg, p))

let checkSignature msig envsugar env signature = 
  let envsugar, env, signature = signature |> 
      List.fold_left (fun (envsugar, env, sigout) se -> 
                        let se = check_sigelt envsugar se in
                        let envsugar = Tcenv.push_sigelt envsugar se in 
                        let se = 
                          if !Options.normalize_monadic_refinements 
                          then normalize_sigelt msig envsugar se
                          else se in 
                        let env = Tcenv.push_sigelt env se in 
                          (envsugar, env, se::sigout))
      (envsugar, env, []) in 
    envsugar, env, List.rev signature
        
let typing_modul env (m : modul) =
  let aux msig = 
    let signature, annots = Tcutil.extractSignature env m in 
    let envsugar, env, signature = checkSignature msig env env signature in 
    let _, _, annots = checkSignature msig envsugar env annots in 
    let env, lbrs = m.letbindings |>  
        List.fold_left (fun (env, lbrs) lbr -> 
                          let annots = AbsynUtils.findValDecls annots lbr in 
                          let env, lbr = infer_and_check_letbinding msig env lbr annots in 
                            env, lbr::lbrs)
        (env, []) in 
    let env, mainExp = 
      match m.main with
        | Some exp -> failwith "Typing main expression not yet implemented"
        | _ -> env, None in
      {name=m.name; 
       extends=m.extends; 
       pos=m.pos; 
       signature=signature@annots;
       letbindings=List.rev lbrs; 
       main=mainExp; 
       exports=signature@annots;
       pragmas=m.pragmas} in
    try
      let msig = get_monadsig env m in 
      let result = Some(aux msig) in 
        result
    with 
      | e when (Tcutil.handleable e) -> Tcutil.handle_err false None e

        
