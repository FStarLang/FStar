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
module FStar.TypeRelations

open Absyn
open AbsynUtils
open Util
open Const
open Tcenv
open Profiling
open Tcutil
open KindAbbrevs

let debug = ref false
let eq_ctr = new_counter "TReln.equivalent"
let inst_ctr = new_counter "TReln.instantiable"
let convert_ctr = new_counter "TReln.convertible"
let refsub_ctr =  new_counter "TReln.refinement_subtyping"
let teq_ctr =  new_counter "TReln.tequiv"

    
(* Utilities on substitution maps *)
let find_equivalence_class (subst:subst) uv = 
  let rec finder seen rest = match rest with 
    | [] -> None, seen
    | eq_cl::rest -> 
        let uvl, _ = eq_cl in
          if (List.exists (fun (uv',_) -> Unionfind.equivalent uv uv') uvl) then 
            Some(eq_cl), seen@rest
          else finder (eq_cl::seen) rest 
  in finder [] subst 

let in_equivalence_class subst uv1 uv2 = 
  let eq1, _ = find_equivalence_class subst uv1 in    
  let eq2, _ = find_equivalence_class subst uv2 in
    match eq1, eq2 with
        None, None -> false
      | Some c1, Some c2 -> LanguagePrimitives.PhysicalEquality c1 c2 
      | _ -> false 
          
(* These functions have strange signatures because that's what absyn's
   type_fold_map functions are more general than what's needed here. *)
let subst_typ subst () () t = match (compress_hard' t) with
  | Typ_uvar (uv,_) -> 
      let eqc, _ = find_equivalence_class subst uv in
        (match eqc with
           | Some (_, Some t') -> (), t'.v, Some t'.sort
           | Some ((uvk::_), None) -> (), (Typ_uvar uvk), Some (snd uvk)
           | _ -> (), t, None)
  | _ -> (),t, None
      
let subst_exp () () e = (), e 

let apply_subst_kind (subst:subst) (k:kind) : kind = 
    match subst with 
        | [] -> k 
        | _ -> let _, k = kind_fold_map (subst_typ subst) subst_exp (fun _ e -> e) Absyn.ignore_env () () k in
                 k
              
let apply_subst (subst:subst) (t:typ) : typ = 
  match subst with 
      []  -> t
    | _ -> 
        let _, t' = typ_fold_map (subst_typ subst) subst_exp (fun _ e -> e) Absyn.ignore_env () () t in
          t' 

let apply_subst_exp (subst:subst) (e:exp) : exp = 
  match subst with 
      [] -> e
    | _ -> 
        let _, e' = exp_fold_map (subst_typ subst) subst_exp (fun _ e -> e) Absyn.ignore_env () () e in
          e' 

let promote_values_affine env t1 t2 = 
  let t1, t2 = expand_typ env t1, expand_typ env t2 in
    match t1.v, t2.v with 
      | Typ_affine _, Typ_affine _ -> t1, t2
      | _, Typ_affine _ ->  (* implicit promotion to affine type for values *)
          (match current_value env with 
             | Some v when is_non_variable_value env v -> (twithsort (Typ_affine t1) Kind_affine), t2
             | _ -> t1, t2)
      | _ -> t1, t2
          
(* assumed equivalences between bound variables *)
type equivs = list<Disj<(btvdef*btvdef), (bvvdef * bvvdef)>>
    
let bvvars_equivalent (bvar1:bvvar) (bvar2:bvvar) equivs : bool = 
  let rn1 = (bvar_real_name bvar1).idText in
  let rn2 = (bvar_real_name bvar2).idText in
    rn1=rn2 ||List.exists 
      (function Inl _ -> false | Inr (b1:bvvdef, b2:bvvdef, _) -> 
         let b1n = real_name b1 in
         let b2n = real_name b2 in
           (b1n.idText = rn1 && b2n.idText = rn2) ||
           (b2n.idText = rn1 && b1n.idText = rn2)) equivs

let btvars_equivalent (bvar1:btvar) (bvar2:btvar) equivs : bool = 
  let rn1 = (bvar_real_name bvar1).idText in
  let rn2 = (bvar_real_name bvar2).idText in
    rn1=rn2 ||List.exists 
      (function Inr _ -> false | Inl (b1:btvdef, b2:btvdef, _) -> 
         let b1n = real_name b1 in
         let b2n = real_name b2 in
           (b1n.idText = rn1 && b2n.idText = rn2) ||
           (b2n.idText = rn1 && b1n.idText = rn2)) equivs

let mk_equivs nopt nopt' t equivs = match nopt, nopt' with 
  | None, None -> equivs
  | Some x, None -> Inr(x, new_bvd None, t)::equivs
  | None, Some x -> Inr(new_bvd None, x, t)::equivs
  | Some bvd1, Some bvd2 -> (Inr (bvd1, bvd2, t))::equivs
      
let mk_equivs_k nopt nopt' k equivs = match nopt, nopt' with 
  | None, None -> equivs
  | Some x, None -> Inl(x, new_bvd None, k)::equivs
  | None, Some x -> Inl(new_bvd None, x, k)::equivs
  | Some bvd1, Some bvd2 -> (Inl (bvd1, bvd2, k))::equivs

(* a list of bvars that can be equated with any term index *)
(* Used to compute the set of match assumptions in pattern matching*)
type equatables<'a,'sort>=list<bvar<'a,'sort>> 
type renv = {equatable_xvars:equatables<exp,typ>;
             equatable_tvars:equatables<typ,kind>;
             tcenv:Tcenv.env;
             subst:subst;
             eqbs:list<binding>;
             evidence:evidence; 
             struct_depth:int;
             curval:option<exp>}

let mk_renv eq_x eq_t env subst = {equatable_xvars=eq_x; equatable_tvars=eq_t; tcenv=env; 
                                   subst=subst; eqbs=[]; evidence=[]; struct_depth=0; curval=current_value env}
let renv_of_env env = mk_renv [] [] env [] 
let renv_of_subst env s = mk_renv [] [] env s
let strEquatables renv = 
  spr "{%s}, {%s}" 
    (String.concat ", " (List.map (fun bv -> Pretty.strBvar bv) renv.equatable_xvars))
    (String.concat ", " (List.map (fun bv -> Pretty.strBtvar bv) renv.equatable_tvars))
let debug_rti renv t1 t2 = 
  if !debug then 
    let eqbs = strEquatables renv in
      pr "Refine_term_indices (%s):\n\t %s\n\t %s\n" eqbs (Pretty.strTyp t1) (Pretty.strTyp t2)
  else ()
let debug_equatable renv e1 b =     
  if !debug then 
    let eqbs = strEquatables renv in
      pr "Testing_equatable (%s):\t %s\t result:%s\n" eqbs (Pretty.strExp e1) (if b then "Yes!" else "no") 
  else ()
let debug_gen_eqb renv e1 e2 =     
  if !debug then 
    let eqbs = strEquatables renv in
      pr "Gen_eqb (%s): adding_equation (%s = %s)\n" eqbs (Pretty.strExp e1) (Pretty.strExp e2)
  else ()

let formula_entailment env forms = 
  match Tcenv.get_solver env with 
    | None -> false
    | Some solver -> 
        List.forall (fun f -> solver.solver_query env f) forms
  
let formula_implication env f1 f2 = 
  let env = List.fold_left (fun env f -> 
                              let t, id = mkRefinedUnit f in 
                              let env = push_local_binding env (Binding_var(id,t)) in 
                                env) env f1 in 
    formula_entailment env f2

let logger, logger_kind =
  let ctr = ref 0 in 
    (fun t1 t2 -> 
      let n = !ctr in 
        ctr := n + 1;
        let _ = pr "Try %d: Trying to unify \n\t%s and\n\t%s\n" n (Pretty.strTyp t1) (Pretty.strTyp t2) in
          function 
              None -> pr "Result %d: Failed\n" n
            | Some _ -> pr "Result %d: Success!\n" n), 
    (fun k1 k2 -> 
      let n = !ctr in 
        ctr := n + 1;
        let _ = pr "Try %d: Trying to unify \n\t%s and\n\t%s\n" n (Pretty.strKind k1) (Pretty.strKind k2) in 
          function 
              None -> pr "Result %d: Failed\n" n
            | Some _ -> pr "Result %d: Success!\n" n) 



  
(* the actual work of unifying a uv with a type t*)      
let rec try_unify env subst uv t : option<subst> = 
  let occurs uv t = 
    let uvs_typ uvs t = match t with 
      | Typ_uvar(uv, _) -> uv::uvs, t
      | _ -> uvs, t in 
    let uvs_exp uvs e = uvs, e in 
    let uvs, _ = descend_typ_map uvs_typ uvs_exp [] t in
      List.exists (fun uv' -> Unionfind.equivalent uv uv') uvs in 
  let is_well_formed t (uv,k) : bool = 
    let r = match Unionfind.find uv with 
      | Uvar wf -> (wf t k && (not (occurs uv t)))
      | t -> pr "Unexpected uvar in well-formedness check: %A\n" t; raise Impos in 
      (* if not r then pr "Type %s failed well-formedness check for unification (occurs = %A)\n" (Pretty.strTyp t) (occurs uv t); *)
      r in
  let is_well_formed_l t uvs : bool = List.forall (is_well_formed t) uvs in 
  let tuv = apply_subst subst uv in
  let tt = apply_subst subst t in
    match tuv.v, tt.v with
      | Typ_uvar(uv1, k1), Typ_uvar (uv2, k2) when Unionfind.equivalent uv1 uv2 -> Some subst
      | Typ_uvar(uv1, k1), Typ_uvar (uv2, k2) when in_equivalence_class subst uv1 uv2 -> Some subst
      | Typ_uvar(uv1, k1), Typ_uvar (uv2, k2) when equivalent_kinds env k1 k2 -> 
          let eqclass1, rest = find_equivalence_class subst uv1 in
          let eqclass2, rest = find_equivalence_class rest uv2 in
          let union12 = match eqclass1, eqclass2 with
              None, None -> Some ([uv1,k1;uv2,k2], None)
            | Some c, None -> 
                (match c with
                   | (uvs, None) -> Some ((uv2,k2)::uvs, None)
                   | (uvs, Some t) -> 
                       if is_well_formed_l t [uv2,k2]
                       then Some ((uv2,k2)::uvs, Some t) 
                       else None)
            | None, Some c -> 
                (match c with
                   | (uvs, None) -> Some ((uv1,k1)::uvs, None)
                   | (uvs, Some t) -> if (is_well_formed_l t [uv1,k1]) then Some ((uv1,k1)::uvs, Some t) else None)
            | Some c1, Some c2 -> 
                (match c1, c2 with
                   | (uvs1, None), (uvs2, None) -> Some (uvs1@uvs2, None)
                   | (uvs1, Some t), (uvs2, None) -> if is_well_formed_l t [uv2,k2] then Some(uvs1@uvs2, Some t) else None                         
                   | (uvs1, None), (uvs2, Some t) -> if is_well_formed_l t [uv1,k1] then Some(uvs1@uvs2, Some t) else None
                   | _ -> None) (* cannot be unified ... already fixed to another type, 
                                   TODO: unless both these types are the same? *) in
            bind_opt union12 (fun eqclass12 -> Some (eqclass12::rest))
      | Typ_uvar (uv, k) as t1, _ -> 
          let eqclass, rest = find_equivalence_class subst uv in
          let eqclass = match eqclass with 
              None -> 
                if is_well_formed_l tt [uv,k] then 
                  Some ([uv,k], Some tt)
                else 
                  None
            | Some (uvs, None) ->  
                if is_well_formed_l tt uvs then 
                  Some (uvs, Some tt)
                else 
                  None
            | Some (uvs, Some tt') -> 
                None (* already unified with something else *) in
            bind_opt eqclass (fun eqc -> Some (eqc::rest))
      | _ -> 
          raise (NYI "Unexpected unification cases")
(* end try_unify *)

and unifiable env subst t1 t2 = 
  (* straight unification of types t1 and t2, without using the solver or the 
     matching assumptions in the context to refine term indices *)
  let rec same_typ env equivs subst t t' : option<subst> =
    let etf t = 
      let t' = reduce_typ_delta_beta env t in 
        if LanguagePrimitives.PhysicalEquality t t' 
        then None
        else Some t' in 
    let tt1 = unname_typ <| apply_subst subst (compress_hard t) in 
    let tt2 = unname_typ <| apply_subst subst (compress_hard t') in
    let tt1, tt2 = 
      match AbsynUtils.flattenTypAppsAndDeps tt1, AbsynUtils.flattenTypAppsAndDeps tt2 with 
        | ({v=Typ_const(tc1, _)}, _), ({v=Typ_const(tc2, _)}, _) -> 
            if Sugar.lid_equals tc1.v tc2.v 
            then tt1, tt2
            else (match etf tt1, etf tt2 with 
                    | Some tt1, Some tt2 -> tt1, tt2
                    | None, Some tt2 -> tt1, tt2
                    | Some tt1, None -> tt1, tt2
                    | None, None -> tt1, tt2)
        | _ -> tt1, tt2 in 
    let retry () = 
      match etf tt1, etf tt2 with 
        | None, None -> None
        | Some tt1, None -> same_typ env equivs subst tt1 tt2
        | None, Some tt2 -> same_typ env equivs subst tt1 tt2
        | Some tt1, Some tt2 -> same_typ env equivs subst tt1 tt2 in 
      match tt1.v, tt2.v with 
        | Typ_ascribed(_, _), _ 
        | _, Typ_ascribed(_, _) -> same_typ env equivs subst (unascribe_typ tt1) (unascribe_typ tt2)

        | Typ_btvar bv1, Typ_btvar bv2 -> 
            if btvars_equivalent bv1 bv2 equivs then Some subst else None
              
        | Typ_const (fv1,eref1), Typ_const (fv2, eref2) -> 
            if fvar_eq fv1 fv2 && eref1=eref2 then Some subst else retry ()
              
        | Typ_record(fnt_l1, _), Typ_record(fnt_l2, _) -> 
            if (List.length fnt_l1 =  List.length fnt_l2) then 
              let l = List.zip fnt_l1 fnt_l2 in
              let rec same_rec subst = function
                  [] -> Some subst
                | ((fn1, t1), (fn2, t2))::tl -> 
                    if (Sugar.path_of_lid fn1)=(Sugar.path_of_lid fn2) then
                      bind_opt (same_typ env equivs subst t1 t2)
                        (fun subst' -> same_rec subst' tl) 
                    else None in
                same_rec subst l
            else None
              
        | Typ_fun (nopt, t1, t2),  Typ_fun (nopt', t1', t2') -> (* equivalence of bound term vars handles by tequiv *)
            bind_opt (same_typ env equivs subst t1 t1')
              (fun subst' -> 
                 let equivs' = mk_equivs nopt nopt' t1 equivs in
                   same_typ env equivs' subst' t2 t2')

        | Typ_lam(x, t1, t2), Typ_lam(y, t1', t2') -> 
            bind_opt (same_typ env equivs subst t1 t1')
              (fun subst' -> 
                 let equivs' = (Inr (x, y, t1))::equivs in
                   same_typ env equivs' subst' t2 t2')

        | Typ_tlam(x, k1, t2), Typ_tlam(y, k1', t2') -> 
            bind_opt (same_kind env equivs subst k1 k1')
              (fun subst' -> 
                 let equivs' = (Inl (x, y, k1))::equivs in
                   same_typ env equivs' subst' t2 t2')
              
        | Typ_univ(bvd1, k, f1, t), Typ_univ(bvd2, k', f2, t') ->                 
            bind_opt (same_kind env equivs subst k k')
              (fun subst -> 
                 same_typs env (Inl(bvd1, bvd2, k)::equivs) subst 
                   (t::f1) (t'::f2))
              
        | Typ_dtuple nt_l, Typ_dtuple nt_l' -> 
            if (List.length nt_l) = (List.length nt_l') then
              let rec equiv_dep_list equivs subst = function
                  [] -> Some subst
                | ((n1, t1), (n2, t2))::tl -> 
                    bind_opt (same_typ env equivs subst t1 t2)
                      (fun subst' -> 
                         let equivs' = mk_equivs n1 n2 t1 equivs in 
                           equiv_dep_list equivs' subst' tl) in 
              let l = List.zip nt_l nt_l' in
                equiv_dep_list equivs subst l 
            else None
              
        | Typ_refine (bvd1, t1, f1, _),  Typ_refine (bvd2, t2, f2, _) -> 
            bind_opt (same_typ env equivs subst t1 t2)
              (fun subst' -> 
                 let equivs = Inr(bvd1,bvd2, t1)::equivs in 
                   match same_typ env equivs subst' f1 f2 with 
                     | Some s -> Some s
                     | None -> None (* try to prove logical equivalence of f1 and f2 *)
                         (* let env = List.fold_left (fun env lr -> match lr with  *)
                         (*                             | Inl(a,b,k) ->  *)
                         (*                                 let env = push_local_binding_fast env (Binding_typ(a.realname,k)) in  *)
                         (*                                 let env = push_local_binding_fast env (Binding_typ(b.realname,k)) in  *)
                         (*                                   push_local_binding_fast env (Binding_tmatch(bvd_to_bvar_s a k, bvd_to_typ b k)) *)
                         (*                             | Inr(x,y,t) ->  *)
                         (*                                 let env = push_local_binding_fast env (Binding_var(x.realname,t)) in  *)
                         (*                                 let env = push_local_binding_fast env (Binding_var(y.realname,t)) in  *)
                         (*                                   push_local_binding_fast env (Binding_match(bvd_to_exp x t, bvd_to_exp y t))) *)
                         (*   env equivs in  *)
                         (*   if (formula_implication env [f1] [f2] && *)
                         (*       formula_implication env [f2] [f1]) *)
                         (*   then Some subst' *)
                         (*   else None *))
              
        | Typ_app (t1, t2), Typ_app (t1', t2') -> 
            bind_opt (same_typ env equivs subst t1 t1')
              (fun subst' -> same_typ env equivs subst' t2 t2')
              
        | Typ_dep (t1, e1), Typ_dep (t2, e2) -> 
            bind_opt (same_typ env equivs subst t1 t2)
              (fun subst' -> same_exp env equivs subst' e1 e2)
          
        | Typ_meta(Meta_alpha t), _ ->     
            same_typ env equivs subst (alpha_convert t) tt2
        | _, Typ_meta(Meta_alpha t) ->
            same_typ env equivs subst tt1 (alpha_convert t) 

        | Typ_meta (Meta_cases tl), Typ_meta (Meta_cases tl') -> 
            same_typs env equivs subst tl tl'

        | Typ_meta(Meta_pattern(t, _)), _ -> 
          same_typ env equivs subst t tt2
        | _, Typ_meta(Meta_pattern(t, _)) -> 
          same_typ env equivs subst tt1 t

        | Typ_unknown, Typ_unknown -> Some subst 
            
        | _, Typ_uvar(uv,k) -> try_unify env subst tt2 tt1
              
        | Typ_uvar(uv,k), _ -> try_unify env subst tt1 tt2
              
        | Typ_affine t1, Typ_affine t2 -> 
            same_typ env equivs subst t1 t2

        | _ -> retry ()
  (* and same_typ env equivs subst t1 t2 = *)
  (*   if Util.queryCount() >= 92 then *)
  (*       let l = logger t1 t2 in *)
  (*       let result = same_typ' env equivs subst t1 t2 in *)
  (*       let _  = l result in *)
  (*           result *)
  (*   else same_typ' env equivs subst t1 t2  *)

  and same_typs env equivs subst tl1 tl2 = match tl1,tl2 with 
    | [],[] -> Some subst
    | t1::tl1, t2::tl2 -> 
        (match same_typ env equivs subst t1 t2 with 
          | None -> None
          | Some subst -> same_typs env equivs subst tl1 tl2)
    | _ -> None

  and same_kind env equivs subst k1 k2 = 
    let k2' = 
      let s = List.map (function
                          | Inl(x,y,k) -> Inl(y, bvd_to_typ x k)  
                          | Inr(x,y,t) -> Inr(y, bvd_to_exp x t)) equivs in 
        substitute_kind_typ_or_exp_l k2 s in 
      if equivalent_kinds env k1 k2'
      then Some subst
      else 
        match (unbox k1)(* .u *), (unbox k2)(* .u *)with 
          | Kind_star, Kind_star 
          | Kind_affine, Kind_affine
          | Kind_prop, Kind_prop
          | Kind_erasable, Kind_erasable -> Some subst
          | Kind_tcon(aopt, k1_1, k1_2), Kind_tcon(bopt, k2_1, k2_2) -> 
              bind_opt (same_kind env equivs subst k1_1 k2_1) 
                (fun subst -> 
                   let equivs' = mk_equivs_k aopt bopt k1_1 equivs in 
                   (* match aopt, bopt with  *)
                   (*   | None, None -> same_kind env equivs subst k1_2 k2_2 *)
                   (*   | Some a, Some b ->  *)
                   (*       let ta = bvd_to_typ a k1_1 in *)
                   (*       let k2_2 = substitute_kind k2_2 b ta in *)
                   (*       let env = push_local_binding env (Binding_typ (real_name a, k1_1)) in  *)
                   (*         same_kind env equivs subst k1_2 k2_2 *)
                   (*   | Some a, None *)
                   (*   | None, Some a -> (\* k1_1 and k2_1 are equivalent; so push either *\) *)
                   (*       let env = push_local_binding env (Binding_typ (real_name a, k1_1)) in  *)
                     same_kind env equivs' subst k1_2 k2_2)
                
          | Kind_dcon(xopt, t1, k1), Kind_dcon(yopt, t2, k2) -> 
              bind_opt (same_typ env equivs subst t1 t2) 
                (fun subst -> 
                   let equivs' = mk_equivs xopt yopt t1 equivs in 
                   (* match xopt, yopt with  *)
                   (*   | None, None -> same_kind env equivs subst k1 k2 *)
                   (*   | Some x, Some y ->  *)
                   (*       let ex = bvd_to_exp x t1 in *)
                   (*       let k2 = substitute_kind_exp k2 y ex in *)
                   (*       let env = push_local_binding env (Binding_var (real_name x, t1)) in  *)
                   (*         same_kind env equivs subst k1 k2 *)
                   (*   | Some x, None *)
                   (*   | None, Some x ->  *)
                   (*       let env = push_local_binding env (Binding_var (real_name x, t1)) in  *)
                           same_kind env equivs' subst k1 k2)
          | _ -> None 

  (* and same_kind env equivs subst k1 k2 = *)
  (*     let l = logger_kind k1 k2 in *)
  (*     let result = same_kind' env equivs subst k1 k2 in *)
  (*     let _  = l result in *)
  (*       result *)
            
  and same_exp env equivs subst e1 e2 = (* only implemented for non-function values *)
(*     let _ = pr "Testing equivalence of expressions (%s) and (%s)\n" (Pretty.strExp e1) (Pretty.strExp e2) in *)
    let result = 
      match e1.v, e2.v with
        | Exp_bvar bv1, Exp_bvar bv2 -> 
            if bvvars_equivalent bv1 bv2 equivs then Some subst else None
        | Exp_fvar (fv1, eref1), Exp_fvar (fv2, eref2) -> 
            if fvar_eq fv1 fv2 && eref1=eref2 then Some subst else None
        | Exp_constant c1, Exp_constant c2 -> 
            if Sugar.const_eq c1 c2 then Some subst else None
        | Exp_constr_app (v1, tl, _, el), Exp_constr_app (v2, tl2, _, el2) ->  
            if ((List.length tl) = (List.length tl2) &&
                (List.length el) = (List.length el2) &&
                (fvar_eq v1 v2)) then
              let rec same_typ_list subst = function
                  [] -> Some subst
                | (t1, t2)::tl -> 
                    bind_opt (same_typ env equivs subst t1 t2)
                      (fun subst' -> same_typ_list subst' tl) in
              let rec same_exp_list subst = function
                  [] -> Some subst
                | (e1, e2)::tl -> 
                    bind_opt (same_exp env equivs subst e1 e2)
                      (fun subst' -> same_exp_list subst' tl) in
                bind_opt (same_typ_list subst (List.zip tl tl2))
                  (fun subst' -> 
                     same_exp_list subst' (List.zip el el2))
            else None
              
        | Exp_recd (_, _, _, fne_l_1), Exp_recd (_, _, _, fne_l_2) ->
            if (List.length fne_l_1 = List.length fne_l_2) then
              let rec same_fn_lists subst = function
                  [] -> Some subst
                | ((f1, e1), (f2,e2))::tl -> 
                    let fn_eq = Sugar.lid_equals f1 f2 in 
                      if fn_eq then
                        bind_opt (same_exp env equivs subst e1 e2)
                          (fun subst' -> same_fn_lists subst' tl)
                      else None in
                same_fn_lists subst (List.zip fne_l_1 fne_l_2)
            else None

        | Exp_proj(e1, fn1), Exp_proj(e2, fn2) -> 
            bind_opt (same_exp env equivs subst e1 e2)
              (fun subst' -> if Sugar.lid_equals fn1 fn2 then Some subst' else None)

        | Exp_ascribed(_, _, _), _ 
        | _, Exp_ascribed(_, _, _) -> same_exp env equivs subst (unascribe e1) (unascribe e2)
              
        | _ -> None in
      result  in
    same_typ env [] subst t1 t2 
      (* end unifiable *)
      
and tequiv renv t1 t2 : option<renv> = (* *list<binding>> =  *)
  (* With environment renv, and substitutions of unification variables
     subst; equate t1 and t2 using equality to refine term AND type indices. If
     successful, return a substitution and a list of inferred equalities
     for the equatables in renv AND any free type variables that may appear in t1/t2 *)
  (* S;G |- t1 ~=~ t2 *)
  let thunk () = 
    let is_equatable renv e = 
      let result = 
        match (unascribe e).v with 
            Exp_bvar bv -> 
              let rn = bvar_real_name bv in
                List.exists (fun (bvar:bvvar) -> (bvar_real_name bvar).idText = rn.idText) renv.equatable_xvars 
          | _ -> false in
      let _ = debug_equatable renv e result in  result in
      
    (* This used to preserve an invariant that there be at most one 
       Binding_match assumption for a bvar in the environment. But, that's 
       an unnecessary invariant, which compromises expressiveness. *)
    let gen_eqb renv e1 e2 = 
      let e1, e2 = unascribe e1, unascribe e2 in
      let already_in_renv =
        List.exists (function
                       | Binding_match(e1',e2') -> 
                           (((equalsExp e1 e1') && (equalsExp e2 e2')) ||
                            ((equalsExp e1 e2') && (equalsExp e2 e1')))
                       | _ -> false) renv.eqbs in
        if already_in_renv then Some renv
        else 
          let new_eqb = Binding_match(e1, e2) in
          let renv' = {renv with eqbs=new_eqb::renv.eqbs} in
            Some renv' in
      
    let matches renv e1 e2 : option<renv> = 
      let e1, e2 = unascribe e1, unascribe e2 in    
      let equiv env e1 e2 = 
        (*       pr "Equiv %s = %s called on environment: " (Pretty.strExp e1)  (Pretty.strExp e2);  *)
        let in_eq_class eqc e' = 
          let result = List.exists (fun e'' -> 
                                      if LanguagePrimitives.PhysicalEquality e' e'' then true
                                      else equalsExp (unascribe e') (unascribe e'')) eqc in
            (*         let _ = Printf.printf "%s %s eq class is [%s]\n"  *)
            (*           (Pretty.strExp e') (if result then "IN" else "NOT IN") *)
            (*           (String.concat ";" (List.map Pretty.strExp eqc)) in *)
            result in
        let mk_eq_class eqc matches = 
          (*         let ctr = ref 0 in *)
          let rec mk_eq_class eqc matches =
            let eqc', matches', changed = Tcenv.fold_env env
              (fun (eqc, matches, changed) b -> match b with
                 | Binding_match(e1', e2') -> 
                     (*                    pr "Environment contains %s=%s\n" (Pretty.strExp e1') (Pretty.strExp e2'); *)
                     let t1 = (in_eq_class eqc e1') in
                     let t2 = (in_eq_class eqc e2') in
                     let eqc' = if t1 || t2 then
                       let eqc1 =(if t1 then eqc else (e1'::eqc)) in
                         if t2 then eqc1 else e2'::eqc1 
                     else eqc in
                     let changed' = ((t1 || t2) && not(t1&&t2)) in
                     let matches' = if changed' then 
                       ((* pr "\tAdding to equiv class\n"; *)
                         (e1',e2')::matches) else matches in
                     let changed = changed || changed' in
                       eqc', matches', changed
                 | _ -> eqc, matches, changed) (eqc, matches, false) in
              if not changed then eqc', matches' 
              else (mk_eq_class eqc' matches') in
            mk_eq_class eqc matches in
        let eqc, matches' = mk_eq_class [e1] [] in
          if in_eq_class eqc e2 then
            Some matches'
          else None in
      let env = renv.tcenv in
        match equiv env e1 e2 with
            Some ev -> let ev' = List.map (fun e -> Inr e) ev in Some ({renv with evidence=ev'@renv.evidence})
          | _ -> 
              if (not (in_derefinement_phase env)) && Tcenv.use_solver env then
                (match Tcenv.get_solver env with 
                    | Some s when s.solver_query_equiv env e1 e2 -> Some renv
                    | _ -> None)
              else None in

    let rec refine_exps renv e1 e2 =  (* Only for non functional values *)
      let e1, e2 = unascribe e1, unascribe e2 in
      let thunk () = 
        if is_equatable renv e1 then gen_eqb renv e1 e2 
        else if is_equatable renv e2 then gen_eqb renv e2 e1
        else match matches renv e1 e2 with
          | Some renv' -> Some renv'
          | _ -> 
              match e1.v, e2.v with
                | Exp_bvar bv1, Exp_bvar bv2 when (bvar_real_name bv1).idText = (bvar_real_name bv2).idText -> Some renv
                | Exp_fvar (fv1,eref1), Exp_fvar (fv2,eref2) when (Sugar.text_of_lid fv1.v) = (Sugar.text_of_lid fv2.v) && (eref1=eref2) -> Some renv
                | Exp_constant c1, Exp_constant c2 when Sugar.const_eq c1 c2  -> Some renv
                | Exp_constr_app (v1, tl, elp1, el), Exp_constr_app (v2, tl2, elp2, el2) ->  
                    if ((List.length tl) = (List.length tl2) &&
                        (List.length elp1) = (List.length elp2) &&
                        (List.length el) = (List.length el2) &&
                        (Sugar.lid_equals v1.v v2.v)) then
                      let rec refine_exp_list renv = function
                          [] -> Some renv
                        | (e1, e2)::tl -> 
                            match refine_exps renv e1 e2 with
                                None -> None
                              | Some renv' -> refine_exp_list renv' tl in
                        refine_exp_list renv (List.zip (elp1@el) (elp2@el2))
                    else None

                | Exp_recd (_, _, _, fne_l_1), Exp_recd (_, _, _, fne_l_2) -> 
                    if (List.length fne_l_1 = List.length fne_l_2) then
                      let rec refine_fnl renv = function
                        | [] -> Some renv
                        | ((f1, e1), (f2,e2))::tl -> 
                            if (Sugar.lid_equals f1 f2) then 
                              match refine_exps renv e1 e2 with
                                  None -> None
                                | Some renv' -> refine_fnl renv' tl 
                            else None in
                        refine_fnl renv (List.zip fne_l_1 fne_l_2)
                    else None
                | _ -> None in    
      let result = thunk () in
      (* let _ = pr "Tested equivalence of %s=%s ... result is %A\n (equatable lhs=%A, rhs = %A)"  *)
      (*        (Pretty.strExp e1) (Pretty.strExp e2) (match result with None -> false | _ -> true)  *)
      (*        (is_equatable renv e1)  (is_equatable renv e2) in *)
        result in
      
    let all_teqs renv = 
      let folder out = function 
        | Binding_tmatch(bv,t) -> (bv,t)::out
        | _ -> out in
      let env_eqs = Tcenv.fold_env renv.tcenv folder [] in 
        List.fold_left folder env_eqs renv.eqbs in

    let test_teq t1 t2 = 
      (t1===t2) || (match unifiable renv.tcenv renv.subst t1 t2 with
                      | Some subst' when subst'===renv.subst -> true (* ensures that no spurious unification constraints are introduced *)
                      | _ -> false) in 
      
    let get_eq_class renv t1 = 
      let rec mk_eq_class c = function
        | [] -> c 
        | (bv_lhs,t_rhs)::rest -> 
            let t_lhs = twithsort (Typ_btvar bv_lhs) bv_lhs.sort in
              if ((List.exists (test_teq t_lhs) c) ||
                    (List.exists (test_teq t_rhs) c)) then 
                mk_eq_class (t_lhs::t_rhs::c) rest 
              else 
                mk_eq_class c rest  in 
        mk_eq_class [t1] (all_teqs renv) in
            
    let matches_typ renv t1 t2 = 
      let t1_eqs = get_eq_class renv t1 in
      let result = List.exists (test_teq t2) t1_eqs in
      let renv = 
        if result then 
          let rec mk_ev = function
            | [sing] -> []
            | bv::t::rest -> (Inl(bv,t))::mk_ev rest in 
          let ev = mk_ev t1_eqs in 
            {renv with evidence=ev@renv.evidence} 
        else renv in 
        result, renv in 
      (* assumes that t1 and t2 are not already in the same equivalence class *)
    let rec refine_typ_indices renv t1 t2 = 
      let log () = () in
        (* pr "Induced equality between types %s and %s\n" (Pretty.strTyp t1) (Pretty.strTyp t2) in *)
      let is_equatable a = List.exists (fun b -> bvar_eq a b) renv.equatable_tvars in
      let try_induce_equality t1 t2 = match t1.v with 
        | Typ_btvar a when is_equatable a -> 
            log ();
            Some {renv with eqbs=(Binding_tmatch(a, t2))::renv.eqbs}
        | _ -> None in 
        (match try_induce_equality t1 t2 with 
             None -> try_induce_equality t2 t1
           | success -> success) in
      
    let refine_term_and_typ_indices renv t1 t2 = 
      let tt1 = compress_hard t1 in
      let tt2 = compress_hard t2 in
        debug_rti renv t1 t2;
        let matches, renv = matches_typ renv t1 t2 in
        if matches then Some renv
        else 
          let rec aux tt1 tt2 = 
            let tt1, tt2 = unname_typ tt1, unname_typ tt2 in 
            match tt1.v, tt2.v with
              | Typ_ascribed(_, _), _ 
              | _, Typ_ascribed(_, _) -> tequiv renv (unascribe_typ tt1) (unascribe_typ tt2)
                  
              | Typ_app(t1, t1'), Typ_app(t2, t2') ->
                  bind_opt 
                    (tequiv renv t1 t2) 
                    (fun renv -> 
                       let t1' = apply_subst renv.subst t1' in
                       let t2' = apply_subst renv.subst t2' in
                         match tequiv renv t1' t2' with 
                           | Some renv -> Some renv
                           | None -> refine_typ_indices renv t1' t2')
                    
              | Typ_dep(t1, e1), Typ_dep(t2, e2) -> 
                  bind_opt (tequiv renv t1 t2)
                    (fun renv' -> 
                       let e1 = apply_subst_exp renv'.subst e1 in
                       let e2 = apply_subst_exp renv'.subst e2 in
                         refine_exps renv' e1 e2)

              | Typ_dtuple([(xopt,t1); (_, t2)]), Typ_dtuple([(yopt,t1'); (_, t2')])  -> 
                  bind_opt (tequiv renv t1 t1') 
                    (fun renv -> 
                       let t2 = apply_subst renv.subst t2 in
                       let t2' = apply_subst renv.subst t2' in
                       let t2' = match xopt, yopt with 
                         | Some x, Some y -> 
                             let ex = bvd_to_exp x (apply_subst renv.subst t1) in
                               substitute_exp t2' y ex
                         | _ -> t2' in 
                         tequiv renv t2 t2')
                    
              | Typ_btvar a, _ -> 
                  let c_1 = get_eq_class renv tt1 in
                  let rec matches_some = function
                    | [] -> None
                    | tt1'::rest -> 
                        match tt1'.v with 
                          | Typ_btvar a' when bvar_eq a a' -> matches_some rest (* to avoid looping *)
                          | _ -> 
(*                               let _ = pr "Found eq class for %A\n calling tequiv for %s, %s\n" a (Pretty.strTyp tt1') (Pretty.strTyp tt2) in *)
                              match tequiv renv tt1' tt2 with 
                                | None -> matches_some rest
                                | success -> success in
                    matches_some c_1
              | _, Typ_btvar a -> aux tt2 tt1 
              | _, _ -> None in 
            aux tt1 tt2  in
      
      if t1===t2 
      then Some renv
      else 
        (* let t1, t2 = expand_typ env t1, expand_typ env t2 in *)
        let t1, t2 = whnf t1, whnf t2 in
          match (unifiable renv.tcenv renv.subst t1 t2) with (* first try to show that t1 and t2 are the same *)
            | None -> 
(*                 let _ = pr "Trying to prove equivalence of \n\t%s\nand\t%s\n" (Pretty.strTyp t1) (Pretty.strTyp t2) in *)
                  refine_term_and_typ_indices renv t1 t2 (* if that fails, then try refining indices *)
            | Some subst' -> Some {renv with subst=subst'} in
    profile thunk teq_ctr
      (* end tequiv *)

and equivalent_ev renv t1 t2 : option<renv> = 
  let thunk = fun () -> 
    let t1, t2 = promote_values_affine renv.tcenv t1 t2 in
      match tequiv renv t1 t2 with
          None -> None
        | Some renv -> 
            if List.length renv.subst <> 0 then None
            else Some renv in 
    profile thunk eq_ctr

and equivalent_kinds_ev renv k1 k2 : option<renv> = 
  match (unbox k1)(* .u *), (unbox k2)(* .u *)with 
    | Kind_star, Kind_star 
    | Kind_affine, Kind_affine
    | Kind_prop, Kind_prop
    | Kind_erasable, Kind_erasable -> Some renv
    | Kind_tcon(aopt, k1_1, k1_2), Kind_tcon(bopt, k2_1, k2_2) -> 
         bind_opt (equivalent_kinds_ev renv k1_1 k2_1) (fun renv -> 
            match aopt, bopt with 
                | None, None -> equivalent_kinds_ev renv k1_2 k2_2
                | Some a, Some b -> 
                    let ta = bvd_to_typ a k1_1 in
                    let k2_2 = substitute_kind k2_2 b ta in
                    let env = push_local_binding renv.tcenv (Binding_typ (real_name a, k1_1)) in 
                    let renv = {renv with tcenv=env} in
                      equivalent_kinds_ev renv k1_2 k2_2
                | Some a, None
                | None, Some a -> (* k1_1 and k2_1 are equivalent; so push either *)
                    let env = push_local_binding renv.tcenv (Binding_typ (real_name a, k1_1)) in 
                    let renv = {renv with tcenv=env} in 
                      equivalent_kinds_ev renv k1_2 k2_2)

    | Kind_dcon(xopt, t1, k1), Kind_dcon(yopt, t2, k2) -> 
        bind_opt (equivalent_ev renv t1 t2) (fun renv -> 
            match xopt, yopt with 
              | None, None -> equivalent_kinds_ev renv k1 k2
              | Some x, Some y -> 
                  let ex = bvd_to_exp x t1 in
                  let k2 = substitute_kind_exp k2 y ex in
                  let env = push_local_binding renv.tcenv (Binding_var (real_name x, t1)) in 
                  let renv = {renv with tcenv=env} in 
                    equivalent_kinds_ev renv k1 k2
              | Some x, None
              | None, Some x -> 
                  let env = push_local_binding renv.tcenv (Binding_var (real_name x, t1)) in 
                  let renv = {renv with tcenv=env} in 
                    equivalent_kinds_ev renv k1 k2)
    | _ -> None 

and equivalent (env:env) t1 t2 : bool = 
    let renv = renv_of_env env in
     match equivalent_ev renv t1 t2 with 
        | None -> false
        | Some renv -> (match renv.evidence with [] -> () | e -> pr "Discarding evidence: %A" e); true
and equivalent_kinds (env:env) k1 k2 : bool = 
    let renv = renv_of_env env in 
     match equivalent_kinds_ev renv k1 k2 with 
        | None -> false
        | Some renv -> (match renv.evidence with [] -> () | e -> pr "Discarding evidence: %A" e); true

(* The type conversion relation S;G |- t1 <: t2 *)
let as_ctr = new_counter "TReln.apply_subst (refsub)"
let query_ctr = new_counter "TReln.query (refsub)"
  
let rec convertible (renv:renv) t1 t2 : option<renv> =
  (* d_convertible is covariant on both; callers re-order args as appropriate *)
  let d_convertible (x1Opt, t1_1, t1_2) (x2Opt, t2_1, t2_2) = 
    bind_opt (convertible_deep renv t1_1 t2_1) (fun renv -> 
       let t1_2 = apply_subst renv.subst t1_2 in                                                       
       let t2_2 = apply_subst renv.subst t2_2 in
         match x1Opt, x2Opt with 
           | None, None -> convertible_deep renv t1_2 t2_2
    
           | Some x1, Some x2 -> 
              let env = push_local_binding renv.tcenv (Binding_var (real_name x1, t1_1)) in (* bind at the more specific type *)
              let renv = {renv with tcenv=env} in
              let t2_2 = substitute_exp t2_2 x2 (bvd_to_exp x1 t1_1) in
                convertible_deep renv t1_2 t2_2
           
           | Some x1, None -> 
               let env = push_local_binding renv.tcenv (Binding_var (real_name x1, t1_1)) in 
               let renv = {renv with tcenv=env} in
                 convertible_deep renv t1_2 t2_2

           | None, Some x2 -> 
               let env = push_local_binding renv.tcenv (Binding_var (real_name x2, t1_1)) in 
               let renv = {renv with tcenv=env} in
                 convertible_deep renv t1_2 t2_2) in
              
  let thunk () = 
    let refinement_subtyping renv t1 t2 : option<renv> = 
      let tt1 = unname_typ <| (Tcutil.reduce_typ_delta_beta renv.tcenv t1) in (* compress t1 in *)
      let tt2 = unname_typ <| (Tcutil.reduce_typ_delta_beta renv.tcenv t2) in (* compress t2 in *)
        match tt1.v, tt2.v with
          | Typ_refine(bvd1, t1, phi1, ghost1), Typ_refine(bvd2, t2, phi2, ghost2)
              when ((ghost1 && ghost2) || (ghost1=ghost2 && renv.struct_depth=0)) -> 
              let t2 = whnf t2 in
              let phi2 = whnf phi2 in
                if not (Tcenv.use_solver renv.tcenv) then 
                  tequiv renv tt1 tt2
                else
                  bind_opt (convertible renv tt1 t2) (* NS 11/13/11: This used to be convertible_deep; but we've moved entirely to ghost refinements *)
                    (fun renv ->  
                       let t1 = whnf t1 in
                       let phi1 = whnf phi1 in
                       let name = bvd2.realname in 
                       let tt1' = apply_subst renv.subst tt1 in
                       let phi2' = apply_subst renv.subst phi2 in 
                       let env' = push_local_binding renv.tcenv (Binding_var (name, tt1'))in
                       (* let _ = pr "*********Trying to prove query: %s\n where bound name is %s\n and LHS is %s\n" *)
                       (*   (Pretty.strTyp phi2') *)
                       (*   (Pretty.strBvd bvd2) *)
                       (*   (Pretty.strTyp tt1') in *)
                         (* let _ = pr "Current substitution is: %s\n" *)
                         (*   (String.concat ";\n" *)
                         (*      (renv.subst |> List.map (fun (uvks, topt) -> spr "[%s] -> %s" (String.concat "; " (List.map (fun (uv, _) -> spr "%d" (Unionfind.uvar_id uv)) uvks))  *)
                         (*                                 (match topt with None -> "-" | Some t -> (Pretty.strTyp t))))) in *)
                       let env' = match current_value env' with 
                         | None -> 
                             (* let _ = pr "Evaluating query WITHOUT equality, no current value\n" in *)
                               if renv.struct_depth = 0 
                               then raise Impos 
                               else env'
                         | Some v -> 
                             let ebv = bvd_to_exp bvd2 tt1' in 
                               if is_value v then 
                                 let v = apply_subst_exp renv.subst v in
                                 let b = Binding_match (ebv, v) in
                                 (* let _ = pr "Evaluating query with equality boundvar = %s : %s\n" (Pretty.strExp v) (Pretty.strTyp v.sort) in *)
                                   push_local_binding env' b
                               else 
                                 (* let _ = pr "Evaluating query without equality; current term %s : %s is not a value\n" (Pretty.strExp v) (Pretty.strTyp v.sort) in *)
                                   env' in
                         (match Tcenv.get_solver env' with 
                            | Some s -> if s.solver_query env' phi2' then Some renv else None
                            | _ -> None))
                  
          | Typ_refine(bvd1, t1, phi1, ghost), _  when ghost || renv.struct_depth=0 -> convertible renv t1 tt2 
              
          | _, Typ_refine(x, t2, phi2, ghost) when ghost || renv.struct_depth=0 -> 
              let fn = genident None in
              let t1' = twithsort (Typ_refine(mkbvd(fn,fn), tt1, true_typ, ghost)) tt1.sort in
                convertible renv t1' tt2 
                  
          (* Structural rules for ghost refinements *)
          | Typ_fun(x1Opt, t1_1, t1_2), Typ_fun(x2Opt, t2_1, t2_2) -> 
              d_convertible (x1Opt, t2_1, t1_2) (x2Opt, t1_1, t2_2) (* note contravariance in arg *)

          | Typ_dtuple([(x1Opt, t1_1); (_, t1_2)]), Typ_dtuple([(x2Opt, t2_1); (_, t2_2)]) -> 
              d_convertible (x1Opt, t1_1, t1_2) (x2Opt, t2_1, t2_2) (* note covariance in both *)

          | Typ_lam(x1, t1_1, t1_2), Typ_lam(x2, t2_1, t2_2) -> 
              d_convertible (Some x1, t2_1, t1_2) (Some x2, t1_1, t2_2) (* note contravariance in arg *)

          | Typ_univ(a1, k1, f1, t1), Typ_univ(a2, k2, f2, t2) -> 
              bind_opt (kind_convertible renv k2 k1) (fun renv -> 
              let env = push_local_binding renv.tcenv (Binding_typ (real_name a2, k2)) in 
              let f1 = List.map (apply_subst renv.subst) f1 in
              let f2 = List.map (apply_subst renv.subst) f2 in
                if not (formula_implication env f2 f1) 
                then None 
                else
                  let t1 = apply_subst renv.subst t1 in                                                       
                  let t2 = apply_subst renv.subst t2 in                     
                  let renv = {renv with tcenv=env} in
                  let t1 = substitute t1 a1 (bvd_to_typ a2 k2) in 
                    convertible_deep renv t1 t2)

          | Typ_tlam(a1, k1, t1), Typ_tlam(a2, k2, t2) -> 
              bind_opt (kind_convertible renv k2 k1) (fun renv -> 
              let t1 = apply_subst renv.subst t1 in                                                       
              let t2 = apply_subst renv.subst t2 in                     
              let env = push_local_binding renv.tcenv (Binding_typ (real_name a2, k2)) in 
              let renv = {renv with tcenv=env} in
              let t1 = substitute t1 a1 (bvd_to_typ a2 k2) in 
                convertible_deep renv t1 t2)

          | Typ_affine t1, Typ_affine t2 -> 
              convertible_deep renv t1 t2 

          | Typ_ascribed(_, _), _ 
          | _, Typ_ascribed(_, _) -> convertible renv (unascribe_typ t1) (unascribe_typ t2)
              
          | _ -> None in 
    let t1, t2 = promote_values_affine renv.tcenv t1 t2 in
      match tequiv renv t1 t2 with (* try unification/equivalence first *)
        | None -> profile (fun () -> 
                             (* let _ = pr "Refinement subtyping for %s <= %s\n" (Pretty.strTyp t1) (Pretty.strTyp t2) in  *)
                               refinement_subtyping renv t1 t2) refsub_ctr  (* if that fails, try refinement implication *)
        | Some renv -> Some renv in
    profile thunk convert_ctr
      
and convertible_deep renv t1 t2 = 
  let incr_depth renv = {renv with 
                           struct_depth=renv.struct_depth + 1; 
                           tcenv=clear_current_value renv.tcenv} in
  let decr_depth renv = 
    let sd = renv.struct_depth - 1 in 
      match sd, renv.curval with 
        | 0, Some e -> {renv with struct_depth=sd; tcenv=set_current_value renv.tcenv e}
        | _ -> {renv with struct_depth=sd} in
    match (convertible (incr_depth renv) t1 t2) with
      | Some renv -> Some (decr_depth renv)
      | None -> (* pr "Failed to prove convertibility of %s and %s\n" (Pretty.strTyp t1) (Pretty.strTyp t2);  *)None 

    (* bind_opt (convertible (incr_depth renv) t1 t2)  *)
    (*   (fun renv -> Some (decr_depth renv)) *)

      
and kind_convertible renv k1 k2 : option<renv> =
    let aux renv k1 k2 = match k1(* .u *), k2(* .u *)with 
      | Kind_affine, Kind_erasable
      | Kind_star, Kind_erasable
      | Kind_prop, Kind_erasable -> Some renv
      | Kind_dcon(xopt, t1, k1), Kind_dcon(yopt, t2, k2) -> 
          bind_opt (convertible_deep renv t2 t1) (fun renv -> 
          let k1 = apply_subst_kind renv.subst k1 in
          let k2 = apply_subst_kind renv.subst k2 in
            match xopt, yopt with 
              | None, None -> kind_convertible renv k1 k2
              | Some x, Some y -> 
                  let ey = bvd_to_exp y t2 in
                  let k1 = substitute_kind_exp k1 x ey in
                  let env = push_local_binding renv.tcenv (Binding_var (real_name y, t2)) in 
                  let renv = {renv with tcenv=env} in
                    kind_convertible renv k1 k2
              | Some x, None -> 
                  let env = push_local_binding renv.tcenv (Binding_var (real_name x, t1)) in
                  let renv = {renv with tcenv=env} in
                    kind_convertible renv k1 k2
              | None, Some y -> 
                  let env = push_local_binding renv.tcenv (Binding_var (real_name y, t2)) in
                  let renv = {renv with tcenv=env} in
                    kind_convertible renv k1 k2)

      | Kind_tcon(aopt, k1, k2), Kind_tcon(bopt, k1', k2') -> 
          bind_opt (kind_convertible renv k1' k1) (fun renv -> 
          let k2 = apply_subst_kind renv.subst k2 in
          let k2' = apply_subst_kind renv.subst k2' in
            match aopt, bopt with 
              | None, None -> kind_convertible renv k2 k2'
              | Some a, Some b -> 
                  let tb = bvd_to_typ b k1' in
                  let k2 = substitute_kind k2 a tb in
                  let env = push_local_binding renv.tcenv (Binding_typ (real_name b, k1')) in 
                  let renv = {renv with tcenv=env} in
                    kind_convertible renv k2 k2'
              | Some a, None -> 
                  let env = push_local_binding renv.tcenv (Binding_typ (real_name a, k1)) in 
                  let renv = {renv with tcenv=env} in
                    kind_convertible renv k2 k2'
              | None, Some b -> 
                  let env = push_local_binding renv.tcenv (Binding_typ (real_name b, k1')) in 
                  let renv = {renv with tcenv=env} in
                    kind_convertible renv k2 k2')
      | _ -> (* kind equivalence already checked *) 
          None in 
      match (equivalent_kinds_ev renv k1 k2) with 
        | None -> aux renv k1 k2 
        | Some renv -> Some renv
        
let force_kind_convertible renv k1 k2 : option<evidence> =
    match kind_convertible renv k1 k2 with 
        | Some renv -> unify_subst_vars renv.subst; Some renv.evidence
        | _ -> None

let next = 
  let ctr = ref 0 in 
    (fun () -> incr ctr; !ctr)

//val convertible_ev: Tcenv.env -> typ -> typ -> option<subst * evidence>
let convertible_ev env t1 t2 = 
  if t1 === t2 
  then Some ([], [])
  else 
    let renv = renv_of_env env in
    (* let _ = pr "Trying to prove conversion between \n\t%s and\n\t%s\n" (Pretty.strTyp t1) (Pretty.strTyp t2) in *)
    (* let _  = match Tcenv.current_value env with  *)
    (*   | None -> () *)
    (*   | Some v -> pr "Current value is %s\n" (Pretty.strExp v) in *)
      bind_opt (convertible renv t1 t2) (fun renv -> Some (renv.subst, renv.evidence)) 

//val kind_convertible_ev : Tcenv.env -> kind -> kind -> option<subst * evidence>
let kind_convertible_ev env k1 k2 = 
    let renv = renv_of_env env in
     bind_opt (kind_convertible renv k1 k2) (fun renv -> Some (renv.subst, renv.evidence))

//val force_kind_convertible_ev : Tcenv.env -> kind -> kind -> (bool * evidence)
let force_kind_convertible_ev env k1 k2 = 
    let renv = renv_of_env env in
     force_kind_convertible renv k1 k2

let instantiable env equatable_xvars equatable_tvars t1 t2 = 
  let thunk = fun () -> 
    let renv = mk_renv equatable_xvars equatable_tvars env [] in 
    let t1, t2 = promote_values_affine env t1 t2 in
      bind_opt 
        (tequiv renv t1 t2)
        (fun renv -> Some (renv.subst, renv.eqbs)) in
    profile thunk inst_ctr
      
let find_all_match_assumptions env : list<binding> = 
  let finder out b = match b with
    | Binding_match (e1, e2) -> b::out
    | _ -> out in 
    Tcenv.fold_env env finder []
    
let equiv env t1 t2 = 
  let renv = renv_of_env env in 
  let t1, t2 = promote_values_affine env t1 t2 in
  bind_opt (tequiv renv t1 t2) (fun renv -> Some renv.subst)
    
let equivalent_with_evidence env t1 t2 = 
(*   Printf.printf "Testing equivalence of types %s and %s\n" (Pretty.strTyp t1) (Pretty.strTyp t2); *)
  let renv = renv_of_env env in 
  let t1, t2 = promote_values_affine env t1 t2 in
    bind_opt (tequiv renv t1 t2) (fun renv -> 
          if List.length renv.subst <> 0 then raise Impos
          else Some renv.evidence)

let equivalent_kinds_with_evidence env k1 k2 = 
    let renv = renv_of_env env in 
    match equivalent_kinds_ev renv k1 k2 with 
        | None -> None
        | Some renv -> Some renv.evidence

let equivalent_with_equations env eq_xvars t1 t2 = 
  let renv = mk_renv eq_xvars [] env [] in 
  let t1, t2 = promote_values_affine env t1 t2 in
    match tequiv renv t1 t2 with
        None -> (* let ma = find_all_match_assumptions env in print_any ("Match assumptions:", ma);  *)None
      | Some renv -> 
          if List.length renv.subst <> 0 then raise Impos
          else Some renv.eqbs

let new_uvar env k (r:Range.range) =
  let wf typ k =
    let renv = renv_of_env env in
      match kind_convertible renv typ.sort k with 
        | Some {subst=[]} -> 
            (match freevars_not_in_env env typ with 
               | [],[] -> true
               | tvs, xvs ->
                   (* let _ = pr "Free variable test failed for unification\n %s \nFTVs %s\nFXVs %s\nIn environment [%s]\n" *)
                   (*   (typ.ToString()) *)
                   (*   (String.concat "," (List.map Pretty.strBtvar tvs)) *)
                   (*   (String.concat "," (List.map Pretty.strBvar xvs))  *)
                   (*   (Tcenv.bindings env) in *)
                   false)
        | Some {subst=s} -> 
            let _ = pr "Unexpected substitution from kind_convertible %s, %s: %A" (Pretty.strKind typ.sort) (Pretty.strKind k) s in 
              raise Impos 
        | None -> false in
  let uvb = Unionfind.fresh (Uvar wf) in
    twithsort (Typ_uvar (uvb, k)) k


let do_instantiate_typ env typ actuals_ck_opt : (list<formula> * typ * list<btvdef*typ>)=  
  let rec n_typ_params out forms tt = match tt.v with
      Typ_univ (bvd, k, f, t) -> 
        n_typ_params ((bvd, k, tt.p)::out) (f::forms) t 
    | _ -> List.rev out, List.rev forms, tt in
  let typ_subst_l t subst = 
    List.fold_left (fun ityp (bvd, actual) -> substitute ityp bvd actual) t subst in 
  let t_formals, formulas_l, mono_typ = n_typ_params [] [] typ in
  let formulas = List.flatten formulas_l in 
    match t_formals, actuals_ck_opt, formulas with
      | [], None, [] -> [], typ, []  
      |  _, None, _ ->       (* need to infer instantiation; constraints not allowed *)
           let bvd_uvars = 
             List.fold_left (fun bvd_uvars (bvd, k, r) -> 
                               let k' = substitute_kind_l k bvd_uvars in
                               let uv = new_uvar env k' r in
                                 (bvd,uv)::bvd_uvars) [] t_formals in
           let inst_typ = substitute_l mono_typ bvd_uvars in 
           let inst_formulas = formulas |> List.map (fun f -> substitute_l f bvd_uvars) in 
             inst_formulas, inst_typ, List.rev bvd_uvars
      | _, (Some(t_actuals, check_kind)), _ when (List.length t_formals) = (List.length t_actuals) -> (* user-provided inst *)
          let bvd_actuals = 
            List.fold_left2 (fun bvd_actuals actual (bvd, formal_kind, _) -> 
                               let formal_kind = substitute_kind_l formal_kind bvd_actuals in
                               let actual = check_kind actual formal_kind in
                                 (bvd,actual)::bvd_actuals) [] t_actuals t_formals in
          let res = typ_subst_l mono_typ bvd_actuals in
          let formulas = List.map (fun f -> typ_subst_l f bvd_actuals) formulas in 
          let _ = match formulas, Tcenv.get_solver env with 
            | [], _ -> ()
            | _, Some s -> 
                List.iter (fun f -> 
                             if s.solver_query env f
                             then ()
                             else raise (Err (spr "Unable to prove instantiation constraint: %s\n" (Pretty.strTypAsFormula f)))) 
                  formulas
            | _,_ -> raise (Err "No solver---unable to prove instantiation constraints") in 
            [], res, List.rev bvd_actuals
      | _ -> raise (Err (spr "Unexpected type arguments; or, unable to infer instantiation of type arguments:\n%s" (Pretty.strTyp typ)))
          
let instantiate_kind env t k = 
    let rec aux t = function
        | Kind_tcon(Some bvd, karg, k) -> 
             let uv = new_uvar env karg t.p in
             let k = substitute_kind k bvd uv in
             let t' = twithinfo (Typ_app(t, uv)) k t.p in
                aux t' k 
        | k -> t, k in
    aux t k
      
let instantiate_typ_gen_constraints env typ = do_instantiate_typ env typ None

let instantiate_typ env typ = 
  match do_instantiate_typ env typ None with 
    | ([], t, args) -> t,args
    | _ -> raise (Err "Unexpected type constraints during instantiation")

let instantiate_typ_with_actuals env typ (actuals:list<typ>) ck = 
  match do_instantiate_typ env typ (Some(actuals, ck)) with 
    | ([], t, args) -> t,args
    | _ -> raise (Err "Unexpected type constraints during instantiation")

let alpha_equiv env t1 t2 = 
  match unifiable env [] t1 t2 with 
    | Some [] -> true
    | _ -> false

let try_instantiate_final_typ env tps to_inst with_t = 
  let env', tparams = 
    List.fold_left (fun (env, abductibles) -> function
                      | Tparam_term(bvd, t) -> 
                          let env' = push_local_binding env (Binding_var (real_name bvd, t)) in
                          let abductibles' = (bvd_to_bvar_s bvd t)::abductibles in
                            env', abductibles'
                      | _ -> raise Impos) (env, []) tps in
  let rec inst_final_typ env abductibles t = match t.v with (* don't try to instantiate when the function is dependent *)
    | Typ_affine({v=Typ_fun (None, t1, t2)})
    | Typ_fun (None, t1, t2) -> inst_final_typ env abductibles t2

    | Typ_affine({v=Typ_fun (Some bvd, t1, t2)})
    | Typ_fun (Some bvd, t1, t2) -> 
        let env' = push_local_binding env (Binding_var (real_name bvd, t1)) in
        let abductibles' = (bvd_to_bvar_s bvd t1)::abductibles in
          inst_final_typ env' abductibles'  t2
    | _ -> 
        let env = clear_solver env in (* set_solver_flag env false in *)
        let do_instantiate env abductibles t with_t =
          (match instantiable env abductibles [] t with_t with
                 None -> 
                   false, (to_inst, [])
               | Some (s, matches) -> 
                   let _ = unify_subst_vars s in 
                   let out, substs = List.fold_left 
                     (fun (out, substs) -> function
                          Binding_match({v=Exp_bvar bv1;sort=_;p=_}, e) -> 
                            if List.exists (bvar_eq bv1) tparams then 
                              let bvd1 = bvar_to_bvd bv1 in
                              let out = substitute_exp out bvd1 e in
                                (out, (bvd1, e)::substs)
                            else out, substs
                        | _ -> raise Impos) (to_inst, []) matches in
                     true, (out, substs)) in
            match do_instantiate env abductibles t with_t with
                true, (t, substs) -> t, substs
              | false, (out, _) -> (* try once more, by looking inside affine type *)
                  match t.v, with_t.v with
                      Typ_affine _, Typ_affine _ -> out, []  (* cannot do anything further *)
                    | _, Typ_affine with_t' -> 
                        (match current_value env with
                           | Some v when is_non_variable_value env v -> 
                               (* try to instantiate underneath a !, relying on value promotion to fix things up later *)
                               let _, (out, substs) = do_instantiate env abductibles t with_t' in 
                                 out, substs
                           | _ -> out, [])
                    | _ -> out, []  (* cannot do anything further *) in
    profile (fun () -> inst_final_typ env' tparams to_inst) (new_counter "Try Inst Final Type")

