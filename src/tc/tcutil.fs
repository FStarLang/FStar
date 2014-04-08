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

module Microsoft.FStar.Tc.Util

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util
open Microsoft.FStar.Tc.Env
        
let handle_err warning ret e = 
  match e with
    | Not_found_binding (env, Inl t) -> 
        Util.print_string (Util.format1 "(Compiler bug?) Type name not found: %s\n" (Print.typ_to_string t));
        ret
    | Not_found_binding (env, Inr e) -> 
        Util.print_string (Util.format1 "(Compiler bug?) Variable not found: %s\n" (Print.exp_to_string e));
        ret
    | Error(msg, r) ->
        Util.print_string (Util.format3 "%s : %s : %s\n" (Range.string_of_range r) (if warning then "Warning" else "Error") msg);
        ret
    | NYI s -> 
        Util.print_string (Util.format1 "Feature not yet implemented: %s" s); 
        ret
    | _ -> raise e
    
let terr env t1 t2 exp = 
  let msg = 
     Util.format3 "Expected an expression of type:\n\n%s\n\nbut got (%s):\n\n%s"
      (Print.typ_to_string t1) 
      (Print.exp_to_string exp)
      (Print.typ_to_string t2) in
    raise (Error (msg, exp.p))

let t_unit = Typ_const (Util.withsort Const.unit_lid Kind_star)
let t_bool = Typ_const (Util.withsort Const.bool_lid Kind_star)
let t_int = Typ_const (Util.withsort Const.int_lid Kind_star)
let t_string = Typ_const (Util.withsort Const.string_lid Kind_star)
let t_float = Typ_const (Util.withsort Const.float_lid Kind_star)

let typing_const (_:env) = function
  | Const_unit -> t_unit
  | Const_bool _ -> t_bool
  | Const_int32 _ -> t_int
  | Const_string _ -> t_string
  | Const_float _ -> t_float
  | _ -> raise (NYI "Unsupported constant")

let push_tparams env tps = 
  List.fold_left (fun env tp -> 
                    let binding = match tp with
                      | Tparam_typ (a, k) -> Binding_typ (a, k) 
                      | Tparam_term (x, t) -> Binding_var (x, t) in
                      push_local_binding env binding) env tps 

let is_xvar_free (x:bvvdef) t = 
  let _, xvs = Util.freevars_typ t in
  Util.for_some (fun (bv:bvvar) -> Util.bvd_eq bv.v x) xvs

let is_tvar_free (a:btvdef) t = 
  let tvs, _ = Util.freevars_typ t in
  Util.for_some (fun (bv:btvar) -> Util.bvd_eq bv.v a) tvs 


let new_kvar env =
  let wf k () =
    let tvs, xvs = Util.freevars_kind k in 
    let tvs', xvs' = Env.idents env in
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    Util.forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
  Kind_uvar (Unionfind.fresh (Uvar wf))

let kind_equiv env k1 k2 = failwith "NYI"

let new_tvar env k =
  let wf t k =
    let tvs, xvs = Util.freevars_typ t in 
    let tvs', xvs' = Env.idents env in 
    let eq bv bvd = Util.bvd_eq bv.v bvd in
    Util.forall_exists eq tvs tvs' && Util.forall_exists eq xvs xvs' in
  Typ_uvar (Unionfind.fresh (Uvar wf), k)

let typ_equiv env t1 t2 = failwith "NYI"
let subtype env t1 t2 = failwith "NYI"
let destruct_function_typ env t : option<typ> = failwith "NYI"

let unify uv t = Unionfind.change uv (Fixed (alpha_convert t))

let check_unify (uv,(k:kind)) t = 
  let occurs uv t = Util.for_some (Unionfind.equivalent uv) (uvars_in_typ t) in
    match Unionfind.find uv with 
      | Uvar wf -> 
          if wf t k
          then 
            (if not (occurs uv t)
             then (unify uv t; None)
             else Some "Unification fails occurs check")
          else Some "Unification fails kinding check"
      | t -> failwith "impossible"


//          
//
//type subst = list<(list<uvar*kind> * option<typ>)>         
//let unify_subst_vars (subst:subst) = 
//  let unify_eq_class (uvl, topt) = match uvl with 
//    | [] -> raise (NYI "Unexpected empty equivalence class")
//    | (uv,_)::tl  -> 
//        List.iter (fun (uv',_) -> Unionfind.union uv uv') tl;
//        match topt with
//          | None -> ()
//          | Some t -> unify uv t in
//    List.iter unify_eq_class subst
//
//let mkTypApp t1 t2 = match t1.sort(* .u *)with 
//  | Kind_tcon(_, _, k2) -> 
//      twithsort (Typ_app(t1, t2)) (open_kind t1.sort t2)
//  | _ -> failwith "impossible"
//
//let mkTypDep t v = match t.sort(* .u *)with 
//  | Kind_dcon(_, _, k2) -> 
//      twithsort (Typ_dep(t, v)) (open_kind_with_exp t.sort v)
//  | _ -> failwith "impossible"
//
//let rec reduce_typ_delta_beta tenv t = 
//  let rec aux t = 
//    let t = expand_typ tenv t in 
//      match t.v with 
//        | Typ_dep(t1orig, e) -> 
//            let t1 = aux t1orig in
//              (match t1.v with 
//                 | Typ_lam(x, t1_a, t1_r) -> 
//                     let t1_r' = substitute_exp t1_r x e in 
//                       aux t1_r'
//                 | _ -> 
//                     if t1orig===t1 
//                     then t
//                     else twithinfo (Typ_dep(t1, e)) t.sort t.p)
//        | Typ_app(t1orig, t2orig) -> 
//            let t1 = aux t1orig in
//            let t2 = aux t2orig in
//              (match t1.v with 
//                 | Typ_tlam(a, t1_a, t1_r) -> 
//                     let t1_r' = substitute t1_r a t2 in
//                       aux t1_r'
//                 | _ -> 
//                     if t1orig===t1 && t2orig===t2 
//                     then t
//                     else twithinfo (Typ_app(t1, t2)) t.sort t.p)
//        | _ -> t in
//    aux t
//
//let rtdb tenv t = 
//  let rec rtdb i tenv t = 
//    let rec aux smap t =
//      let t = expand_typ tenv t in 
//        match t.v with 
//          | Typ_dep(t1orig, e) -> 
//              let smap, t1 = aux smap t1orig in
//                (match t1.v with 
//                   | Typ_lam(x, t1_a, t1_r) -> 
//                       let smap = Inr(x,(substitute_exp_typ_or_exp_l e smap))::smap in 
//                         aux smap t1_r
//                   | _ -> 
//                       if t1orig===t1 
//                       then smap, t
//                       else smap, twithinfo (Typ_dep(t1, e)) t.sort t.p)
//          | Typ_app(t1orig, t2orig) -> 
//              let smap, t1 = aux smap t1orig  in
//              let smap, t2 = aux smap t2orig in
//                (match t1.v with 
//                   | Typ_tlam(a, t1_a, t1_r) -> 
//                       let smap = Inl(a, (substitute_l_typ_or_exp t2 smap))::smap in 
//                         aux smap t1_r
//                   | _ -> 
//                       if t1orig===t1 && t2orig===t2 
//                       then smap, t
//                       else smap, twithinfo (Typ_app(t1, t2)) t.sort t.p)
//          | _ -> smap, t in
//    let smap, t = aux [] t in 
//      match smap with 
//        | [] -> (* pr "rtdb %d noop\n" i; *)
//            t
//        | _ -> 
//            (* pr "rtdb %d subst %d\n" i (List.length smap);  *)
//            rtdb (i+1) tenv (substitute_l_typ_or_exp t smap) in 
//    rtdb 0 tenv t
//          
//let generalize_with_constraints env forms t e : (list<formula> * typ * exp) = 
//  if not (is_value e) then forms, t, e 
//  else
//    let find uv sub = List.tryFind (fun (uv', _) -> Unionfind.equivalent uv uv') sub in
//    let uvars_in_env = Tcenv.uvars_in_env env in
//    let is_uvar_in_env uv = match List.tryFind (fun uv' -> Unionfind.equivalent uv uv') uvars_in_env with 
//      | None -> false
//      | Some _ -> true in
//    let subst_and_collect_uvars_typ sub () t = match t with 
//      | Typ_uvar (uv, k) -> 
//          (match find uv sub with
//             | Some (_,tv) -> sub, tv, None
//             | _ -> 
//                 if is_uvar_in_env uv then sub, t, None
//                 else
//                   let fn = new_bvd None in 
//                   let btv = (Typ_btvar (bvwithinfo fn k dummyRange))  in
//                     (uv, btv)::sub, btv, None)
//      | _ -> sub, t, None in
//    let exp_folder_noop env () e = (env,e) in
//    let sub, (tsub::forms_sub) = typs_fold_map subst_and_collect_uvars_typ exp_folder_noop (fun _ e -> e) Absyn.ignore_env [] () (t::forms) in
//    let tvars = sub |> List.map (fun (uv, ((Typ_btvar btv) as tv)) -> 
//                                   let _ = unify uv (twithsort tv btv.sort) in 
//                                     (tv, fst <| freevarsKind btv.sort)) in
//    let tvars = tvars |> List.sortWith (fun (Typ_btvar tv1, fv1) (Typ_btvar tv2, fv2) -> 
//                                          if fv1 |> List.exists (bvar_eq tv2) then 1
//                                          else if fv2 |> List.exists (bvar_eq tv1) then -1
//                                          else String.compare ((bvar_real_name tv1).idText) ((bvar_real_name tv2).idText)) in
//    let residue, univ_typ, Lambda_e = List.fold_right 
//      (fun (tv, _) (residue, out_typ, Lambda_e) -> 
//         let forms, residue = match residue with 
//           | [] -> [], []
//           | f -> f, [] in (* TODO: optimize and simplify constraints --- only include forms with the appropriate variables *)
//           match tv with 
//             | Typ_btvar btv -> 
//                 let out_typ = twithsort (Typ_univ (btv.v, btv.sort, forms, out_typ)) Kind_star  in
//                 let Lambda_e = ewithinfo (Exp_tabs (btv.v, btv.sort, forms, Lambda_e)) out_typ Lambda_e.p in
//                   (residue, out_typ, Lambda_e)
//             | _ -> failwith "impossible") tvars (forms_sub, tsub, e) in
//      residue, univ_typ, Lambda_e
//
//let generalize env t e = 
//  match generalize_with_constraints env [] t e with 
//    | ([], t, e) -> t, e
//    | _ -> failwith "impossible"
