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

module Microsoft.FStar.ToSMT.Env
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Term

type tbinding =
  | Var_binding of (bvvdef * typ * sort)
  | Tvar_binding of (btvdef * knd * sort)
  | Formula of tbinding

let rec tbinding_name = function
  | Var_binding(x, _, _) -> Print.strBvd x
  | Tvar_binding(x, _, _) -> Print.strBvd x
  | Formula t -> tbinding_name t
  
type transenv = {gamma:list<tbinding>; 
                 tcenv:Tc.Env.env;}

let mk_transenv tcenv = {gamma=[]; tcenv=tcenv}
let push te b = {te with gamma=b::te.gamma}
let push_formula_var te b = push te (Formula b)  

//let lookupTypConst tenv tc = 
//  try 
//    if lid_equals tc.v Const.unit_lid then unitType
//    else if Sugar.lid_equals tc.v Const.bool_lid then boolType
//    else if Sugar.lid_equals tc.v Const.int_lid then intType
//    else if Sugar.lid_equals tc.v Const.string_lid then strType
//    else if Sugar.lid_equals tc.v Const.float_lid then floatType
//    else
//      let k = Tcenv.lookup_typ_const tenv.tcenv tc in
//        FreeV(typeNameOfLid tc.v, Type_sort)
//  with _ -> raise (Z3Encoding (spr "Type constant %s not found" (Pretty.sli tc.v)))
//
//let lookupBvar tenv bv = 
//  let rec aux bix ix phi_ix = function 
//    | (Var_binding(bvd,k,_,tref))::tl -> 
//        if bvd_eq_bv bvd bv then 
//          match !tref with
//            | Some tm -> 
//              (match tm.tm with
//                | BoundV(j, s, x, r) -> BoundV(j + phi_ix, s, x, r)
//                | _ -> tm)
//            | _ -> mk_Exp_bvar ix
//        else aux bix (ix + 1) phi_ix tl
//          
//    | (Tvar_binding _)::tl ->
//        aux bix (ix + 1) phi_ix tl
//                  
//    | Formula(Var_binding(bvd,l,s,tref))::tl ->           
//        if bvd_eq_bv bvd bv then 
//          match !tref with 
//            | None -> BoundV(phi_ix, s, string_of_bvd bvd, tref)
//            | Some tm -> tm
//        else aux bix ix (phi_ix + 1) tl
//
//    | Formula(Tvar_binding _)::tl -> 
//        aux bix ix (phi_ix + 1) tl
//          
//    | (BVar_binding(bvd,_))::tl -> 
//        if bvd_eq_bv bvd bv then 
//          mk_Exp_bvar bix
//        else aux (bix + 1) ix phi_ix tl 
//
//    | (BTvar_binding _)::tl -> 
//        aux (bix + 1) ix phi_ix tl 
//          
//    | [] -> 
//        (match findOpt (function (Inr bvd,_,_,_) -> bvd_eq_bv bvd bv | _ -> false) tenv.holes with
//           | Some (_, i,s,_) -> withSort s <| Hole i
//           | _ -> 
//               let k = Tcenv.lookup_bvar tenv.tcenv bv in
//                 FreeV(funNameOfBvar bv, Term_sort)) in
//    try aux 0 0 0 tenv.gamma 
//    with _ -> raise (Z3Encoding (spr "Term variable %s not found;\n bindings are (%s)\n" (Pretty.strBvar bv) (names tenv)))
//
//let lookupFvar tenv fv = 
//  try 
//    let _ = Tcenv.lookup_fvar tenv.tcenv fv in
//      FreeV(funNameOfFvar fv.v, Term_sort)
//  with _ -> raise (Z3Encoding (spr "Free variable %s not found" (Pretty.sli fv.v)))
//
//let fieldProjector tenv t fn = 
//  let rec pos ix = function 
//    | (fn', _)::tl when Sugar.lid_equals fn fn' -> ix
//    | _::tl -> pos (ix+1) tl 
//    | [] -> raise Not_found in
//  try 
//    if AbsynUtils.isTupleProj fn then 
//      let ix = if fn=Const.tuple_proj_one then 2 else 3 in (* two type arguments come first *)
//        match (Tcenv.expand_typ tenv.tcenv t).v with
//          | Typ_dtuple([(_, t1); (_, t2)]) -> 
//              let constrLid = funNameOfConstr (Const.tuple_data_lid t1.sort t2.sort) in
//                mkProj constrLid ix
//          | _ -> raise Impos
//    else
//      let (lid, _, tps, {v=Typ_record(fn_t_l, _)}) = Tcenv.lookup_record_typ tenv.tcenv fn in
//      let b = List.length tps in 
//      let offset = pos 0 fn_t_l in
//      let projName = mkProj (recordConstrName lid) (b + offset) in
//        projName
//  with _ -> raise (Z3Encoding (spr "Field name %s not found" (Pretty.sli fn)))
//  
//let tcenv tenv = 
//  List.fold_left (fun env -> function
//                    | BVar_binding(x,t)
//                    | Var_binding(x,t,_,_)
//                    | Formula(Var_binding(x,t,_,_)) -> 
//                        Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, t))
//                    | BTvar_binding(a,k)
//                    | Tvar_binding(a,k,_,_)
//                    | Formula(Tvar_binding(a,k,_,_)) -> 
//                        Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(a.realname, k))) tenv.tcenv tenv.gamma
