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

module Microsoft.FStar.Z3Encoding.Env
open Microsoft.FStar
open Z3Encoding.Basic
open Util
open Absyn
open AbsynUtils
open Term
open Profiling 

exception Z3Encoding of string

type tbinding<'a> = 
  | Var_binding of (bvvdef * typ * sort * termref<'a>)
  | Tvar_binding of (btvdef * kind * sort * termref<'a>)
  | Formula of tbinding<'a>
  | BVar_binding of bvvdef * typ
  | BTvar_binding of btvdef * kind

let prname x r = match !r with 
    | None -> string_of_bvd x 
    | Some tm -> spr "(%s --> %s)" (string_of_bvd x) (tm.ToString())
let rec tbinding_name = function
  | Var_binding(x, _, _, r) -> prname x r
  | Tvar_binding(x, _, _, r) -> prname x r
  | Formula t -> tbinding_name t
  | BVar_binding(x, _) -> string_of_bvd x
  | BTvar_binding(x, _) -> string_of_bvd x
  
type holes = list<Disj<btvdef,bvvdef> * Term.var * sort * Disj<typ,kind>>

type transenv<'a> = {gamma:list<tbinding<'a>>; 
                     vsubsts:list<bvvdef*exp>;
                     tsubsts:list<btvdef*typ>;
                     pendingSubsts:list<btvdef * typ>;
                     holes:holes;
                     tcenv:Tcenv.env;
                     allow_residue:bool;
                     erase_spec_only:bool;
                     subterms:bool;
                     query:bool}
let strTenv e = 
  let rec strBinding = function 
    | Formula b -> spr "Formula(%s)" (strBinding b)
    | Var_binding(x,t,s,_) -> spr "%s(%s)" (Pretty.strBvd x) (* (Pretty.strTyp t) *) (strSort s)
    | Tvar_binding(a,k,s,_) -> spr "%s(%s)" (Pretty.strBvd a) (* (Pretty.strKind k) *) (strSort s) 
    | BVar_binding(a, _) -> spr "%s" (Pretty.strBvd a) 
    | BTvar_binding(a, _) -> spr "%s" (Pretty.strBvd a) in
    String.concat ", " (List.map strBinding e.gamma)
let push_vsubst tenv vs = {tenv with vsubsts=vs::tenv.vsubsts}
let push_tsubst tenv ts = {tenv with tsubsts=ts::tenv.tsubsts}
let lookup_tsubst tenv btvd = 
  "lookup_tsubst" ^^ lazy 
  match findOpt (fun (btvd', _) -> btvd'.instantiation === btvd.instantiation) tenv.tsubsts with 
    | None -> None
    | Some (_, t) -> Some t
let lookup_vsubst tenv bvvd = 
  "lookup_vsubst" ^^ lazy 
  match findOpt (fun (bvvd', _) -> bvvd'.instantiation === bvvd.instantiation) tenv.vsubsts with 
    | None -> None
    | Some (_, v) -> Some v
let get_substs tenv = (tenv.tsubsts, tenv.vsubsts)
let subst_as_smap tenv =
  (List.map (fun (x,e) -> Inr(x,e)) tenv.vsubsts)@
  (List.map (fun (a,t) -> Inl(a,t)) tenv.tsubsts)
let substs_as_str tenv = 
  spr "[%s]; [%s]"
    (String.concat "; " (List.map (fun (x,e) -> spr "%s --> %s" (Pretty.strBvd x) (Pretty.strExp e)) tenv.vsubsts))
    (String.concat "; " (List.map (fun (x,t) -> spr "%s --> %s" (Pretty.strBvd x) (Pretty.strTyp t)) tenv.tsubsts))
    
    

let string_of_disj_bvd = function 
  | Inl x -> string_of_bvd x
  | Inr x -> string_of_bvd x

let names tenv = spr "Gamma = %s\n Holes = %s\n" 
  (String.concat ", " (List.map tbinding_name tenv.gamma))
  (String.concat ", " (List.map (fun (x,h,_,_) -> spr "%s --> %s" (string_of_disj_bvd x) (h.ToString())) tenv.holes))

(* let rename env renaming =  *)
(*   let replace s tmopt bvd =  *)
(*     match findOpt (fun (bvd', _) -> bvd_eq bvd bvd') renaming with  *)
(*       | None -> tmopt *)
(*       | Some(_, t) ->  *)
(*           if t.tmsort = s then Some t  *)
(*           else raise (Bad (spr "Environment renaming sort mismatch; Expected %A got %A\n" s t.tmsort)) in *)
(*   let rec aux = function  *)
(*     | Var_binding(bvd, t, s, tm) -> Var_binding(bvd, t, s, replace s tm bvd) *)
(*     | Tvar_binding(bvd, k, s, tm) -> Tvar_binding(bvd, k, s, replace s tm bvd) *)
(*     | Formula tb -> Formula (aux tb) in  *)
(*     {env with gamma=env.gamma |> List.map aux} *)
  
let mkTransenv = function
  | Some tcenv -> {gamma=[]; vsubsts=[]; tsubsts=[];
                   pendingSubsts=[]; holes=[]; tcenv=tcenv; 
                   allow_residue=true; erase_spec_only=false; 
                   subterms=true; query=false} 
  | None -> raise Impos

let holectr = ref 0 
let newHole tenv x sort tk = 
  let id = incr holectr; !holectr in 
    {tenv with holes=(x,id,sort,tk)::tenv.holes}, id
      
let push te b = {te with gamma=b::te.gamma}

let pushFormulaVar te b = push te (Formula b)  
  
let bvd_eq_bv (bvdef:bvdef<'a>) (bv:bvar<'a,'b>) = 
  (real_name bvdef).idText = (bvar_real_name bv).idText

let bv_name bv = (bvar_real_name bv).idText
  
let btv_not_bound tenv btvdx = 
  let rec aux = function 
    | [] -> 
        (match Tcenv.lookup_btvar_ident tenv.tcenv btvdx.realname with
           | None -> true
           | _ -> false)
    | Formula(Tvar_binding(btvd,_,_,_))::tl
    | (BTvar_binding(btvd, _))::tl
    | (Tvar_binding(btvd,_,_,_))::tl -> 
        (if bvd_eq btvd btvdx (* btvd.instantiation===btvdx.instantiation  *)
         then false
         else aux tl)
    | _::tl -> aux tl in 
    aux tenv.gamma 
      
let bvv_not_bound tenv bvdx = 
  let rec aux = function 
    | [] -> 
        (match Tcenv.lookup_bvar_ident tenv.tcenv bvdx.realname with
           | None -> true
           | _ -> false)
    | Formula(Var_binding(bvd,_,_,_))::tl
    | (BVar_binding(bvd, _))::tl        
    | (Var_binding(bvd,_,_,_))::tl -> 
        (if bvd_eq bvd bvdx (* bvd.instantiation===bvdx.instantiation  *)
         then false
         else aux tl)
    | _::tl -> aux tl in 
    aux tenv.gamma 

let test_bvv_not_bound tenv bvdx =
  if bvv_not_bound tenv bvdx 
  then match lookup_vsubst tenv bvdx with
    | None -> true
    | _ -> false
  else false

let check_bvv_not_bound tenv bvdx = 
  let fail () = raise (Z3Encoding (spr "Variable %s is already in scope" (strBvd bvdx))) in 
    if bvv_not_bound tenv bvdx 
    then 
      match lookup_vsubst tenv bvdx with
        | None -> ()
        | _ -> fail ()
    else fail()

let test_btv_not_bound tenv btvdx =
  if btv_not_bound tenv btvdx 
  then match lookup_tsubst tenv btvdx with
    | None -> true
    | _ -> false
  else false
    
let check_btv_not_bound tenv btvdx = 
  let fail () = raise (Z3Encoding (spr "Type variable %s is already in scope" (strBvd btvdx))) in 
    if btv_not_bound tenv btvdx 
    then 
      match lookup_tsubst tenv btvdx with
        | None -> ()
        | _ -> fail ()
    else fail ()
      
let lookupBtvarWithKind tenv bv = 
  let rec aux bix ix phi_ix = function 
    | (Var_binding _)::tl -> 
        aux bix (ix + 1) phi_ix tl
          
    | (Tvar_binding(bvd,k,s,tref))::tl ->
        if bvd_eq_bv bvd bv then 
          (match !tref with 
             | Some tm -> 
               (match tm.tm with 
                 | BoundV(i, x, s, r) -> (BoundV(i + phi_ix, x, s, r), k)
                 | _ -> (tm, k))
             | _ -> (mk_Typ_btvar ix, k))
        else aux bix (ix + 1) phi_ix tl
          
    | Formula(Var_binding _)::tl ->           
        aux bix ix (phi_ix + 1) tl

    | Formula(Tvar_binding(bvd,k,s,tref))::tl -> 
        if bvd_eq_bv bvd bv then 
          match !tref with 
            | None ->  (BoundV(phi_ix, s, string_of_bvd bvd, tref), k)
            | Some tm -> (tm, k)
        else aux bix ix (phi_ix + 1) tl
          
    | (BVar_binding _)::tl -> 
        aux (bix + 1) ix phi_ix tl 

    | (BTvar_binding(bvd,k))::tl -> 
        if bvd_eq_bv bvd bv then 
          mk_Typ_btvar bix, k
        else aux (bix + 1) ix phi_ix tl 
          
    | [] -> 
        (match findOpt (function (Inr _, _, _, _) -> false | (Inl bvd,_,_,_) -> bvd_eq_bv bvd bv) tenv.holes with
           | Some (_, i, s, Inr k) -> withSort s <| Hole i, k
           | Some (_, i, _, Inl _) -> raise (Bad "Expected type hole; got term hole")
           | None -> 
               let k = Tcenv.lookup_btvar tenv.tcenv bv in
                 (FreeV(typeNameOfBtvar bv, Type_sort), k)) in
    try 
      aux 0 0 0 tenv.gamma 
    with _ -> raise (Z3Encoding (spr "Type variable %s not found" (Pretty.strBtvar bv)))

let addPendingSubst tenv x = {tenv with pendingSubsts=x::tenv.pendingSubsts}

let lookupPendingSubst tenv bv = 
  match findOpt (fun (bv', _) -> bvd_eq bv bv') tenv.pendingSubsts with 
    | None -> None
    | Some(_,t) -> Some t

let lookupBtvar tenv bv = fst <| lookupBtvarWithKind tenv bv
      
let lookupTypConst tenv tc = 
  try 
    if Sugar.lid_equals tc.v Const.unit_lid then unitType
    else if Sugar.lid_equals tc.v Const.bool_lid then boolType
    else if Sugar.lid_equals tc.v Const.int_lid then intType
    else if Sugar.lid_equals tc.v Const.string_lid then strType
    else if Sugar.lid_equals tc.v Const.float_lid then floatType
    else
      let k = Tcenv.lookup_typ_const tenv.tcenv tc in
        FreeV(typeNameOfLid tc.v, Type_sort)
  with _ -> raise (Z3Encoding (spr "Type constant %s not found" (Pretty.sli tc.v)))

let lookupBvar tenv bv = 
  let rec aux bix ix phi_ix = function 
    | (Var_binding(bvd,k,_,tref))::tl -> 
        if bvd_eq_bv bvd bv then 
          match !tref with
            | Some tm -> 
              (match tm.tm with
                | BoundV(j, s, x, r) -> BoundV(j + phi_ix, s, x, r)
                | _ -> tm)
            | _ -> mk_Exp_bvar ix
        else aux bix (ix + 1) phi_ix tl
          
    | (Tvar_binding _)::tl ->
        aux bix (ix + 1) phi_ix tl
                  
    | Formula(Var_binding(bvd,l,s,tref))::tl ->           
        if bvd_eq_bv bvd bv then 
          match !tref with 
            | None -> BoundV(phi_ix, s, string_of_bvd bvd, tref)
            | Some tm -> tm
        else aux bix ix (phi_ix + 1) tl

    | Formula(Tvar_binding _)::tl -> 
        aux bix ix (phi_ix + 1) tl
          
    | (BVar_binding(bvd,_))::tl -> 
        if bvd_eq_bv bvd bv then 
          mk_Exp_bvar bix
        else aux (bix + 1) ix phi_ix tl 

    | (BTvar_binding _)::tl -> 
        aux (bix + 1) ix phi_ix tl 
          
    | [] -> 
        (match findOpt (function (Inr bvd,_,_,_) -> bvd_eq_bv bvd bv | _ -> false) tenv.holes with
           | Some (_, i,s,_) -> withSort s <| Hole i
           | _ -> 
               let k = Tcenv.lookup_bvar tenv.tcenv bv in
                 FreeV(funNameOfBvar bv, Term_sort)) in
    try aux 0 0 0 tenv.gamma 
    with _ -> raise (Z3Encoding (spr "Term variable %s not found;\n bindings are (%s)\n" (Pretty.strBvar bv) (names tenv)))

let lookupFvar tenv fv = 
  try 
    let _ = Tcenv.lookup_fvar tenv.tcenv fv in
      FreeV(funNameOfFvar fv.v, Term_sort)
  with _ -> raise (Z3Encoding (spr "Free variable %s not found" (Pretty.sli fv.v)))

let fieldProjector tenv t fn = 
  let rec pos ix = function 
    | (fn', _)::tl when Sugar.lid_equals fn fn' -> ix
    | _::tl -> pos (ix+1) tl 
    | [] -> raise Not_found in
  try 
    if AbsynUtils.isTupleProj fn then 
      let ix = if fn=Const.tuple_proj_one then 2 else 3 in (* two type arguments come first *)
        match (Tcenv.expand_typ tenv.tcenv t).v with
          | Typ_dtuple([(_, t1); (_, t2)]) -> 
              let constrLid = funNameOfConstr (Const.tuple_data_lid t1.sort t2.sort) in
                mkProj constrLid ix
          | _ -> raise Impos
    else
      let (lid, _, tps, {v=Typ_record(fn_t_l, _)}) = Tcenv.lookup_record_typ tenv.tcenv fn in
      let b = List.length tps in 
      let offset = pos 0 fn_t_l in
      let projName = mkProj (recordConstrName lid) (b + offset) in
        projName
  with _ -> raise (Z3Encoding (spr "Field name %s not found" (Pretty.sli fn)))
  
let tcenv tenv = 
  List.fold_left (fun env -> function
                    | BVar_binding(x,t)
                    | Var_binding(x,t,_,_)
                    | Formula(Var_binding(x,t,_,_)) -> 
                        Tcenv.push_local_binding_fast env (Tcenv.Binding_var(x.realname, t))
                    | BTvar_binding(a,k)
                    | Tvar_binding(a,k,_,_)
                    | Formula(Tvar_binding(a,k,_,_)) -> 
                        Tcenv.push_local_binding_fast env (Tcenv.Binding_typ(a.realname, k))) tenv.tcenv tenv.gamma

let derivableEquality tenv t = match t.v with 
  | Typ_dtuple _ 
  | Typ_record _ -> true
  | _ -> 
      let t, _ = AbsynUtils.flattenTypAppsAndDeps t in 
        match t.v with 
          | Typ_const(tc, _) -> 
              let tcenv = tenv.tcenv in
                (try 
                   let _ = Tcenv.lookup_record_typ_by_name tcenv tc.v in true
                 with _ -> false)
          | _ -> false
