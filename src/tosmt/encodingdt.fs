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
 
module Microsoft.FStar.Z3Encoding.EncodingDT

open Microsoft.FStar
open Z3Encoding.Env
open Z3Encoding.BasicDT
open Microsoft.Z3
open Util
open Absyn
open Term
open Profiling 
open DecodeTyp
open KindAbbrevs

let isQuery = ref false
exception CatchMe of string * Range.range

type config = {skip_pf:bool;
               subterm_typing:bool}
let config = {skip_pf=true;
              subterm_typing=false}
type vres        = {term:tm; 
                    subterm_phi:list<phi>}
let vres t = {term=t; subterm_phi=[]}
let vresphi t phi = {term=t; subterm_phi=phi}
type res        = {term:tm; 
                   binding_phi:option<phi>}

type transenv = transenv<residue>

let strip tenv top = 
  let rec strip tenv t =
    if AbsynUtils.is_pf_typ t 
    then strip tenv (AbsynUtils.strip_pf_typ t)
    else 
      let t = compress t in 
        match t.v with
          | Typ_meta(Meta_alpha t) -> 
              strip tenv (AbsynUtils.alpha_fast t)
                
          | Typ_ascribed(t, _) -> strip tenv t
              
          | Typ_btvar btv -> 
              if btv_not_bound tenv btv.v then 
                (match lookup_tsubst tenv btv.v with
                   | None -> 
                       (match lookupPendingSubst tenv btv.v with 
                          | None -> 
                              (* let _ = pr "Env is \n%s\n" (strTenv tenv) in  *)
                                raise (Z3Encoding (spr "In type %s: Bound tvar not found: %s :: %s\n" (Pretty.strTyp top) (strBvd btv.v) (Pretty.strKind t.sort)))
                          | Some t -> strip tenv t)
                   | Some t -> strip tenv t)
              else t
                
          | Typ_const(fv, _) ->
              (match Tcenv.lookup_typ_abbrev tenv.tcenv fv with 
                 | None -> t
                 | Some t' -> 
                     let t'' = alpha_convert t' in 
                       (* let _ = pr "%s expanded to %s\n" (t.ToString()) (t''.ToString()) in  *)
                       strip tenv t'')

          | _ -> t in 
    strip tenv top

(* let norm tenv top =  *)
let rec norm tenv t = 
  let t = strip tenv t in 
    match t.v with 
      | Typ_app(t1,t2) ->
          let tenv, t1 = norm tenv t1 in
            (match t1.v with
               | Typ_tlam(a, k, body) ->
                   let tenv, t2 = norm tenv t2 in
                     if test_btv_not_bound tenv a 
                     then 
                       let tenv = push_tsubst tenv (a,t2) in 
                         norm tenv body 
                     else (match alpha_convert t1 with 
                             | {v=Typ_tlam(a, k, body)} ->
                                 let tenv = push_tsubst tenv (a,t2) in 
                                   norm tenv body 
                             | _ -> raise Impos)

               | _ -> tenv, twithinfo (Typ_app(t1, t2)) t.sort t.p)
              
      | Typ_dep(t1,e) ->
          let tenv, t1 = norm tenv t1 in
            (match t1.v with
               | Typ_lam(x, t, body) ->
                   if test_bvv_not_bound tenv x 
                   then 
                     let tenv = push_vsubst tenv (x,e) in 
                       norm tenv body
                   else (match alpha_convert t1 with 
                           | {v=Typ_lam(x,t,body)} ->
                               let tenv = push_vsubst tenv (x,e) in 
                                 norm tenv body
                           | _ -> raise Impos)
               | _ -> tenv, twithinfo (Typ_dep(t1, e)) t.sort t.p)
              
      | _ -> tenv, t 
          (* in  *)
          (*   try norm tenv top  *)
          (*   with Z3Encoding _ when (pr "Normalization of %s failed\n" (Pretty.strTyp top); false) -> raise Impos *)
      
let bvvars_equivalent (bvar1:bvvar) (bvar2:bvvar) equivs : bool = 
  let rn1 = (bvar_real_name bvar1).idText in
  let rn2 = (bvar_real_name bvar2).idText in
    rn1=rn2 ||List.exists 
      (function Inl _ -> false | Inr (b1:bvvdef, b2:bvvdef) -> 
         let b1n = real_name b1 in
         let b2n = real_name b2 in
           (b1n.idText = rn1 && b2n.idText = rn2) ||
           (b2n.idText = rn1 && b1n.idText = rn2)) equivs

let btvars_equivalent (bvar1:btvar) (bvar2:btvar) equivs : bool = 
  let rn1 = (bvar_real_name bvar1).idText in
  let rn2 = (bvar_real_name bvar2).idText in
    rn1=rn2 ||List.exists 
      (function Inr _ -> false | Inl (b1:btvdef, b2:btvdef) -> 
         let b1n = real_name b1 in
         let b2n = real_name b2 in
           (b1n.idText = rn1 && b2n.idText = rn2) ||
           (b2n.idText = rn1 && b1n.idText = rn2)) equivs    

let rec same_typ env equivs t t' : bool = 
  let tt1 = compress t in 
  let tt2 = compress t' in 
    match (tt1.v, tt2.v) with 
      | Typ_ascribed(_, _), _ 
      | _, Typ_ascribed(_, _) -> same_typ env equivs (unascribe_typ tt1) (unascribe_typ tt2)

      | Typ_btvar bv1, Typ_btvar bv2 -> btvars_equivalent bv1 bv2 equivs 
          
      | Typ_const (fv1,eref1), Typ_const (fv2, eref2) -> fvar_eq fv1 fv2 && eref1=eref2 
      
      | Typ_record(fnt_l1, _), Typ_record(fnt_l2, _) -> 
          if (List.length fnt_l1 =  List.length fnt_l2) then 
            List.forall2 (fun (fn1,t1) (fn2,t2) -> 
                            ((Sugar.path_of_lid fn1)=(Sugar.path_of_lid fn2) &&
                                (same_typ env equivs t1 t2))) fnt_l1 fnt_l2 
          else false
            
      | Typ_fun (nopt, t1, t2),  Typ_fun (nopt', t1', t2') -> (* equivalence of bound term vars handles by tequiv *)
          (same_typ env equivs t1 t1') &&
            (match nopt, nopt' with 
               | None, None 
               | Some _, None
               | None, Some _ -> 
                   same_typ env equivs t2 t2'
               | Some bvd1, Some bvd2 -> 
                   let equivs' = (Inr(bvd1, bvd2))::equivs in
                     same_typ env equivs' t2 t2')
            
      | Typ_lam(x, t1, t2), Typ_lam(y, t1', t2') -> 
          (same_typ env equivs t1 t1') &&
            (let equivs' = (Inr(x, y))::equivs in
               same_typ env equivs' t2 t2')

      | Typ_tlam(x, k1, t2), Typ_tlam(y, k1', t2') -> 
          (same_kind env equivs k1 k1') &&
            (let equivs' = (Inl(x, y))::equivs in
               same_typ env equivs' t2 t2')
            
      | Typ_univ(bvd1, k, f1, t), Typ_univ(bvd2, k', f2, t') ->                 
          (same_kind env equivs k k') &&
            (same_typs env ((Inl(bvd1, bvd2))::equivs) (t::f1) (t'::f2))
            
      | Typ_dtuple nt_l, Typ_dtuple nt_l' -> 
          if (List.length nt_l) = (List.length nt_l') then
            let rec equiv_dep_list equivs  = function
                [] -> true
              | ((n1, t1), (n2, t2))::tl -> 
                  (same_typ env equivs t1 t2) &&
                    (match n1, n2 with
                       | None, None 
                       | Some _, None
                       | None, Some _ ->
                           equiv_dep_list equivs tl
                       | Some bvd1, Some bvd2 -> 
                           let equivs' = (Inr(bvd1, bvd2))::equivs in
                             equiv_dep_list equivs' tl) in 
            let l = List.zip nt_l nt_l' in
              equiv_dep_list equivs l 
          else false
            
      | Typ_refine (bvd1, t1, f1, _),  Typ_refine (bvd2, t2, f2, _) -> 
          (same_typ env equivs t1 t2) && 
            (same_typ env (Inr(bvd1,bvd2)::equivs) f1 f2)

      | Typ_app (t1, t2), Typ_app (t1', t2') -> 
          (same_typ env equivs t1 t1') &&
            (same_typ env equivs t2 t2')
            
      | Typ_dep (t1, e1), Typ_dep (t2, e2) -> 
          (same_typ env equivs t1 t2) &&
            (same_exp env equivs e1 e2)
        
      | Typ_meta(Meta_alpha t), _ ->     
          same_typ env equivs (alpha_convert t) tt2
      | t2, Typ_meta(Meta_alpha t) ->
          same_typ env equivs tt1 (alpha_convert t) 
            
      | Typ_meta(Meta_pattern(t, _)), _ -> 
          same_typ env equivs t tt2
      | _, Typ_meta(Meta_pattern(t, _)) -> 
          same_typ env equivs tt1 t

      | Typ_meta (Meta_cases tl), Typ_meta (Meta_cases tl') -> 
          same_typs env equivs tl tl'

      | Typ_unknown, Typ_unknown -> true
          
      | Typ_uvar(uv1, _), Typ_uvar(uv2, _) -> Unionfind.equivalent uv1 uv2

      | Typ_affine t1, Typ_affine t2 -> 
          same_typ env equivs t1 t2

      | _ -> false

and same_typs env equivs tl1 tl2 =  List.forall2 (same_typ env equivs) tl1 tl2

and same_kind env equivs k1 k2 = 
  match (unbox k1)(* .u *), (unbox k2)(* .u *)with 
    | Kind_star, Kind_star 
    | Kind_affine, Kind_affine
    | Kind_prop, Kind_prop
    | Kind_erasable, Kind_erasable -> true
    | Kind_tcon(aopt, k1_1, k1_2), Kind_tcon(bopt, k2_1, k2_2) -> 
        (same_kind env equivs k1_1 k2_1)  &&
          (match aopt, bopt with 
             | Some a, Some b -> 
                 same_kind env (Inl(a,b)::equivs) k1_2 k2_2
             | _ -> 
                 same_kind env equivs k1_2 k2_2)

    | Kind_dcon(xopt, t1, k1), Kind_dcon(yopt, t2, k2) -> 
        (same_typ env equivs t1 t2)  &&
          (match xopt, yopt with 
             | Some x, Some y -> same_kind env (Inr(x,y)::equivs) k1 k2
             | _ -> same_kind env equivs k1 k2)
    | _ -> false

        
and same_exp env equivs e1 e2 = (* only implemented for non-function values *)
  match e1.v, e2.v with
    | Exp_bvar bv1, Exp_bvar bv2 -> bvvars_equivalent bv1 bv2 equivs 
    | Exp_fvar (fv1, eref1), Exp_fvar (fv2, eref2) -> fvar_eq fv1 fv2 && eref1=eref2 
    | Exp_constant c1, Exp_constant c2 -> Sugar.const_eq c1 c2
    | Exp_constr_app (v1, tl, _, el), Exp_constr_app (v2, tl2, _, el2) ->  
        ((fvar_eq v1 v2) &&
           (List.length tl) = (List.length tl2) &&
            (List.length el) = (List.length el2) &&
            (List.forall2 (same_typ env equivs) tl tl2) && 
            (List.forall2 (same_exp env equivs) el el2)) 
          
    | Exp_recd (_, _, _, fne_l_1), Exp_recd (_, _, _, fne_l_2) ->
        (List.length fne_l_1 = List.length fne_l_2) &&
          (List.forall2 (fun (f1, e1) (f2,e2) -> 
                           (Sugar.lid_equals f1 f2) &&
                             (same_exp env equivs e1 e2)) fne_l_1 fne_l_2)

    | Exp_proj(e1, fn1), Exp_proj(e2, fn2) ->            
        (Sugar.lid_equals fn1 fn2) &&
          (same_exp env equivs e1 e2)

    | Exp_ascribed(_, _, _), _ 
    | _, Exp_ascribed(_, _, _) -> same_exp env equivs (unascribe e1) (unascribe e2)
        
    | _ -> false 

let alphaEquiv env t1 t2 = 
  same_typ env [] t1 t2 

let flatten_l l = List.flatten l
let flattenTypAppsAndDeps t = AbsynUtils.flattenTypAppsAndDeps t

let is_unfold_lid (lid:lident) = 
  let _, l = Util.pfx lid.lid in 
    l.idText.StartsWith("__Unfold_")

let mkAndOpt p1 p2 = match p1, p2  with
  | Some p1, Some p2 -> Some (And(p1, p2))
  | Some p, None
  | None, Some p -> Some p
  | None, None -> None

let mkAndOpt_l pl = 
  List.fold_left (fun out p -> mkAndOpt p out) None pl 

let mkAnd_l l = match l with 
  | [] -> []
  | hd::tl -> [List.fold_left (fun p1 p2 -> And(p1,p2)) hd tl]
  
let mkConj tenv p l = 
  if tenv.subterms
  then List.fold_left (fun out p -> And(out, p)) p l
  else p

let join phi1 phi2 = mkAnd_l (phi1@phi2)

let is_tfun checksort tctx tenv typ = 
  match flattenTypAppsAndDeps (strip tenv typ) with 
    | {v=Typ_const(tc,_)}, args -> 
        (match tctx.funSymMap.isTfun tc.v with 
           | None -> None
           | Some(nm, s, tag) -> 
               let rec sort_ok s args = match s,args with 
                 | Arrow(Type_sort, s), (Inl _)::args 
                 | Arrow(Term_sort, s), (Inr _)::args -> sort_ok s args
                 | Type_sort, [] 
                 | Term_sort, [] 
                 | Bool_sort, [] -> true
                 | _ -> false in 
                 if (not checksort) || (sort_ok s args)
                 then 
                   (* let _ = pr "++++++++++%s is a logic fun at sort %s with %d args\n" (Pretty.sli tc.v) (strSort s) (List.length args) in  *)
                     Some (nm, s, tag, args)
                 else 
                   let _ = pr "----------%s is at sort %s cannot be applied to %d args\n" (Pretty.sli tc.v) (strSort s) (List.length args) in
                     None)
    | _ -> None

let destruct tenv typ lid = 
  match flattenTypAppsAndDeps (strip tenv typ) with 
    | {v=Typ_const(tc,_)}, args when Sugar.lid_equals tc.v lid -> Some args
    | _ -> None

let is_builtin lid = 
    Sugar.lid_equals lid Const.int_lid ||
    Sugar.lid_equals lid Const.bool_lid ||
    Sugar.lid_equals lid Const.string_lid ||
    Sugar.lid_equals lid Const.unit_lid

let is_lid_skippable = 
  let skippables = [Const.forall_lid;
                    Const.forallA_lid;
                    Const.forallP_lid;
                    Const.exists_lid;
                    Const.existsA_lid;
                    Const.existsP_lid;
                    Const.ifthenelse_lid;
                    Const.assume_lid;
                    Const.eq_lid;
                    Const.eq2_lid;
                    Const.eqA_lid;
                    Const.eqTyp_lid;
                    Const.lt_lid;
                    Const.gt_lid;
                    Const.lte_lid;
                    Const.gte_lid;
                    Const.reln_lid;
                    Const.doublesided_lid;
                    Const.and_lid;
                    Const.or_lid;
                    Const.not_lid;
                    Const.implies_lid;
                    Const.iff_lid;
                    Const.pf_lid;
                    Const.true_lid;
                    Const.false_lid;
                    Const.add_lid;
                    Const.sub_lid;
                    Const.mul_lid;
                    Const.div_lid;
                    Const.minus_lid;
                    Const.modulo_lid;
                    Const.op_And_lid;
                    Const.op_Or_lid;
                    Const.op_Not_lid;
                    Const.op_Add_lid;
                    Const.op_Subtraction_lid;
                    Const.op_Division_lid;
                    Const.op_Modulus_lid;
                    Const.op_Multiply_lid;
                    Const.op_GreaterThanOrEqual_lid;
                    Const.op_Dereference_lid;
                    Const.op_Eq;
                    Const.unfold_lid] in
    fun l -> List.exists (Sugar.lid_equals l) skippables 

                    

let rec isProp k = match k(* .u *)with
  | Kind_prop
  | Kind_erasable -> true
  | Kind_star 
  | Kind_affine -> false
  | Kind_dcon(_, _, k) 
  | Kind_tcon(_, _, k) -> isProp k


(* let mkTransenv tctx f = match f with *)
(*   | Some tcenv ->  *)
(*       let tenv = mkTransenv f in *)
(*         Tcenv.fold_env tcenv (fun tenv b -> match b with  *)
(*                                 | Tcenv.Binding_var(id, t) ->  *)
(*                                     (match lookupArraySort tctx t with *)
(*                                        | None -> tenv *)
(*                                        | Some s ->  *)
(*                                            let x = mkbvd(id,id) in  *)
(*                                            let nm = funNameOfBvdef x in *)
(*                                              push tenv (Var_binding(x, t, s.arr_sort, ref (Some(FreeV(nm, s.arr_sort)))))) *)
(*                                 | _ -> tenv) tenv *)
(*   | None -> raise Impos *)

let rec kindToSorts tctx k = match k(* .u *)with
  | Kind_tcon(_, _, k) -> Type_sort::kindToSorts tctx k
  | Kind_dcon(_, t, k) -> Term_sort::kindToSorts tctx k
  | Kind_star
  | Kind_affine 
  | Kind_prop
  | Kind_erasable -> []
  | _ -> raise Impos 

let arrayDomSortFromTyp tcenv dom = 
  let fail () = raise (Z3Encoding(spr "Unsupported domain of array: expected int, string, or ref; got %s\n" (Pretty.strTyp dom))) in
    match flattenTypAppsAndDeps (Tcenv.expand_typ tcenv dom) with 
      | {v=Typ_const(tc,_)}, _ -> 
          if Sugar.lid_equals tc.v Const.int_lid then Int_sort
          else if Sugar.lid_equals tc.v Const.string_lid then String_sort
          else if Sugar.lid_equals tc.v Const.ref_lid then Ref_sort
          else fail ()
      | _ -> fail ()

let debugSortFromTyp tenv t = 
  let rec aux tenv t = match (strip tenv t).v with 
    | Typ_fun(xopt, t, t') -> 
        let s = Term_sort in
        let tenv = match xopt with None -> tenv | Some x -> push tenv (Var_binding(x, t, s, termref())) in 
          Arrow(s, aux tenv t')
    | Typ_univ(a, k, _, t') -> 
        let tenv = push tenv (Tvar_binding(a, k, Type_sort, termref())) in 
          Arrow(Type_sort, aux tenv t') 
    | _ -> Term_sort in
    aux tenv t

let debugSortFromKind k = 
  let rec aux b k = match k(* .u *)with 
    | Kind_dcon(_, t, k') -> 
        let s = Term_sort in 
          Arrow(s, aux true k')
    | Kind_tcon(_, k1, k2) -> 
        Arrow(aux false k1, aux true k2)
    | Kind_star
    | Kind_affine -> Type_sort
    | Kind_prop -> Bool_sort
    | Kind_erasable -> if b then Bool_sort else Type_sort in
    aux true k

let isAtom tenv p = 
  let pred, args = flattenTypAppsAndDeps p in 
    match p.sort(* .u *)with 
      | Kind_prop 
      | Kind_erasable -> 
          (match (strip tenv pred).v with 
             | Typ_const _
             | Typ_btvar _ 
             | Typ_uvar _ -> true
             | _ -> false)
      | _ -> false
          
let getBvd = function Some x -> x | None -> new_bvd None 

let typeOfEq =
  let bool_t = mk_Typ_const (typeNameOfLid Const.bool_lid) in
  let int_t = mk_Typ_const (typeNameOfLid Const.int_lid) in
  let string_t = mk_Typ_const (typeNameOfLid Const.string_lid) in
  let heap_t = mk_Typ_const (typeNameOfLid Const.heap_lid) in
  let ref_t = mk_Typ_const (typeNameOfLid Const.ref_lid) in
  let unit_t = mk_Typ_const (typeNameOfLid Const.unit_lid) in
    fun tenv tm t -> 
      let eqt = Eq(typeOf tm, t) in 
        if termEq t bool_t then
          And(eqt, App(mkTester "BoxBool", Arrow(Term_sort, Bool_sort), [|tm|]))
        else if termEq t int_t then
          And(eqt, App(mkTester "BoxInt", Arrow(Term_sort, Bool_sort), [|tm|]))
        else if termEq t string_t then
          And(eqt, App(mkTester "BoxString", Arrow(Term_sort, Bool_sort), [|tm|]))
        else if termEq t heap_t && Tcenv.is_logic_array tenv Const.heap_lid then
          And(eqt, App(mkTester "Term_arr_Prims.heap", Arrow(Term_sort, Bool_sort), [|tm|]))
        else if termEq t unit_t then 
          And(eqt, Eq(tm, unitTerm))
        else match t.tm with 
          | App("Typ_app", _, [| s; tt|]) when termEq s ref_t -> 
              And(eqt, 
                  And(App(mkTester "BoxRef", Arrow(Term_sort, Bool_sort), [|tm|]), 
                      Eq(kindOf tt, mk_Kind_star())))
          | _ -> eqt

let mkTypeOf tenv tm_opt t  = 
  match tm_opt with 
    | None -> None
    | Some tm -> 
        try 
          Some (typeOfEq tenv.tcenv tm t)
        with Bad msg as e -> 
          pr "Bad %s\n" msg;
          pr "While mkTypeOf %s %s\n" (tm.ToString()) (t.ToString());
          pr "LHS sort = %A\n" tm.tmsort;
          pr "RHS sort = %A\n" t.tmsort;
          raise e
                
let mkKindOf tm_opt k = 
  match tm_opt with 
    | None -> None
    | Some tm -> Some (Eq(kindOf tm, k))

let add_bvar_mapping bvar nm h : STR<unit>  =
  let p, h = incrCtr h in 
  let tm = mkTermConstant p in 
  let op = Assume(Eq(FreeV(nm, Term_sort), tm), None, AName (spr "mapping %s" nm)) in 
  let _, h = addOp op h in 
    internBvar bvar tm [op] h

let add_fvar_mapping fvar nm h : STR<unit> =
  let p, h = incrCtr h in 
  let tm = mkTermConstant p in 
  let op = Assume(Eq(FreeV(nm, Term_sort), tm), None, AName (spr "mapping %s" nm)) in 
  let _, h = addOp op h in 
    internFvar fvar tm [op] h
      
let newTermConstant (h:opState) : STR<tm> =
  let p, _ = incrCtr h in 
  let tm = mkTermConstant p in 
    tm, h

let newStringConstant (h:opState) : STR<tm> =
  let p, _ = incrCtr h in 
  let tm = mkStringConstant p in 
    tm, h

let newFunSym h : STR<tm> =
  let p, h = incrCtr h in 
  let fname = spr "fun_%d" p in
  let op = DeclFun(fname, [| |], Term_sort, None) in 
  let _, h = addOp op h in 
    (FreeV(fname, Term_sort), h)
      
let newName nm h : STR<tm> = 
  let p, h = incrCtr h in 
  let fname = spr "%s_%d" nm p in
  let op = DeclFun(fname, [| |], Term_sort, None) in 
  let _, h = addOp op h in 
    (FreeV(fname, Term_sort), h)

let newPredSym pfx k h : STR<string> = 
  let p, h = incrCtr h in 
  let fname = spr "Pred_%s_%d" pfx p in
  (* let _ = pr "Generating pred sym %s\n" fname in  *)
  let sorts = kindToSorts h.termctx k in 
  let op = mkPred fname sorts in 
  let _, h = addOp op h in 
    fname, h

let newTypSym kopt pfx h : STR<tm> =
  let p, h = incrCtr h in 
  let fname = spr "type_%s_%d" pfx p in
  let op = DeclFun(fname, [| |], Type_sort, None) in 
  let _, h = addOp op h in 
  let tm = FreeV(fname, Type_sort) in
    match kopt with 
      | None -> tm, h
      | Some k -> 
          let _, h = addOp (Assume(Eq(kindOf tm, k), None, AName (spr "Kinding for uvar %s" (tm.ToString())))) h in
            tm, h

let lookupNamedType s h : STR<tm> = 
  match h.st.named_typ_map |> Util.findOpt (fun (s',_) -> s=s') with 
    | Some (_, t) -> t, h
    | None -> 
        let nm = cleanString (Util.unicodeEncoding.GetBytes s) in
        let t, h = newTypSym None (spr "named_%s" nm) h in 
        let p, h = incrCtr h in 
        let tc = mkTypeConstant p in
        let op = Assume(Eq(t, tc), None, AName "named type eq") in
        let _, h = addOps [op] h in 
          t, {h with st={h.st with named_typ_map=(s,t)::h.st.named_typ_map}}

(* ******************************************************************************** *)
(* Encoding core language: kinds, types, terms, formulas                            *)
(* ******************************************************************************** *)
let destructConnectives f = 
  let oneType = [Type_sort] in
  let twoTypes = [Type_sort;Type_sort] in
  let threeTypes = [Type_sort;Type_sort;Type_sort] in
  let twoTerms = [Term_sort;Term_sort] in
  let connectives = [(Const.and_lid,     twoTypes);
                     (Const.or_lid,      twoTypes);
                     (Const.implies_lid, twoTypes);
                     (Const.iff_lid,     twoTypes);
                     (Const.ifthenelse_lid, threeTypes);
                     (Const.not_lid,     oneType);
                     (Const.spec_only_lid, oneType);
                     (Const.lt_lid,      twoTerms);
                     (Const.gt_lid,      twoTerms);
                     (Const.gte_lid,     twoTerms);
                     (Const.lte_lid,     twoTerms);
                     (Const.eqTyp_lid,   twoTypes);
                     (Const.eq_lid,      twoTerms@[Type_sort]);
                     (Const.eq2_lid,     twoTerms@twoTypes);
                     (Const.eqA_lid,     twoTerms@[Type_sort]);
                     (Const.reln_lid,    oneType)] in 
  let rec aux args f lid arity =  match f.v, arity with
    | Typ_app(tc, arg), [t] 
        when (t=Type_sort && AbsynUtils.is_constructor tc lid) -> Some (lid, Inl arg::args)
    | Typ_dep(tc, arg), [t] 
        when (t=Term_sort && AbsynUtils.is_constructor tc lid) -> Some (lid, Inr arg::args)
    | Typ_app(f, arg), t::farity 
        when t=Type_sort -> aux (Inl arg::args) f lid farity
    | Typ_dep(f, arg), t::farity 
        when t=Term_sort -> aux (Inr arg::args) f lid farity
    | _ -> None in
    Util.find_map connectives (fun (lid, arity) -> aux [] f lid arity)

let collect_u_quants t = 
  let rec aux out t = 
    let t' = AbsynUtils.strip_pf_typ t in
      match AbsynUtils.flattenTypAppsAndDeps t' with
        | {v = Typ_fun(Some x, t1, t2)}, _ -> aux ((x, t1)::out) t2
        | {v=Typ_const(tc,_)}, [Inl t1; Inl {v=Typ_lam(x, _, t2)}] 
            when (Const.is_forall tc.v) -> 
            aux ((x, t1)::out) t2
        | _ -> List.rev out, t'
  in aux [] t

let maybeAddHoldsPred k = 
  get >> (fun st -> 
  let sorts = kindToSorts st.termctx k in 
  let sortkey = List.fold_right (fun s out -> Arrow(s, out)) sorts Type_sort in
  lookupHoldsMap sortkey >> 
    (function 
       | Some f -> ret f
       | None -> 
           let name = predNameOfLid (Sugar.lid_of_path ("Holds"::(List.map strSort sorts)) Absyn.dummyRange) in 
           let sorts = Type_sort::sorts in 
             insertHoldsMap (sortkey, name) 
             >> (fun _ -> 
                   addOp (mkPred name sorts) 
                   >> (fun _ -> ret name))))

let rec encodeKind (tenv:transenv) (binding:option<tm>) (k:kind) h : STR<res> = 
  let rec aux tenv (k:kind) h : STR<tm> = match k(* .u *)with
    | Kind_prop (* for the purposes of Z3, P and E are the same *)
    | Kind_erasable -> mk_Kind_erasable(), h
    | Kind_star ->     mk_Kind_star(), h
    | Kind_affine ->   mk_Kind_affine(), h

    | Kind_dcon(xopt, t, k) -> (* NS: should we translate this to opaque constants as well? *)
        let ({term=tm_t}:res), h = encodeTyp tenv None t h in 
        let x = getBvd xopt in
        let tenv = push tenv (Var_binding(x,t,Term_sort,termref())) in
        let tm_k, h = aux tenv k h in 
          (mk_Kind_dcon tm_t tm_k, h)

    | Kind_tcon(aopt, k1, k2) -> 
        let k1_tm, h = aux tenv k1 h in 
        let a = getBvd aopt in
        let tenv = push tenv (Tvar_binding(a, k1, Type_sort,termref())) in
        let k2_tm, h = aux tenv k2 h in 
          (mk_Kind_tcon k1_tm k2_tm, h)

    | _ -> raise (CatchMe(spr "Unexpected kind (%s)" (Pretty.strKind k), dummyRange))
  in
  let k, h = aux tenv k h in 
    {term=k; binding_phi=mkKindOf binding k}, h

and lookupTransformer tenv t h : STR<option<tm * option<phi>>> =       
  let equiv t t' = 
    if t === t' then true 
    else 
      (* match dprof "treln.kequiv" *)
      (*   (function Some _ -> "treln.kequiv.hit" | _ -> "treln.kequiv.miss") *)
      (*   (lazy TypeRelations.equivalent_kinds_with_evidence tenv.tcenv t.sort t'.sort) with        *)
      (*     | None -> false *)
      (*     | Some _ ->  *)
      dprof "treln.tequiv" 
        (function true  -> "treln.tequiv.hit" | false -> "treln.tequiv.miss") 
        (lazy alphaEquiv tenv.tcenv t t')  in
        
      (* match dprof "treln.tequiv"  *)
      (*   (function Some _  -> "treln.tequiv.hit" | None -> "treln.tequiv.miss")  *)
      (*   (lazy TypeRelations.equivalent_with_evidence tenv.tcenv t t') with  *)
      (*     | Some _ -> true *)
      (*     | _ -> false in  *)
    
  let finder (tx, _) = 
    let hkt = AbsynUtils.hashkey_typ t in 
      match map_tryfind tx hkt with
        | None -> None
        | Some ktable ->        (* pr "level 1 hit (%d)\n" t.sort.khashkey; *)
            let hkk = AbsynUtils.hashkey_kind t.sort in 
              (match map_tryfind ktable hkk with
                 | None -> None
                 | Some l -> findOpt (fun (t', _, _) -> "lookupTransformer.equiv" ^^ lazy equiv t t') l) in
    
  let st, h = get h in 
    match finder st.st.transformers with 
      | Some (_, tm, phiopt) -> Some (tm, phiopt), h
      | _ -> None, h
    
and encodeTransformer tenv t h : STR<tm * option<phi>> = 
  let substs = get_substs tenv in 
  let t = AbsynUtils.subst_fast (get_substs tenv) t in 
  let r, h = lookupTransformer tenv t h in 
    match r with 
      | Some res -> 
          res, h
      | None -> 
          let tm, h = internNewTransformer tenv t None h in 
            (tm, None), h

and internNewTransformer tenv t phiopt h = 
  let p, h = incrCtr h in 
  let tm = mkTypeConstant p in
  (* let _ = pr "Interning type\n%s\nas term %s\nSubsts are %s\n" (Pretty.strTyp t) (tm.ToString()) (substs_as_str tenv) in *)
  (* let _ = pr "Interning type\n%s\nas term %s\n" (Pretty.strTyp t) (tm.ToString()) in *)
  let _, h = internTransformer "" t tm phiopt h in 
    tm, h

and encodeTyp (tenv:transenv) (binding:option<tm>) (t:typ) h : STR<res> =
#if CHECKED      
  let res, h = preEncodeTyp tenv binding t h in 
    if res.term.tmsort <> Type_sort 
    then raise (Bad (spr "encodeType expected to produce a Type_sort; got %A" res.term.tmsort))
    else res, h
and preEncodeTyp (tenv:transenv) (binding:option<tm>) (t:typ) h : STR<res> =
#endif
  let rec aux tenv (t:typ) h : STR<tm> = 
    let tenv, t = norm tenv t in 
      match destruct tenv t Const.typeof_lid with 
        | Some [_; Inr v] -> 
            let vtm, h = encodeValue tenv v h in 
              typeOf vtm, h
        | _ -> 
            match destruct tenv t Const.kindof_lid with 
              | Some [_; Inl t] -> 
                  let t_tm, h = aux tenv t h in 
                    kindOf t_tm, h
              | _ -> 
                  match is_tfun true h.termctx tenv t with 
                    | Some(tfun, sort, tag, args) when tag <> Sugar.Logic_discriminator -> 
                        let tms, h = stfold [] args 
                          (fun out a -> match a with 
                             | Inl t -> encodeTyp tenv None t >>
                                 (fun tres -> ret (tres.term::out))
                             | Inr v -> encodeValue tenv v >> 
                                 (fun vtm -> ret (vtm::out))) h in
                        let tms = List.rev tms in 
                          App(tfun, sort, Array.ofList tms), h 
                            
                    | _ -> match t.v with 
                        | Typ_meta (Meta_tid _)
                        | Typ_unknown
                        | Typ_record(_,  None) -> raise Impos
                            
                        | Typ_uvar(uv,k) -> lookupUvar tenv (uv,k) h

                        | Typ_meta(Meta_pattern(t, _)) 
                        | Typ_meta(Meta_alpha t)
                        | Typ_ascribed(t, _) 
                        | Typ_record(_, Some t) 
                        | Typ_refine(_, t, _, _) -> aux tenv t h (* top-level refinements handled separately below *)

                        | Typ_meta(Meta_named(s, t)) -> 
                            lookupNamedType s h 
                              
                        | Typ_affine t -> 
                            let t_tm, h =  aux tenv t h in 
                              mk_Typ_affine t_tm, h

                        | Typ_btvar bv -> 
                            let tm = lookupBtvar tenv bv in
                              (if !Options.logQueries then 
                                 match tm.tm with 
                                   | FreeV(name, _) -> 
                                       let _, h = addPPName (name, typePPNameOfBvar bv) h in 
                                         tm, h
                                   | _ -> tm, h
                               else tm, h)
                                
                        | Typ_const (tc, _) -> mk_Typ_const (typeNameOfLid tc.v), h

                        | Typ_app(t1, t2) when AbsynUtils.is_constructor t1 Const.unname_lid -> 
                            aux tenv (unname_typ t2) h

                        | Typ_app(t1, t2) ->
                            let t1_tm, h = aux tenv t1 h in 
                            let t2_tm, h = aux tenv t2 h in 
                              mk_Typ_app t1_tm t2_tm, h
                                
                        | Typ_dep(t, v) -> 
                            let t_tm, h = aux tenv t h in 
                            let v_tm, h = encodeValue tenv v h in 
                              mk_Typ_dep t_tm v_tm, h
                                
                        | _ when !Options.use_type_constants -> 
                            encodeAsTypeConstant tenv t h 

                        | Typ_meta(Meta_cases tl) -> 
                            let tms, h = stfold [] tl (fun out t h ->
                                                         let t_tm, h = aux tenv t h in 
                                                           t_tm::out, h) h in 
                            let tm = match tms with 
                              | last::rest -> 
                                  List.fold_left (fun out t -> mk_Typ_app (mk_Typ_app (mk_Typ_const (typeNameOfLid Const.and_lid)) t) out) last rest
                              | _ -> mk_Typ_const (typeNameOfLid Const.true_lid) in 
                              tm, h
                                
                        | Typ_dtuple ([t1;(_, t2)]) -> 
                            aux_binder tenv t1 t2 mk_Typ_dtuple h
                        | Typ_fun(xopt, t1, t2) -> 
                            aux_binder tenv (xopt, t1) t2 mk_Typ_fun h
                        | Typ_lam(x, t1, t2) -> 
                            aux_binder tenv (Some x, t1) t2 mk_Typ_lam h
                        | Typ_univ(a, k, _, t) -> 
                            aux_tbinder tenv (a,k) t mk_Typ_univ h 
                        | Typ_tlam(a, k, t) -> 
                            aux_tbinder tenv (a,k) t mk_Typ_tlam h 

  and aux_tbinder tenv (a,k) t f h = 
    let {term=ktm}, h = encodeKind tenv None k h in 
    let tenv = push tenv (BTvar_binding(a,k)) in 
    let tm, h = aux tenv t h in 
      f ktm tm, h

  and aux_binder tenv (xopt,t1) t2 f h = 
    let tm1, h = aux tenv t1 h in 
    let tenv = match xopt with 
      | None -> tenv 
      | Some x -> push tenv (BVar_binding(x,t1)) in 
    let tm2, h = aux tenv t2 h in 
      f tm1 tm2, h
        
  and encodeAsTypeConstant tenv t = 
    (encodeTransformer tenv t >> 
       (fun (tm:tm, _) -> encodeKind tenv (Some tm) t.sort >>
       (fun {binding_phi=Some phi} -> 
          let op = Assume(phi, None, AName (spr "Kinding for %s" (tm.ToString()))) in 
            addOp op >> (fun _ -> ret tm))))
  in 
  let tenv, et = norm tenv t in 
    match et.v with 
      | Typ_refine(x, t, form, _) -> 
          let res, h = encodeTyp tenv binding t h in 
            (match form.sort(* .u *)with 
               | Kind_dcon _  when tenv.tcenv.object_invariants ->  res, h
               | Kind_prop
               | Kind_erasable -> 
                   let tenv = push tenv (Var_binding(x, t, Term_sort, ref binding)) in 
                   let phi, h = encodeFormula {tenv with allow_residue=false} form h in 
                     {res with 
                        binding_phi=mkAndOpt_l [res.binding_phi; (Some phi)]}, h
               | _ -> raise (Error(spr "Unexpected kind of refinement formula (%s)\n" (Pretty.strKind form.sort), 
                                          t.p)))
      | _ -> 
          let tm, h = aux tenv et h in
          let phis = mkTypeOf tenv binding tm in 
            {term=tm; binding_phi=phis}, h
              
and encodeValueVres (tenv:transenv) (e:exp) h : STR<vres> = 
  let rec aux e h = match e.v with 
    | Exp_bvar x -> 
        if bvv_not_bound tenv x.v 
        then 
          (match lookup_vsubst tenv x.v with
             | None -> 
                 let msg = spr "Bound var not found: %s : %s\n" (strBvd x.v) (e.sort.ToString()) in
                 raise (CatchMe (msg, x.p))
             | Some e -> aux e h)
        else
          let tm = lookupBvar tenv x in
          let h = match tm.tm with 
            | FreeV(name, _) when !Options.logQueries -> 
                let _, h = addPPName (name, funPPNameOfBvar x) h in 
                  h
            | _ -> h in 
            vres tm, h
              
    | Exp_fvar (x, _) -> 
        let tm = lookupFvar tenv x in
          vres tm, h                    
            
    | Exp_constant c -> 
        let tm, h = encodeConstant tenv e.sort c h in
          vres tm, h
                      
    | Exp_constr_app(d, tl, el1, el2) -> 
        let encodeArith args mk = 
          (stmap args (encodeValueVres tenv)) >> (fun args -> 
                                                (* let args, phis = List.unzip args in *)
                                                let args = args |> List.map (fun a -> {a with term=unboxInt a.term}) in 
                                                  ret (vresphi 
                                                         (boxInt (mk (args |> List.map (fun a -> a.term))))
                                                         (args |> List.collect (fun a -> a.subterm_phi)))) in 
        let encodeConstr () = 
            let is_logic_function = Tcenv.is_logic_function tenv.tcenv d in 
            let dname = funNameOfConstr d.v in
            let tl_res, h = stmap tl (encodeTyp tenv None) h in 
            let el, h = stmap (el1@el2) (encodeValueVres tenv) h in 
            let tl = List.map (fun r -> r.term) tl_res in
            let args = tl@(el |> List.map (fun e -> e.term)) in 
            let tctx = h.termctx in 
            let tm = Appl(dname, debugSortFromTyp tenv d.sort, args) in 
            let phis = el |> List.collect (fun e -> e.subterm_phi) in 
              vresphi tm phis, h in

          if Sugar.lid_equals d.v Const.add_lid then encodeArith el2 (fun [arg1; arg2] -> Add(arg1, arg2)) h
          else if Sugar.lid_equals d.v Const.sub_lid then encodeArith el2 (fun [arg1; arg2] -> Sub(arg1, arg2)) h
          else if Sugar.lid_equals d.v Const.mul_lid then encodeArith el2 (fun [arg1; arg2] -> Mul(arg1, arg2)) h
          else if Sugar.lid_equals d.v Const.div_lid then encodeArith el2 (fun [arg1; arg2] -> Div(arg1, arg2)) h
          else if Sugar.lid_equals d.v Const.modulo_lid then encodeArith el2 (fun [arg1; arg2] -> Mod(arg1, arg2)) h
          else if Sugar.lid_equals d.v Const.minus_lid then encodeArith el2 (fun [arg1] -> Minus(arg1)) h
          else if Sugar.lid_equals d.v Const.lproj_lid then encodeConstr ()
          else if Sugar.lid_equals d.v Const.rproj_lid then encodeConstr ()
          else 
            let getSelHeapType () = 
              match el2 with 
                | [_;e2] -> 
                    (match Tcenv.expand_typ_until tenv.tcenv e2.sort Const.ref_lid with 
                       | None -> None 
                       | Some t ->
                           (match AbsynUtils.flattenTypAppsAndDeps t with 
                              | _, [Inl t] -> 
                                    Some t
                              | _ -> raise Impos))
                | _ -> 
                    let _ = pr "Unexpected args [%s]\n" (String.concat "; " (el2 |> List.map Pretty.strExp)) in
                      raise Impos in 
              
              (match lookup_array_function h.termctx d.v with 
                 | None -> 
                     let res, h = encodeConstr () in
                       if Sugar.lid_equals d.v (p2l ["DST"; "SelHeap"])
                       then 
                         try
                           match getSelHeapType() with 
                             | None -> res, h
                             | Some t -> 
                                 let {binding_phi=Some phi}, h = encodeTyp tenv (Some res.term) t h in
                                   {res with subterm_phi=phi::res.subterm_phi}, h
                         with _ -> 
                           pr "WARNING: Failed to encode sort %s; you may miss a trigger\n" (Pretty.strTyp e.sort);
                           res,h
                             (* raise exn *)
                       else res, h
                 | Some arr -> 
                     let tl,h = stmap tl (encodeTyp tenv None) h in
                     let tl = tl |> List.map (fun r -> r.term) in
                     let el,h = stmap el2 (encodeValueVres tenv) h in 
                     let phis = el |> List.collect (fun e -> e.subterm_phi) in 
                     let el = el |> List.map (fun e -> e.term) in
                     let vres = match el with 
                       | [a;l] when Sugar.lid_equals d.v (fst arr.arr_sel) -> 
                           let tm, p = snd arr.arr_sel tl a l in 
                           let tm = PP(tm,p) in
                           if not (!Options.monadic_subtyping) (* TODO: Revise heap typing! *)
                           then vresphi tm phis
                           else (match getSelHeapType() with
                             | None -> vresphi tm phis
                             | Some t ->
                               let {binding_phi=Some phi}, h = encodeTyp tenv (Some tm) t h in
                               vresphi tm (phi::phis))
                       | [a;l;v] when Sugar.lid_equals d.v (fst arr.arr_upd) -> 
                           let tm, p = snd arr.arr_upd tl a l v in 
                             vresphi (PP(tm,p)) phis
                       | _ when Sugar.lid_equals d.v (fst arr.arr_emp) -> 
                           let tm, p = snd arr.arr_emp in 
                             vresphi (PP(tm,p)) phis
                       | _ -> pr "Failed to encode array %A, d.v=%s, args=[%s]\n" arr (Sugar.text_of_lid d.v) (String.concat ", " (List.map (fun e -> e.ToString()) el)); raise Impos in 
                       
                       (* let _ = match result.tm with *)
                       (*   | PP(a,b) -> *)
                       (*       let _ = pr "Made array operation PP(%s,%s) \n" (a.ToString()) (b.ToString()) in *)
                       (*         () *)
                       (*   | _ -> raise Impos in *)
                       vres, h)
            
    | Exp_recd(Some rec_lid, targs, vargs, fn_e_l) -> 
        (* let tenv = {tenv with expect=Term_sort} in  *)
        let el = List.map snd fn_e_l in
        let tl_res, h = stmap targs (encodeTyp tenv None) h in 
        let el, h = stmap (vargs@el) (encodeValueVres tenv) h in 
        let recDname = recordConstrName rec_lid in 
        let tl = List.map (fun r -> r.term) tl_res in
        let phis = el |> List.collect (fun e -> e.subterm_phi) in
        let el = el |> List.map (fun e -> e.term) in 
        let args = tl@el in 
        let tm = Appl(recDname, arrowSort Term_sort args, (tl@el)) in 
          vresphi tm phis, h

    | Exp_proj(e1, fn) -> 
        (* let tenv = {tenv with expect=Term_sort} in  *)
        let e1_term, h = encodeValueVres tenv e1 h in 
        let projName = fieldProjector tenv e1.sort fn in
        let projection = Appl(projName, arrowSort Term_sort [e1_term.term], [e1_term.term]) in 
          vresphi projection e1_term.subterm_phi, h
            
    | Exp_abs _ 
    | Exp_tabs _ -> 
        let fterm, h = newTermConstant h in 
          vres fterm, h

    | Exp_ascribed(e, _, _) -> aux e h

    | Exp_primop(primop, el) -> 
       (* let tenv = {tenv with expect=Term_sort} in  *)
       let tms, h = stmap el (encodeValueVres tenv) h in 
       let phis = tms |> List.collect (fun t -> t.subterm_phi) in 
       let tms = tms |> List.map (fun t -> t.term) in 
       let tm = encodePrimop primop tms in 
         vresphi tm phis, h

    | Exp_app  _ -> 
       let rec aux args e' h = match e'.v with
         | Exp_app(e, arg) -> aux (arg::args) e h
         | Exp_fvar(fv, _) -> 
             let primop = string2ident (Pretty.str_of_lident fv.v) in 
             let e = ewithsort (Exp_primop(primop, args)) e.sort in 
               encodeValueVres tenv e h
                 (* encodeValueVres {tenv with expect=Term_sort} e h *)
         | _ -> raise Impos in
         aux [] e h 
           
    | Exp_tapp _ 
    | Exp_match _ 
    | Exp_cond _
    | Exp_let _ 
    | Exp_gvar _
    | Exp_extern_call _
    | Exp_bot _ -> raise Impos (* expression forms *) 
  in 
    aux e h

and encodeValue tenv v h = 
  let tm, h = encodeValueVres tenv v h in 
    tm.term, h

and encodeValueWithTyp tenv v h = 
  let tm, h = encodeValueVres tenv v h in 
    (tm.term,tm.subterm_phi), h
  (* let {binding_phi=Some phi}, h = encodeTyp tenv (Some tm) v.sort h in  *)
  (* let phi = match phi.tm with  *)
  (*   | Eq({tm=App("TypeOf", _, _)}, _) -> [] *)
  (*   | _ -> [phi] in *)
  (*   (tm, phi), h  *)
          
and encodeConstant tenv typ c h = 
  match c with 
    | Sugar.Const_unit -> unitTerm, h
    | Sugar.Const_bool b -> boxBool (boolTerm b), h
    | Sugar.Const_int32 i -> boxInt (Integer i), h
    | Sugar.Const_string(bytes, _) -> lookupStringConstant tenv bytes h
    | Sugar.Const_float f -> lookupFloatConstant tenv f h
    | _ -> 
        let fterm, h = newFunSym h in 
        let res, h = encodeTyp tenv None typ h in 
          fterm, h
            
and encodePrimop primop tms = match primop.idText, tms with 
  | "op_AmpAmp", [t1;t2] -> boxBool (And(unboxBool t1, unboxBool t2))
  | "op_BarBar", [t1;t2] -> boxBool (Or(unboxBool t1, unboxBool t2))
  | "_dummy_op_Negation", [t] -> boxBool (Not(unboxBool t))
  | "_dummy_op_Addition", _    
  | "_dummy_op_Subtraction", _ 
  | "_dummy_op_Multiply", _    
  | _ -> raise (NYI "Primop")

and lookupUvar tenv (uvar,k) h = 
  let st, h = get h in 
  let uvars = st.st.uvars in
    match uvars |> Util.findOpt (fun ((uvar', _), _, _) -> (Unionfind.equivalent uvar uvar')) with
      | Some (_, tm, _) -> tm, h
      | None -> 
          let {term=ktm}, h = encodeKind tenv None k h in 
          let tm, h = newTypSym (Some ktm) "" h in 
          let _, h = internUvar (uvar, k) tm [] h in 
            tm, h

and lookupStringConstant tenv b h = 
  let st, h = get h in 
  let strings = st.st.strings in
    match strings |> Util.findOpt (fun (b', _, _) -> b=b') with 
      | Some (_, tm, _) -> tm, h
      | None -> 
          let nm = cleanString b in(* Util.unicodeEncoding.GetString(b) in  *)
          let v, h = newName (spr "const_string_%s" nm) h in 
          let op = Assume(typeOfEq tenv.tcenv v (mk_Typ_const (typeNameOfLid Const.string_lid)), 
                          Some nm,
                          AName "string constant") in
          let tm, h = newStringConstant h in 
          let op' = Assume(Eq(boxString tm, v), None, AName "nm eq") in
          let _, h = addOps [op';op] h in 
          let _, h = internString b tm [op;op'] h in 
          let _, h = internString b v [op;op'] h in 
            v, h
              
and lookupFloatConstant tenv f h =
  let st, h = get h in 
  let floats = st.st.floats in
    match floats |> Util.findOpt (fun (f', _, _) -> f=f') with 
      | Some (_, tm, _) -> tm, h
      | None -> 
          let tm, h = newTermConstant h in 
          let op = Assume(typeOfEq tenv.tcenv tm (mk_Typ_const (typeNameOfLid Const.float_lid)), 
                          Some (spr "%f" f),
                          AName "float constant") in
          let _, h = addOps [op] h in 
          let _, h = internFloat f tm [op] h in 
            tm, h

and dedupAndEncodeFormula tenv f h : STR<phi> = 
  let f = if !Options.relational then project_vars_or_duplicate (tcenv tenv) f else f in 
    if !isQuery then (pr "Dedup'd query is %s\n" (f.ToString()); isQuery := false);
    encodeFormula tenv f h

and dedupAndEncodeTyp tenv tmopt t = 
  if !Options.relational then 
    let t = project_vars_or_duplicate (tcenv tenv) t in 
      encodeTyp tenv tmopt t >> (fun r -> ret (r,tenv))
  else 
    let tenv, t = norm tenv t in 
      encodeTyp tenv tmopt t >> (fun r -> ret (r, tenv))
  
        
and encodeFormula tenv f h : STR<phi> = 
#if CHECKED
  let phi, h = preEncodeFormula tenv (strip tenv f) h in 
  let termctx = h.termctx in 
    if (sortFromKind termctx tenv f.sort) <> phi.tmsort
    then raise (Bad (spr "Sorts diverge for %s\n Expected %A (%s) \n got %A\n" (f.ToString()) (sortFromKind termctx tenv f.sort) (f.sort.ToString()) phi.tmsort))
    else phi, h
and preEncodeFormula tenv f h : STR<phi> = 
   #endif 
  (* let _ = pr "Encoding formula %s\n" (Pretty.strTyp f) in  *)
 let mkQuant tenv mkQ binders body h : STR<phi> = 
   let body, pats = match strip tenv body with 
     | {v=Typ_meta(Meta_pattern(body, pats))} -> body, pats
     | body -> body, [] in 
   let tenv = List.fold_left (fun tenv -> function
                                | Inl (a, k) -> pushFormulaVar tenv (Tvar_binding(a, k, Type_sort, termref()))
                                | Inr (x,t1) -> pushFormulaVar tenv (Var_binding(x, t1, Term_sort, termref()))) tenv binders in 
    (* let _ = pr "Tenv in mkQuant: %s\n" (names tenv) in  *)
    (* let pats, h = stmap pats (function Inl t -> encodeFormula tenv t | Inr e -> encodeValue {tenv with expect=Heap_sort} e) h in  *)
   let nbinders = (List.length binders) - 1 in
   let (_, vars), h = stfold (nbinders, []) binders 
     (fun (ix,out) b h -> 
        match b with 
          | Inr(x,t) -> 
              let xterm = lookupBvar tenv (Absyn.bvd_to_bvar_s x t) in  
              let xref = match xterm.tm with BoundV(_, _, _, xref) -> xref | _ -> raise Impos in 
              let {binding_phi=g}, h = encodeTyp tenv (Some xterm) t h in 
                ((ix-1,((Inr x,xref), Term_sort, g)::out), h)
          | Inl(a,k) -> 
              let aterm = lookupBtvar tenv (Absyn.bvd_to_bvar_s a k) in  
              let aref = match aterm.tm with BoundV(_, _, _, aref) -> aref | _ -> raise Impos in 
              let {binding_phi=g}, h = encodeKind tenv (Some aterm) k h in 
                ((ix-1,((Inl a,aref), Type_sort, g)::out), h))
     h in 
   let body, h = encodeFormula tenv body h in 
   let tenv = {tenv with subterms=false} in 
   let pats, h = stmap pats (function Inl t -> encodeFormula tenv t | Inr e -> encodeValue tenv e) h in 
   let xs, sorts, guards = List.unzip3 (List.rev vars) in  
   let guard = mkAndOpt_l guards in 
     if tenv.query 
     then mkQ [] sorts xs guard body, h 
     else mkQ pats sorts xs guard body, h in
 let handleExistential tenv f h = 
   if not tenv.allow_residue then failwith "Unexpected residue in formula";
   match f.v with 
     | Typ_tlam(txname, txkind, body) ->
       let uvb = Unionfind.fresh (Uvar (fun t k -> true)) in  (* uvar for detecting cycles via an occurs check, but otherwise no environment constraints *)
       let uv = twithinfo (Typ_uvar (uvb, txkind)) txkind f.p in 
            (* let uv = TypeRelations.new_uvar env txkind f.p in *)
       let ({term=uv_tm}:res), h = encodeTyp tenv None uv h in
            (* let _ = txname.instantiation := Some uv in  *)
            (* let exform = body in (\* substitute_l body [(txname, uv)] in  *\) *)
       let pendingSubst = (txname, uv) in 
       let tenv, exform = norm tenv body in 
       (match destruct tenv exform Const.and_lid with 
         | Some [Inl guard; Inl body] ->
           let tenv = addPendingSubst tenv (txname,uv) in 
                     (* let _ = pr "In encodeExistential, guard is %s\n" (guard.ToString()) in  *)
           let guard, h = encodeFormula tenv guard h in 
           let tenv, body = norm tenv body in 
           let (guess, body), h = match destruct tenv body Const.and_lid with 
             | Some [Inl guess; Inl body] -> 
               let guess, h = encodeFormula tenv guess h in 
               (Some guess, body), h
             | _ -> (None, body), h in 
           let residue = MkResidue(uv_tm, (* uv.sort, *) guess,
                                   (fun _ _ h ->
                                     let formula = body in 
                                     let i, h = incrCtr h in 
                                     let _, h = addOp (Mark (Inr i)) h in                
                                                (* let _ = pr "Residue formula is %s\n" (formula.ToString()) in *)
                                     let tm, h = encodeFormula tenv formula h in 
                                     let ops, _ = takeUntil (function (Mark (Inr j)) -> i=j | _ -> false) h.st.ops in 
                                                  (* let _ = pr "Residue resolved to %s\n" (tm.ToString()) in *)
                                     (ops, tm), h)) in 
           Residue(guard, residue), h
         | _ -> failwith (spr "Expected conjunction in existsTx; got %s" (body.ToString())))
     |  _ -> raise Impos in 
 let range = f.p in 
 let tenv, f = norm tenv f in
 match f.v with
   | Typ_ascribed(t, _) -> encodeFormula tenv t h
            
   | Typ_meta (Meta_cases tl) -> 
     let tl, h = stmap tl (encodeFormula tenv) h in 
     Cases(tl), h
       
   | Typ_app({v=Typ_dep(lbl, str)}, f) when  AbsynUtils.is_constructor lbl Const.lbl_lid -> 
     if h.strip_labels then encodeFormula tenv f h 
     else 
       let sorig = match unascribe str with 
         | {v=Exp_constant(Sugar.Const_string(sorig,_))} -> sorig
         | _ -> raise Impos in
       let f, h = encodeFormula tenv f h in
       let sorig = Util.unicodeEncoding.GetString(sorig) in
       let pfx = sorig.Replace(' ', '_') in 
       let pfx = Util.unicodeEncoding.GetBytes("label_" ^ pfx) in 
       let term, h = match h.st.labels |> Util.findOpt (fun (s', _) -> sorig=s') with 
         | None -> 
           let fname,h = newPredSym (cleanString pfx) Kind_erasable h in 
           let term = FreeV(fname, Bool_sort) in 
           let h = {h with st={h.st with labels=(sorig,term)::h.st.labels}} in 
           term, h
         | Some (_, tm) -> 
           tm, h in 
       Or(f, term), h

   | Typ_app(t1, t2) when AbsynUtils.is_constructor t1 Const.unfold_lid -> 
     let {st={unfoldings=ufs}}, h = get h in 
     let rec unfold = function 
       | [] -> raise Impos (* failed to unfold *)
       | (binders,lhs,rhs)::tl -> 
         let f = AbsynUtils.subst_fast (get_substs tenv) f in (* Absyn.substitute_l_typ_or_exp f (subst_as_smap tenv) in  *)
         match TypeRelations.equivalent_with_equations tenv.tcenv binders lhs f with 
           | None -> unfold tl
           | Some(equations) -> 
                (* let _ = pr "Unfolding to rhs=%s with subst ... " (rhs.ToString()) in  *)
             let subst = equations |> List.map 
                 (function 
                   | Tcenv.Binding_match({v=Exp_bvar(bv)}, x) -> 
                        (* pr "%s --> %s" (strBvd bv.v) (x.ToString()); *)
                     (bvar_to_bvd bv, x) 
                   | _ -> raise Impos) in 
             Absyn.substitute_exp_l rhs subst in
     let ff = unfold ufs in 
        (* let _ = pr "Formula %s unfolded to\n %s\n" (f.ToString()) (ff.ToString()) in  *)
     let res, h = encodeFormula tenv ff h  in 
        (* let _ = pr "Encoding of unfolded formula done" in  *)
     res, h
       
   | Typ_app(t1,t2) when AbsynUtils.is_constructor t1 Const.exists_tx_lid -> 
     handleExistential tenv t2 h                               

   | Typ_app(t1, t2) when (AbsynUtils.is_constructor t1 Const.withpatterns_lid) ->
     encodeFormula tenv t2 h
       
   | Typ_fun(Some _, _, _) 
   | Typ_univ _ -> 
     let binders, body = AbsynUtils.collect_forall_xt f in 
     mkQuant tenv (mkPatsForall range) binders body h

   | Typ_app({v=Typ_app({v=Typ_const(fv, _)},t1)}, {v=Typ_lam(x, _, t2)})
       when Const.is_forall fv.v ->
       let binders, body = AbsynUtils.collect_forall_xt f in 
         mkQuant tenv (mkPatsForall range) binders body h
       
   | Typ_app({v=Typ_app({v=Typ_const(fv, _)},t1)}, {v=Typ_lam(x, _, t2)})
       when Const.is_exists fv.v -> 
     let binders, body = AbsynUtils.collect_exists_xt f in 
     mkQuant tenv (mkPatsExists range) binders body h

   | Typ_const _
   | Typ_app _
   | Typ_dep _  when isProp f.sort ->
     encodeConnectives tenv f h

   | Typ_btvar _
   | Typ_lam _ 
   | Typ_tlam _ 
   | Typ_unknown
   | Typ_uvar _
   | Typ_refine _
   | Typ_affine _
   | Typ_record _
   | _ -> raise (Error(spr "Unexpected type in encodeFormula\n%s\n" (f.ToString()), f.p)) 
          
and encodeConnectives  tenv (f:typ) h : STR<phi> = 
  match destructConnectives f with 
    | None -> 
        if isAtom tenv f 
        then encodeAtom tenv f h
        else raise (Z3Encoding (spr "Unexpected formula %s\n" (f.ToString())))
          
    | Some (lid, [Inl p]) when Sugar.lid_equals lid Const.reln_lid -> 
        let msg = spr "Found relational formula at %s: %s\n" (Range.string_of_range f.p) (Pretty.strTyp f)  in 
          raise (CatchMe(msg, f.p))
        
    | Some (lid, [Inl p; Inl {v=Typ_lam(_, _, p1)}; Inl {v=Typ_lam(_, _, p2)}]) 
        when (Sugar.lid_equals lid Const.ifthenelse_lid) -> 
        let t, h = encodeFormula tenv p h in
        let t1, h = encodeFormula tenv p1 h in
        let t2, h = encodeFormula tenv p2 h in
          And(Imp(t, t1), Imp(Not t, t2)), h
            
    (* | Some (lid, [Inl p1; Inl p2]) when (Sugar.lid_equals lid Const.and_lid && *)
    (*                                      AbsynUtils.is_constructor (AbsynUtils.strip_pf_typ p1) (Const.p2l ["Test";"PRED"])) ->  *)
    (*   let t1, h = encodeFormula tenv p1 h in *)
    (*   let t2, h = encodeFormula tenv p2 h in *)
    (*   pr "\n****Translated %s to %s\n****\n" (Pretty.strTyp p2) (t2.ToString()); *)
    (*   And(t1,t2),h *)
               
    | Some (lid, [Inl p1; Inl p2]) when not (Sugar.lid_equals lid Const.eqTyp_lid) -> 
        let t1, h = encodeFormula tenv p1 h in
        let t2, h = encodeFormula tenv p2 h in
          (if      lid=Const.and_lid     then And(t1,t2)
           else if lid=Const.or_lid      then Or(t1,t2)
           else if lid=Const.implies_lid then Imp(t1,t2)
           else if lid=Const.iff_lid     then Iff(t1,t2)
           else raise Impos), h

    | Some (lid, [Inl p])          when lid=Const.not_lid -> 
        let t, h = encodeFormula tenv p h in 
          Not t, h

    | Some (lid, [Inl p])          when lid=Const.spec_only_lid -> 
        if tenv.erase_spec_only 
        then True(), h
        else encodeFormula tenv p h 

    | Some (lid, [Inr v1; Inr v2])   when lid=Const.gt_lid -> 
        let (t1,phi1), h = encodeValueWithTyp tenv v1 h in 
        let (t2,phi2), h = encodeValueWithTyp tenv v2 h in 
          mkConj tenv (GT(unboxInt t1, unboxInt t2)) (List.flatten [phi1;phi2]), h
            
    | Some (lid, [Inr v1; Inr v2])   when lid=Const.lt_lid -> 
        let (t1,phi1), h = encodeValueWithTyp tenv v1 h in 
        let (t2,phi2), h = encodeValueWithTyp tenv v2 h in 
          mkConj tenv (LT(unboxInt t1, unboxInt t2)) (List.flatten [phi1;phi2]), h
            
    | Some (lid, [Inr v1; Inr v2])   when lid=Const.gte_lid -> 
        let (t1,phi1), h = encodeValueWithTyp tenv v1 h in 
        let (t2,phi2), h = encodeValueWithTyp tenv v2 h in 
          mkConj tenv (GTE(unboxInt t1, unboxInt t2)) (List.flatten [phi1;phi2]), h
            
    | Some (lid, [Inr v1; Inr v2])   when lid=Const.lte_lid -> 
        let (t1,phi1), h = encodeValueWithTyp tenv v1 h in 
        let (t2,phi2), h = encodeValueWithTyp tenv v2 h in 
          mkConj tenv (LTE(unboxInt t1, unboxInt t2)) (List.flatten [phi1;phi2]), h

    (* | Some (lid, [Inl t; Inr e1; Inr e2]) when is_heap_typ t && AbsynUtils.is_lid_equality lid ->  *)
    (*     let t1, h = encodeValue tenv e1 h in  *)
    (*     let t2, h = encodeValue tenv e2 h in  *)
    (*       Eq(t1, t2), h *)

    | Some (lid, [Inl t1; Inl t2]) when Sugar.lid_equals lid Const.eqTyp_lid -> 
        let {term=t1}, h = encodeTyp tenv None t1 h in 
        let {term=t2}, h = encodeTyp tenv None t2 h in 
          Eq(t1, t2), h
            
    | Some (lid, [Inl _; Inl _; Inr e1; Inr e2]) 
    | Some (lid, [Inl _; Inr e1; Inr e2]) when AbsynUtils.is_lid_equality lid -> 
        let (t1, phi1), h = encodeValueWithTyp tenv e1 h in 
        let (t2, phi2), h = encodeValueWithTyp tenv e2 h in 
          mkConj tenv (Eq(t1, t2)) (List.flatten [phi1;phi2]), h
            
    | Some _ -> raise Impos 
          
and encodeAtom tenv (p_orig:typ) h : STR<tm> = 
  let p, args = flattenTypAppsAndDeps p_orig in
    if (AbsynUtils.is_constructor p Const.forall_lid ||
        AbsynUtils.is_constructor p Const.forallP_lid ||
        AbsynUtils.is_constructor p Const.forallA_lid)
    then      
      (let _  = pr "Unexpected quantifier in atom!\n" in 
       let _ = match args with 
         | [Inl _; Inl ({v=Typ_lam _})] -> pr "Second arg is a typ_lam"
         | [Inl _; Inl t2] -> pr "Second arg is %A\n" t2
         | _ -> pr "Unexpected %d args\n" (List.length args) in 
         raise Impos);
    encodePredicate tenv p args h

and encodePredicate tenv p args h : STR<tm> = 
  let encodeTypOrValue tenv tv h = match tv with
    | Inl t -> let res, h = encodeTyp tenv None t h in (res.term,[]), h
    | Inr e -> encodeValueWithTyp tenv e h in
  let porig = p in
  let tenv, p = norm tenv p in 
  let tctx = h.termctx in 
    match p.v, args with 
      | Typ_const(tc, _), [] when Sugar.lid_equals tc.v Const.true_lid -> 
          True(), h
      | Typ_const(tc, _), [] when Sugar.lid_equals tc.v Const.false_lid -> 
          False(), h
      | Typ_const(tc, _), args when is_array_function tctx tc.v ->
          (match lookup_array_function tctx tc.v with 
             | None -> raise Impos
             | Some arr -> 
                 let targs, vargs = args |> List.partition (function Inl _ -> true | Inr _ -> false) in 
                 let t_phi_l,h = stmap targs (encodeTypOrValue tenv) h in 
                 let e_phi_l,h = stmap vargs (encodeTypOrValue tenv) h in 
                 let tl, _ = List.unzip t_phi_l in 
                 let el, phis = List.unzip e_phi_l in 
                 let result = match el with 
                   | [a;d] -> let tm,p = snd arr.arr_indom tl a d in PP(tm,p)
                   | _ -> raise Impos in 
                   mkConj tenv result (List.flatten phis), h)

      | Typ_const(tc, _), _  -> 
          (match is_tfun false h.termctx tenv p with
             | Some (predName,_,Sugar.Logic_discriminator,_) -> 
                 let tms_phis_l, h = stmap args (encodeTypOrValue tenv) h in 
                 let tms, phis = List.unzip tms_phis_l in 
                 let tm = Appl(predName, arrowSort Bool_sort tms, tms) in
                   mkConj tenv tm (List.flatten phis), h 
             | Some (nm,_,Sugar.Logic_projector,_) -> 
                 let rec mkHolds t k args = match k, args with
                   | Kind_tcon(_, _, k), Inl arg::args -> 
                       let t = twithsort (Typ_app(t, arg)) k in 
                         mkHolds t k args 
                   | Kind_dcon(_, _, k), Inr arg::args -> 
                       let t = twithsort (Typ_dep(t, arg)) k in 
                       let {term=t}, h = encodeTyp tenv None t h in
                       let holds, h = maybeAddHoldsPred k h in                        
                       let args_phis_l, h = stmap args (encodeTypOrValue tenv) h in 
                       let args, phis = List.unzip args_phis_l in
                       let tm = Appl(holds, Arrow(Type_sort, debugSortFromKind p.sort), t::args) in 
                         mkConj tenv tm (List.flatten phis), h
                   | _ -> 
                       let _ = pr "Unexpected projector %s with kind %s\n" nm (Pretty.strKind p.sort) in 
                         raise Impos in 
                   mkHolds p p.sort args 
             | _ ->
                 if Const.is_forall tc.v
                 then (pr "Unexpected quantifier in atom!\n porig=%s\n p=%s\n" 
                         (Pretty.strTyp porig) (Pretty.strTyp p);
                       raise Impos);
                 let predName = predNameOfLid tc.v in 
                 let tms_phis_l, h = stmap args (encodeTypOrValue tenv) h in 
                 let tms, phis = List.unzip tms_phis_l in
                 let tm = Appl(predName, arrowSort Bool_sort tms, tms) in
                   mkConj tenv tm (List.flatten phis), h)
      | Typ_btvar _, _  
      | Typ_uvar _, _ -> 
          let {term=t}, h = encodeTyp tenv None p h in
          let holds, h = maybeAddHoldsPred p.sort h in
          let args_phis_l, h = stmap args (encodeTypOrValue tenv) h in 
          let args,phis = List.unzip args_phis_l in
          let tm = Appl(holds, Arrow(Type_sort, debugSortFromKind p.sort), t::args) in 
            mkConj tenv tm (List.flatten phis), h
      | _ -> raise (Bad (spr "Unexpected predicate: %s\n" (Pretty.strTyp p)))

and encodeCompleteFormula tenv (f:typ) h : STR<phi> = 
  dedupAndEncodeFormula {tenv with allow_residue=false} f h
    
let encodeKind' (binding:option<tm>) (k:kind) h : STR<res> = 
  let st, h = get h in 
    encodeKind (mkTransenv st.st.env) binding k h

let encodeTyp' (binding:option<tm>) (t:typ) h : STR<res> = 
  let st, h = get h in 
    encodeTyp (mkTransenv st.st.env) binding t h

let encodeFormula' (f:typ) st : STR<phi> =
    dedupAndEncodeFormula (mkTransenv st.st.env) f st

let encodeQuery (f:typ) st : STR<phi> =
  (* isQuery := true; *)
  dedupAndEncodeFormula {(mkTransenv st.st.env) with query=true} f st 

let encodeCompleteFormula' (f:typ) st : STR<phi> =
    encodeCompleteFormula (mkTransenv st.st.env) f st
    
(* ******************************************************************************** *)
(* Encoding signatures *)
(* ******************************************************************************** *)
let is_qop = function 
  | {tm=Forall _} -> true
  | _ -> false

let lookupDiscriminator (tenv:transenv<'a>) (d:lident) = 
  let ns, nm = Util.pfx d.lid in 
  let nm' = ident(spr "%s_is" (nm.idText), nm.idRange) in 
  let discName = asLid <| ns@[nm'] in 
  match Tcenv.lookup_typ_lid tenv.tcenv discName with 
    | Kind_unknown -> None
    | k -> 
      let primitiveDiscName = spr "is-%s" (funNameOfConstr d) in
      Some (primitiveDiscName, k)

let addKindingAssumption tlid tname k : ST<unit> = 
  get >> (fun {st={env=Some tcenv}; termctx=termctx} -> 
    let tenv_orig = mkTransenv (Some tcenv) in 
    let tc = AbsynUtils.mkTypConst tlid in 
    let addIt ctr binders k = 
      let (_, tenv, sorts, vars, args, typ) = 
        List.fold_right (fun b (ix, tenv, sorts, vars, args, typ) -> match b with
          | Inl (a, k1) -> 
            let v = new_bvd None in
            let vref = termref () in
            let tenv = push tenv (Formula(Tvar_binding(a, k, Type_sort, vref))) in 
            let varg = Inl(BoundV(ix, Type_sort, v.ppname.idText, vref), k1) in 
            let typ = AbsynUtils.Wt (Typ_app(typ, bvd_to_typ a k1)) in
            (ix-1, tenv, Type_sort::sorts, ((Inl v, vref)::vars), varg::args, typ)
              
          | Inr (x, t) -> 
            let v = new_bvd None in 
            let vref = termref() in 
            let tenv = push tenv (Formula(Var_binding(x, t, Term_sort, vref))) in 
            let varg = Inr(BoundV(ix, Term_sort, v.ppname.idText, vref),t) in 
            let typ = AbsynUtils.Wt (Typ_dep(typ, bvd_to_exp x t)) in
            (ix-1, tenv, Term_sort::sorts, ((Inr v, vref)::vars), varg::args, typ))
          binders (List.length binders - 1, tenv_orig, [], [], [], tc) in 
      let sorts = List.rev sorts in 
      let vars = List.rev vars in 
      let args = List.rev args in 
      encodeTyp tenv None typ >>
        (fun {term=tm} -> encodeKind tenv (Some tm) k >>
          (fun {binding_phi=Some kof} -> 
            Util.stmap args (function 
              | Inl(var, k) -> 
                encodeKind tenv (Some var) k >> (fun {binding_phi=Some g} -> ret g)
              | Inr(var, t) ->
                encodeTyp tenv (Some var) t >> (fun  {binding_phi=Some g} -> ret g)) >>
              (fun guards -> 
                let phi = match sorts with 
                  | [] -> kof
                  | _ -> Forall([kindOf tm], 
                                Array.ofList sorts, 
                                Array.ofList vars, 
                                Imp(mkAnd guards, kof)) in 
                addOps [Assume(phi, None, AName (spr "Kinding %d for %s" ctr tname))])))
    in 

    let rec aux i binders k = 
      addIt i binders k 
        >> (fun _ -> match k with
          | Kind_star 
          | Kind_prop
          | Kind_erasable
          | Kind_affine -> ret ()
          | Kind_tcon(aopt, k1, k2) -> 
            let binder = match aopt with 
              | None -> Inl(new_bvd None, k1)
              | Some a -> Inl (a, k1) in
            aux (i + 1) (binder::binders) k2
          | Kind_dcon(xopt, t1, k2) -> 
            let binder = match xopt with 
              | None -> Inr (new_bvd None, t1)
              | Some x -> Inr (x, t1) in
            aux (i + 1) (binder::binders) k2
          | _ -> raise Impos) in 
           
    if Sugar.lid_equals tlid Const.typeof_lid 
    then addIt 0 [] k
    else aux 0 [] k)
  
let addTypingAssumption dname mk_term t : ST<unit> = 
  get >> (fun {st={env=Some tcenv}; termctx=termctx} -> 
    let tenv_orig = mkTransenv (Some tcenv) in 
    let fname = funNameOfConstr dname in 
    let rec aux (tenv, sorts, vars, args, kts, ix) tt = match tt.v with
      | Typ_fun(xopt, t1, t2) -> 
        let v = new_bvd None in 
        let vref = termref () in 
        let varg = BoundV(ix, Term_sort, v.ppname.idText, vref) in 
        let tenv = match xopt with
          | None -> push tenv (Formula(Var_binding(v, t1, Term_sort, vref)))
          | Some x -> push tenv (Formula(Var_binding(x, t1, Term_sort, vref))) in
        aux (tenv, Term_sort::sorts, (Inr v, vref)::vars, varg::args, (Inr t1)::kts, ix - 1) t2
      | Typ_univ(a, k, _, t) -> 
        let v = new_bvd None in 
        let vref = termref () in 
        let varg = BoundV(ix, Type_sort, v.ppname.idText, vref) in 
        let tenv = push tenv (Formula (Tvar_binding(a, k, Type_sort, vref))) in
        aux (tenv, Type_sort::sorts, (Inl v, vref)::vars, varg::args, (Inl k)::kts, ix - 1) t
      | _ -> 

        let tm = mk_term (debugSortFromTyp tenv t) (List.rev args) in 
                (* Appl(dname, debugSortFromTyp termctx tenv t, List.rev args) in  *)
        dedupAndEncodeTyp tenv (Some tm) tt
        >> (fun ({binding_phi=Some typeOfTm}, _) -> 
                  (* let _ = pr "Encoding type %s as %s\n" (Pretty.strTyp tt) (typeOfTm.ToString()) in *)
          match sorts with 
            | [] -> addOp (Assume(typeOfTm, None, AName(spr "%s typing" fname)))
            | _ -> 
              let vkts = List.zip args kts in 
                (if !Options.relational 
                 then ret []
                 else Util.stmap vkts (function 
                                        | (var, Inl k) -> 
                                            encodeKind tenv (Some var) k >> (fun {binding_phi=Some g} -> ret g)
                                        | (var, Inr t) ->
                                            encodeTyp tenv (Some var) t >> (fun  {binding_phi=Some g} -> ret g)))
                >> (fun guards -> 
                      let pats = match typeOfTm.tm with 
                        | Eq(t1, t2) -> [t1]
                        | _ -> [] in 
                      let phi = Forall(pats,
                                       Array.ofList <| List.rev sorts,
                                       Array.ofList <| List.rev vars,
                                       (match guards with [] -> typeOfTm | _ -> Imp(mkAnd guards, typeOfTm))) in
                      let op = Assume(phi, 
                                      None, 
                                      AName (spr "%s typing" fname)) in 
                        addOp op)
                >> (fun _ ->  (* inversions *)
                      if !Options.relational then ret ()
                      else
                        let proj i = spr "Primitive_%s_proj_%d" fname i in
                          match lookupDiscriminator tenv dname with
                            | None -> ret ()
                            | Some (discName, discK) -> 
                                let x = new_bvd None in 
                                let xref = termref() in 
                                let xarg = BoundV(0, Term_sort, x.ppname.idText, xref) in 
                                let guard1 = Appl(discName, Arrow(Term_sort, Bool_sort), [xarg]) in 
                                let rec aux i tenv concs t = match t.v with 
                                  | Typ_fun(xopt, t1, t2) ->
                                      let tm = Appl(proj i, Arrow(Term_sort, Term_sort), [xarg]) in 
                                        encodeTyp tenv (Some tm) t1 >> (fun {binding_phi=Some conc} -> 
                                                                          let tenv = match xopt with 
                                                                            | None ->  tenv
                                                                            | Some x -> 
                                                                                let tref = termref() in 
                                                                                  tref := Some tm;
                                                                                  push tenv (Formula(Var_binding(x, t1, Term_sort, tref))) in 
                                                                            aux (i + 1) tenv (conc::concs) t2)
                                          
                                  | Typ_univ(a, k, _, t) -> 
                                      let tm = Appl(proj i, Arrow(Term_sort, Type_sort), [xarg]) in 
                                        encodeKind tenv (Some tm) k >> (fun {binding_phi=Some conc} -> 
                                                                          let tenv = 
                                                                            let tref = termref() in 
                                                                              tref := Some tm;
                                                                              push tenv (Formula(Tvar_binding(a, k, Type_sort, tref))) in 
                                                                            aux (i + 1) tenv (conc::concs) t)
                                  | _ -> 
                                      let t = AbsynUtils.unrefine t in
                                        encodeTyp tenv (Some xarg) t >> (fun {binding_phi=Some guard2} -> 
                                                                           let guard = And(guard1, guard2) in 
                                                                           let phi = Forall([guard1], 
                                                                                            [| Term_sort |],
                                                                                            [|(Inl x, xref)|],
                                                                                            Imp(guard, mkAnd concs)) in 
                                                                           let op = Assume(phi, 
                                                                                           None, 
                                                                                           AName (spr "%s typing inversion" fname)) in 
                                                                             addOp op) in
                                  aux 0 tenv_orig [] t)) in 
      aux (tenv_orig, [], [], [], [], (List.length (sortsFromTyp t) - 1)) t)

let mkLogicFunction __D_lid top_t : ST<unit> = 
  get >> (fun st ->
            let tenv = mkTransenv st.st.env in
            let rec aux ix qsorts tenv t : ST<unit> = 
              match t.v with
                | Typ_univ(a, k, _, t) ->
                    (* (encodeKind tenv None k) >> (fun res ->  *)
                    let qsorts = Type_sort::qsorts in 
                    let tenv = pushFormulaVar tenv (Tvar_binding(a, k, Type_sort, termref())) in
                      aux (ix+1) qsorts tenv t(* ) *)

                | Typ_fun(xopt, t1, t2) -> 
                    let x = getBvd xopt in
                    let s = Term_sort in 
                    let tenv = pushFormulaVar tenv (Var_binding(x, t1, s, termref())) in
                      aux (ix+1) (s::qsorts) tenv t2
                        
                | _ -> 
                    let qsorts = List.rev qsorts in
                    let resultSort = Term_sort in 
                    let __D = funNameOfConstr __D_lid in 
                    let df = mkFunSym __D qsorts resultSort in 
                    (addOps [df]                 (* Adding this typing assumption causes a failure for JSVerify *)
                     >> (fun _ -> 
                       if !Options.logic_function_typing 
                       then addTypingAssumption __D_lid (fun sort args -> Appl(__D, sort, args)) top_t
                       else ret ())) in
            aux 0 [] tenv top_t)

let dataconOfRecord se = match se with
  | Sig_record_typ(__R_lid, tps, k, {v=Typ_record(fn_t_l, _)}, _) -> 
      let k_r = Tcenv.tycon_kind_from_tparams tps k in
      let rec_typ = twithsort (Typ_const(fvwithsort __R_lid k, None)) k_r in
      let rec_typ = List.fold_left (fun out tp -> match tp with 
                                      | Tparam_typ(a, k) -> 
                                          let t_a = bvd_to_typ a k in 
                                            Tcutil.mkTypApp out t_a
                                      | Tparam_term(x,t) -> 
                                          let v_x = bvd_to_exp x t in
                                            Tcutil.mkTypDep out v_x) rec_typ tps in
      let data_lid = recordConstrLid __R_lid in 
      let data_typ =
        (rec_typ |> (fn_t_l |> List.fold_right
                         (fun (fn,t) out -> twithsort (Typ_fun(None, t, out)) out.sort))) in
        [Sig_tycon_kind(__R_lid, tps, k, false, [], []);
         Sig_datacon_typ(data_lid, tps, data_typ, None, Public, Some __R_lid, None, [])], rec_typ

  | _ -> raise Impos
                
let rec encodeSigelt : sigelt -> ST<unit> = function (* fun se -> *)
  (* pr "Encoding sigelt %s\n" (Sugar.text_of_lid (lid_of_sigelt se)); *)
  (* match se with *)
  | Sig_typ_abbrev _  -> ret ()

  | Sig_extern_typ(_, se) -> encodeSigelt se

  (* Abstract function symbols *)
  | Sig_value_decl(lid, t)
  | Sig_extern_value(_, lid, t) -> 
       (* let t = AbsynUtils.set_hashkeys t in  *)
       get >> (fun st -> 
       let tenv = mkTransenv st.st.env in 
       let fvar = fvwithsort lid t in 
       let name = funNameOfFvar lid in 
       let tm = mkTerm name in
       (* let _ = pr "!!!!!!!!!!!!Deduping %s : %s\n"  (Pretty.sli lid) (Pretty.strTyp t) in  *)
       (dedupAndEncodeTyp tenv (Some tm) t >> (fun ({term=tm_t; binding_phi=Some phi_b}, tenv) -> 
       let df = mkConstant name Term_sort in       (* :extrafuns ((name Term)) *)
       let ops = [mkAssumption name phi_b;df] in   (* :assumption (= (TypeOf name) ... ) *)
         addOps ops)))
        
  (* Axioms *)
  | Sig_datacon_typ(lid, [], formula, Some _, _, _, _, _) when is_unfold_lid lid -> 
      (* let formula = AbsynUtils.set_hashkeys formula in  *)
      get >> (fun st -> 
      let tenv = mkTransenv st.st.env in
      let tenv, formula = norm tenv formula in 
        match destruct tenv formula Const.forall_lid with 
          | None -> raise Impos
          | Some _ -> 
              let binders, body = collect_u_quants formula in 
              let tenv, body = norm tenv body in 
                match destruct tenv body Const.eqTyp_lid with 
                  | Some([Inl lhs; Inl unfolding]) -> 
                      pr "Given formula %s\n body %s\n Adding unfolding of %s to %s\n" (formula.ToString()) (body.ToString()) (lhs.ToString()) (unfolding.ToString());
                      addUnfolding (binders |> List.map (fun (bvd,t) -> bvd_to_bvar_s bvd t), lhs, unfolding)
                        (* >> (fun _ -> ret (pr "Done adding unfolding")) *)
                  | _ -> raise Impos)

  | Sig_datacon_typ(lid, [], formula, Some Sugar.Assumption, _, _, _, _) ->
      (* let formula = AbsynUtils.set_hashkeys formula in  *)
    
      get >> (fun st -> 
        (encodeCompleteFormula {(mkTransenv st.st.env) with erase_spec_only=true} formula) >> (fun phi ->     (* :assumption (phi) *)
          let op1 = mkAssumption (funNameOfFvar lid) phi in
          if is_qop phi && !Options.separate_qops
          then addQops [op1]
          else addOps [op1]))
        
  | Sig_datacon_typ(lid, [], formula, Some Sugar.Definition, _, _, _, _) ->
      (* let formula = AbsynUtils.set_hashkeys formula in  *)

      get >> (fun st ->
      let tenv = mkTransenv st.st.env in 
      let rec remove_refinements f = match (strip tenv f).v with 
        | Typ_univ(a, k, c, t) -> twithsort (Typ_univ(a, k, c, remove_refinements t)) f.sort 
        | Typ_fun(xopt, t1, t2) -> twithsort (Typ_fun(xopt, AbsynUtils.unrefine t1, remove_refinements t2)) f.sort 
        | Typ_app({v=Typ_app(t,t1); sort=s1}, {v=Typ_lam(x, _, t2); sort=s2})
            when (AbsynUtils.is_constructor t Const.forall_lid ||
                    AbsynUtils.is_constructor t Const.forallP_lid ||
                    AbsynUtils.is_constructor t Const.forallA_lid) -> 
            twithsort (Typ_app(twithsort (Typ_app(t, AbsynUtils.unrefine t1)) s1,
                               twithsort (Typ_lam(x, AbsynUtils.unrefine t1, remove_refinements t2)) s2)) f.sort
        | _ -> f in 
      let rec collect_vars f = match f.tm with 
        | Imp(_, {tm=Eq({tm=App(f, tms, _)}, t2)})
        | Eq({tm=App(f, tms, _)}, t2) -> 
            let rec rsort = function
              | Arrow(_, b) -> rsort b
              | s -> s in 
              [],f,t2,rsort tms
        | Forall([], sorts, args, {tm=Imp(_, body)})
        | Forall([], sorts, args, body) -> 
            let formals', f, body, tms = collect_vars body in
            let formals = List.ofArray <| (args |> Array.map2 (fun s (x, _) -> 
                                                                 let x = match x with 
                                                                   | Inl btv -> btv.realname.idText
                                                                   | Inr bvv -> bvv.realname.idText in 
                                                                   x, s) sorts) in
              formals@formals', f, body, tms
        | _ -> pr "Unexpected formula %s\n" (f.ToString()); raise Impos in 
      let formula = remove_refinements formula in
      addOp (Mark (Inr -1)) >> (fun _ -> 
        (encodeFormula {(mkTransenv st.st.env) with erase_spec_only=true; subterms=false} formula) >> 
          (fun phi ->    
            let nm = funNameOfFvar lid in
            let formals, f, def, tms = collect_vars phi in 
            get >> (fun st -> 
              let ops, (Mark _::rest) = takeUntil (function (Mark (Inr -1)) -> true | _ -> false) st.st.ops in 
              let opState' = {st.st with ops=rest} in
              let st = {st with st=opState'} in
              put st >> (fun _ -> 
                let newops = DefineFun(f, Array.ofList formals, tms, def, Some nm)::ops in 
                replaceDeclaration f newops)))))
  (* removeDeclaration f >> (fun _ -> *)
  (*   addOps [DefineFun(f, Array.ofList formals, tms, def, Some nm)]))) *)
  (* Using replace instead of removeDecl breaks JSVerify: *)

  | Sig_ghost_assume(lid, formula, _)
  | Sig_query(lid, formula) -> 
      (* let formula = AbsynUtils.set_hashkeys formula in  *)
      (encodeCompleteFormula' formula) >> (fun phi ->     (* :assumption (phi) *) 
       let op1 = mkAssumption (funNameOfFvar lid) phi in
         addOps [op1])

  (* Type functions *)
  | Sig_tycon_kind(dlid, _, k, _, _, [Sugar.Logic_discriminator]) -> 
      get >> (fun {termctx=tctx} -> 
      let ds = Arrow(Term_sort, Bool_sort) in
      (* let ds = debugSortFromKind k in *)
      let pfx, nmid = Util.pfx dlid.lid in
      let nm = nmid.idText in
      let nm = nm.Substring(0, nm.Length - 3) in
      let nm = funNameOfConstr (asLid <| pfx@[ident(nm, nmid.idRange)]) in  
      let sorts = kindToSorts tctx k in 
      let formals = sorts |> List.mapi (fun i s -> spr "tm%d" i, s) in 
      let flid = funNameOfConstr dlid in 
      tctx.funSymMap.addTfun (dlid,(flid,debugSortFromKind k,Sugar.Logic_discriminator));
      addOps [DefineFun(flid, Array.ofList formals, Bool_sort, 
                        App(mkTester nm, ds, [| BoundV(0, Term_sort, spr "tm%d" (List.length formals - 1), termref()) |]), 
                        Some ("Definition_"^flid))])

  | Sig_tycon_kind(lid, tps, k, isProp, _, [Sugar.Logic_projector]) ->

    (match tps with 
      | _::_ -> raise Impos
      | [] -> 
        get >> (fun {termctx=tctx} ->
          let nm = typeNameOfLid lid in
          (* let _ = pr "Got logic t projector %s as name %s\n" (Pretty.sli lid) nm in  *)
          let builtin = "Primitive_" ^ (funNameOfConstr lid) in
          let bv0, formals =
            let rec formals (out,ix) k = match k with
              | Kind_tcon(_,_,k) -> formals ((spr "typ%d" ix, Type_sort)::out, ix + 1) k
              | Kind_dcon(_,_,k) -> 
                  let p = (spr "tm%d" ix, Term_sort) in 
                    fst p, List.rev (p::out)                  (* formals ((spr "tm%d" ix, Term_sort)::out, ix + 1) k *)
              | _ -> raise Impos in
              formals ([],0) k in
          let ds = List.fold_right (fun (_, s) ds -> Arrow(s, ds)) formals Type_sort in
          tctx.funSymMap.addTfun (lid,(nm,ds,Sugar.Logic_projector));
            addOps [DefineFun(nm, Array.ofList formals, (* [| formal |],  *)
                              Type_sort,
                              App(builtin, Arrow(Term_sort, Type_sort), [| BoundV(0, Term_sort, bv0, termref()) |]),
                              Some ("Definition_"^nm))] 
          >> (fun _ -> 
            if isProp
            then let name = predNameOfLid lid in
                 let sorts = kindToSorts tctx k in (* :extrapred ((name Type1...Typen Term1...Termn)) *)
                 addOp (mkPred name sorts)
            else ret ())))

  | Sig_tycon_kind(lid, [], k, isProp, _, [Sugar.Logic_tfun]) -> 
      get >> (fun {termctx=tctx} -> 
      let sorts_l = kindToSorts tctx k in 
      let ds = List.fold_right (fun s ds -> Arrow(s, ds)) sorts_l Type_sort in 
      let nm = tfunNameOfLid lid in 
      tctx.funSymMap.addTfun (lid,(nm,ds,Sugar.Logic_tfun));
        let sorts = Array.ofList <| sorts_l in 
        let op = DeclFun(nm, sorts, Type_sort, None) in 
          addOp op
          >> (fun _ -> 
                if not isProp then ret ()
                else addOp (mkPred (predNameOfLid lid) sorts_l)))
        
  (* Array types *)
  | Sig_tycon_kind(lid, [], Kind_star, _, _, [Sugar.Logic_array larr]) -> 
      get >> (fun {termctx=tctx; st={env=Some tcenv}} ->
      let sel_t = Tcenv.lookup_lid tcenv (larr.array_sel) in
      let tenv = mkTransenv (Some tcenv) in 
      let rec mk_array qvars sel_t = match sel_t.v with 
        | Typ_univ(a, k, _, t) ->  mk_array ((a,k)::qvars) t 
        | Typ_fun(_, {v=Typ_const(tc, _)}, {v=Typ_fun(_, dom, range)}) -> 
            let tenv = List.fold_right 
              (fun (a,k) tenv -> push tenv (Tvar_binding(a, k, Type_sort, termref()))) 
              qvars tenv in 

            let dom_sort = arrayDomSortFromTyp tcenv dom in 
            let range_sort = Pseudo_term_opt_sort in 
            let arr_sort = Array(dom_sort, range_sort) in 
            let arr_constr_name = arrConstrName lid in 
            let mk_arr_term arr = App(arr_constr_name, Arrow(arr_sort, Term_sort), [| arr |]) in 
            let arr_proj h = App(mkProj arr_constr_name 0, Arrow(Term_sort, arr_sort), [|h|]) in
            let targs = List.rev <| (qvars |> List.map (fun (a,k) -> (genident None).idText, Type_sort)) in 

            let arr_sel_sort = List.fold_right (fun _ t -> Arrow(Type_sort, t)) targs (Arrow(Term_sort, Arrow(Term_sort, Term_sort))) in 
            let arr_sel targs h d = 
              (p2t (ptsome_proj_0 (Select(arr_proj h, unboxTerm dom_sort d))), 
               App(funNameOfConstr larr.array_sel, arr_sel_sort, (Array.ofList (targs@[h; d])))) in 
              
            let sel_op = DefineFun(funNameOfConstr larr.array_sel, 
                                   Array.ofList (targs@[("h", Term_sort);
                                                        ("d", Term_sort)]),
                                   Term_sort,
                                   fst <| arr_sel []
                                       (BoundV(1, Term_sort, "h", termref()))
                                       (BoundV(0, Term_sort, "d", termref())), 
                                   None) in 
              
            let arr_upd_sort = List.fold_right (fun _ t -> Arrow(Type_sort, t)) targs (Arrow(Term_sort, Arrow(Term_sort, Arrow(Term_sort, Term_sort)))) in 
            let arr_upd targs h d f = 
              (mk_arr_term (Update(arr_proj h, unboxTerm dom_sort d, ptsome (t2p f))),
               App(funNameOfConstr (larr.array_upd), arr_upd_sort, (Array.ofList (targs@[h; d; f])))) in 
            let upd_op = DefineFun(funNameOfConstr larr.array_upd, 
                                   Array.ofList (targs@[("h", Term_sort);
                                                        ("d", Term_sort);
                                                        ("f", Term_sort)]),
                                   Term_sort,
                                   fst <| arr_upd []
                                       (BoundV(2, Term_sort, "h", termref()))
                                       (BoundV(1, Term_sort, "d", termref()))
                                       (BoundV(0, Term_sort, "f", termref())), 
                                   None) in 

            let upd_typing_op =
              let x, xref = new_bvd None, termref() in
              let xvar = BoundV(0, Term_sort, x.ppname.idText, xref) in
                Assume(Forall([], [|Term_sort|], [|(Inr x, xref)|],
                              (Imp(App(mkTester arr_constr_name, Arrow(Term_sort, Bool_sort), [|xvar|]),
                                   Eq(typeOf xvar, mk_Typ_const (typeNameOfLid lid))))),
                       None,
                       AName (spr "%s typing" arr_constr_name)) in
              
            let arr_emp = (mk_arr_term (ConstArray(strSort arr_sort, arr_sort, ptnone)),
                           Appl(funNameOfConstr larr.array_emp, arr_sort, [])) in 
            let emp_op = DefineFun(funNameOfConstr larr.array_emp, 
                                   [| |], 
                                   Term_sort, 
                                   fst arr_emp, 
                                   None) in
            let emp_typing_op = 
              Assume(typeOfEq tcenv (PP(arr_emp)) (mk_Typ_const (typeNameOfLid lid)), 
                     None, 
                     AName (spr "%s typing" (funNameOfConstr larr.array_emp))) in 

            let arr_indom_sort = List.fold_right (fun _ t -> Arrow(Type_sort, t)) targs (Arrow(Term_sort, Arrow(Term_sort, Bool_sort))) in 
            let arr_indom targs h d = (App(mkTester ptsome_name, Arrow(Pseudo_term_opt_sort, Bool_sort), [|Select(arr_proj h, unboxTerm dom_sort d)|]),
                                       App(predNameOfLid larr.array_indom, arr_indom_sort, Array.ofList (targs@[h; d]))) in 
            let indom_op = DefineFun(predNameOfLid larr.array_indom, 
                                     Array.ofList (targs@[("h", Term_sort);
                                                          ("d", Term_sort)]),
                                     Bool_sort,
                                     fst <| arr_indom []
                                         (BoundV(1, Term_sort, "h", termref()))
                                         (BoundV(0, Term_sort, "d", termref())), 
                                     None) in 
              
            (* let lproj_name, rproj_name = spr "L_%s" (Sugar.text_of_lid lid), spr "R_%s" (Sugar.text_of_lid lid) in  *)
            (* let proj_ops = [DeclFun(lproj_name, [| arr_sort |], arr_sort, None); *)
            (*                 DeclFun(rproj_name, [| arr_sort |], arr_sort, None)] in  *)
            (* let projector side tm = match side with  *)
            (*   | Left -> App(lproj_name, Arrow(arr_sort, arr_sort), [| tm |]) *)
            (*   | Right -> App(rproj_name, Arrow(arr_sort, arr_sort), [| tm |]) *)
            (*   | Both -> tm in  *)

            let array_sort = {arr_sort=arr_sort;
                              arr_sel=(larr.array_sel, arr_sel);
                              arr_upd=(larr.array_upd, arr_upd);
                              arr_emp=(larr.array_emp, arr_emp);
                              arr_indom=(larr.array_indom, arr_indom);
                              arr_projector=(fun _ _ -> failwith "NYI")} in 
              upd (fun st -> {st with termctx={st.termctx with sortMap={st.termctx.sortMap with arraySorts=(lid,array_sort)::st.termctx.sortMap.arraySorts}}})
              >> (fun _ -> addOps [emp_typing_op; upd_typing_op; indom_op; emp_op; upd_op; sel_op]) in 
        mk_array [] sel_t)

  (* Predicate symbols *)
  | Sig_tycon_kind(lid, tps, k, isProp, muts, tags) when isProp -> 
      if config.skip_pf && Sugar.lid_equals lid Const.pf_lid then ret ()
      else
      get >> (fun st -> 
                if is_array_function st.termctx lid 
                then ret ()
                else
                  let k = Tcenv.tycon_kind_from_tparams tps k in 
                  let predName = predNameOfLid lid in 
                  let sorts_l = kindToSorts st.termctx k in
                    addOp (mkPred predName sorts_l)
                    >> (fun _ -> encodeSigelt (Sig_tycon_kind(lid, [], k, false, muts, tags)))
                    >> (fun _ ->    (* :extrapred ((name Type1...Typen Term1...Termn)) *)
                          let t = mk_Typ_const (typeNameOfLid lid) in 
                          let l = List.length sorts_l  in
                          let formals, actuals = List.unzip <| 
                              (sorts_l |> List.mapi 
                                   (fun i s -> 
                                      match s with 
                                        | Type_sort -> 
                                            let x = new_bvd None in 
                                            let xref = termref () in 
                                            let formal = Inl(x),xref in
                                            let actual = BoundV(l - i - 1, s, x.ppname.idText, xref) in
                                              formal, actual 
                                        | Term_sort -> 
                                            let x = new_bvd None in 
                                            let xref = termref () in 
                                            let formal = Inr(x),xref in
                                            let actual = BoundV(l - i - 1, s, x.ppname.idText, xref) in
                                              formal, actual )) in 
                          let predSort = List.fold_right (fun t out -> Arrow(t, out)) sorts_l Bool_sort in
                          let pred = Appl(predName, predSort, actuals) in
                          let rec addHoldsPreds t actuals k =
                            maybeAddHoldsPred k 
                            >> (fun holds -> 
                                  let holdsPred = Appl(holds, Arrow(Type_sort, debugSortFromKind k), t::actuals) in 
                                  let form = match sorts_l with 
                                    | [] -> Iff(holdsPred, pred)
                                    | _ -> mkPatsForall (Sugar.range_of_lid lid) [holdsPred] sorts_l formals None (Iff(holdsPred, pred)) in 
                                    addOp (Assume(form, None, AName (spr "Holds for pred %s" predName)))
                                    >> (fun _ -> match k with 
                                          | Kind_dcon(_, _, k) -> 
                                              let t = mk_Typ_dep t (List.hd actuals) in 
                                                addHoldsPreds t (List.tl actuals) k
                                          | Kind_tcon(_, _, k) -> 
                                              let t = mk_Typ_app t (List.hd actuals) in 
                                                addHoldsPreds t (List.tl actuals) k
                                          | _ -> ret ())) in 
                            addHoldsPreds t actuals k))
        
  (* Ordinary type constructors *)
  | Sig_tycon_kind(lid, tps, k, _, _, _) -> 
      get >> (fun st -> 
                if is_array_function st.termctx lid 
                then ret ()
                else
                  let k = Tcenv.tycon_kind_from_tparams tps k in 
                  let name = typeNameOfLid lid in 
                  addKindingAssumption lid name k)

                    (* (encodeKind' (Some (mk_Typ_const name)) k) >> (fun {binding_phi=Some phi}  ->  *)
                    (*  let ops = [mkAssumption (spr "Kind of %s" name) phi] in *)
                    (*  addOps ops  *)
                    (*  >> (fun _ -> addKindingAssumption lid name k))) *)

  (* Logical projectors need to be mapped to the builtin projectors *)
  | Sig_logic_function(lid, t, [Sugar.Logic_projector]) -> 
    let nm = funNameOfConstr lid in 
    let builtin = "Primitive_" ^ nm in 
    let formals = 
      let rec formals (out,ix) t = match t.v with 
        | Typ_univ(a,k,_,t) -> formals ((spr "typ%d" ix, Type_sort)::out, ix + 1) t
        | Typ_fun(Some x,t1,t2) -> formals ((spr "tm%d" ix, Term_sort)::out, ix + 1) t2
        | _ -> out in 
      formals ([],0) t in
    let (actual, _)::_ = formals in
    addOps [DefineFun(nm, Array.ofList <| List.rev formals, 
                      Term_sort, 
                      App(builtin, Arrow(Term_sort, Term_sort), [| BoundV(0, Term_sort, actual, termref()) |]),
                      Some ("Definition_"^nm))]
      
  | Sig_logic_function(lid, t, _) -> 
      get >> (fun st -> 
                match lookup_array_function st.termctx lid with 
                  | None -> mkLogicFunction lid t
                  | Some arr -> ret ())
                      (* if Sugar.lid_equals lid (fst arr.arr_sel) *)
                      (* then ret () *)
                      (* else  *)
                      (*   let dname = funNameOfConstr lid in  *)
                      (*   let mk_term = *)
                      (*     if Sugar.lid_equals lid (fst arr.arr_upd) *)
                      (*     then (fun sort args -> match List.rev args with *)
                      (*             | v::r::h::rest -> *)
                      (*                 let tm, p = snd arr.arr_upd (List.rev rest) h r v in PP(tm,p) *)
                      (*             | _ -> raise Impos) *)
                      (*     else if Sugar.lid_equals lid (fst arr.arr_emp) *)
                      (*     then (fun sort args -> match args with *)
                      (*             | [] -> let tm, p = snd arr.arr_emp in PP(tm,p) *)
                      (*             | _ -> raise Impos) *)
                      (*     else raise Impos in *)
                      (*     addTypingAssumption dname mk_term t) *)
        
  (* Tuple constructor *)
  | Sig_datacon_typ(__tup_lid, _, t, _, _, Some tcName, _, _) 
      when Const.is_tuple_data_lid __tup_lid -> 
      ret ()
          
  (* Data item only *)
  | Sig_datacon_typ(__D_lid, tps, t, _, _, Some tcName, _, _) -> 
      get >> (fun {st={env=Some tcenv}; termctx=termctx} -> 
        if Sugar.lid_equals tcName Const.pf_lid 
        then ret ()
        else
          (* if (Tcenv.is_logic_data tcenv tcName || Tcenv.is_record tcenv tcName) *)
          (* then *)
          let t = AbsynUtils.closeTyp tps t in 
          let dname = funNameOfConstr __D_lid in 
          addTypingAssumption __D_lid (fun sort args -> Appl(dname, sort, args)) t
      (* else ret () *)
      )
  
  | Sig_record_typ(__R_lid, tps, k, {v=Typ_record(fn_t_l, _)}, _) as record ->
      get 
      >> (fun {st={env=Some tcenv}} ->
            let tenv = mkTransenv (Some tcenv) in
            let [tc;dt],rec_typ = dataconOfRecord record in 
              encodeSigelt tc
              >> (fun _ -> encodeSigelt dt)
              >> (fun _ -> 
                    (* if !Options.relational  *)
                    (* then ret () (\* TODO: add record typing properly for relational mode *\) *)
                    (* else *)
                      let n = List.length tps in 
                      let accum, tenv, _ = 
                        List.fold_left (fun (accum, tenv, i) tp -> 
                                          let ix = n - i in 
                                          let vref = termref () in 
                                            match tp with 
                                              | Tparam_typ(a, k) -> 
                                                  let tm = BoundV(ix, Type_sort, a.ppname.idText, vref) in 
                                                  let tenv = push tenv (Formula(Tvar_binding(a,k,Type_sort,vref))) in 
                                                    ((Type_sort,tm,(Inl a, vref))::accum, tenv, i+1)
                                              | Tparam_term(x, t) -> 
                                                  let tm =  BoundV(ix, Term_sort, x.ppname.idText, termref()) in 
                                                  let tenv = push tenv (Formula(Var_binding(x,t,Term_sort,vref))) in 
                                                    ((Term_sort,tm,(Inr x,vref))::accum, tenv, i+1))
                          ([], tenv, 0) tps in
                      let sorts, tms, vars = List.unzip3 (List.rev accum) in 
                      let recVar = new_bvd None, termref() in 
                      let recTm = BoundV(0, Term_sort, (fst recVar).ppname.idText, snd recVar) in
                      let tenv = push tenv (Formula(Var_binding(fst recVar, rec_typ, Term_sort, snd recVar))) in
                        Util.stmap fn_t_l (fun (fn,t) -> 
                                             let projName = fieldProjector tenv rec_typ fn in 
                                             let projection = Appl(projName, Arrow(Term_sort, Term_sort), [recTm]) in 
                                               encodeTyp tenv (Some projection) t
                                               >> (fun ({binding_phi=Some tm}) -> ret tm))
                        >> (fun projections -> 
                              encodeTyp tenv (Some recTm) rec_typ 
                              >> (fun {binding_phi=Some guard} -> 
                                    Util.stiter projections (fun p -> 
                                                               let phi = Forall([], 
                                                                                Array.ofList <| (sorts@[Term_sort]), 
                                                                                Array.ofList <| (vars@[(Inr (fst recVar), snd recVar)]), 
                                                                                Imp(guard, p)) in
                                                                 addOp (Assume(phi, None, AName (spr "Projection typing for %s" (Pretty.sli __R_lid)))))))))
          

let encodeSigelt' se h =
  try 
    let res = encodeSigelt se h in
      res
  with 
    | CatchMe(msg, p) 
    | Single_sided(msg, p) -> 
        let _ = pr "Failed to encode sigelt %s\n %s" (Pretty.strSigelt se) msg in 
          raise (Error(msg, p))      
        
(* ******************************************************************************** *)
let encodeBinding env_pfx b = 
  get >> (fun st ->
  let tenv = mkTransenv (Some env_pfx) in 
     match b with 
       | Tcenv.Binding_var(id, t) ->
           (* let _ = pr "Encoding binding_var %s ... %s \n" (id.idText) (t.ToString()) in *)
           let idbvd = mkbvd (id,id) in  
           (* let tenv, t = norm tenv t in  *)
           (* let t = match AbsynUtils.normalizeRefinement t with *)
           (*   | {v=Typ_refine(x, t', phi, g)} as t ->  *)
           (*       let phi = Absyn.substitute_exp_l phi [x, bvd_to_exp idbvd t'] in  *)
           (*         twithsort (Typ_refine(idbvd, t', phi, g)) t.sort  *)
           (*   | t -> t in  *)
           let nm = funNameOfBvdef idbvd in
           let bvar = Absyn.bvd_to_bvar_s idbvd t in 
           let sort = Term_sort in 
           (addOp (DeclFun(nm, [||], sort, None))) >> (fun _ -> ret (FreeV(nm, sort))) >> (fun tm -> 
           dedupAndEncodeTyp tenv (Some tm) t >> (fun ({term=tm_t; binding_phi=phiOpt}, tenv) -> 
           incrCtr >> (fun p ->
           let ops = match phiOpt with Some phi -> [Assume (phi, Some id.idText, ABindingVar p)] | _ -> [] in
           let tt = AbsynUtils.unrefine t in 
             match tt.sort(* .u *)with
               | Kind_prop ->
                   encodeCompleteFormula tenv tt >> (fun phi ->
                   incrCtr >> (fun q ->
                   let op' = Assume(phi, Some (spr "%s_P" id.idText), ABindingVar q) in
                     addOps (ops@[op'])))
               | _ -> addOps ops)))
               
       | Tcenv.Binding_typ(id, k) -> 
           (if (isProp k) then maybeAddHoldsPred k >> (fun _ -> ret ())
            else ret ()) >>
            (fun _ -> 
               let nm = typeNameOfBtvar (bvd_to_bvar_s (mkbvd(id,id)) k) in 
               let df = DeclFun(nm, [||], Type_sort, None) in
               let tm = FreeV(nm, Type_sort) in
                 encodeKind tenv (Some tm) k >> (fun {binding_phi=Some phi} -> 
                 incrCtr >> (fun p ->
                 let op' = Assume (phi, Some id.idText, ABindingVar p) in
                 let ops = [op';df] in 
                 addOps ops)))

       | Tcenv.Binding_match(e1exp, e2exp) when !Options.relational ->
           let t = mkEq (tcenv tenv) e1exp e2exp in
           (* let _ = pr "Encoding Binding_match in relational mode: %s\n" (Pretty.strTyp t) in *)
           encodeCompleteFormula tenv t >> (fun phi -> 
           incrCtr >> (fun p ->
           let op = Assume(phi, None, ABindingMatch p) in
             addOps [op]))

       | Tcenv.Binding_match(e1exp, e2exp) -> 
           (encodeValue tenv e1exp) >> (fun e1 -> 
           (encodeValue tenv e2exp) >> (fun e2 -> 
            incrCtr >> (fun p -> 
            let tm = Eq(e1,e2) in
            let op1 = Assume(tm, Some (spr "(%s) = (%s)" (e1exp.ToString()) (e2exp.ToString())), ABindingMatch p) in
              addOps [op1])))

       | Tcenv.Binding_tmatch(a, t) -> 
           (encodeTyp tenv None (AbsynUtils.btvar_to_typ a))  >> (fun res_a -> 
           (encodeTyp tenv None t) >> (fun res_t -> 
            incrCtr >> (fun p -> 
            let tm = Eq(res_a.term, res_t.term) in
            let op1 = Assume(tm, None, ABindingMatch p) in
            let ops = [op1] in 
              addOps ops))))

let encodeBinding' env_pfx b h = 
  try 
    encodeBinding env_pfx b h 
  with 
    | CatchMe(e,p)
    | Single_sided(e, p) -> 
        let str = match b with 
          | Tcenv.Binding_var(id, t) -> spr "%s : %s" (id.idText) (Pretty.strTyp t)
          | Tcenv.Binding_typ(id, k) -> spr "%s :: %s" (id.idText) (Pretty.strKind k)
          | Tcenv.Binding_match(e1, e2) -> spr "%s = %s" (Pretty.strExp e1) (Pretty.strExp e2)
          | Tcenv.Binding_tmatch(a, k) -> "Binding_tmatch" in 
        let _ = pr "Failed to encode binding %s\n%s\n" str e in 
          raise (Error(e, p))
            
            
(* ******************************************************************************** *)
let encodeEnvironment : ST<unit> =
  get >> (fun {st={env=Some env}} ->
    let sigs = (List.rev (Tcenv.modules env)) |> List.map (fun (mname, m) ->  
                                                Inl (Comment (spr "Module %s" (sli mname)))::(List.map Inr m.signature)) in
    let sigs =  List.rev <| (flatten_l (sigs@[Inl(Comment "current module")::(List.rev (List.map Inr (Tcenv.signature env)))])) in
    stfoldr_pfx sigs (fun _ se -> match se with 
                        | Inl op -> addOp op 
                        | Inr se -> 
                            if is_lid_skippable (lid_of_sigelt se) 
                            then addOp (Comment (spr "Skipping %s\n" (Sugar.text_of_lid (lid_of_sigelt se))))
                            else encodeSigelt' se) >>
      (fun _ -> addOp (Comment "Local environment") 
         >> (fun _ -> (Tcenv.stfoldr env encodeBinding')
         >> (fun _ -> 
               if !Options.relational 
               then 
                 let mk_lr_teq lr = 
                   let t, tref = new_bvd None, termref() in 
                   let x, xref = new_bvd None, termref() in 
                   let tvar = BoundV(1, Type_sort, t.ppname.idText, tref) in 
                   let xvar = BoundV(0, Term_sort, x.ppname.idText, xref) in 
                   let lrtm = App(funNameOfConstr lr, Arrow(Type_sort, Arrow(Term_sort, Term_sort)), [| tvar; xvar |]) in
                     Assume(Forall([lrtm], 
                                   [| Type_sort; Term_sort |], 
                                   [| (Inl t, termref()); (Inr x, termref()) |],
                                   mkAnd [typeOfEq env lrtm tvar;
                                          Iff(App(mkTester "BoxBool", Arrow(Term_sort, Bool_sort), [| xvar|]), 
                                              App(mkTester "BoxBool", Arrow(Term_sort, Bool_sort), [| lrtm |]));
                                          Iff(App(mkTester "BoxInt", Arrow(Term_sort, Bool_sort), [| xvar|]), 
                                              App(mkTester "BoxInt", Arrow(Term_sort, Bool_sort), [| lrtm |])); 
                                          Iff(App(mkTester "BoxString", Arrow(Term_sort, Bool_sort), [| xvar|]), 
                                              App(mkTester "BoxString", Arrow(Term_sort, Bool_sort), [| lrtm |]));
                                          Iff(App(mkTester "BoxRef", Arrow(Term_sort, Bool_sort), [| xvar|]), 
                                              App(mkTester "BoxRef", Arrow(Term_sort, Bool_sort), [| lrtm |]));
                                          Iff(App(mkTester "Term_arr_Prims.heap", Arrow(Term_sort, Bool_sort), [| xvar|]), 
                                              App(mkTester "Term_arr_Prims.heap", Arrow(Term_sort, Bool_sort), [| lrtm |]))]),
                            None,
                            AName "LR_typing") in 
                 addOps [mk_lr_teq Const.lproj_lid;
                         mk_lr_teq Const.rproj_lid]
               else ret ()))))

let initState env = 
  let collectTypenames env =
    let sigs = Tcenv.modules env |> List.map (fun (mname, m) ->  m.signature) in
    let sigs = flatten_l <| (Tcenv.signature env)::sigs in
    let rec tn_of_sigelt se =
      (* if is_lid_skippable (lid_of_sigelt se) then [],[] *)
      (* else *) 
      match se with 
        | Sig_tycon_kind(_, _, _, _, _, [Sugar.Logic_tfun])
        | Sig_tycon_kind(_, _, _, _, _, [Sugar.Logic_projector]) -> [], []
        | Sig_tycon_kind(arr_typ_lid, [], Kind_star, _, _, [Sugar.Logic_array larr]) -> 
            let rec mk_array_constr qvars sel_t = match sel_t.v with 
              | Typ_univ(a, k, _, t) ->  mk_array_constr ((a,k)::qvars) t 
              | Typ_fun(_, {v=Typ_const(tc, _)}, {v=Typ_fun(_, dom, range)}) -> 
                  let dom_sort = arrayDomSortFromTyp env dom in 
                  let range_sort = Pseudo_term_opt_sort in 
                  let arr_sort = Array(dom_sort, range_sort) in 
                    [(arrConstrName arr_typ_lid, [arr_sort])] in
            let tn = [typeNameOfLid arr_typ_lid] in 
            let dc = mk_array_constr [] (Tcenv.lookup_lid env (larr.array_sel)) in
              tn, dc
        | Sig_tycon_kind(lid, _, _, _, _, _) 
        | Sig_record_typ(lid, _, _, _, _) -> [typeNameOfLid lid], []
        | Sig_extern_typ(_, se) -> tn_of_sigelt se
        | _ -> [],[] in
      sigs |> List.map tn_of_sigelt |> List.unzip |> (fun (tns, dns) -> (List.flatten tns, List.flatten dns)) in 
    
  let collectDatacons env =
    let sigs = Tcenv.modules env |> List.map (fun (mname, m) ->  m.signature) in
    let sigs = flatten_l <| (Tcenv.signature env)::sigs in
    let rec datacon_of_sigelt = function 
      | Sig_datacon_typ(__tup_lid, _, t, _, _, Some tcName, _, _) 
          when Const.is_tuple_data_lid __tup_lid -> 
          if Sugar.lid_equals __tup_lid Const.tuple_UU_lid 
          then [(funNameOfConstr __tup_lid, [Type_sort; Type_sort; Term_sort; Term_sort])]
          else []
            
      | Sig_datacon_typ(__D_lid, tps, t, None, _, Some tcName, _, _) -> 
          if config.skip_pf && Sugar.lid_equals tcName Const.pf_lid 
          then []
          else
            let t = t |> (tps |> List.fold_right (
                            fun tp out -> match tp with 
                              | Tparam_typ (a,k) -> twithsort (Typ_univ (a,k,[],out)) Kind_star
                              | Tparam_term (x,t) -> twithsort (Typ_fun (Some x,t,out)) Kind_star)) in
            let sorts = sortsFromTyp t in 
              [(funNameOfConstr __D_lid, sorts)]
                
      | Sig_record_typ _ as record -> 
          let [_;sig_data], _ = dataconOfRecord record in 
            datacon_of_sigelt sig_data 
              
      (* | Sig_logic_function(lid, t, _) ->  *)
      (*     let sorts = sortsFromTyp t in  *)
      (*       [(funNameOfConstr lid, sorts)] *)

      | _ -> [] in 
      sigs |> List.collect datacon_of_sigelt in 

  let tns, dcs' = collectTypenames env in 
  let dcs = collectDatacons env in
  let dcs = dcs@dcs' in 
  let mkTctx i = mkTermctx i (mkZ3()) tns dcs in 
  let tctx, basicops = mkTermctx (if !Options.logQueries then (Some "") else None) (mkZ3()) tns dcs in
  let os' = {ops=basicops;
             qops=[];
             env=Some env;
             ctr=100;
             uvars=[];
             strings=[];
             floats=[];
             cached_ops=[];
             bvars=[];
             fvars=[];
             transformers=(map_create 1277, map_create 1277);
             holds_map=[];
             qid=0;
             unfoldings=[];
             labels=[];
             pp_name_map=Hashtbl.create 100;
             named_typ_map=[]} in 
    {st=os';termctx=tctx;strip_labels=true}, mkTctx
      
