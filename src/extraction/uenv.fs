﻿(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStar.Extraction.ML.UEnv
open FStar
open FStar.Util
open FStar.Ident
open FStar.Extraction.ML.Syntax
open FStar.Syntax
open FStar.Syntax.Syntax

type ty_or_exp_b = either<(mlident * mlty), (mlexpr * mltyscheme * bool)>

type binding =
    | Bv  of bv * ty_or_exp_b
    | Fv  of fv * ty_or_exp_b

type env = {
    tcenv: TypeChecker.Env.env;
    gamma:list<binding>;
    tydefs:list<(list<mlsymbol> * mltydecl)>;
    //erasableTypes : mlty -> bool; // Unit is not the only type that can be erased. We could erase inductive families which had only 1 element, or become so after extraction.
    //if so, just convert them to type abbreviations returning unit.
    currentModule: mlpath // needed to properly translate the definitions in the current file
}

let debug g f =
    let c = string_of_mlpath g.currentModule in
    if Options.debug_at_level c (Options.Other "Extraction")
    then f ()

// TODO delete
let mkFvvar (l: lident) (t:typ) : fv = lid_as_fv l Delta_constant None

(* MLTY_Tuple [] extracts to (), and is an alternate choice.
    However, it represets both the unit type and the unit value. Ocaml gets confused sometimes*)
let erasedContent : mlty = ml_unit_ty

let erasableTypeNoDelta (t:mlty) =
    if t = ml_unit_ty then true
    else match t with
        | MLTY_Named (_, (["FStar"; "Ghost"], "erased")) -> true
        | _ -> false // this function is used by another function which does delta unfolding

(* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
let unknownType : mlty =  MLTY_Top

(*copied from ocaml-strtrans.fs*)
let prependTick (x,n) = if Util.starts_with x "'" then (x,n) else ("'A"^x,n) ///the addition of the space is intentional; it's apparently valid syntax of tvars
let removeTick (x,n) = if Util.starts_with x "'" then (Util.substring_from x 1,n) else (x,n)

let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = id.idText, 0

(* TODO : need to make sure that the result of this name change does not collide with a variable already in the context. That might cause a change in semantics.
   E.g. , consider the following in F*
   let mkPair (a:Type) ('a:Type) (ta : a) (ta' : a') = (ta, ta')

   Perhaps this function also needs to look at env.Gamma*)

(* TODO : if there is a single quote in the name of the type variable, the additional tick in the beginning causes issues with the lexer/parser of OCaml (syntax error).
  Perhaps the type variable is interpreted as a string literal.
  For an example, see https://github.com/FStarLang/FStar/blob/f53844512c76bd67b21b4cf68d774393391eac75/lib/FStar.Heap.fst#L49

   Coq seems to add a space after the tick in such cases. Always adding a space for now
  *)

let bv_as_ml_tyvar x = prependTick (bv_as_mlident x)
let bv_as_ml_termvar x =  removeTick (bv_as_mlident x)

let rec lookup_ty_local (gamma:list<binding>) (b:bv) : mlty =
    match gamma with
        | (Bv (b', Inl (mli, mlt))) :: tl -> if (bv_eq b b') then mlt else lookup_ty_local tl b
        | (Bv (b', Inr _)) :: tl -> if (bv_eq b b') then failwith ("Type/Expr clash: "^(b.ppname.idText)) else lookup_ty_local tl b
        | _::tl -> lookup_ty_local tl b
        | [] -> failwith ("extraction: unbound type var "^(b.ppname.idText))

let tyscheme_of_td (_, _, vars, body_opt) : option<mltyscheme> = match body_opt with
    | Some (MLTD_Abbrev t) -> Some (vars, t)
    | _ -> None

//TODO: this two-level search is pretty inefficient: we should optimize it
let lookup_ty_const (env:env) ((module_name, ty_name):mlpath) : option<mltyscheme> =
    Util.find_map env.tydefs  (fun (m, tds) ->
        if module_name = m
        then Util.find_map tds (fun td ->
             let (_, n, _, _) = td in
             if n=ty_name
             then tyscheme_of_td td
             else None)
        else None)

let lookup_tyvar (g:env) (bt:bv) : mlty = lookup_ty_local g.gamma bt

let lookup_fv_by_lid (g:env) (lid:lident) : ty_or_exp_b =
    let x = Util.find_map g.gamma (function
        | Fv (fv', x) when fv_eq_lid fv' lid -> Some x
        | _ -> None) in
    match x with
        | None -> failwith (Util.format1 "free Variable %s not found\n" (lid.nsstr))
        | Some y -> y

(*keep this in sync with lookup_fv_by_lid, or call it here. lid does not have position information*)
let lookup_fv (g:env) (fv:fv) : ty_or_exp_b =
    let x = Util.find_map g.gamma (function
        | Fv (fv', t) when fv_eq fv fv' -> Some t
        | _ -> None) in
    match x with
        | None -> failwith (Util.format2 "(%s) free Variable %s not found\n" (Range.string_of_range fv.fv_name.p) (Print.lid_to_string fv.fv_name.v))
        | Some y -> y

let lookup_bv (g:env) (bv:bv) : ty_or_exp_b =
    let x = Util.find_map g.gamma (function
        | Bv (bv', r) when bv_eq bv bv' -> Some (r)
        | _ -> None) in
    match x with
        | None -> failwith (Util.format2 "(%s) bound Variable %s not found\n" (Range.string_of_range bv.ppname.idRange) (Print.bv_to_string bv))
        | Some y -> y


let lookup  (g:env) (x:either<bv,fv>) : ty_or_exp_b * option<fv_qual> =
    match x with
        | Inl x -> lookup_bv g x, None
        | Inr x -> lookup_fv g x, x.fv_qual

let lookup_term g (t:term) = match t.n with
    | Tm_name x -> lookup g (Inl x)
    | Tm_fvar x -> lookup g (Inr x)
    | _ -> failwith "Impossible: lookup_term for a non-name"

(* do we really need to keep gamma uptodate with hidden binders? For using F* utils, we just need to keep tcenv update.
 An alternative solution is to remove these binders from the type of the inductive constructors

let extend_hidden_ty (g:env) (a:btvar) (mapped_to:mlty) : env =
    let ml_a = as_mlident a.v in
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with tcenv=tcenv}
*)

let extend_ty (g:env) (a:bv) (mapped_to:option<mlty>) : env =
    let ml_a =  bv_as_ml_tyvar a in
    let mapped_to = match mapped_to with
        | None -> MLTY_Var ml_a
        | Some t -> t in
    let gamma = Bv(a, Inl (ml_a, mapped_to))::g.gamma in
    let tcenv = TypeChecker.Env.push_bv g.tcenv a in // push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with gamma=gamma; tcenv=tcenv}

let extend_bv (g:env) (x:bv) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool) (mk_unit:bool (*some pattern terms become unit while extracting*)) : env =
    let ml_ty = match t_x with 
        | ([], t) -> t
        | _ -> MLTY_Top in
    let mlx = MLE_Var (bv_as_mlident x) in
    let mlx = if mk_unit 
              then ml_unit 
              else if add_unit 
              then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mlx, [ml_unit]) 
              else with_ty ml_ty mlx in
    let gamma = Bv(x, Inr(mlx, t_x, is_rec))::g.gamma in
    let tcenv = TypeChecker.Env.push_binders g.tcenv (binders_of_list [x]) in
    {g with gamma=gamma; tcenv=tcenv}

let rec mltyFvars (t: mlty) : list<mlident>  =
    match t with
    | MLTY_Var  x -> [x]
    | MLTY_Fun (t1, f, t2) -> List.append (mltyFvars t1) (mltyFvars t2)
    | MLTY_Named(args, path) -> List.collect mltyFvars args
    | MLTY_Tuple ts -> List.collect mltyFvars ts
    | MLTY_Top -> []

let rec subsetMlidents (la : list<mlident>) (lb : list<mlident>)  : bool =
    match la with
    | h::tla -> List.contains h lb && subsetMlidents tla lb
    | [] -> true

let tySchemeIsClosed (tys : mltyscheme) : bool =
    subsetMlidents  (mltyFvars (snd tys)) (fst tys)

let extend_fv' (g:env) (x:fv) (y:mlpath) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool) : env =
    if tySchemeIsClosed t_x
    then
        let ml_ty = match t_x with 
            | ([], t) -> t
            | _ -> MLTY_Top in
        let mly = MLE_Name y in
        let mly = if add_unit then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mly, [ml_unit]) else with_ty ml_ty mly in
        let gamma = Fv(x, Inr(mly, t_x, is_rec))::g.gamma in
        let tcenv = TypeChecker.Env.push_let_binding g.tcenv (Inr x) ([], x.fv_name.ty) in
        {g with gamma=gamma; tcenv=tcenv}
    else //let _ = printfn  "(* type scheme of \n %A \n is not closed or misses an unit argument: \n %A *) \n"  x.v.ident t_x in
         failwith "freevars found"

let extend_fv (g:env) (x:fv) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool) : env =
    let mlp = mlpath_of_lident x.fv_name.v in
    // the mlpath cannot be determined here. it can be determined at use site, depending on the name of the module where it is used
    // so this conversion should be moved to lookup_fv

    //let _ = printfn "(* old name  \n %A \n new name \n %A \n name in dependent module \n %A \n *) \n"  (Backends.ML.Syntax.mlpath_of_lident x.v) mlp (mlpath_of_lident ([],"SomeDepMod") x.v) in
    extend_fv' g x mlp t_x add_unit is_rec

let extend_lb (g:env) (l:lbname) (t:typ) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool) : (env * mlident) =
    match l with
        | Inl x ->
          extend_bv g x t_x add_unit is_rec false, bv_as_ml_termvar x // FIXME missing in lib; NS: what does ths mean??
        | Inr f ->
          let p, y = mlpath_of_lident f.fv_name.v in
          extend_fv' g f (p, y) t_x add_unit is_rec, (y,0)

let extend_tydef (g:env) (td:mltydecl) : env =
    let m = fst (g.currentModule) @ [snd g.currentModule] in
    {g with tydefs=(m,td)::g.tydefs}


let emptyMlPath : mlpath = ([],"")

let mkContext (e:TypeChecker.Env.env) : env =
   let env = { tcenv = e; gamma =[] ; tydefs =[]; currentModule = emptyMlPath} in
   let a = "'a", -1 in
   let failwith_ty = ([a], MLTY_Fun(MLTY_Named([], (["Prims"], "string")), E_IMPURE, MLTY_Var a)) in
   extend_lb env (Inr (lid_as_fv Const.failwith_lid Delta_constant None)) tun failwith_ty false false |> fst    
   
let monad_op_name (ed:Syntax.eff_decl) nm =
    let module_name, eff_name = ed.mname.ns, ed.mname.ident in
    let mangled_name = Ident.reserved_prefix ^ eff_name.idText ^ "_" ^ nm in
    let mangled_lid = Ident.lid_of_ids (module_name@[Ident.id_of_text mangled_name]) in
    let ml_name = mlpath_of_lident mangled_lid in
    let lid = Ident.ids_of_lid ed.mname @ [Ident.id_of_text nm] |> Ident.lid_of_ids in
    ml_name, lid

let action_name (ed:Syntax.eff_decl) (a:Syntax.action) = 
    monad_op_name ed a.action_name.ident.idText

let bind_name (ed:Syntax.eff_decl) =
    monad_op_name ed "bind"

let return_name (ed:Syntax.eff_decl) =
    monad_op_name ed "return"
