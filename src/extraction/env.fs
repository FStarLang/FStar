(*
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
module FStar.Extraction.ML.Env
open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML
open FStar.Tc

type binding =
    | Ty  of btvar * mlident * mlty           //a, 'a, ('a | Top)
    | Bv  of bvvar * mlexpr * mltyscheme     //x,  x, translation (typeof x)
    | Fv  of fvvar * mlexpr * mltyscheme     //f,  f, translation (typeof f)

type env = {
    tcenv:Tc.Env.env;
    gamma:list<binding>;
    tydefs:list<(list<mlsymbol> * mltydecl)>;
    //erasableTypes : mlty -> bool; // Unit is not the only type that can be erased. We could erase inductive families which had only 1 element, or become so after extraction.
    //if so, just convert them to type abbreviations returning unit.
    currentModule: mlpath // needed to properly translate the definitions in the current file
}

let debug g f =
    if !Options.debug <> []
    && (List.contains "Prims" (!Options.debug) ||
        g.currentModule <> ([], "Prims"))
    then f ()

let mkFvvar (l: lident) (t:typ) : fvvar =
{ v= l;
  sort= t;
  p=Range.mk_range "" 0 0;
}

(* MLTY_Tuple [] extracts to (), and is an alternate choice.
    However, it represets both the unit type and the unit value. Ocaml gets confused sometimes*)
let erasedContent : mlty = ml_unit_ty

let erasableTypeNoDelta (t:mlty) =
match  t with
//| MLTY_Fun (l, etag ,r) -> etag = MayErase && erasableType_init r // TODO : do we need to check etag here? it is checked just before erasing
| _ ->
    if t = ml_unit_ty then true
    else match t with
        | MLTY_Named (_, (["FStar"; "Ghost"], "erased")) -> true
        | _ -> false // this function is used by another function which does delta unfolding

(* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
let unknownType : mlty =  MLTY_Top

(*copied from ocaml-strtrans.fs*)
let prependTick (x,n) = if Util.starts_with x "'" then (x,n) else ("' "^x,n) ///the addition of the space is intentional; it's apparently valid syntax of tvars
let removeTick (x,n) = if Util.starts_with x "'" then (Util.substring_from x 1,n) else (x,n)

let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = (id.idText ,(convRange id.idRange))

(* TODO : need to make sure that the result of this name change does not collide with a variable already in the context. That might cause a change in semantics.
   E.g. , consider the following in F*
   let mkPair (a:Type) ('a:Type) (ta : a) (ta' : a') = (ta, ta')

   Perhaps this function also needs to look at env.Gamma*)

(* TODO : if there is a single quote in the name of the type variable, the additional tick in the beginning causes issues with the lexer/parser of OCaml (syntax error).
  Perhaps the type variable is interpreted as a string literal.
  For an example, see https://github.com/FStarLang/FStar/blob/f53844512c76bd67b21b4cf68d774393391eac75/lib/heap.fst#L49

   Coq seems to add a space after the tick in such cases. Always adding a space for now
  *)

let btvar_as_mltyvar (btv: btvar) : mlident =  (prependTick (convIdent btv.v.ppname))

let btvar_as_mlTermVar (btv: btvar) : mlident =  (removeTick (convIdent btv.v.ppname))

let rec lookup_ty_local (gamma:list<binding>) (b:btvar) : mlty =
    match gamma with
        | (Ty (bt, mli, mlt))::tl ->  if (Util.bvd_eq bt.v b.v) then mlt else lookup_ty_local tl b
        | _::tl -> lookup_ty_local tl b
        | [] -> failwith ("extraction: unbound type var "^(b.v.ppname.idText))

let tyscheme_of_td (_, vars, body_opt) : option<mltyscheme> = match body_opt with
    | Some (MLTD_Abbrev t) -> Some (vars, t)
    | _ -> None

//TODO: this two-level search is pretty inefficient: we should optimize it
let lookup_ty_const (env:env) ((module_name, ty_name):mlpath) : option<mltyscheme> =
    Util.find_map env.tydefs  (fun (m, tds) ->
        if module_name = m
        then Util.find_map tds (fun td ->
             let (n, _, _) = td in
             if n=ty_name
             then tyscheme_of_td td
             else None)
        else None)

let lookup_tyvar (g:env) (bt:btvar) : mlty = lookup_ty_local g.gamma bt

let lookup_fv_by_lid (g:env) (fv:lident) : mlexpr * mltyscheme =
    let x = Util.find_map g.gamma (function
        | Fv (fv', path, sc) when lid_equals fv fv'.v -> Some (path, sc)
        | _ -> None) in
    match x with
        | None -> failwith (Util.format1 "free Variable %s not found\n" (Print.sli fv))
        | Some y -> y

(*keep this in sync with lookup_fv_by_lid, or call it here. lid does not have position information*)
let lookup_fv (g:env) (fv:fvvar) : mlexpr * mltyscheme =
    let x = Util.find_map g.gamma (function
        | Fv (fv', path, sc) when lid_equals fv.v fv'.v -> Some (path, sc)
        | _ -> None) in
    match x with
        | None -> failwith (Util.format2 "(%s) free Variable %s not found\n" (Range.string_of_range fv.p) (Print.sli fv.v))
        | Some y -> y

let lookup_bv (g:env) (bv:bvvar) : mlexpr * mltyscheme =
    let x = Util.find_map g.gamma (function
        | Bv (bv', id, sc) when Util.bvar_eq bv bv' -> Some (id, sc)
        | _ -> None) in
    match x with
        | None -> failwith (Util.format2 "(%s) bound Variable %s not found\n" (Range.string_of_range bv.p) (Print.strBvd bv.v))
        | Some y -> y


let lookup  (g:env) (x:either<bvvar,fvvar>) : (mlexpr * mltyscheme) =
    match x with
        | Inl x -> lookup_bv g x
        | Inr x -> lookup_fv g x

let lookup_var g e = match e.n with
    | Exp_bvar x -> (lookup g (Inl x), None)
    | Exp_fvar (x, b) -> (lookup g (Inr x), b)
    | _ -> failwith "impossible"

(* do we really need to keep gamma uptodate with hidden binders? For using F* utils, we just need to keep tcenv update.
 An alternative solution is to remove these binders from the type of the inductive constructors

let extend_hidden_ty (g:env) (a:btvar) (mapped_to:mlty) : env =
    let ml_a = as_mlident a.v in
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with tcenv=tcenv}
*)

let extend_ty (g:env) (a:btvar) (mapped_to:option<mlty>) : env =
    let ml_a =  btvar_as_mltyvar a in
    let mapped_to = match mapped_to with
        | None -> MLTY_Var ml_a
        | Some t -> t in
    let gamma = Ty(a, ml_a, mapped_to)::g.gamma in
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with gamma=gamma; tcenv=tcenv}

let extend_bv (g:env) (x:bvvar) (t_x:mltyscheme) (add_unit:bool) (mk_unit:bool (*some pattern terms become unit while extaction*)) : env =
    let mlx = MLE_Var (as_mlident x.v) in
    let mlx = if mk_unit then ml_unit else (if add_unit then MLE_App(mlx, [ml_unit]) else mlx) in
    let gamma = Bv(x, mlx, t_x)::g.gamma in
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_var(x.v, x.sort)) in
    {g with gamma=gamma; tcenv=tcenv}

let rec mltyFvars (t: mlty) : list<mlident>  =
    match t with
    | MLTY_Var  x -> [x]
    | MLTY_Fun (t1, f, t2) -> List.append (mltyFvars t1) (mltyFvars t2)
    | MLTY_Named(args, path) -> List.collect mltyFvars args
    | MLTY_Tuple ts -> List.collect mltyFvars ts
    | MLTY_App(t1, t2) -> List.append (mltyFvars t1) (mltyFvars t2)
    | MLTY_Top -> []

let rec subsetMlidents (la : list<mlident>) (lb : list<mlident>)  : bool =
    match la with
    | h::tla -> List.contains h lb && subsetMlidents tla lb
    | [] -> true

let tySchemeIsClosed (tys : mltyscheme) : bool =
    subsetMlidents  (mltyFvars (snd tys)) (fst tys)

let extend_fv' (g:env) (x:fvvar) (y:mlpath) (t_x:mltyscheme) (add_unit:bool) : env =
    if  tySchemeIsClosed t_x
    then
        let mly = MLE_Name y in
        let mly = if add_unit then MLE_App(mly, [ml_unit]) else mly in
        let gamma = Fv(x, mly, t_x)::g.gamma in
        let tcenv = Env.push_local_binding g.tcenv (Env.Binding_lid(x.v, x.sort)) in
        {g with gamma=gamma; tcenv=tcenv}
    else //let _ = printfn  "(* type scheme of \n %A \n is not closed or misses an unit argument: \n %A *) \n"  x.v.ident t_x in
         failwith "freevars found"

let extend_fv (g:env) (x:fvvar) (t_x:mltyscheme) (add_unit:bool) : env =
    let mlp = (mlpath_of_lident x.v) in
    // the mlpath cannot be determined here. it can be determined at use site, depending on the name of the module where it is used
    // so this conversion should be moved to lookup_fv

    //let _ = printfn "(* old name  \n %A \n new name \n %A \n name in dependent module \n %A \n *) \n"  (Backends.ML.Syntax.mlpath_of_lident x.v) mlp (mlpath_of_lident ([],"SomeDepMod") x.v) in
    extend_fv' g x mlp t_x add_unit

let extend_lb (g:env) (l:lbname) (t:typ) (t_x:mltyscheme) (add_unit:bool) : (env * mlident) =
    match l with
        | Inl x ->
          extend_bv g (Util.bvd_to_bvar_s x t) t_x add_unit false, as_mlident x
        | Inr f ->
          let p, y = mlpath_of_lident f in
          extend_fv' g (Util.fvvar_of_lid f t) (p, y) t_x add_unit, (y,0)

let extend_tydef (g:env) (td:mltydecl) : env =
    let m = fst (g.currentModule) @ [snd g.currentModule] in
    {g with tydefs=(m,td)::g.tydefs}


let emptyMlPath : mlpath = ([],"")

let mkContext (e:Tc.Env.env) : env =
   let env = { tcenv = e; gamma =[] ; tydefs =[]; currentModule = emptyMlPath} in
   let a = "'a", -1 in
   let failwith_ty = ([a], MLTY_Fun(MLTY_Named([], (["Prims"], "string")), E_IMPURE, MLTY_Var a)) in
   extend_lb env (Inr Const.failwith_lid) tun failwith_ty false |> fst
