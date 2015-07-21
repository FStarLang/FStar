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
module Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML
open Microsoft.FStar.Tc

type binding = 
    | Ty  of btvar * mlident * mlty           //a, 'a, ('a | Top)  
    | Bv  of bvvar * mlident * mltyscheme     //x,  x, translation (typeof x)
    | Fv  of fvvar * mlpath * mltyscheme     //f,  f, translation (typeof f)

type env = {
    tcenv:Tc.Env.env;
    gamma:list<binding>;
    tydefs:list<mltydecl>; 
    erasableTypes : mlty -> bool; // Unit is not the only type that can be erased. We could erase inductive families which had only 1 element, or become so after extraction.
    currentModule: mlpath // needed to properly translate the definitions in the current file
}

(*copied from ocaml-asttrans.fs*)

(* -------------------------------------------------------------------- *)
let outmod = [
    ["Prims"];
    ["System"];
    ["ST"];
    ["Option"];
    ["String"];
    ["Char"];
    ["Bytes"];
    ["List"];
    ["Array"];
    ["Set"];
    ["Map"];
    ["Heap"];
    ["DST"];
    ["IO"];
    ["Tcp"];
    ["Crypto"];
    ["Collections"];
    ["Microsoft"; "FStar"; "Bytes"];
    ["Microsoft"; "FStar"; "Platform"];
    ["Microsoft"; "FStar"; "Util"];
    ["Microsoft"; "FStar"; "Getopt"];
    ["Microsoft"; "FStar"; "Unionfind"];
    ["Microsoft"; "FStar"; "Range"];
    ["Microsoft"; "FStar"; "Parser"; "Util"];
]


let rec in_ns = function
| [], _ -> true
| x1::t1, x2::t2 when (x1 = x2) -> in_ns (t1, t2)
| _, _ -> false

(* -------------------------------------------------------------------- *)
let path_of_ns (currentModule : mlpath) ns =
    let ns = List.map (fun x -> x.idText) ns in
    let outsupport = fun (ns1,ns2) -> if ns1 = ns2 then [] else [String.concat "_" ns2]
    
    (*function
    | x1 :: p1, x2 :: p2 when x1 = x2 -> outsupport (p1, p2)
    | _, p -> p
    *)
    in let chkin sns = if in_ns (sns, ns) then Some sns else None
    in match List.tryPick chkin outmod with
    | None -> 
        (match List.tryPick chkin (!Microsoft.FStar.Options.codegen_libs) with
         | None -> outsupport ((fst currentModule) @ [snd currentModule], ns)
         | _ -> ns)
    | Some sns -> "Support" :: ns

let mlpath_of_lident (currentModule : mlpath) (x : lident) : mlpath =
    match x.str with
    | "Prims.Some" -> ([], "Some")
    | "Prims.None" -> ([], "None")
    | "Prims.failwith" -> ([], "failwith")
    | "ST.alloc" -> ([], "ref")
    | "ST.read" -> (["Support";"Prims"], "op_Bang")
    | "ST.op_ColonEquals" -> (["Support";"Prims"], "op_ColonEquals")
    | _ ->
      begin
        let ns = x.ns in
        let x  = x.ident.idText in
        (path_of_ns currentModule ns, x)
      end


let mkFvvar (l: lident) (t:typ) : fvvar =
{ v= l;
  sort= t;
  p=Range.mk_range "" 0 0;
}

(* MLTY_Tuple [] extracts to (), and is an alternate choice. 
    However, it represets both the unit type and the unit value. Ocaml gets confused sometimes*)
let erasedContent : mlty = MLTY_Named ([],(["Support"; "Prims"], "unit"))
let ml_unit_ty = erasedContent

let erasable_init (t:mlty) = 
    if t = ml_unit_ty then true
    else match t with 
        | MLTY_Named (_, (["Ghost"], "erased")) -> true //when would a named type like this be produced?
        | _ -> false //what about types that reduce/unfold to unit/erased t? Do a syntactic check with ml_unit_ty?

(* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
let unknownType : mlty =  MLTY_Top

(*copied from ocaml-strtrans.fs*)
let prependTick (x,n) = if Util.starts_with x "'" then (x,n) else ("'"^x,n)
let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = (id.idText ,(convRange id.idRange))
let btvar_as_mlident (btv: btvar) : mlident =  (prependTick (convIdent btv.v.ppname))

let rec lookup_ty_local (gamma:list<binding>) (b:btvar) : mlty = 
    match gamma with
        | (Ty (bt, mli, mlt))::tl ->  if (Util.bvd_eq bt.v b.v) then mlt else lookup_ty_local tl b
        | _::tl -> lookup_ty_local tl b
        | [] -> failwith ("extraction: unbound type var "^(b.v.ppname.idText))

let lookup_ty_const tydefs ftv = failwith "Should not be looking up a constant"

let lookup_ty (g:env) (x:either<btvar,ftvar>) : mlty = 
    match x with
    | Inl bt  -> lookup_ty_local g.gamma bt
    | Inr ftv -> lookup_ty_const g.tydefs ftv

let lookup_fv (g:env) (fv:fvvar) : mlpath * mltyscheme = 
    let x = Util.find_map g.gamma (function 
        | Fv (fv', path, sc) when lid_equals fv.v fv'.v -> Some (path, sc)
        | _ -> None) in
    match x with 
        | None -> failwith (Util.format2 "(%s) free Variable %s not found\n" (Range.string_of_range fv.p) (Print.sli fv.v))
        | Some y -> y

let lookup_bv (g:env) (bv:bvvar) : mlident * mltyscheme = 
    let x = Util.find_map g.gamma (function 
        | Bv (bv', id, sc) when Util.bvar_eq bv bv' -> Some (id, sc)
        | _ -> None) in
    match x with 
        | None -> failwith (Util.format2 "(%s) bound Variable %s not found\n" (Range.string_of_range bv.p) (Print.strBvd bv.v))
        | Some y -> y


let lookup  (g:env) (x:either<bvvar,fvvar>) : (mlexpr * mltyscheme) = 
    match x with 
        | Inl x -> let id, t = lookup_bv g x in MLE_Var id, t
        | Inr x -> let id, t = lookup_fv g x in MLE_Name id, t

let lookup_var g e = match e.n with 
    | Exp_bvar x -> (lookup g (Inl x),false)
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
    let ml_a =  btvar_as_mlident a in 
    let mapped_to = match mapped_to with 
        | None -> MLTY_Var ml_a
        | Some t -> t in
    let gamma = Ty(a, ml_a, mapped_to)::g.gamma in 
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with gamma=gamma; tcenv=tcenv} 
    
let extend_bv (g:env) (x:bvvar) (t_x:mltyscheme) : env =
    let gamma = Bv(x, as_mlident x.v, t_x)::g.gamma in 
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_var(x.v, x.sort)) in
    {g with gamma=gamma; tcenv=tcenv} 

let extend_fv' (g:env) (x:fvvar) (y:mlpath) (t_x:mltyscheme) : env =
    let gamma = Fv(x, y, t_x)::g.gamma in 
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_lid(x.v, x.sort)) in
    {g with gamma=gamma; tcenv=tcenv} 

let extend_fv (g:env) (x:fvvar) (t_x:mltyscheme) : env =
    extend_fv' g x (mlpath_of_lident g.currentModule x.v) t_x

let extend_lb (g:env) (l:lbname) (t:typ) (t_x:mltyscheme) : (env * mlident) = 
    match l with 
        | Inl x -> 
          extend_bv g (Util.bvd_to_bvar_s x t) t_x, as_mlident x
        | Inr f -> 
          let _, y = mlpath_of_lident g.currentModule f in
          extend_fv' g (Util.fvvar_of_lid f t) ([], y) t_x, (y,0)

let extend_tydef (g:env) (td:mltydecl) : env = {g with tydefs=td::g.tydefs}

let erasableType (g:env) (t:mlty) = 
 //printfn "(* erasability of %A is %A *)\n" t (g.erasableTypes t);
   g.erasableTypes t
  