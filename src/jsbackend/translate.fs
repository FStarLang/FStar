(*
   Copyright 2014 Antoine Delignat-Lavaud and Microsoft Research

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

module Microsoft.FStar.Backends.JS.Translate

open Microsoft.FStar.Backends.JS.Ast

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Range
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Util

let constructors = Util.smap_create 100

let _ = 
    Util.smap_add constructors "Prims.op_Minus" (1, Some(function x::[] -> JSE_Minus(x) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Negation" (1, Some(function x::[] -> JSE_Lnot(x) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Addition" (2, Some(function x::y::[] -> JSE_Add(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Subtraction" (2, Some(function x::y::[] -> JSE_Sub(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Division" (2, Some(function x::y::[] -> JSE_Divide(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Multiply" (2, Some(function x::y::[] -> JSE_Multiply(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Modulus" (2, Some(function x::y::[] -> JSE_Mod(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_BarBar" (2, Some(function x::y::[] -> JSE_Lor(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_AmpAmp" (2, Some(function x::y::[] -> JSE_Land(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_GreaterThan" (2, Some(function x::y::[] -> JSE_Gt(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_LessThanOrEqual" (2, Some(function x::y::[] -> JSE_Le(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_LessThan" (2, Some(function x::y::[] -> JSE_Lt(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_GreaterThanOrEqual" (2, Some(function x::y::[] -> JSE_Ge(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Equality" (2, Some(function x::y::[] -> JSE_Equal(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_disEquality" (2, Some(function x::y::[] -> JSE_Lnot(JSE_Equal(x,y)) | _ -> failwith ""));
    Util.smap_add constructors "String.strcat" (2, Some(function x::y::[] -> JSE_Add(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.MkTuple2" (2, None);
    Util.smap_add constructors "Prims.MkTuple3" (3, None);
    Util.smap_add constructors "Prims.MkTuple4" (4, None);
    Util.smap_add constructors "Prims.MkTuple5" (5, None);
    Util.smap_add constructors "Prims.MkTuple6" (6, None);
    Util.smap_add constructors "Prims.MkTuple7" (7, None);
    Util.smap_add constructors "Prims.MkTuple8" (8, None);
    ()

let rec js_of_const (c:sconst) : expression_t =
    match c with
    | Const_unit -> JSE_Undefined
    | Const_uint8(n) -> JSE_Number((float)n)
    | Const_bool(b) -> JSE_Bool(b)
    | Const_int32(n) -> JSE_Number((float)n)
    | Const_int64(n) -> JSE_Number((float)n)
    | Const_char(c) -> JSE_String((string)c)
    | Const_float(f) -> JSE_Number(f)
    | Const_bytearray(ba,r) | Const_string(ba,r) -> JSE_String(Util.string_of_bytes ba)

and js_of_fun (fn:option<string>) (x:bvvdef) (t:typ) (e:exp) : expression_t =
    JSE_Function(fn, [x.ppname.idText], [JS_Statement(JSS_Return(
        match js_of_expr None e with JSE_Elision | JSE_Undefined -> None | e -> Some(e)
    ))])

and try_compile_constructor (e:exp) : option<expression_t> =
    let uncur cons args arity compiler =
        let rec fv d = match d with
        | 0 -> [] | n -> (Absyn.Util.gensym ())::(fv (d-1)) in
        let rec red a d = match a with
        | h::t -> red t (d-1)
        | [] -> fv d in
        let freevars = red args arity in
        let ae = (List.map (js_of_expr None) args) @ (List.map (fun x->JSE_Identifier(x)) freevars) in
        let compiled_cons = match compiler with
            | None -> (JSE_Object([JSP_Property("t", JSE_Identifier(cons)); JSP_Property("v", JSE_Array(ae))]))
            | Some(f) -> f ae
        in List.fold_left (fun v s->JSE_Function(None, [s], [JS_Statement(
                JSS_Return(Some(v)))])) compiled_cons freevars
    in let rec aux (args:list<exp>) (e:exp) = match e with
    | Exp_fvar(x, b) ->
        (match Util.smap_try_find constructors x.v.str with
        | None -> None
        | Some(arity, compiler) -> Some(uncur x.v.str args arity compiler))
    | Exp_app(e1, e2, f) -> aux (e2::args) e1
    | _ -> None
    in aux [] e

and js_of_binding (x:either<bvvdef,lident>, t:typ, e:exp) =
    let n = match x with Inl(x) -> x.ppname.idText | Inr(x) -> x.ident.idText in
    (n, Some(js_of_expr None e))

and compress_let (e:exp) =
    match e with
    | Exp_let((_, bnds), e) -> let (b,ee) = compress_let e in (List.concat [bnds; b], ee)
    | _ -> ([], e)

and js_of_match (e:exp) (cases:list<(pat * option<exp> * exp)>) =
    let compile_pat (p:pat, cond:option<exp>, ret:exp) : source_t =
        let and_cond e1 e2 = match (e1, e2) with
            | (_, JSE_Bool(true)) -> e1 | (JSE_Bool(true), _) -> e2
            | _ -> JSE_Land(e1, e2) in
        let or_cond e1 e2 = match (e1, e2) with
            | (_, JSE_Bool(false)) -> e1 | (JSE_Bool(false), _) -> e2
            | _ -> JSE_Lor(e1, e2) in
        let pat_return props = let rs = JSS_Return(Some(js_of_expr None ret)) in
            let r = match cond with None -> rs | Some(c) -> JSS_If(js_of_expr None c, rs, None)
            in if props=[] then r else JSS_With(JSE_Object(props),r) in
        let rec aux (id:string) (p:pat) = match p with
        | Pat_cons(x, l) -> let tagcond = JSE_Equal(JSE_Identifier(id^".t"), JSE_String(x.str)) in
            let (valcond, valbinds, _) = List.fold_left (
                fun (cur, b, i) p -> let (next, nb) = aux (sprintf "%s.v[%d]" id i) p in
                (and_cond cur next, b @ nb, i+1)
            ) (JSE_Bool(true), [], 0) l in (and_cond tagcond valcond, valbinds)
        | Pat_var(bv) -> (JSE_Bool(true), [JSP_Property(bv.ppname.idText, JSE_Identifier(id))])
        | Pat_tvar(_) -> failwith "fail..."
        | Pat_constant(c) -> (JSE_Sequal(JSE_Identifier(id), js_of_const c), [])
        | Pat_disj(l) -> List.fold_left (fun (cur,b) p->
            let (next, nb) = aux id p in (or_cond cur next, b @ nb)) (JSE_Bool(false), []) l
        | Pat_wild -> (JSE_Bool(true), [])
        | Pat_withinfo(p,_) -> aux id p
        | _ -> failwith "fail..."
        in let (conds, binds) = (aux "$v" p) in
        let finalret = pat_return binds in
        JS_Statement(match conds with JSE_Bool(true) -> finalret | _ -> JSS_If(conds, finalret, None))
    in JSE_Call(
        JSE_Function(None, ["$v"], List.map compile_pat cases),
        [js_of_expr None e])

and js_of_expr (binder:option<string>) (expr:exp) : expression_t =
    match try_compile_constructor expr with
    | Some(result) -> result
    | None -> (match expr with
        | Exp_bvar(x) -> JSE_Identifier(x.v.ppname.idText)
        | Exp_fvar(x,b) -> JSE_Identifier(x.v.str)
        | Exp_constant(c) -> js_of_const c
        | Exp_abs(x, t, e) -> js_of_fun binder x t e
        | Exp_app(e1, e2, f) -> JSE_Call(js_of_expr None e1, [js_of_expr None e2])
        | Exp_match(e, c) -> js_of_match e c
        | Exp_let((_, bnds), e) -> let (bext, ee) = compress_let expr in
            JSE_Call(JSE_Function(None, [],
                [JS_Statement(JSS_Declaration(List.map js_of_binding bext));
                JS_Statement(JSS_Return(Some(js_of_expr None ee)))]
            ), [])
        | _ -> Util.print_any expr; JSE_Elision)

and untype_expr (e:exp) =
    let e = Absyn.Util.compress_exp e in
    let unt_pat (p:pat, cnd:option<exp>, v:exp) = 
        (p, (match cnd with None->None | Some(e)->Some(untype_expr e)), untype_expr v) in
    let unt_bnd (x,t,e) =  (x, t, untype_expr e) in
    match e with
    | Exp_tapp(ee, _) -> untype_expr ee
    | Exp_meta(m) -> (match m with
        | Meta_info(exp, _, _) -> untype_expr exp
        | Meta_desugared(exp, _) -> untype_expr exp
        | Meta_datainst(exp, _) -> untype_expr exp)
    | Exp_abs(x, t, e) -> Exp_abs(x, t, untype_expr e)
    | Exp_app(e1, e2,f) -> Exp_app(untype_expr e1, untype_expr e2, f)
    | Exp_let((b,binds), e) -> Exp_let((b,List.map unt_bnd binds), untype_expr e)
    | Exp_match(e, pl) -> Exp_match(untype_expr e, List.map unt_pat pl)
    | _ -> e

and type_arity = function
  | Typ_fun(_,t,_,_) -> 1 + (type_arity t.t)
  | Typ_refine(_, t, _) -> type_arity t.t
  | Typ_app(t, _, _) -> (type_arity t.t) - 1
  | Typ_dep(t,_,_) -> type_arity t.t
  | Typ_lam(_,_,t) -> 1 + (type_arity t.t)
  | Typ_tlam(_, _, t) -> type_arity t.t
  | Typ_ascribed(t,_) -> type_arity t.t
  | Typ_meta(Meta_pos(t,_)) -> type_arity t.t
  | Typ_meta(Meta_pattern(t,_)) -> type_arity t.t
  | Typ_meta(Meta_named(t,_)) -> type_arity t.t
  | _ -> 0 

and compile_def (d:sigelt) =
    match d with
    | Sig_datacon(n,ty,tyn,_) -> printf "\nAdding %s\n" n.str; Util.smap_add constructors n.str (type_arity ty.t, None)
    | Sig_bundle(defs, range) -> List.iter compile_def defs
    | _ -> ()

and js_of_exports isrec (id,typ,expr) : source_t =
    let (n,sn) = match id with Inl(x) -> failwith "unexpected boundvar in module export"
            | Inr(x) -> (x.str,x.ident.idText) in
    let s = match js_of_expr (if isrec then Some(sn) else None) (untype_expr expr) with
    | JSE_Elision -> JSS_Empty
    | e -> JSS_Expression(JSE_Assign(JSE_Identifier(n), e))
    in JS_Statement(s)

let rec js_of_singl (p:sigelt) : list<source_t> =
    match p with
    | Sig_let((isrec, bind),range) -> List.map (js_of_exports isrec) bind
    | Sig_bundle(defs, range) -> List.iter compile_def defs; []
    | _ -> []

let js_of_fstar (m:modul) : Ast.t =
    (JS_Statement(JSS_Expression(JSE_Assign(JSE_Identifier(m.name.str),JSE_Object([])))))
        :: (List.map js_of_singl m.exports |> List.concat)

let js_of_fstars (fmods : list<modul>) : Ast.t =
    let fmods = List.map js_of_fstar fmods in
    List.concat fmods



