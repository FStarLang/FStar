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

let rec js_of_const (c:sconst) : expression_t =
    match c with
    | Const_unit -> JSE_Undefined
    | Const_uint8(n) -> JSE_Number((float)n)
    | Const_bool(b) -> JSE_Bool(b)
    | Const_int32(n) -> JSE_Number((float)n)
    | Const_int64(n) -> JSE_Number((float)n)
    | Const_char(c) -> failwith "no chars..."
    | Const_float(f) -> JSE_Number(f)
    | Const_bytearray(ba,r) | Const_string(ba,r) -> JSE_String(Util.string_of_bytes ba)

and js_of_fun (fn:option<string>) (x:bvvdef) (t:typ) (e:exp) : expression_t =
    JSE_Function(fn, [x.ppname.idText], [JS_Statement(JSS_Return(
        match js_of_expr None e with JSE_Elision | JSE_Undefined -> None | e -> Some(e)
    ))])

and js_of_app (e1:exp) (e2:exp) =
    let (e1,e2) = (Absyn.Util.compress_exp e1, Absyn.Util.compress_exp e2) in
    let nonstd e1 e2 = Util.print_any e1; JSE_Call(js_of_expr None e1, [js_of_expr None e2]) in
    match e1 with
    | Exp_fvar(x,b) -> (match x.v.str with
        | "Prims.op_Minus" -> JSE_Minus(js_of_expr None e2)
        | "Prims.op_Negation" -> JSE_Lnot(js_of_expr None e2)
        | _ -> nonstd e1 e2)
    | Exp_app(Exp_fvar(x,b), e3, f) ->
        (match x.v.str with
        | "Prims.op_Addition" -> JSE_Add(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_Subtraction" -> JSE_Sub(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_Multiply" -> JSE_Multiply(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_Modulus" -> JSE_Mod(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_Division" -> JSE_Divide(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_BarBar" -> JSE_Lor(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_AmpAmp" -> JSE_Land(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_GreaterThan" -> JSE_Gt(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_LessThanOrEqual" -> JSE_Le(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_LessThan" -> JSE_Lt(js_of_expr None e3, js_of_expr None e2)
        | "Prims.op_GreaterThanOrEqual" -> JSE_Ge(js_of_expr None e3, js_of_expr None e2)
        | "" -> JSE_Lor(js_of_expr None e3, js_of_expr None e2)
        | _ -> nonstd e1 e2)
    | _ -> nonstd e1 e2

and js_of_binding (x:either<bvvdef,lident>, t:typ, e:exp) =
    let n = match x with Inl(x) -> x.ppname.idText | Inr(x) -> x.ident.idText in
    (n, Some(js_of_expr None e))

and compress_let (e:exp) =
    match e with
    | Exp_let((_, bnds), e) -> let (b,ee) = compress_let e in (List.concat [bnds; b], ee)
    | _ -> ([], e)

and js_of_match (e:exp) (cases:list<(pat * option<exp> * exp)>) =
    let rec compile_pat (last:statement_t) (id:string) (p:pat) : statement_t =
        match p with
        | Pat_cons(x, l) ->
            let next = List.fold_left (fun cur p -> compile_pat cur (id^".v") p) last l in
            (*let next = (match l with [] -> last | h::t -> compile_pat last (id^".t") h) in*)
            JSS_If(JSE_Equal(JSE_Identifier(id^".t"), JSE_String(x.str)), next, None)
        | Pat_var(bv) -> JSS_If(JSE_Sequence([JSE_Assign(
                JSE_Dot(JSE_Identifier("$bind"), bv.ppname.idText), JSE_Identifier(id^".v")
            ); JSE_Bool(true)]), last, None)
        | Pat_tvar(_) -> failwith "fail..."
        | Pat_constant(c) -> JSS_If(JSE_Sequal(JSE_Identifier(id), js_of_const c), last, None)
        (*| Pat_disj     of list<pat>*)
        | Pat_wild -> last
        | Pat_withinfo(p,_) -> compile_pat last id p
        | _ -> failwith "fail..."
    and wrap_pat (pat, cond, res) =
        let success = JSS_With(JSE_Identifier("$bind"), JSS_Return(
                let jsr = js_of_expr None res in
                match cond with None -> Some(jsr)
                | Some(c) -> Some(JSE_Conditional(js_of_expr None c, jsr, JSE_Null))
            )) in
        JSE_Function(None, ["$v"], [
            JS_Statement(JSS_Declaration(["$bind", Some(JSE_Object([]))]));
            JS_Statement(compile_pat success "$v" pat);
            JS_Statement(JSS_Return(Some(JSE_Null)))
        ])
    in JSE_Call(JSE_Identifier("this.$pm"), [js_of_expr None e; JSE_Array(
        List.map wrap_pat cases
    )])

and js_of_expr (binder:option<string>) (expr:exp) : expression_t =
    match expr with
    | Exp_bvar(x) -> JSE_Identifier(x.v.ppname.idText)
    | Exp_fvar(x,b) -> JSE_Identifier(x.v.str)
    | Exp_constant(c) -> js_of_const c
    | Exp_abs(x, t, e) -> js_of_fun binder x t e
    | Exp_app(e1, e2,f) -> js_of_app e1 e2
    | Exp_match(e, c) -> js_of_match e c
    | Exp_let((_, bnds), e) -> let (bext, ee) = compress_let expr in
        JSE_Call(JSE_Function(None, [],
            [JS_Statement(JSS_Declaration(List.map js_of_binding bext));
             JS_Statement(JSS_Return(Some(js_of_expr None ee)))]
        ), [])
    | _ -> Util.print_any expr; JSE_Elision (*Util.print_any expr; failwith "unsupported expression"*)

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
    | _ -> []

let js_of_fstar (m:modul) : Ast.t =
    (JS_Statement(JSS_Expression(JSE_Assign(JSE_Dot(JSE_This, m.name.str),JSE_Object([])))))
        :: (List.map js_of_singl m.exports |> List.concat)

let js_of_fstars (fmods : list<modul>) : Ast.t =
    let fmods = List.map js_of_fstar fmods in
    [JS_FunctionDeclaration(Some "FStar", [], List.concat fmods)]



