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
    JSE_Function(fn, [x.ppname.idText], [JS_Statement(JSS_Return(js_of_expr None e))])

and js_of_meta (e:meta_e) : option<expression_t> =
    let r = match e with
    | Meta_info(exp, typ, range) -> js_of_expr None exp
    | Meta_desugared(exp, srcinfo) -> js_of_expr None exp
    | Meta_datainst(exp, _) -> js_of_expr None exp
    in r

and js_of_expr (binder:option<string>) (expr:exp) : option<expression_t> =
    let r = match Absyn.Util.compress_exp expr with
    | Exp_bvar(x) -> JSE_Identifier(x.v.ppname.idText)
    | Exp_fvar(x,b) -> JSE_Identifier(x.v.str)
    | Exp_constant(c) -> js_of_const c
    | Exp_abs(x, t, e) -> js_of_fun binder x t e
    | Exp_app(e1, e2,f) -> (match (js_of_expr None e1, js_of_expr None e2) with
        | (Some(x), Some(y)) -> JSE_Call(x, [y]) | _ -> failwith "Failed")
        (* flag indicates whether the argument is explicit instantiation of an implict param *)
    (*
    | Exp_match      of exp * list<(pat * option<exp> * exp)>      (* optional when clause in each equation *)
    | Exp_let        of letbindings * exp                          (* let (rec?) x1 = e1 AND ... AND xn = en in e *)
    *)
    | Exp_meta(m) -> (match js_of_meta m with None->JSE_Elision | Some(w) -> w)
    | _ -> JSE_Elision (*Util.print_any expr; failwith "unsupported expression"*)
    in if r=JSE_Elision then None else Some r

and js_of_let isrec (id,typ,expr) : list<object_prop_t> =
    let n = match id with Inl(x) -> failwith "unexpected boundvar in module export"
            | Inr(x) -> x.ident.idText in
    match js_of_expr (if isrec then Some n else None) expr with
    | Some e -> [JSP_Property(n, e)]
    | None -> []

let rec js_of_singl (p:sigelt) : list<object_prop_t> =
    match p with
    | Sig_let((isrec, bind),range) -> List.map (js_of_let isrec) bind |> List.concat
    | _ -> []

let js_of_fstar (m:modul) : source_t =
    (JS_Statement(JSS_Expression(JSE_Assign(JSE_Identifier(m.name.str),JSE_Object(
        if m.is_interface then [] else List.map js_of_singl m.exports |> List.concat
    )))))

let js_of_fstars (fmods : list<modul>) : Ast.t =
    let fmods = List.map js_of_fstar fmods in
    (JS_Statement(JSS_Declaration(["FStar",Some(JSE_Object([]))]))) :: fmods



