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

module FStar.Backends.JS.Translate

open FStar.Backends.JS.Ast

open System
open System.Text

open FStar
open FStar.Util
open FStar.Range
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Util

let constructors : smap<(option<int> * option<(list<expression_t> -> expression_t)>)>   = Util.smap_create 1000

let nothing =
    Util.smap_add constructors "Prims.op_Minus" (Some 1, Some(function x::[] -> JSE_Minus(x) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Negation" (Some 1, Some(function x::[] -> JSE_Lnot(x) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Addition" (Some 2, Some(function x::y::[] -> JSE_Add(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Subtraction" (Some 2, Some(function x::y::[] -> JSE_Sub(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Division" (Some 2, Some(function x::y::[] -> JSE_Divide(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Multiply" (Some 2, Some(function x::y::[] -> JSE_Multiply(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Modulus" (Some 2, Some(function x::y::[] -> JSE_Mod(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_BarBar" (Some 2, Some(function x::y::[] -> JSE_Lor(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_AmpAmp" (Some 2, Some(function x::y::[] -> JSE_Land(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_GreaterThan" (Some 2, Some(function x::y::[] -> JSE_Gt(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_LessThanOrEqual" (Some 2, Some(function x::y::[] -> JSE_Le(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_LessThan" (Some 2, Some(function x::y::[] -> JSE_Lt(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_GreaterThanOrEqual" (Some 2, Some(function x::y::[] -> JSE_Ge(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_Equality" (Some 2, Some(function x::y::[] -> JSE_Equal(JSE_Add(x,JSE_String("")),JSE_Add(y,JSE_String(""))) | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_disEquality" (Some 2, Some(function x::y::[] -> JSE_Lnot(JSE_Equal(JSE_Add(x,JSE_String("")),JSE_Add(y,JSE_String("")))) | _ -> failwith ""));
    Util.smap_add constructors "String.strcat" (Some 2, Some(function x::y::[] -> JSE_Add(x,y) | _ -> failwith ""));
    Util.smap_add constructors "String.length" (Some 1, Some(function x::[] -> JSE_Dot(x,"length") | _ -> failwith ""));
    Util.smap_add constructors "Prims.fst" (Some 1, Some(function x::[] -> JSE_Dot(x, "v[0]") | _ -> failwith ""));
    Util.smap_add constructors "Prims.snd" (Some 1, Some(function x::[] -> JSE_Dot(x, "v[1]") | _ -> failwith ""));
    Util.smap_add constructors "Prims.op_ColonEquals" (Some 2, Some(function x::y::[] -> JSE_Assign(x,y) | _ -> failwith ""));
    Util.smap_add constructors "Prims.Nil" (None, None);
    Util.smap_add constructors "Prims.Cons" (None, None);
    Util.smap_add constructors "Prims.None" (None, None);
    Util.smap_add constructors "Prims.Some" (None, None);
    Util.smap_add constructors "Prims.MkTuple2" (None, None);
    Util.smap_add constructors "Prims.MkTuple3" (None, None);
    Util.smap_add constructors "Prims.MkTuple4" (None, None);
    Util.smap_add constructors "Prims.MkTuple5" (None, None);
    Util.smap_add constructors "Prims.MkTuple6" (None, None);
    Util.smap_add constructors "Prims.MkTuple7" (None, None);
    Util.smap_add constructors "Prims.MkTuple8" (None, None);
    Util.smap_add constructors "Prims.failwith" (Some 1, Some(function x::[] -> JSE_Call(
        JSE_Function(None,[],[JS_Statement(JSS_Throw(x))]),[]) | _ -> failwith ""));
    ()

let rec js_of_const (c:sconst) : expression_t =
    match c with
    | Const_int _ -> failwith "Unexpected mathematical integer constant"
    | Const_unit -> JSE_Undefined
    | Const_uint8(n) -> JSE_Number(Util.float_of_byte n)
    | Const_bool(b) -> JSE_Bool(b)
    | Const_int32(n) -> JSE_Number(Util.float_of_int32 n)
    | Const_int64(n) -> JSE_Number(Util.float_of_int64 n)
    | Const_char(c) -> JSE_String(Util.string_of_char c)
    | Const_float(f) -> JSE_Number(f)
    | Const_bytearray(ba,r) | Const_string(ba,r) -> JSE_String(Util.string_of_bytes ba)

and js_of_fun (fn:option<string>) (x:bvvdef) (t:typ) (e:exp) : expression_t =
    JSE_Function(fn, [(text_of_id x.ppname)], [JS_Statement(JSS_Return(
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
            | None -> JSE_Call(JSE_Identifier("$C"), [JSE_String(cons);JSE_Array(ae)])
            | Some(f) -> f ae
        in List.fold_left (fun v s->JSE_Function(None, [s], [JS_Statement(
                JSS_Return(Some(v)))])) compiled_cons freevars
    in let rec aux (args:list<exp>) (e:exp) = match e.n with
    | Exp_fvar(x, b) ->
        (match Util.smap_try_find constructors x.v.str with
        | Some(None, compiler) -> Some(uncur x.v.str args (List.length args) compiler)
        | Some(Some(arity), compiler) when (arity >= List.length args) -> Some(uncur x.v.str args arity compiler)
        | _ -> None)
    | Exp_app(e, args) ->
        if args |> Util.for_some (function Inl _, _ -> true | _ -> false)
        then None
        else aux (args |> List.collect (function Inl _, _ -> [] | Inr e, _ -> [e])) e
    | _ -> None
    in aux [] e

and js_of_binding ((x,t,e):(either<bvvdef,lident> * typ * exp)) =
    let n = match x with Inl(x) -> (text_of_id x.ppname) | Inr(x) -> (text_of_id x.ident) in
    (n, Some(js_of_expr None e))

and compress_let (e:exp) =
    match e.n with
    | Exp_let((_, bnds), e) -> let (b,ee) = compress_let e in (List.concat [bnds; b], ee)
    | _ -> ([], e)

and js_of_match (e:exp) (cases:list<(pat * option<exp> * exp)>) =
    let compile_pat ((p,cond,ret):(pat * option<exp> * exp)) : source_t =
        let and_cond e1 e2 = match (e1, e2) with
            | (_, JSE_Bool(true)) -> e1 | (JSE_Bool(true), _) -> e2
            | _ -> JSE_Land(e1, e2) in
        let or_cond e1 e2 = match (e1, e2) with
            | (_, JSE_Bool(false)) -> e1 | (JSE_Bool(false), _) -> e2
            | _ -> JSE_Lor(e1, e2) in
        let pat_return props = let rs = JSS_Return(Some(js_of_expr None ret)) in
            let r = match cond with None -> rs | Some(c) -> JSS_If(js_of_expr None c, rs, None)
            in if props=[] then r else JSS_With(JSE_Object(props),r) in
        let rec aux (id:string) (p:pat) = match p.v with
        | Pat_cons(x, l) -> let tagcond = JSE_Equal(JSE_Identifier(id^".t"), JSE_String(x.v.str)) in
            let (valcond, valbinds, _) = List.fold_left (
                fun (cur, b, i) p -> let (next, nb) = aux (id^".v["^(Util.string_of_int i)^"]") p in
                (and_cond cur next, b @ nb, i+1)
            ) (JSE_Bool(true), [], 0) l in (and_cond tagcond valcond, valbinds)
        | Pat_var(bv, _) -> (JSE_Bool(true), [(text_of_id JSP_Property(bv.v.ppname), JSE_Identifier(id))])
        | Pat_tvar(_) -> failwith "fail..."
        | Pat_constant(c) -> (JSE_Sequal(JSE_Identifier(id), js_of_const c), [])
        | Pat_disj(l) -> List.fold_left (fun (cur,b) p->
            let (next, nb) = aux id p in (or_cond cur next, b @ nb)) (JSE_Bool(false), []) l
        | Pat_wild _ -> (JSE_Bool(true), [])
        | _ -> failwith "fail..."
        in let (conds, binds) = (aux "$v" p) in
        let finalret = pat_return binds in
        JS_Statement(match conds with JSE_Bool(true) -> finalret | _ -> JSS_If(conds, finalret, None))
    in let add_fallback cases =
        let r = List.map compile_pat cases in
        if Util.for_some (function JS_Statement(JSS_Return(_))->true|_->false) r
        then r else r @ [JS_Statement(JSS_Throw(JSE_String("Incomplete pattern")))]
    in match cases with
        | [({v=Pat_constant(Const_bool(true))}, None, e1); ({v=Pat_constant(Const_bool(false))}, None, e2)] ->
             JSE_Conditional(js_of_expr None e, js_of_expr None e1, js_of_expr None e2)
        | _ -> JSE_Call(JSE_Function(None, ["$v"], add_fallback cases), [js_of_expr None e])

and js_of_expr (binder:option<string>) (expr:exp) : expression_t =
    match try_compile_constructor expr with
    | Some(result) -> result
    | None -> (match expr.n with
        | Exp_bvar(x) -> (text_of_id JSE_Identifier(x.v.ppname))
        | Exp_fvar(x,b) -> JSE_Identifier(x.v.str)
        | Exp_constant(c) -> js_of_const c
        | Exp_abs([], e) -> js_of_expr binder e
        | Exp_abs((Inl _, _)::rest, e) ->
          js_of_expr binder (mk_Exp_abs(rest, e) None expr.pos)
        | Exp_abs((Inr x, _)::rest, e) -> js_of_fun binder x.v x.sort (mk_Exp_abs(rest, e) None e.pos)
        | Exp_app(e, args) -> JSE_Call(js_of_expr None e, args |> List.collect (function Inr e, _ -> [js_of_expr None e] | _ -> []))
        | Exp_match(e, c) -> js_of_match e c
        | Exp_let((_, bnds), e) -> let (bext, ee) = compress_let expr in
            JSE_Call(JSE_Function(None, [],
                [JS_Statement(JSS_Declaration(List.map js_of_binding bext));
                JS_Statement(JSS_Return(Some(js_of_expr None ee)))]
            ), [])
        | Exp_ascribed(e,_) -> js_of_expr binder e
        | Exp_meta(m) -> (match m with
            | Meta_desugared(e, _) -> js_of_expr binder e)
        | _ -> Util.print_any expr; JSE_Elision)

and untype_expr (e:exp) =
    let e = Absyn.Util.compress_exp e in
    let unt_pat ((p,cnd,v):(pat * option<exp> * exp)) =
        (p, (match cnd with None->None | Some(e)->Some(untype_expr e)), untype_expr v) in
    let unt_bnd (x,t,e) =  (x, t, untype_expr e) in
    match e.n with
    | Exp_app(ee, args) -> mk_Exp_app(untype_expr ee, args |> List.filter (function Inl _, _ -> false | _ -> true)) None e.pos
    | Exp_meta(m) -> (match m with
        | Meta_desugared(exp, _) -> untype_expr exp)
    | Exp_abs(bs, ee) -> syn e.pos None <| mk_Exp_abs(bs |> List.filter (function Inl _, _ -> false | _ -> true), untype_expr ee)
    | Exp_let((b,binds), e) -> syn e.pos None <| mk_Exp_let((b,List.map unt_bnd binds), untype_expr e)
    | Exp_match(e, pl) -> syn e.pos None <| mk_Exp_match(untype_expr e, List.map unt_pat pl)
    | _ -> e

and comp_vars ct = match ct with
    | Total(t) -> type_vars t.n
    | Comp(ct) -> type_vars ct.result_typ.n

and type_vars ty = match ty with
    | Typ_fun(bs,c) -> (bs |> List.collect (function
       | Inr x, _ ->
        let tl = type_vars x.sort.n in
        let hd = if is_null_binder (Inr x, None) then None else Some x.v in
        hd::tl
       | _ -> [])) @ (comp_vars c.n)
    | Typ_lam(_,t) | Typ_refine({sort=t}, _) | Typ_app(t, _)
    | Typ_ascribed(t,_)
    | Typ_meta(Meta_pattern(t,_))
    | Typ_meta(Meta_named(t,_)) -> type_vars t.n
    | _ -> []

and compile_def (d:sigelt) =
    (* TODO Surely there must be a better way of figuring out the field names from records in the desugared AST *)
    let add_fieldnames cons vnames =
        let rec aux i l = match l with
        | x::r -> (match x with None -> aux i r
            | Some(v) -> if Util.starts_with (text_of_id v.ppname) "^fname^" then
                (Util.smap_add constructors (cons^"."^(Util.substring_from (text_of_id v.ppname) 7))
                (Some(1), Some(function x::[] -> JSE_Dot(x, "v["^(Util.string_of_int i)^"]") | _ -> failwith "")));
                aux (i+1) r)
        | [] -> ()
        in aux 0 vnames
    in match d with
    | Sig_datacon(n,ty,_,_,_,_) ->
        let fields = type_vars ty.n in
        Util.smap_add constructors n.str ((match fields with []->Some(1) | _ -> None), None);
        add_fieldnames n.str fields
    | Sig_bundle(defs, _, _, _) -> List.iter compile_def defs
    | _ -> ()

and js_of_exports isrec (id,typ,expr) : source_t =
    let (n,sn) = match id with Inl(x) -> failwith "unexpected boundvar in module export"
            | Inr(x) -> ((text_of_id x.str,x.ident)) in
    let s = match js_of_expr (if isrec then Some(sn) else None) (untype_expr expr) with
    | JSE_Elision -> JSS_Empty
    | e -> JSS_Expression(JSE_Assign(JSE_Identifier(n), e))
    in JS_Statement(s)

let rec js_of_singl (p:sigelt) : list<source_t> =
    match p with
    | Sig_let((isrec, bind),range, _, _) -> List.map (js_of_exports isrec) bind
    | Sig_bundle(defs, _, _, range) -> List.iter compile_def defs; []
    | _ -> []

let js_of_fstar (m:modul) : Ast.t =
    (JS_Statement(JSS_If(JSE_Lnot(JSE_Dot(JSE_This, m.name.str)), JSS_Expression(JSE_Assign(JSE_Identifier(m.name.str),JSE_Object([]))),None)))
        :: (List.map js_of_singl m.exports |> List.concat)

let js_of_fstars (fmods : list<modul>) : Ast.t =
    let fmods = List.concat (List.map js_of_fstar fmods) in
    [JS_Statement(JSS_Expression(JSE_Call(JSE_Function(None, [],
        (JS_Statement(JSS_Declaration(["$C", Some(JSE_Function(None, ["t";"v"],
            [JS_Statement(JSS_Return(Some(JSE_Object([
                JSP_Property("t", JSE_Identifier("t"));
                JSP_Property("v", JSE_Identifier("v"));
                JSP_Property("toString", JSE_Function(None,[],[JS_Statement(JSS_Return(Some(
                    JSE_Add(JSE_Add(JSE_Identifier("this.t"), JSE_String(":")), JSE_Identifier("this.v"))
                    )))]))
            ]))))]
        ))])))::fmods
    ), [])))]
