module Microsoft.FStar.Absyn.SSyntax

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FSharp.Reflection
open System.Reflection
open System.Xml
open System.Runtime.Serialization

exception Err of string

(* AST for serialization of modules *)

let serialize_list (f:'a -> 'b) (l: list<'a>) :array<'b> = Array.map f (List.toArray l)
let deserialize_list (f:'a -> 'b) (a: array<'a>) :list<'b> = Array.toList (Array.map f a)

type s_ident = string

let serialize_ident (ast : ident) : s_ident = ast.idText
let deserialize_ident (ast : s_ident) : ident = mk_ident (ast, dummyRange)

type s_LongIdent = 
    { ns : array<s_ident>;
      ident : s_ident }

let serialize_LongIdent (ast : LongIdent) : s_LongIdent = 
    { ns = serialize_list serialize_ident ast.ns;
      ident = serialize_ident ast.ident }

let deserialize_LongIdent (ast : s_LongIdent) : LongIdent = 
    lid_of_ids (deserialize_list deserialize_ident ast.ns @ [ deserialize_ident ast.ident ])

type s_lident = s_LongIdent

let serialize_lident (ast : lident) : s_lident = serialize_LongIdent ast
let deserialize_lident (ast : s_lident) : lident = deserialize_LongIdent ast

type s_withinfo_t<'sa, 'st> = 
    { v : 'sa;
      sort : 'st }

let serialize_withinfo_t (s_v : 'a -> 'sa) (s_sort : 't -> 'st) (ast : withinfo_t<'a, 't>) : s_withinfo_t<'sa, 'st> = 
    { v = s_v ast.v;
      sort = s_sort ast.sort }

let deserialize_withinfo_t (ds_v : 'sa -> 'a) (ds_sort : 'st -> 't) (ast : s_withinfo_t<'sa, 'st>) : withinfo_t<'a, 't> = 
    { v = ds_v ast.v;
      sort = ds_sort ast.sort;
      p = dummyRange }

type s_var<'st> = s_withinfo_t<s_lident, 'st>

let serialize_var (s_sort : 't -> 'st) (ast : var<'t>) : s_var<'st> = serialize_withinfo_t serialize_lident s_sort ast
let deserialize_var (ds_sort : 'st -> 't) (ast : s_var<'st>) : var<'t> = 
    deserialize_withinfo_t deserialize_lident ds_sort ast

type s_fieldname = s_lident

type s_bvdef<'sa> = 
    { ppname : s_ident;
      realname : s_ident }

let serialize_bvdef (ast : bvdef<'a>) : s_bvdef<'sa> = 
    { ppname = serialize_ident ast.ppname;
      realname = serialize_ident ast.realname }

let deserialize_bvdef (ast : s_bvdef<'sa>) : bvdef<'a> = 
    { ppname = deserialize_ident ast.ppname;
      realname = deserialize_ident ast.realname }

type s_bvar<'sa, 'st> = s_withinfo_t<s_bvdef<'sa>, 'st>

let serialize_bvar (s_sort : 't -> 'st) (ast : bvar<'a, 't>) : s_bvar<'sa, 'st> = 
    serialize_withinfo_t serialize_bvdef s_sort ast
let deserialize_bvar (ds_sort : 'st -> 't) (ast : s_bvar<'sa, 'st>) : bvar<'a, 't> = 
    deserialize_withinfo_t deserialize_bvdef ds_sort ast

[<KnownType("KnownTypes")>]
type s_sconst = 
    | S_Const_unit
    | S_Const_uint8 of byte
    | S_Const_bool of bool
    | S_Const_int32 of int32
    | S_Const_int64 of int64
    | S_Const_char of char
    | S_Const_float of double
    | S_Const_bytearray of array<byte>
    | S_Const_string of array<byte>
    static member KnownTypes() = 
        typeof<s_sconst>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

let serialize_sconst (ast : sconst) : s_sconst = 
    match ast with
    | Const_unit -> S_Const_unit
    | Const_uint8(v) -> S_Const_uint8(v)
    | Const_bool(v) -> S_Const_bool(v)
    | Const_int32(v) -> S_Const_int32(v)
    | Const_int64(v) -> S_Const_int64(v)
    | Const_char(v) -> S_Const_char(v)
    | Const_float(v) -> S_Const_float(v)
    | Const_bytearray(v, _) -> S_Const_bytearray(v)
    | Const_string(v, _) -> S_Const_string(v)

let deserialize_sconst (ast : s_sconst) : sconst = 
    match ast with
    | S_Const_unit -> Const_unit
    | S_Const_uint8(v) -> Const_uint8(v)
    | S_Const_bool(v) -> Const_bool(v)
    | S_Const_int32(v) -> Const_int32(v)
    | S_Const_int64(v) -> Const_int64(v)
    | S_Const_char(v) -> Const_char(v)
    | S_Const_float(v) -> Const_float(v)
    | S_Const_bytearray(v) -> Const_bytearray(v, dummyRange)
    | S_Const_string(v) -> Const_string(v, dummyRange)

type s_either<'sa, 'sb> = 
    { tag : string
      s_Inl : 'sa option
      s_Inr : 'sb option }

let serialize_either (s_l : 'a -> 'sa) (s_r : 'b -> 'sb) (ast : either<'a, 'b>) : s_either<'sa, 'sb> = 
    match ast with
    | Inl(v) -> 
        { tag = "C1"
          s_Inl = Some(s_l v)
          s_Inr = None }
    | Inr(v) -> 
        { tag = "C2"
          s_Inl = None
          s_Inr = Some(s_r v) }

let deserialize_either (ds_l : 'sa -> 'a) (ds_r : 'sb -> 'b) (ast : s_either<'sa, 'sb>) : either<'a, 'b> = 
    match ast.tag with
    | "C1" -> Inl(ds_l ast.s_Inl.Value)
    | "C2" -> Inr(ds_r ast.s_Inr.Value)
    | _ -> raise (Err "Unknown tag in either datatype")

type s_syntax<'sa, 'sb> = 
    { n : 'sa }

let serialize_syntax (s_a : 'a -> 'sa) (ast : syntax<'a, 'b>) : s_syntax<'sa, 'sb> = { n = s_a ast.n }

let deserialize_syntax (ds_a : 'sa -> 'a) (ds_b : 'b) (ast : s_syntax<'sa, 'sb>) : syntax<'a, 'b> = 
    { n = ds_a ast.n
      tk = ds_b
      pos = dummyRange
      fvs = ref None
      uvs = ref None }

[<KnownType("KnownTypes")>]
type s_typ' = 
    | S_Typ_btvar of s_btvar
    | S_Typ_const of s_ftvar
    | S_Typ_fun of s_binders * s_comp
    | S_Typ_refine of s_bvvar * s_typ
    | S_Typ_app of s_typ * s_args
    | S_Typ_lam of s_binders * s_typ
    | S_Typ_ascribed of s_typ * s_knd
    | S_Typ_meta of s_meta_t
    | S_Typ_unknown
    static member KnownTypes() = 
        typeof<s_typ'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and [<KnownType("KnownTypes")>] s_meta_t = 
    | S_Meta_pattern of s_typ * array<s_arg>
    | S_Meta_named of s_typ * s_lident
    | S_Meta_labeled of s_typ * string * bool
    static member KnownTypes() = 
        typeof<s_meta_t>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and s_arg = s_either<s_typ, s_exp> * bool

and s_args = array<s_arg>

and s_binder = s_either<s_btvar, s_bvvar> * bool

and s_binders = array<s_binder>

and s_typ = s_syntax<s_typ', s_knd>

and s_comp_typ = 
    { effect_name : s_lident
      result_typ : s_typ
      effect_args : s_args
      flags : array<s_cflags> }

and [<KnownType("KnownTypes")>] s_comp' = 
    | S_Total of s_typ
    | S_Comp of s_comp_typ
    static member KnownTypes() = 
        typeof<s_comp'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and s_comp = s_syntax<s_comp', unit>

and s_cflags = string

(* this is an enum *)
and [<KnownType("KnownTypes")>] s_exp' = 
    | S_Exp_bvar of s_bvvar
    | S_Exp_fvar of s_fvvar * bool
    | S_Exp_constant of s_sconst
    | S_Exp_abs of s_binders * s_exp
    | S_Exp_app of s_exp * s_args
    | S_Exp_match of s_exp * array<s_pat * option<s_exp> * s_exp>
    | S_Exp_ascribed of s_exp * s_typ
    | S_Exp_let of s_letbindings * s_exp
    | S_Exp_meta of s_meta_e
    static member KnownTypes() = 
        typeof<s_exp'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and [<KnownType("KnownTypes")>] s_meta_e = 
    | S_Meta_desugared of s_exp * s_meta_source_info
    | S_Meta_datainst of s_exp * s_typ option
    static member KnownTypes() = 
        typeof<s_meta_e>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and [<KnownType("KnownTypes")>] s_meta_source_info = 
    | S_Data_app
    | S_Sequence
    | S_Primop
    static member KnownTypes() = 
        typeof<s_meta_source_info>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and s_exp = s_syntax<s_exp', s_typ>

and s_btvdef = s_bvdef<s_typ>

and s_bvvdef = s_bvdef<s_exp>

and [<KnownType("KnownTypes")>] s_pat' = 
    | S_Pat_disj of array<s_pat>
    | S_Pat_constant of s_sconst
    | S_Pat_cons of s_fvvar * array<s_pat>
    | S_Pat_var of s_bvvar
    | S_Pat_tvar of s_btvar
    | S_Pat_wild of s_bvvar
    | S_Pat_twild of s_btvar
    | S_Pat_dot_term of s_bvvar * s_exp
    | S_Pat_dot_typ of s_btvar * s_typ
    static member KnownTypes() = 
        typeof<s_pat'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and s_pat = s_withinfo_t<s_pat', s_either<s_knd, s_typ>>

and [<KnownType("KnownTypes")>] s_knd' = 
    | S_Kind_type
    | S_Kind_effect
    | S_Kind_abbrev of s_kabbrev * s_knd
    | S_Kind_arrow of s_binders * s_knd
    | S_Kind_lam of s_binders * s_knd
    | S_Kind_unknown
    (* AR: leaving out uvar, delayed, and unknown ? *)
    static member KnownTypes() = 
        typeof<s_knd'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and s_knd = s_syntax<s_knd', unit>

and s_kabbrev = s_lident * s_args

and s_lbname = s_either<s_bvvdef, s_lident>

and s_letbindings = bool * array<s_lbname * s_typ * s_exp>

and s_fvar = s_either<s_btvdef, s_bvvdef>

and s_btvar = s_bvar<s_typ, s_knd>

and s_bvvar = s_bvar<s_exp, s_typ>

and s_ftvar = s_var<s_knd>

and s_fvvar = s_var<s_typ>

let rec serialize_typ' (ast : typ') : s_typ' = 
    match ast with
    | Typ_btvar(v) -> S_Typ_btvar(serialize_btvar v)
    | Typ_const(v) -> S_Typ_const(serialize_ftvar v)
    | Typ_fun(bs, c) -> S_Typ_fun(serialize_binders bs, serialize_comp c)
    | Typ_refine(v, t) -> S_Typ_refine(serialize_bvvar v, serialize_typ t)
    | Typ_app(t, ars) -> S_Typ_app(serialize_typ t, serialize_args ars)
    | Typ_lam(bs, t) -> S_Typ_lam(serialize_binders bs, serialize_typ t)
    | Typ_ascribed(t, k) -> S_Typ_ascribed(serialize_typ t, serialize_knd k)

    | Typ_meta(m) -> S_Typ_meta(serialize_meta_t m)
    | Typ_unknown -> S_Typ_unknown
    | Typ_uvar(_, _) -> raise (Err "typ not impl:1")
    | Typ_delayed(_, _, _) -> raise (Err "typ not impl:2")

and serialize_meta_t (ast : meta_t) : s_meta_t = 
    match ast with
    | Meta_pattern(t, l) -> S_Meta_pattern(serialize_typ t, serialize_list serialize_arg l)
    | Meta_named(t, lid) -> S_Meta_named(serialize_typ t, serialize_lident lid)
    | Meta_labeled(t, s, b) -> S_Meta_labeled(serialize_typ t, s, b)
    | _ -> raise (Err "unimplemented meta_t")

and serialize_arg (ast : arg) : s_arg = (serialize_either serialize_typ serialize_exp (fst ast), (snd ast))

and serialize_args (ast : args) : s_args = serialize_list serialize_arg ast

and serialize_binder (ast : binder) : s_binder = (serialize_either serialize_btvar serialize_bvvar (fst ast), (snd ast))

and serialize_binders (ast : binders) : s_binders = serialize_list serialize_binder ast

and serialize_typ (ast : typ) : s_typ = serialize_syntax serialize_typ' (Util.compress_typ ast) 

and serialize_comp_typ (ast : comp_typ) : s_comp_typ = 
    { effect_name = serialize_lident ast.effect_name
      result_typ = serialize_typ ast.result_typ
      effect_args = serialize_args ast.effect_args
      flags = serialize_list serialize_cflags ast.flags }

and serialize_comp' (ast : comp') : s_comp' = 
    match ast with
    | Total(t) -> S_Total(serialize_typ t)
    | Comp(c) -> S_Comp(serialize_comp_typ c)

and serialize_comp (ast : comp) : s_comp = serialize_syntax serialize_comp' ast

and serialize_cflags (ast : cflags) : s_cflags = 
    match ast with
    | TOTAL -> "C1"
    | MLEFFECT -> "C2"
    | RETURN -> "C3"
    | SOMETRIVIAL -> "C4"
    | LEMMA -> "C5"
    | DECREASES _ -> failwith "NYI: Decreases"

and serialize_exp' (ast : exp') : s_exp' = 
    match ast with
    | Exp_bvar(v) -> S_Exp_bvar(serialize_bvvar v)
    | Exp_fvar(v, b) -> S_Exp_fvar(serialize_fvvar v, b)
    | Exp_constant(c) -> S_Exp_constant(serialize_sconst c)
    | Exp_abs(bs, e) -> S_Exp_abs(serialize_binders bs, serialize_exp e)
    | Exp_app(e, ars) -> S_Exp_app(serialize_exp e, serialize_args ars)
    | Exp_match(e, l) -> 
        let g eopt = 
            match eopt with
            | Some(e1) -> Some(serialize_exp e1)
            | None -> None
        
        let f (p, eopt, e) = (serialize_pat p, g eopt, serialize_exp e)
        S_Exp_match(serialize_exp e, serialize_list f l)
    | Exp_ascribed(e, t) -> S_Exp_ascribed(serialize_exp e, serialize_typ t)
    | Exp_let(lbs, e) -> S_Exp_let(serialize_letbindings lbs, serialize_exp e)
    | Exp_meta(m) -> S_Exp_meta(serialize_meta_e m)
    | _ -> raise (Err "unimplemented exp'")

and serialize_meta_e (ast : meta_e) : s_meta_e = 
    match ast with
    | Meta_desugared(e, s) -> S_Meta_desugared(serialize_exp e, serialize_meta_source_info s)
    | Meta_datainst(e, topt) -> 
        S_Meta_datainst(serialize_exp e, 
                        match topt with
                        | None -> None
                        | Some(t) -> Some(serialize_typ t))

and serialize_meta_source_info (ast : meta_source_info) : s_meta_source_info = 
    match ast with
    | Data_app -> S_Data_app
    | Sequence -> S_Sequence
    | Primop -> S_Primop

and serialize_exp (ast : exp) : s_exp = serialize_syntax serialize_exp' (Util.compress_exp ast)

and serialize_btvdef (ast : btvdef) : s_btvdef = serialize_bvdef ast

and serialize_bvvdef (ast : bvvdef) : s_bvvdef = serialize_bvdef ast

and serialize_pat' (ast : pat') : s_pat' = 
    match ast with
    | Pat_disj(l) -> S_Pat_disj(serialize_list serialize_pat l)
    | Pat_constant(c) -> S_Pat_constant(serialize_sconst c)
    | Pat_cons(v, l) -> S_Pat_cons(serialize_fvvar v, serialize_list serialize_pat l)
    | Pat_var(v) -> S_Pat_var(serialize_bvvar v)
    | Pat_tvar(v) -> S_Pat_tvar(serialize_btvar v)
    | Pat_wild(v) -> S_Pat_wild(serialize_bvvar v)
    | Pat_twild(v) -> S_Pat_tvar(serialize_btvar v)
    | Pat_dot_term(v, e) -> S_Pat_dot_term(serialize_bvvar v, serialize_exp e)
    | Pat_dot_typ(v, t) -> S_Pat_dot_typ(serialize_btvar v, serialize_typ t)

and serialize_pat (ast : pat) : s_pat = 
    serialize_withinfo_t serialize_pat' (serialize_either serialize_knd serialize_typ) ast

and serialize_knd' (ast : knd') : s_knd' = 
    match ast with
    | Kind_type -> S_Kind_type
    | Kind_effect -> S_Kind_effect
    | Kind_abbrev(ka, k) -> S_Kind_abbrev(serialize_kabbrev ka, serialize_knd k)
    | Kind_arrow(bs, k) -> S_Kind_arrow(serialize_binders bs, serialize_knd k)
    | Kind_lam(bs, k) -> S_Kind_lam(serialize_binders bs, serialize_knd k)
    | Kind_unknown -> S_Kind_unknown
    | Kind_uvar(uv, args) -> raise (Err "knd' serialization unimplemented:1")
    | Kind_delayed(_, _, _) -> raise (Err "knd' serialization unimplemented:2")

and serialize_knd (ast : knd) : s_knd = serialize_syntax serialize_knd' (Util.compress_kind ast)

and serialize_kabbrev (ast : kabbrev) : s_kabbrev = (serialize_lident (fst ast), serialize_args (snd ast))

and serialize_lbname (ast : lbname) : s_lbname = serialize_either serialize_bvvdef serialize_lident ast

and serialize_letbindings (ast : letbindings) : s_letbindings = 
    let f (n, t, e) = (serialize_lbname n, serialize_typ t, serialize_exp e)
    (fst ast, serialize_list f (snd ast))

and serialize_fvar (ast : fvar) : s_fvar = serialize_either serialize_btvdef serialize_bvvdef ast

and serialize_btvar (ast : btvar) : s_btvar = serialize_bvar serialize_knd ast

and serialize_bvvar (ast : bvvar) : s_bvvar = serialize_bvar serialize_typ ast

and serialize_ftvar (ast : ftvar) : s_ftvar = serialize_var serialize_knd ast

and serialize_fvvar (ast : fvvar) : s_fvvar = serialize_var serialize_typ ast

let rec deserialize_typ' (ast : s_typ') : typ' = 
    match ast with
    | S_Typ_btvar(v) -> Typ_btvar(deserialize_btvar v)
    | S_Typ_const(v) -> Typ_const(deserialize_ftvar v)
    | S_Typ_fun(bs, c) -> Typ_fun(deserialize_binders bs, deserialize_comp c)
    | S_Typ_refine(v, t) -> Typ_refine(deserialize_bvvar v, deserialize_typ t)
    | S_Typ_app(t, ars) -> Typ_app(deserialize_typ t, deserialize_args ars)
    | S_Typ_lam(bs, t) -> Typ_lam(deserialize_binders bs, deserialize_typ t)
    | S_Typ_ascribed(t, k) -> Typ_ascribed(deserialize_typ t, deserialize_knd k)
    | S_Typ_meta(m) -> Typ_meta(deserialize_meta_t m)
    | S_Typ_unknown -> Typ_unknown

and deserialize_meta_t (ast : s_meta_t) : meta_t = 
    match ast with
    | S_Meta_pattern(t, l) -> Meta_pattern(deserialize_typ t, deserialize_list deserialize_arg l)
    | S_Meta_named(t, lid) -> Meta_named(deserialize_typ t, deserialize_lident lid)
    | S_Meta_labeled(t, s, b) -> Meta_labeled(deserialize_typ t, s, b)

and deserialize_arg (ast : s_arg) : arg = (deserialize_either deserialize_typ deserialize_exp (fst ast), (snd ast))

and deserialize_args (ast : s_args) : args = deserialize_list deserialize_arg ast

and deserialize_binder (ast : s_binder) : binder = 
    (deserialize_either deserialize_btvar deserialize_bvvar (fst ast), (snd ast))

and deserialize_binders (ast : s_binders) : binders = deserialize_list deserialize_binder ast

and deserialize_typ (ast : s_typ) : typ = deserialize_syntax deserialize_typ' mk_Kind_unknown ast

and deserialize_comp_typ (ast : s_comp_typ) : comp_typ = 
    { effect_name = deserialize_lident ast.effect_name
      result_typ = deserialize_typ ast.result_typ
      effect_args = deserialize_args ast.effect_args
      flags = deserialize_list deserialize_cflags ast.flags }

and deserialize_comp' (ast : s_comp') : comp' = 
    match ast with
    | S_Total(t) -> Total(deserialize_typ t)
    | S_Comp(c) -> Comp(deserialize_comp_typ c)

and deserialize_comp (ast : s_comp) : comp = deserialize_syntax deserialize_comp' () ast

and deserialize_cflags (ast : s_cflags) : cflags = 
    match ast with
    | "C1" -> TOTAL
    | "C2" -> MLEFFECT
    | "C3" -> RETURN
    | "C4" -> SOMETRIVIAL
    | "C5" -> LEMMA
    | _ -> raise (Err "unknown cflag")

and deserialize_exp' (ast : s_exp') : exp' = 
    match ast with
    | S_Exp_bvar(v) -> Exp_bvar(deserialize_bvvar v)
    | S_Exp_fvar(v, b) -> Exp_fvar(deserialize_fvvar v, b)
    | S_Exp_constant(c) -> Exp_constant(deserialize_sconst c)
    | S_Exp_abs(bs, e) -> Exp_abs(deserialize_binders bs, deserialize_exp e)
    | S_Exp_app(e, ars) -> Exp_app(deserialize_exp e, deserialize_args ars)
    | S_Exp_match(e, l) -> 
        let g eopt = 
            match eopt with
            | Some(e1) -> Some(deserialize_exp e1)
            | None -> None
        
        let f (p, eopt, e) = (deserialize_pat p, g eopt, deserialize_exp e)
        Exp_match(deserialize_exp e, deserialize_list f l)
    | S_Exp_ascribed(e, t) -> Exp_ascribed(deserialize_exp e, deserialize_typ t)
    | S_Exp_let(lbs, e) -> Exp_let(deserialize_letbindings lbs, deserialize_exp e)
    | S_Exp_meta(m) -> Exp_meta(deserialize_meta_e m)

and deserialize_meta_e (ast : s_meta_e) : meta_e = 
    match ast with
    | S_Meta_desugared(e, s) -> Meta_desugared(deserialize_exp e, deserialize_meta_source_info s)
    | S_Meta_datainst(e, topt) -> 
        Meta_datainst(deserialize_exp e, 
                      match topt with
                      | None -> None
                      | Some(t) -> Some(deserialize_typ t))

and deserialize_meta_source_info (ast : s_meta_source_info) : meta_source_info = 
    match ast with
    | S_Data_app -> Data_app
    | S_Sequence -> Sequence
    | S_Primop -> Primop

and deserialize_exp (ast : s_exp) : exp = deserialize_syntax deserialize_exp' mk_Typ_unknown ast

and deserialize_btvdef (ast : s_btvdef) : btvdef = deserialize_bvdef ast

and deserialize_bvvdef (ast : s_bvvdef) : bvvdef = deserialize_bvdef ast

and deserialize_pat' (ast : s_pat') : pat' = 
    match ast with
    | S_Pat_disj(l) -> Pat_disj(deserialize_list deserialize_pat l)
    | S_Pat_constant(c) -> Pat_constant(deserialize_sconst c)
    | S_Pat_cons(v, l) -> Pat_cons(deserialize_fvvar v, deserialize_list deserialize_pat l)
    | S_Pat_var(v) -> Pat_var(deserialize_bvvar v)
    | S_Pat_tvar(v) -> Pat_tvar(deserialize_btvar v)
    | S_Pat_wild(v) -> Pat_wild(deserialize_bvvar v)
    | S_Pat_twild(v) -> Pat_tvar(deserialize_btvar v)
    | S_Pat_dot_term(v, e) -> Pat_dot_term(deserialize_bvvar v, deserialize_exp e)
    | S_Pat_dot_typ(v, t) -> Pat_dot_typ(deserialize_btvar v, deserialize_typ t)

and deserialize_pat (ast : s_pat) : pat = 
    deserialize_withinfo_t deserialize_pat' (deserialize_either deserialize_knd deserialize_typ) ast

and deserialize_knd' (ast : s_knd') : knd' = 
    match ast with
    | S_Kind_type -> Kind_type
    | S_Kind_effect -> Kind_effect
    | S_Kind_abbrev(ka, k) -> Kind_abbrev(deserialize_kabbrev ka, deserialize_knd k)
    | S_Kind_arrow(bs, k) -> Kind_arrow(deserialize_binders bs, deserialize_knd k)
    | S_Kind_lam(bs, k) -> Kind_lam(deserialize_binders bs, deserialize_knd k)
    | S_Kind_unknown -> Kind_unknown

and deserialize_knd (ast : s_knd) : knd = deserialize_syntax deserialize_knd' () ast

and deserialize_kabbrev (ast : s_kabbrev) : kabbrev = (deserialize_lident (fst ast), deserialize_args (snd ast))

and deserialize_lbname (ast : s_lbname) : lbname = deserialize_either deserialize_bvvdef deserialize_lident ast

and deserialize_letbindings (ast : s_letbindings) : letbindings = 
    let f (n, t, e) = (deserialize_lbname n, deserialize_typ t, deserialize_exp e)
    (fst ast, deserialize_list f (snd ast))

and deserialize_fvar (ast : s_fvar) : fvar = deserialize_either deserialize_btvdef deserialize_bvvdef ast

and deserialize_btvar (ast : s_btvar) : btvar = deserialize_bvar deserialize_knd ast

and deserialize_bvvar (ast : s_bvvar) : bvvar = deserialize_bvar deserialize_typ ast

and deserialize_ftvar (ast : s_ftvar) : ftvar = deserialize_var deserialize_knd ast

and deserialize_fvvar (ast : s_fvvar) : fvvar = deserialize_var deserialize_typ ast

type s_formula = s_typ

let serialize_formula (ast : formula) : s_formula = serialize_typ ast
let deserialize_formula (ast : s_formula) : formula = deserialize_typ ast

[<KnownType("KnownTypes")>]
type s_qualifier = 
    | S_Private
    | S_Public
    | S_Assumption
    | S_Definition
    | S_Query
    | S_Lemma
    | S_Logic
    | S_Opaque
    | S_Discriminator of s_lident
    | S_Projector of s_lident * s_either<s_btvdef, s_bvvdef>
    | S_RecordType of array<s_ident>
    | S_RecordConstructor of array<s_ident>
    | S_ExceptionConstructor
    | S_Effect
    static member KnownTypes() = 
        typeof<s_qualifier>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

let serialize_qualifier (ast : qualifier) : s_qualifier = 
    match ast with
    | Private -> S_Private
    | Public -> S_Public
    | Assumption -> S_Assumption
    | Definition -> S_Definition
    | Query -> S_Query
    | Lemma -> S_Lemma
    | Logic -> S_Logic
    | Opaque -> S_Opaque
    | Discriminator(lid) -> S_Discriminator(serialize_lident lid)
    | Projector(lid, v) -> S_Projector(serialize_lident lid, serialize_either serialize_btvdef serialize_bvvdef v)
    | RecordType(l) -> S_RecordType(serialize_list serialize_ident l)
    | RecordConstructor(l) -> S_RecordConstructor(serialize_list serialize_ident l)
    | ExceptionConstructor -> S_ExceptionConstructor
    | Effect -> S_Effect

let deserialize_qualifier (ast : s_qualifier) : qualifier = 
    match ast with
    | S_Private -> Private
    | S_Public -> Public
    | S_Assumption -> Assumption
    | S_Definition -> Definition
    | S_Query -> Query
    | S_Lemma -> Lemma
    | S_Logic -> Logic
    | S_Opaque -> Opaque
    | S_Discriminator(lid) -> Discriminator(deserialize_lident lid)
    | S_Projector(lid, v) -> 
        Projector(deserialize_lident lid, deserialize_either deserialize_btvdef deserialize_bvvdef v)
    | S_RecordType(l) -> RecordType(deserialize_list deserialize_ident l)
    | S_RecordConstructor(l) -> RecordConstructor(deserialize_list deserialize_ident l)
    | S_ExceptionConstructor -> ExceptionConstructor
    | S_Effect -> Effect

type s_tycon = s_lident * s_binders * s_knd
let serialize_tycon ((lid, bs, k): tycon) :s_tycon = (serialize_lident lid, serialize_binders bs, serialize_knd k)
let deserialize_tycon ((lid, bs, k):s_tycon) :tycon = (deserialize_lident lid, deserialize_binders bs, deserialize_knd k)

type s_monad_abbrev = 
    { mabbrev : s_lident
      parms : s_binders
      def : s_typ }

let serialize_monad_abbrev (ast : monad_abbrev) : s_monad_abbrev = 
    { mabbrev = serialize_lident ast.mabbrev
      parms = serialize_binders ast.parms
      def = serialize_typ ast.def }

let deserialize_monad_abbrev (ast : s_monad_abbrev) : monad_abbrev = 
    { mabbrev = deserialize_lident ast.mabbrev
      parms = deserialize_binders ast.parms
      def = deserialize_typ ast.def }

type s_monad_order = 
    { source : s_lident
      target : s_lident
      lift : s_typ }

let serialize_monad_order (ast : monad_order) : s_monad_order = 
    { source = serialize_lident ast.source
      target = serialize_lident ast.target
      lift = serialize_typ ast.lift }

let deserialize_monad_order (ast : s_monad_order) : monad_order = 
    { source = deserialize_lident ast.source
      target = deserialize_lident ast.target
      lift = deserialize_typ ast.lift }

type s_monad_lat = array<s_monad_order>

let serialize_monad_lat (ast : monad_lat) : s_monad_lat = serialize_list serialize_monad_order ast
let deserialize_monad_lat (ast : s_monad_lat) : monad_lat = deserialize_list deserialize_monad_order ast

type s_monad_decl = 
    { mname : s_lident
      total : bool
      signature : s_knd
      ret : s_typ
      bind_wp : s_typ
      bind_wlp : s_typ
      if_then_else : s_typ
      ite_wp : s_typ
      ite_wlp : s_typ
      wp_binop : s_typ
      wp_as_type : s_typ
      close_wp : s_typ
      close_wp_t : s_typ
      assert_p : s_typ
      assume_p : s_typ
      null_wp : s_typ
      trivial : s_typ
      abbrevs : array<s_sigelt>
      kind_abbrevs: array<s_lident * array<s_either<s_btvdef, s_bvvdef>> * s_knd> }

and [<KnownType("KnownTypes")>] s_sigelt = 
    | S_Sig_tycon of s_lident * s_binders * s_knd * array<s_lident> * array<s_lident> * array<s_qualifier>
    | S_Sig_typ_abbrev of s_lident * s_binders * s_knd * s_typ * array<s_qualifier>
    | S_Sig_datacon of s_lident * s_typ * s_tycon * array<s_qualifier>
    | S_Sig_val_decl of s_lident * s_typ * array<s_qualifier>
    | S_Sig_assume of s_lident * s_formula * array<s_qualifier>
    | S_Sig_let of s_letbindings * array<s_lident>
    | S_Sig_main of s_exp
    | S_Sig_bundle of array<s_sigelt> * array<s_lident>
    | S_Sig_monads of array<s_monad_decl> * s_monad_lat * array<s_lident>
    static member KnownTypes() = 
        typeof<s_sigelt>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

let rec serialize_monad_decl (ast : monad_decl) : s_monad_decl = 
    { mname = serialize_lident ast.mname
      total = ast.total
      signature = serialize_knd ast.signature
      ret = serialize_typ ast.ret
      bind_wp = serialize_typ ast.bind_wp
      bind_wlp = serialize_typ ast.bind_wlp
      if_then_else = serialize_typ ast.if_then_else
      ite_wp = serialize_typ ast.ite_wp
      ite_wlp = serialize_typ ast.ite_wlp
      wp_binop = serialize_typ ast.wp_binop
      wp_as_type = serialize_typ ast.wp_as_type
      close_wp = serialize_typ ast.close_wp
      close_wp_t = serialize_typ ast.close_wp_t
      assert_p = serialize_typ ast.assert_p
      assume_p = serialize_typ ast.assume_p
      null_wp = serialize_typ ast.null_wp
      trivial = serialize_typ ast.trivial
      abbrevs = serialize_list serialize_sigelt ast.abbrevs
      kind_abbrevs = serialize_list (fun (lid, l, k) -> serialize_lident lid, serialize_list (fun vdef -> serialize_either serialize_btvdef serialize_bvvdef vdef) l, serialize_knd k) ast.kind_abbrevs }

and serialize_sigelt (ast : sigelt) : s_sigelt = 
    match ast with
    | Sig_tycon(lid, bs, k, l1, l2, qs, _) -> 
        S_Sig_tycon
            (serialize_lident lid, serialize_binders bs, serialize_knd k, serialize_list serialize_lident l1, 
             serialize_list serialize_lident l2, serialize_list serialize_qualifier qs)
    | Sig_typ_abbrev(lid, bs, k, t, qs, _) -> 
        S_Sig_typ_abbrev
            (serialize_lident lid, serialize_binders bs, serialize_knd k, serialize_typ t, 
             serialize_list serialize_qualifier qs)
    | Sig_datacon(lid1, t, tyc, qs, _) ->
      let t' =
        match Util.function_formals t with 
        | Some (f, c) -> mk_Typ_fun (f, Syntax.mk_Total  (Util.comp_result c)) t.tk dummyRange
        | None -> t
      in
      S_Sig_datacon(serialize_lident lid1, serialize_typ t', serialize_tycon tyc, serialize_list serialize_qualifier qs)
    | Sig_val_decl(lid, t, qs, _) -> 
        S_Sig_val_decl(serialize_lident lid, serialize_typ t, serialize_list serialize_qualifier qs)
    | Sig_assume(lid, fml, qs, _) -> 
        S_Sig_assume(serialize_lident lid, serialize_formula fml, serialize_list serialize_qualifier qs)
    | Sig_let(lbs, _, l) -> S_Sig_let(serialize_letbindings lbs, serialize_list serialize_lident l)
    | Sig_main(e, _) -> S_Sig_main(serialize_exp e)
    | Sig_bundle(l, _, lids) -> S_Sig_bundle(serialize_list serialize_sigelt l, serialize_list serialize_lident lids)
    | Sig_monads(l, lat, _, lids) -> 
        S_Sig_monads(serialize_list serialize_monad_decl l, serialize_monad_lat lat, serialize_list serialize_lident lids)

let rec deserialize_monad_decl (ast : s_monad_decl) : monad_decl = 
    { mname = deserialize_lident ast.mname
      total = ast.total
      signature = deserialize_knd ast.signature
      ret = deserialize_typ ast.ret
      bind_wp = deserialize_typ ast.bind_wp
      bind_wlp = deserialize_typ ast.bind_wlp
      if_then_else = deserialize_typ ast.if_then_else
      ite_wp = deserialize_typ ast.ite_wp
      ite_wlp = deserialize_typ ast.ite_wlp
      wp_binop = deserialize_typ ast.wp_binop
      wp_as_type = deserialize_typ ast.wp_as_type
      close_wp = deserialize_typ ast.close_wp
      close_wp_t = deserialize_typ ast.close_wp_t
      assert_p = deserialize_typ ast.assert_p
      assume_p = deserialize_typ ast.assume_p
      null_wp = deserialize_typ ast.null_wp
      trivial = deserialize_typ ast.trivial
      abbrevs = deserialize_list deserialize_sigelt ast.abbrevs
      kind_abbrevs = deserialize_list (fun (lid, l, k) -> deserialize_lident lid, deserialize_list (fun vdef -> deserialize_either deserialize_btvdef deserialize_bvvdef vdef) l, deserialize_knd k) ast.kind_abbrevs;
      default_monad = None } //FIXME!

and deserialize_sigelt (ast : s_sigelt) : sigelt = 
    match ast with
    | S_Sig_tycon(lid, bs, k, l1, l2, qs) -> 
        Sig_tycon
            (deserialize_lident lid, deserialize_binders bs, deserialize_knd k, deserialize_list deserialize_lident l1, 
             deserialize_list deserialize_lident l2, deserialize_list deserialize_qualifier qs, dummyRange)
    | S_Sig_typ_abbrev(lid, bs, k, t, qs) -> 
        Sig_typ_abbrev
            (deserialize_lident lid, deserialize_binders bs, deserialize_knd k, deserialize_typ t, 
             deserialize_list deserialize_qualifier qs, dummyRange)
    | S_Sig_datacon(lid1, t, tyc, qs) -> 
        Sig_datacon
            (deserialize_lident lid1, deserialize_typ t, deserialize_tycon tyc, deserialize_list deserialize_qualifier qs, 
             dummyRange)
    | S_Sig_val_decl(lid, t, qs) -> 
        Sig_val_decl(deserialize_lident lid, deserialize_typ t, deserialize_list deserialize_qualifier qs, dummyRange)
    | S_Sig_assume(lid, fml, qs) -> 
        Sig_assume(deserialize_lident lid, deserialize_formula fml, deserialize_list deserialize_qualifier qs, dummyRange)
    | S_Sig_let(lbs, l) -> Sig_let(deserialize_letbindings lbs, dummyRange, deserialize_list deserialize_lident l)
    | S_Sig_main(e) -> Sig_main(deserialize_exp e, dummyRange)
    | S_Sig_bundle(l, lids) -> Sig_bundle(deserialize_list deserialize_sigelt l, dummyRange, deserialize_list deserialize_lident lids)
    | S_Sig_monads(l, lat, lids) -> 
        Sig_monads
            (deserialize_list deserialize_monad_decl l, deserialize_monad_lat lat, dummyRange, deserialize_list deserialize_lident lids)

type s_sigelts = array<s_sigelt>

let serialize_sigelts (ast : sigelts) : s_sigelts = serialize_list serialize_sigelt ast
let deserialize_sigelts (ast : s_sigelts) : sigelts = deserialize_list deserialize_sigelt ast

type s_modul = 
    { name : s_lident
      declarations : s_sigelts
      exports : s_sigelts
      is_interface : bool }

let serialize_modul (ast : modul) : s_modul = 
    { name = serialize_lident ast.name
      declarations = serialize_sigelts ast.declarations
      exports = serialize_sigelts (*[]*) ast.exports
      is_interface = ast.is_interface }

let deserialize_modul (ast : s_modul) : modul = 
    { name = deserialize_lident ast.name
      declarations = deserialize_sigelts ast.declarations
      exports = deserialize_sigelts (*[||]*) ast.exports
      is_interface = ast.is_interface
      is_deserialized = true }
