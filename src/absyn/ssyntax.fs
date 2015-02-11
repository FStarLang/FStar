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

open System.IO

exception Err of string

(*type Writer = {
    write_byte:      byte   -> unit
    write_bool:      bool   -> unit
    write_int32:     int    -> unit
    write_int64:     int    -> unit
    write_char:      char   -> unit
    write_double:    double -> unit
    write_bytearray: byte[] -> unit    
}

type Reader = {
    read_byte:      unit -> byte
    read_bool:      unit -> bool
    read_int32:     unit -> int
    read_int64:     unit -> int64
    read_char:      unit -> char
    read_double:    unit -> double
    read_bytearray: unit -> byte[]
}*)

type Writer = BinaryWriter

type Reader = BinaryReader

(* AST for serialization of modules *)

(*let serialize_list (f:'a -> 'b) (l: list<'a>) :array<'b> = if List.length l = 0 then null else Array.map f (List.toArray l)
let deserialize_list (f:'a -> 'b) (a: array<'a>) :list<'b> = if a = null then List.empty else Array.toList (Array.map f a) *)

let serialize_list (writer:Writer) (f:Writer -> 'a -> unit) (l:list<'a>) :unit =
    writer.Write(List.length l);
    List.iter (fun elt -> f writer elt) (List.rev_append l [])

let deserialize_list (reader: Reader) (f:Reader -> 'a) :list<'a> =
    let n = reader.ReadInt32() in
    let rec helper (accum:list<'a>) (n:int) :list<'a> =
        if n = 0 then accum
        else
            helper ((f reader)::accum) (n - 1)
    in
    helper [] n
    
(*type s_ident = string

let serialize_ident (ast : ident) : s_ident = ast.idText
let deserialize_ident (ast : s_ident) : ident = mk_ident (ast, dummyRange)*)

let serialize_ident (writer: Writer) (ast:ident) :unit = writer.Write(ast.idText)
let deserialize_ident (reader: Reader) :ident = mk_ident (reader.ReadString(), dummyRange)

(*type s_LongIdent = 
    { ns : array<s_ident>;
      id : s_ident }

let serialize_LongIdent (ast : LongIdent) : s_LongIdent = 
    { ns = serialize_list serialize_ident ast.ns;
      id = serialize_ident ast.ident }

let deserialize_LongIdent (ast : s_LongIdent) : LongIdent = 
    lid_of_ids (deserialize_list deserialize_ident ast.ns @ [ deserialize_ident ast.id ]) *)

let serialize_LongIdent (writer:Writer) (ast:LongIdent) :unit =
    serialize_list writer serialize_ident ast.ns;
    serialize_ident writer ast.ident

let deserialize_LongIdent (reader:Reader) :LongIdent =
    lid_of_ids (deserialize_list reader deserialize_ident @ [ deserialize_ident reader ])

(*type s_lident = s_LongIdent

let serialize_lident (ast : lident) : s_lident = serialize_LongIdent ast
let deserialize_lident (ast : s_lident) : lident = deserialize_LongIdent ast *)

let serialize_lident = serialize_LongIdent
let deserialize_lident = deserialize_LongIdent

(*type s_withinfo_t<'sa, 'st> = 
    { v : 'sa;
      (* sort *) s : 'st }

let serialize_withinfo_t (s_v : 'a -> 'sa) (s_sort : 't -> 'st) (ast : withinfo_t<'a, 't>) : s_withinfo_t<'sa, 'st> = 
    { v = s_v ast.v;
      s = s_sort ast.sort }

let deserialize_withinfo_t (ds_v : 'sa -> 'a) (ds_sort : 'st -> 't) (ast : s_withinfo_t<'sa, 'st>) : withinfo_t<'a, 't> = 
    { v = ds_v ast.v;
      sort = ds_sort ast.s;
      p = dummyRange } *)

let serialize_withinfo_t (writer: Writer) (s_v:Writer -> 'a -> unit) (s_sort:Writer -> 't -> unit) (ast:withinfo_t<'a, 't>) :unit =
    s_v writer ast.v;
    s_sort writer ast.sort

let deserialize_withinfo_t (reader:Reader) (ds_v:Reader -> 'a) (ds_sort:Reader -> 't) :withinfo_t<'a, 't> =
    { v = ds_v reader;
      sort = ds_sort reader;
      p = dummyRange}

(*type s_var<'st> = s_withinfo_t<s_lident, 'st>

let serialize_var (s_sort : 't -> 'st) (ast : var<'t>) : s_var<'st> = serialize_withinfo_t serialize_lident s_sort ast
let deserialize_var (ds_sort : 'st -> 't) (ast : s_var<'st>) : var<'t> = 
    deserialize_withinfo_t deserialize_lident ds_sort ast *)

let serialize_var (writer:Writer) (s_sort:Writer -> 't -> unit) (ast:var<'t>) :unit =
    serialize_withinfo_t writer serialize_lident s_sort ast

let deserialize_var (reader:Reader) (ds_sort:Reader -> 't) :var<'t> =
    deserialize_withinfo_t reader deserialize_lident ds_sort

(*type s_bvdef<'sa> = 
    { (* ppname *) p : s_ident;
      (* realname *) r : s_ident }

let serialize_bvdef (ast : bvdef<'a>) : s_bvdef<'sa> = 
    { p = serialize_ident ast.ppname;
      r = serialize_ident ast.realname }

let deserialize_bvdef (ast : s_bvdef<'sa>) : bvdef<'a> = 
    { ppname = deserialize_ident ast.p;
      realname = deserialize_ident ast.r }*)

let serialize_bvdef (writer:Writer) (ast:bvdef<'a>) :unit =
    serialize_ident writer ast.ppname;
    serialize_ident writer ast.realname

let deserialize_bvdef (reader:Reader) :bvdef<'a> =
    { ppname = deserialize_ident reader;
      realname = deserialize_ident reader}

(*type s_bvar<'sa, 'st> = s_withinfo_t<s_bvdef<'sa>, 'st>

let serialize_bvar (s_sort : 't -> 'st) (ast : bvar<'a, 't>) : s_bvar<'sa, 'st> = 
    serialize_withinfo_t serialize_bvdef s_sort ast
let deserialize_bvar (ds_sort : 'st -> 't) (ast : s_bvar<'sa, 'st>) : bvar<'a, 't> = 
    deserialize_withinfo_t deserialize_bvdef ds_sort ast*)

let serialize_bvar (writer:Writer) (s_sort:Writer -> 't -> unit) (ast:bvar<'a, 't>) :unit =
    serialize_withinfo_t writer serialize_bvdef s_sort ast

let deserialize_bvar (reader:Reader) (ds_sort:Reader -> 't) :bvar<'a, 't> =
    deserialize_withinfo_t reader deserialize_bvdef ds_sort

(*[<KnownType("KnownTypes")>]
type s_sconst = 
    | (* S_Const_unit *)       A
    | (* S_Const_uint8 *)      B of byte
    | (* S_Const_bool *)       C of bool
    | (* S_Const_int32 *)      D of int32
    | (* S_Const_int64 *)      E of int64
    | (* S_Const_char *)       F of char
    | (* S_Const_char *)       G of double
    | (* S_Const_bytearray *)  H of array<byte>
    | (* S_Const_string *)     I of array<byte>
    static member KnownTypes() = 
        typeof<s_sconst>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

let serialize_sconst (ast : sconst) : s_sconst = 
    match ast with
    | Const_unit -> (* S_Const_unit *)                 A
    | Const_uint8(v) -> (* S_Const_uint8 *)            B(v)
    | Const_bool(v) -> (* S_Const_bool *)              C(v)
    | Const_int32(v) -> (* S_Const_int32 *)            D(v)
    | Const_int64(v) -> (* S_Const_int64 *)            E(v)
    | Const_char(v) -> (* S_Const_char *)              F(v)
    | Const_float(v) -> (* S_Const_char *)             G(v)
    | Const_bytearray(v, _) -> (* S_Const_bytearray *) H(v)
    | Const_string(v, _) -> (* S_Const_string *)       I(v)

let deserialize_sconst (ast : s_sconst) : sconst = 
    match ast with
    | (* S_Const_unit *)      A -> Const_unit
    | (* S_Const_uint8 *)     B(v) -> Const_uint8(v)
    | (* S_Const_bool *)      C(v) -> Const_bool(v)
    | (* S_Const_int32 *)     D(v) -> Const_int32(v)
    | (* S_Const_int64 *)     E(v) -> Const_int64(v)
    | (* S_Const_char *)      F(v) -> Const_char(v)
    | (* S_Const_char *)      G(v) -> Const_float(v)
    | (* S_Const_bytearray *) H(v) -> Const_bytearray(v, dummyRange)
    | (* S_Const_string *)    I(v) -> Const_string(v, dummyRange)*)

let serialize_sconst (writer:Writer) (ast:sconst) :unit =
    match ast with
    | Const_unit -> writer.Write('a')
    | Const_uint8(v) -> writer.Write('b'); writer.Write(v)
    | Const_bool(v) -> writer.Write('c'); writer.Write(v)
    | Const_int32(v) -> writer.Write('d'); writer.Write(v)
    | Const_int64(v) -> writer.Write('e'); writer.Write(v)
    | Const_char(v) -> writer.Write('f'); writer.Write(v)
    | Const_float(v) -> writer.Write('g'); writer.Write(v)
    | Const_bytearray(v, _) -> writer.Write('h'); writer.Write(v.Length); writer.Write(v)
    | Const_string(v, _) -> writer.Write('i'); writer.Write(v.Length); writer.Write(v)

let deserialize_sconst (reader:Reader) :sconst =
    let c = reader.ReadChar() in
    match c with
    | 'a' -> Const_unit
    | 'b' -> Const_uint8(reader.ReadByte())
    | 'c' -> Const_bool(reader.ReadBoolean())
    | 'd' -> Const_int32(reader.ReadInt32())
    | 'e' -> Const_int64(reader.ReadInt64())
    | 'f' -> Const_char(reader.ReadChar())
    | 'g' -> Const_float(reader.ReadDouble())
    | 'h' -> let n = reader.ReadInt32() in Const_bytearray(reader.ReadBytes(n), dummyRange)
    | 'i' -> let n = reader.ReadInt32() in Const_string(reader.ReadBytes(n), dummyRange)
    
(*type s_either<'sa, 'sb> = 
    { t : string     (* tag *)
      l : 'sa option (* Inl *)
      r : 'sb option (* Inr *) }

let serialize_either (s_l : 'a -> 'sa) (s_r : 'b -> 'sb) (ast : either<'a, 'b>) : s_either<'sa, 'sb> = 
    match ast with
    | Inl(v) -> 
        { t = "C1"
          l = Some(s_l v)
          r = None }
    | Inr(v) -> 
        { t = "C2"
          l = None
          r = Some(s_r v) }

let deserialize_either (ds_l : 'sa -> 'a) (ds_r : 'sb -> 'b) (ast : s_either<'sa, 'sb>) : either<'a, 'b> = 
    match ast.t with
    | "C1" -> Inl(ds_l ast.l.Value)
    | "C2" -> Inr(ds_r ast.r.Value)
    | _ -> raise (Err "Unknown tag in either datatype")*)

let serialize_either (writer:Writer) (s_l:Writer -> 'a -> unit) (s_r:Writer -> 'b -> unit) (ast:either<'a, 'b>) :unit =
    match ast with
    | Inl(v) -> writer.Write('a'); s_l writer v
    | Inr(v) -> writer.Write('b'); s_r writer v

let deserialize_either (reader:Reader) (ds_l:Reader -> 'a) (ds_r: Reader -> 'b) :either<'a, 'b> =
    match (reader.ReadChar()) with
    | 'a' -> Inl(ds_l reader)
    | 'b' -> Inr(ds_r reader)
    |  _ -> raise (Err "Unknown tag in either datatype")

(*type s_syntax<'sa, 'sb> = 
    { n : 'sa }

let serialize_syntax (s_a : 'a -> 'sa) (ast : syntax<'a, 'b>) : s_syntax<'sa, 'sb> = { n = s_a ast.n }

let deserialize_syntax (ds_a : 'sa -> 'a) (ds_b : 'b) (ast : s_syntax<'sa, 'sb>) : syntax<'a, 'b> = 
    { n = ds_a ast.n
      tk = Util.mk_ref None
      pos = dummyRange
      fvs = ref None
      uvs = ref None }*)

let serialize_syntax (writer:Writer) (s_a:Writer -> 'a -> unit) (ast:syntax<'a, 'b>) :unit = s_a writer ast.n

let deserialize_syntax (reader:Reader) (ds_a:Reader -> 'a) (ds_b:'b) :syntax<'a, 'b> =
    { n = ds_a reader
      tk = Util.mk_ref None
      pos = dummyRange
      fvs = ref None
      uvs = ref None}

(*[<KnownType("KnownTypes")>]
type s_typ' = 
    | (* S_Typ_btvar *)    A of s_btvar
    | (* S_Typ_const *)    B of s_ftvar
    | (* S_Typ_fun *)      C of s_binders * s_comp
    | (* S_Typ_refine *)   D of s_bvvar * s_typ
    | (* S_Typ_app *)      E of s_typ * s_args
    | (* S_Typ_lam *)      F of s_binders * s_typ
    | (* S_Typ_ascribed *) G of s_typ * s_knd
    | (* S_Typ_meta *)     H of s_meta_t
    | (* S_Typ_unknown *)  I
    static member KnownTypes() = 
        typeof<s_typ'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and [<KnownType("KnownTypes")>] s_meta_t = 
    | (* S_Meta_pattern *) A of s_typ * array<s_arg>
    | (* S_Meta_named *)   B of s_typ * s_lident
    | (* S_Meta_labeled *) C of s_typ * string * bool
    static member KnownTypes() = 
        typeof<s_meta_t>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and s_arg = s_either<s_typ, s_exp> * bool

and s_args = array<s_arg>

and s_binder = s_either<s_btvar, s_bvvar> * bool

and s_binders = array<s_binder>

and s_typ = s_syntax<s_typ', s_knd>

and s_comp_typ = 
    { en : s_lident (* effect_name *)
      rt : s_typ    (* result_typ *)
      ea : s_args   (* effect_args *)
      fs : array<s_cflags>  (* flags *) }

and [<KnownType("KnownTypes")>] s_comp' = 
    | (* S_Total*) A of s_typ
    | (* S_Comp *) B of s_comp_typ
    static member KnownTypes() = 
        typeof<s_comp'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and s_comp = s_syntax<s_comp', unit>

and [<KnownType("KnownTypes")>] s_cflags =
    | (* S_Total *)          A
    | (* S_MLEFFECT *)       B
    | (* S_RETURN *)         C
    | (* S_PARTIAL_RETURN *) D
    | (* S_SOMETRIVIAL *)    E
    | (* S_LEMMA *)          F
    | (* S_DECREASES *)      G of s_exp
    static member KnownTypes() = 
        typeof<s_cflags>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

(* this is an enum *)
and [<KnownType("KnownTypes")>] s_exp' = 
    | (* S_Exp_bvar *)     A of s_bvvar
    | (* S_Exp_fvar *)     B of s_fvvar * bool
    | (* S_Exp_constant *) C of s_sconst
    | (* S_Exp_abs *)      D of s_binders * s_exp
    | (* S_Exp_app *)      E of s_exp * s_args
    | (* S_Exp_match *)    F of s_exp * array<s_pat * option<s_exp> * s_exp>
    | (* S_Exp_ascribed *) G of s_exp * s_typ
    | (* S_Exp_let *)      H of s_letbindings * s_exp
    | (* S_Exp_meta *)     I of s_meta_e
    static member KnownTypes() = 
        typeof<s_exp'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and [<KnownType("KnownTypes")>] s_meta_e = 
    | (* S_Meta_desugared *) A of s_exp * s_meta_source_info
    static member KnownTypes() = 
        typeof<s_meta_e>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and [<KnownType("KnownTypes")>] s_meta_source_info = 
    | (* S_Data_app *)     A
    | (* S_Sequence *)     B
    | (* S_Primop *)       C
    | (* S_MaskedEffect *) D
    static member KnownTypes() = 
        typeof<s_meta_source_info>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) 
        |> Array.filter FSharpType.IsUnion

and s_exp = s_syntax<s_exp', s_typ>

and s_btvdef = s_bvdef<s_typ>

and s_bvvdef = s_bvdef<s_exp>

and [<KnownType("KnownTypes")>] s_pat' = 
    | (* S_Pat_disj *)     A of array<s_pat>
    | (* S_Pat_constant *) B of s_sconst
    | (* S_Pat_cons *)     C of s_fvvar * array<s_pat>
    | (* S_Pat_var *)      D of s_bvvar * bool
    | (* S_Pat_tvar *)     E of s_btvar
    | (* S_Pat_wild *)     F of s_bvvar
    | (* S_Pat_twild *)    G of s_btvar
    | (* S_Pat_dot_term *) H of s_bvvar * s_exp
    | (* S_Pat_dot_typ *)  I of s_btvar * s_typ
    static member KnownTypes() = 
        typeof<s_pat'>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic) |> Array.filter FSharpType.IsUnion

and s_pat = s_withinfo_t<s_pat', s_either<s_knd, s_typ>>

and [<KnownType("KnownTypes")>] s_knd' = 
    | (* S_Kind_type *)    A
    | (* S_Kind_effect *)  B
    | (* S_Kind_abbrev *)  C of s_kabbrev * s_knd
    | (* S_Kind_arrow *)   D of s_binders * s_knd
    | (* S_Kind_lam *)     E of s_binders * s_knd
    | (* S_Kind_unknown *) F
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
    | Typ_btvar(v) -> (* S_Typ_btvar *) s_typ'.A(serialize_btvar v)
    | Typ_const(v) -> (* S_Typ_const *) s_typ'.B(serialize_ftvar v)
    | Typ_fun(bs, c) -> (* S_Typ_fun *) s_typ'.C(serialize_binders bs, serialize_comp c)
    | Typ_refine(v, t) -> (* S_Typ_refine *) s_typ'.D(serialize_bvvar v, serialize_typ t)
    | Typ_app(t, ars) -> (* S_Typ_app *) s_typ'.E(serialize_typ t, serialize_args ars)
    | Typ_lam(bs, t) -> (* S_Typ_lam *) s_typ'.F(serialize_binders bs, serialize_typ t)
    | Typ_ascribed(t, k) -> (* S_Typ_ascribed *) s_typ'.G(serialize_typ t, serialize_knd k)

    | Typ_meta(m) -> (* S_Typ_meta *) s_typ'.H(serialize_meta_t m)
    | Typ_unknown -> (* S_Typ_unknown *) s_typ'.I
    | Typ_uvar(_, _) -> raise (Err "typ not impl:1")
    | Typ_delayed(_, _) -> raise (Err "typ not impl:2")

and serialize_meta_t (ast : meta_t) : s_meta_t = 
    match ast with
    | Meta_pattern(t, l) -> (* S_Meta_pattern *) s_meta_t.A(serialize_typ t, serialize_list serialize_arg l)
    | Meta_named(t, lid) -> (* S_Meta_named *) s_meta_t.B(serialize_typ t, serialize_lident lid)
    | Meta_labeled(t, s, b) -> (* S_Meta_labeled *) s_meta_t.C(serialize_typ t, s, b)
    | _ -> raise (Err "unimplemented meta_t")

and serialize_arg (ast : arg) : s_arg = (serialize_either serialize_typ serialize_exp (fst ast), (snd ast))

and serialize_args (ast : args) : s_args = serialize_list serialize_arg ast

and serialize_binder (ast : binder) : s_binder = (serialize_either serialize_btvar serialize_bvvar (fst ast), (snd ast))

and serialize_binders (ast : binders) : s_binders = serialize_list serialize_binder ast

and serialize_typ (ast : typ) : s_typ = serialize_syntax serialize_typ' (Util.compress_typ ast) 

and serialize_comp_typ (ast : comp_typ) : s_comp_typ = 
    { en = serialize_lident ast.effect_name
      rt = serialize_typ ast.result_typ
      ea = serialize_args ast.effect_args
      fs = serialize_list serialize_cflags ast.flags }

and serialize_comp' (ast : comp') : s_comp' = 
    match ast with
    | Total(t) -> (* S_Total *) s_comp'.A(serialize_typ t)
    | Comp(c) -> (* S_Comp *) s_comp'.B(serialize_comp_typ c)

and serialize_comp (ast : comp) : s_comp = serialize_syntax serialize_comp' ast

and serialize_cflags (ast : cflags) : s_cflags = 
    match ast with
    | TOTAL -> (* S_TOTAL *) s_cflags.A
    | MLEFFECT -> (* S_MLEFFECT *) s_cflags.B
    | RETURN -> (* S_RETURN *) s_cflags.C
    | PARTIAL_RETURN -> (* S_PARTIAL_RETURN *) s_cflags.D
    | SOMETRIVIAL -> (* S_SOMETRIVIAL *) s_cflags.E
    | LEMMA -> (* S_LEMMA *) s_cflags.F
    | DECREASES e -> (* S_DECREASES *) s_cflags.G(serialize_exp e)

and serialize_exp' (ast : exp') : s_exp' = 
    match ast with
    | Exp_bvar(v) -> (* S_Exp_bvar *) s_exp'.A(serialize_bvvar v)
    | Exp_fvar(v, b) -> (* S_Exp_fvar *) s_exp'.B(serialize_fvvar v, b)
    | Exp_constant(c) -> (* S_Exp_constant *) s_exp'.C(serialize_sconst c)
    | Exp_abs(bs, e) -> (* S_Exp_abs *) s_exp'.D(serialize_binders bs, serialize_exp e)
    | Exp_app(e, ars) -> (* S_Exp_app *) s_exp'.E(serialize_exp e, serialize_args ars)
    | Exp_match(e, l) -> 
        let g eopt = 
            match eopt with
            | Some(e1) -> Some(serialize_exp e1)
            | None -> None
        
        let f (p, eopt, e) = (serialize_pat p, g eopt, serialize_exp e) in
        (* S_Exp_match *) s_exp'.F(serialize_exp e, serialize_list f l)
    | Exp_ascribed(e, t) -> (* S_Exp_ascribed *) s_exp'.G(serialize_exp e, serialize_typ t)
    | Exp_let(lbs, e) -> (* S_Exp_let *) s_exp'.H(serialize_letbindings lbs, serialize_exp e)
    | Exp_meta(m) -> (* S_Exp_meta *) s_exp'.I(serialize_meta_e m)
    | _ -> raise (Err "unimplemented exp'")

and serialize_meta_e (ast : meta_e) : s_meta_e = 
    match ast with
    | Meta_desugared(e, s) -> (* S_Meta_desugared *) s_meta_e.A(serialize_exp e, serialize_meta_source_info s)
   
and serialize_meta_source_info (ast : meta_source_info) : s_meta_source_info = 
    match ast with
    | Data_app -> (* S_Data_app *) s_meta_source_info.A
    | Sequence -> (* S_Sequence *) s_meta_source_info.B
    | Primop -> (* S_Primop *) s_meta_source_info.C
    | MaskedEffect -> (* S_MaskedEffect *) s_meta_source_info.D

and serialize_exp (ast : exp) : s_exp = serialize_syntax serialize_exp' (Util.compress_exp ast)

and serialize_btvdef (ast : btvdef) : s_btvdef = serialize_bvdef ast

and serialize_bvvdef (ast : bvvdef) : s_bvvdef = serialize_bvdef ast

and serialize_pat' (ast : pat') : s_pat' = 
    match ast with
    | Pat_disj(l) -> (* S_Pat_disj *) s_pat'.A(serialize_list serialize_pat l)
    | Pat_constant(c) -> (* S_Pat_constant *) s_pat'.B(serialize_sconst c)
    | Pat_cons(v, l) -> (* S_Pat_cons *) s_pat'.C(serialize_fvvar v, serialize_list serialize_pat l)
    | Pat_var(v, b) -> (* S_Pat_var *) s_pat'.D(serialize_bvvar v, b)
    | Pat_tvar(v) -> (* S_Pat_tvar *) s_pat'.E(serialize_btvar v)
    | Pat_wild(v) -> (* S_Pat_wild *) s_pat'.F(serialize_bvvar v)
    | Pat_twild(v) -> (* S_Pat_tvar *) s_pat'.G(serialize_btvar v)
    | Pat_dot_term(v, e) -> (* S_Pat_dot_term *) s_pat'.H(serialize_bvvar v, serialize_exp e)
    | Pat_dot_typ(v, t) -> (* S_Pat_dot_typ *) s_pat'.I(serialize_btvar v, serialize_typ t)

and serialize_pat (ast : pat) : s_pat = 
    serialize_withinfo_t serialize_pat' (serialize_either serialize_knd serialize_typ) ast

and serialize_knd' (ast : knd') : s_knd' = 
    match ast with
    | Kind_type -> (* S_Kind_type *) s_knd'.A
    | Kind_effect -> (* S_Kind_effect *) s_knd'.B
    | Kind_abbrev(ka, k) -> (* S_Kind_abbrev *) s_knd'.C(serialize_kabbrev ka, serialize_knd k)
    | Kind_arrow(bs, k) -> (* S_Kind_arrow *) s_knd'.D(serialize_binders bs, serialize_knd k)
    | Kind_lam(bs, k) -> (* S_Kind_lam *) s_knd'.E(serialize_binders bs, serialize_knd k)
    | Kind_unknown -> (* S_Kind_unknown *) s_knd'.F
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

and serialize_fvvar (ast : fvvar) : s_fvvar = serialize_var serialize_typ ast *)

let rec serialize_typ' (writer:Writer) (ast:typ') :unit = 
    match ast with
    | Typ_btvar(v) -> writer.Write('a'); serialize_btvar writer v
    | Typ_const(v) -> writer.Write('b'); serialize_ftvar writer v
    | Typ_fun(bs, c) -> writer.Write('c'); serialize_binders writer bs; serialize_comp writer c
    | Typ_refine(v, t) -> writer.Write('d'); serialize_bvvar writer v; serialize_typ writer t
    | Typ_app(t, ars) ->
        writer.Write('e'); serialize_typ writer t; serialize_args writer ars;
        (match t.n with
        | Typ_lam (_, _) -> print_string "type application node with lam\n"
        | _ -> ())
    | Typ_lam(bs, t) -> writer.Write('f'); serialize_binders writer bs; serialize_typ writer t
    | Typ_ascribed(t, k) -> writer.Write('g'); serialize_typ writer t; serialize_knd writer k
    | Typ_meta(m) -> writer.Write('h'); serialize_meta_t writer m
    | Typ_unknown -> writer.Write('i')
    | Typ_uvar(_, _) -> raise (Err "typ not impl:1")
    | Typ_delayed(_, _) -> raise (Err "typ not impl:2")

and serialize_meta_t (writer:Writer) (ast:meta_t) :unit = 
    match ast with
    | Meta_pattern(t, l) -> writer.Write('a'); serialize_typ writer t; serialize_list writer serialize_arg l
    | Meta_named(t, lid) -> writer.Write('b'); serialize_typ writer t; serialize_lident writer lid
    | Meta_labeled(t, s, b) -> writer.Write('c'); serialize_typ writer t; writer.Write(s); writer.Write(b)
    | _ -> raise (Err "unimplemented meta_t")

and serialize_arg (writer:Writer) (ast:arg) :unit = serialize_either writer serialize_typ serialize_exp (fst ast); writer.Write(snd ast)

and serialize_args (writer:Writer) (ast:args) :unit = serialize_list writer serialize_arg ast

and serialize_binder (writer:Writer) (ast:binder) :unit = serialize_either writer serialize_btvar serialize_bvvar (fst ast); writer.Write(snd ast)

and serialize_binders (writer:Writer) (ast:binders) :unit = serialize_list writer serialize_binder ast

and serialize_typ (writer:Writer) (ast:typ) :unit = serialize_syntax writer serialize_typ' (Util.compress_typ ast)

and serialize_comp_typ (writer:Writer) (ast:comp_typ) :unit =
    serialize_lident writer ast.effect_name;
    serialize_typ writer ast.result_typ;
    serialize_args writer ast.effect_args;
    serialize_list writer serialize_cflags ast.flags

and serialize_comp' (writer:Writer) (ast:comp') :unit = 
    match ast with
    | Total(t) -> writer.Write('a'); serialize_typ writer t
    | Comp(c) -> writer.Write('b'); serialize_comp_typ writer c

and serialize_comp (writer:Writer) (ast:comp) :unit = serialize_syntax writer serialize_comp' ast

and serialize_cflags (writer:Writer) (ast:cflags) :unit = 
    match ast with
    | TOTAL -> writer.Write('a')
    | MLEFFECT -> writer.Write('b')
    | RETURN -> writer.Write('c')
    | PARTIAL_RETURN -> writer.Write('d')
    | SOMETRIVIAL -> writer.Write('e')
    | LEMMA -> writer.Write('f')
    | DECREASES e -> writer.Write('g'); serialize_exp writer e

and serialize_exp' (writer:Writer) (ast:exp') :unit = 
    match ast with
    | Exp_bvar(v) -> writer.Write('a'); serialize_bvvar writer v
    | Exp_fvar(v, b) -> writer.Write('b'); serialize_fvvar writer v; writer.Write(b)
    | Exp_constant(c) -> writer.Write('c'); serialize_sconst writer c
    | Exp_abs(bs, e) -> writer.Write('d'); serialize_binders writer bs; serialize_exp writer e
    | Exp_app(e, ars) -> writer.Write('e'); serialize_exp writer e; serialize_args writer ars
    | Exp_match(e, l) -> 
        let g (writer:Writer) eopt = 
            match eopt with
            | Some(e1) -> writer.Write('a'); serialize_exp writer e1
            | None -> writer.Write('b')
        
        let f writer (p, eopt, e) = serialize_pat writer p; g writer eopt; serialize_exp writer e in
        writer.Write('f'); serialize_exp writer e; serialize_list writer f l
    | Exp_ascribed(e, t) -> writer.Write('g'); serialize_exp writer e; serialize_typ writer t
    | Exp_let(lbs, e) -> writer.Write('h'); serialize_letbindings writer lbs; serialize_exp writer e
    | Exp_meta(m) -> writer.Write('i'); serialize_meta_e writer m
    | _ -> raise (Err "unimplemented exp'")

and serialize_meta_e (writer:Writer) (ast:meta_e) :unit = 
    match ast with
    | Meta_desugared(e, s) -> writer.Write('a'); serialize_exp writer  e; serialize_meta_source_info writer s
   
and serialize_meta_source_info (writer:Writer) (ast:meta_source_info) :unit = 
    match ast with
    | Data_app -> writer.Write('a')
    | Sequence -> writer.Write('b')
    | Primop -> writer.Write('c')
    | MaskedEffect -> writer.Write('d')

and serialize_exp (writer:Writer) (ast:exp) :unit = serialize_syntax writer serialize_exp' (Util.compress_exp ast)

and serialize_btvdef (writer:Writer) (ast:btvdef) :unit = serialize_bvdef writer ast

and serialize_bvvdef (writer:Writer) (ast:bvvdef) :unit = serialize_bvdef writer ast

and serialize_pat' (writer:Writer) (ast:pat') :unit = 
    match ast with
    | Pat_disj(l) -> writer.Write('a'); serialize_list writer serialize_pat l
    | Pat_constant(c) -> writer.Write('b'); serialize_sconst writer c
    | Pat_cons(v, l) -> writer.Write('c'); serialize_fvvar writer v; serialize_list writer serialize_pat l
    | Pat_var(v, b) -> writer.Write('d'); serialize_bvvar writer v; writer.Write(b)
    | Pat_tvar(v) -> writer.Write('e'); serialize_btvar writer v
    | Pat_wild(v) -> writer.Write('f');  serialize_bvvar writer v
    | Pat_twild(v) -> writer.Write('g');  serialize_btvar writer v
    | Pat_dot_term(v, e) -> writer.Write('h'); serialize_bvvar writer v; serialize_exp writer e
    | Pat_dot_typ(v, t) -> writer.Write('i'); serialize_btvar writer v; serialize_typ writer t

and serialize_pat (writer:Writer) (ast:pat) :unit = 
    serialize_withinfo_t writer serialize_pat' (fun w kt -> () (* serialize_either w serialize_knd serialize_typ kt*)) ast

and serialize_knd' (writer:Writer) (ast:knd') :unit = 
    match ast with
    | Kind_type -> writer.Write('a')
    | Kind_effect -> writer.Write('b')
    | Kind_abbrev(ka, k) -> writer.Write('c'); serialize_kabbrev writer ka; serialize_knd writer k
    | Kind_arrow(bs, k) -> writer.Write('d'); serialize_binders writer bs; serialize_knd writer k
    | Kind_lam(bs, k) -> writer.Write('e'); serialize_binders writer bs; serialize_knd writer k
    | Kind_unknown -> writer.Write('f')
    | Kind_uvar(uv, args) -> raise (Err "knd' serialization unimplemented:1")
    | Kind_delayed(_, _, _) -> raise (Err "knd' serialization unimplemented:2")

and serialize_knd (writer:Writer) (ast:knd) :unit = serialize_syntax writer serialize_knd' (Util.compress_kind ast)

and serialize_kabbrev (writer:Writer) (ast:kabbrev) :unit = serialize_lident writer (fst ast); serialize_args writer (snd ast)

and serialize_lbname (writer:Writer) (ast:lbname) :unit = serialize_either writer serialize_bvvdef serialize_lident ast

and serialize_letbindings (writer:Writer) (ast:letbindings) :unit = 
    let f writer (n, t, e) = serialize_lbname writer n; serialize_typ writer t; serialize_exp writer e
    writer.Write(fst ast); serialize_list writer f (snd ast)

and serialize_fvar (writer:Writer) (ast:fvar) :unit = serialize_either writer serialize_btvdef serialize_bvvdef ast

and serialize_btvar (writer:Writer) (ast:btvar) :unit = serialize_bvar writer serialize_knd ast

and serialize_bvvar (writer:Writer) (ast:bvvar) :unit = serialize_bvar writer serialize_typ ast

and serialize_ftvar (writer:Writer) (ast:ftvar) :unit = serialize_var writer serialize_knd ast

and serialize_fvvar (writer:Writer) (ast:fvvar) :unit = serialize_var writer serialize_typ ast

(* let rec deserialize_typ' (ast : s_typ') : typ' =  *)
(*     match ast with *)
(*     | (\* S_Typ_btvar *\) s_typ'.A(v) -> Typ_btvar(deserialize_btvar v) *)
(*     | (\* S_Typ_const *\) s_typ'.B(v) -> Typ_const(deserialize_ftvar v) *)
(*     | (\* S_Typ_fun *\) s_typ'.C(bs, c) -> Typ_fun(deserialize_binders bs, deserialize_comp c) *)
(*     | (\* S_Typ_refine *\) s_typ'.D(v, t) -> Typ_refine(deserialize_bvvar v, deserialize_typ t) *)
(*     | (\* S_Typ_app *\) s_typ'.E(t, ars) -> Typ_app(deserialize_typ t, deserialize_args ars) *)
(*     | (\* S_Typ_lam *\) s_typ'.F(bs, t) -> Typ_lam(deserialize_binders bs, deserialize_typ t) *)
(*     | (\* S_Typ_ascribed *\) s_typ'.G(t, k) -> Typ_ascribed(deserialize_typ t, deserialize_knd k) *)
(*     | (\* S_Typ_meta *\) s_typ'.H(m) -> Typ_meta(deserialize_meta_t m) *)
(*     | (\* S_Typ_unknown *\) s_typ'.I -> Typ_unknown *)

(* and deserialize_meta_t (ast : s_meta_t) : meta_t =  *)
(*     match ast with *)
(*     | (\* S_Meta_pattern *\) s_meta_t.A(t, l) -> Meta_pattern(deserialize_typ t, deserialize_list deserialize_arg l) *)
(*     | (\* S_Meta_named *\) s_meta_t.B(t, lid) -> Meta_named(deserialize_typ t, deserialize_lident lid) *)
(*     | (\* S_Meta_labeled *\) s_meta_t.C(t, s, b) -> Meta_labeled(deserialize_typ t, s, b) *)

(* and deserialize_arg (ast : s_arg) : arg = (deserialize_either deserialize_typ deserialize_exp (fst ast), (snd ast)) *)

(* and deserialize_args (ast : s_args) : args = deserialize_list deserialize_arg ast *)

(* and deserialize_binder (ast : s_binder) : binder =  *)
(*     (deserialize_either deserialize_btvar deserialize_bvvar (fst ast), (snd ast)) *)

(* and deserialize_binders (ast : s_binders) : binders = deserialize_list deserialize_binder ast *)

(* and deserialize_typ (ast : s_typ) : typ = deserialize_syntax deserialize_typ' mk_Kind_unknown ast *)

(* and deserialize_comp_typ (ast : s_comp_typ) : comp_typ =  *)
(*     { effect_name = deserialize_lident ast.en *)
(*       result_typ = deserialize_typ ast.rt *)
(*       effect_args = deserialize_args ast.ea *)
(*       flags = deserialize_list deserialize_cflags ast.fs } *)

(* and deserialize_comp' (ast : s_comp') : comp' =  *)
(*     match ast with *)
(*     | (\* S_Total *\) s_comp'.A(t) -> Total(deserialize_typ t) *)
(*     | (\* S_Comp *\) s_comp'.B(c) -> Comp(deserialize_comp_typ c) *)

(* and deserialize_comp (ast : s_comp) : comp = deserialize_syntax deserialize_comp' () ast *)

(* and deserialize_cflags (ast : s_cflags) : cflags =  *)
(*     match ast with *)
(*     | (\* S_TOTAL *\) s_cflags.A -> TOTAL *)
(*     | (\* S_MLEFFECT *\) s_cflags.B -> MLEFFECT *)
(*     | (\* S_RETURN *\) s_cflags.C -> RETURN *)
(*     | (\* S_PARTIAL_RETURN *\) s_cflags.D -> PARTIAL_RETURN *)
(*     | (\* S_SOMETRIVIAL *\) s_cflags.E -> SOMETRIVIAL *)
(*     | (\* S_LEMMA *\) s_cflags.F -> LEMMA *)
(*     | (\* S_DECREASES *\) s_cflags.G e-> DECREASES(deserialize_exp e) *)

(* and deserialize_exp' (ast : s_exp') : exp' =  *)
(*     match ast with *)
(*     | (\* S_Exp_bvar *\) s_exp'.A(v) -> Exp_bvar(deserialize_bvvar v) *)
(*     | (\* S_Exp_fvar *\) s_exp'.B(v, b) -> Exp_fvar(deserialize_fvvar v, b) *)
(*     | (\* S_Exp_constant *\) s_exp'.C(c) -> Exp_constant(deserialize_sconst c) *)
(*     | (\* S_Exp_abs *\) s_exp'.D(bs, e) -> Exp_abs(deserialize_binders bs, deserialize_exp e) *)
(*     | (\* S_Exp_app *\) s_exp'.E(e, ars) -> Exp_app(deserialize_exp e, deserialize_args ars) *)
(*     | (\* S_Exp_match *\) s_exp'.F(e, l) ->  *)
(*         let g eopt =  *)
(*             match eopt with *)
(*             | Some(e1) -> Some(deserialize_exp e1) *)
(*             | None -> None *)
        
(*         let f (p, eopt, e) = (deserialize_pat p, g eopt, deserialize_exp e) *)
(*         Exp_match(deserialize_exp e, deserialize_list f l) *)
(*     | (\* S_Exp_ascribed *\) s_exp'.G(e, t) -> Exp_ascribed(deserialize_exp e, deserialize_typ t) *)
(*     | (\* S_Exp_let *\) s_exp'.H(lbs, e) -> Exp_let(deserialize_letbindings lbs, deserialize_exp e) *)
(*     | (\* S_Exp_meta *\) s_exp'.I(m) -> Exp_meta(deserialize_meta_e m) *)

(* and deserialize_meta_e (ast : s_meta_e) : meta_e =  *)
(*     match ast with *)
(*     | (\* S_Meta_desugared *\) s_meta_e.A(e, s) -> Meta_desugared(deserialize_exp e, deserialize_meta_source_info s) *)
  
(* and deserialize_meta_source_info (ast : s_meta_source_info) : meta_source_info =  *)
(*     match ast with *)
(*     | (\* S_Data_app *\) s_meta_source_info.A -> Data_app *)
(*     | (\* S_Sequence *\) s_meta_source_info.B -> Sequence *)
(*     | (\* S_Primop *\) s_meta_source_info.C -> Primop *)
(*     | (\* S_MaskedEffect *\) s_meta_source_info.D  -> MaskedEffect *)

(* and deserialize_exp (ast : s_exp) : exp = deserialize_syntax deserialize_exp' mk_Typ_unknown ast *)

(* and deserialize_btvdef (ast : s_btvdef) : btvdef = deserialize_bvdef ast *)

(* and deserialize_bvvdef (ast : s_bvvdef) : bvvdef = deserialize_bvdef ast *)

(* and deserialize_pat' (ast : s_pat') : pat' =  *)
(*     match ast with *)
(*     | (\* S_Pat_disj *\) s_pat'.A(l) -> Pat_disj(deserialize_list deserialize_pat l) *)
(*     | (\* S_Pat_constant *\) s_pat'.B(c) -> Pat_constant(deserialize_sconst c) *)
(*     | (\* S_Pat_cons *\) s_pat'.C(v, l) -> Pat_cons(deserialize_fvvar v, deserialize_list deserialize_pat l) *)
(*     | (\* S_Pat_var *\) s_pat'.D(v, b) -> Pat_var(deserialize_bvvar v, b) *)
(*     | (\* S_Pat_tvar *\) s_pat'.E(v) -> Pat_tvar(deserialize_btvar v) *)
(*     | (\* S_Pat_wild *\) s_pat'.F(v) -> Pat_wild(deserialize_bvvar v) *)
(*     | (\* S_Pat_twild *\) s_pat'.G(v) -> Pat_tvar(deserialize_btvar v) *)
(*     | (\* S_Pat_dot_term *\) s_pat'.H(v, e) -> Pat_dot_term(deserialize_bvvar v, deserialize_exp e) *)
(*     | (\* S_Pat_dot_typ *\) s_pat'.I(v, t) -> Pat_dot_typ(deserialize_btvar v, deserialize_typ t) *)

(* and deserialize_pat (ast : s_pat) : pat =  *)
(*     deserialize_withinfo_t deserialize_pat' (deserialize_either deserialize_knd deserialize_typ) ast *)

(* and deserialize_knd' (ast : s_knd') : knd' =  *)
(*     match ast with *)
(*     | (\* S_Kind_type *\) s_knd'.A -> Kind_type *)
(*     | (\* S_Kind_effect *\) s_knd'.B -> Kind_effect *)
(*     | (\* S_Kind_abbrev *\) s_knd'.C(ka, k) -> Kind_abbrev(deserialize_kabbrev ka, deserialize_knd k) *)
(*     | (\* S_Kind_arrow *\) s_knd'.D(bs, k) -> Kind_arrow(deserialize_binders bs, deserialize_knd k) *)
(*     | (\* S_Kind_lam *\) s_knd'.E(bs, k) -> Kind_lam(deserialize_binders bs, deserialize_knd k) *)
(*     | (\* S_Kind_unknown *\) s_knd'.F -> Kind_unknown *)

(* and deserialize_knd (ast : s_knd) : knd = deserialize_syntax deserialize_knd' () ast *)

(* and deserialize_kabbrev (ast : s_kabbrev) : kabbrev = (deserialize_lident (fst ast), deserialize_args (snd ast)) *)

(* and deserialize_lbname (ast : s_lbname) : lbname = deserialize_either deserialize_bvvdef deserialize_lident ast *)

(* and deserialize_letbindings (ast : s_letbindings) : letbindings =  *)
(*     let f (n, t, e) = (deserialize_lbname n, deserialize_typ t, deserialize_exp e) *)
(*     (fst ast, deserialize_list f (snd ast)) *)

(* and deserialize_fvar (ast : s_fvar) : fvar = deserialize_either deserialize_btvdef deserialize_bvvdef ast *)

(* and deserialize_btvar (ast : s_btvar) : btvar = deserialize_bvar deserialize_knd ast *)

(* and deserialize_bvvar (ast : s_bvvar) : bvvar = deserialize_bvar deserialize_typ ast *)

(* and deserialize_ftvar (ast : s_ftvar) : ftvar = deserialize_var deserialize_knd ast *)

(* and deserialize_fvvar (ast : s_fvvar) : fvvar = deserialize_var deserialize_typ ast *)

let rec deserialize_typ' (reader:Reader) :typ' = 
    match (reader.ReadChar()) with
    | 'a' -> Typ_btvar(deserialize_btvar reader)
    | 'b' -> Typ_const(deserialize_ftvar reader)
    | 'c' -> Typ_fun(deserialize_binders reader, deserialize_comp reader)
    | 'd' -> Typ_refine(deserialize_bvvar reader, deserialize_typ reader)
    | 'e' -> Typ_app(deserialize_typ reader, deserialize_args reader)
    | 'f' -> Typ_lam(deserialize_binders reader, deserialize_typ reader)
    | 'g' -> Typ_ascribed(deserialize_typ reader, deserialize_knd reader)
    | 'h' -> Typ_meta(deserialize_meta_t reader)
    | 'i' -> Typ_unknown

and deserialize_meta_t (reader:Reader) :meta_t = 
    match (reader.ReadChar()) with
    | 'a' -> Meta_pattern(deserialize_typ reader, deserialize_list reader deserialize_arg)
    | 'b' -> Meta_named(deserialize_typ reader, deserialize_lident reader)
    | 'c' -> Meta_labeled(deserialize_typ reader, reader.ReadString(), reader.ReadBoolean())

and deserialize_arg (reader:Reader) :arg = (deserialize_either reader deserialize_typ deserialize_exp, reader.ReadBoolean())

and deserialize_args (reader:Reader) :args = deserialize_list reader deserialize_arg

and deserialize_binder (reader:Reader) :binder = 
    (deserialize_either reader deserialize_btvar deserialize_bvvar, reader.ReadBoolean())

and deserialize_binders (reader:Reader) :binders = deserialize_list reader deserialize_binder

and deserialize_typ (reader:Reader) :typ = deserialize_syntax reader deserialize_typ' mk_Kind_unknown

and deserialize_comp_typ (reader:Reader) :comp_typ = 
    { effect_name = deserialize_lident reader
      result_typ = deserialize_typ reader
      effect_args = deserialize_args reader
      flags = deserialize_list reader deserialize_cflags }

and deserialize_comp' (reader:Reader) :comp' = 
    match (reader.ReadChar()) with
    | 'a' -> Total(deserialize_typ reader)
    | 'b' -> Comp(deserialize_comp_typ reader)

and deserialize_comp (reader:Reader) :comp = deserialize_syntax reader deserialize_comp' ()

and deserialize_cflags (reader:Reader) :cflags = 
    match (reader.ReadChar()) with
    | 'a' -> TOTAL
    | 'b' -> MLEFFECT
    | 'c' -> RETURN
    | 'd' -> PARTIAL_RETURN
    | 'e' -> SOMETRIVIAL
    | 'f' -> LEMMA
    | 'g' -> DECREASES(deserialize_exp reader)

and deserialize_exp' (reader:Reader) :exp' = 
    match (reader.ReadChar()) with
    | 'a' -> Exp_bvar(deserialize_bvvar reader)
    | 'b' -> Exp_fvar(deserialize_fvvar reader, reader.ReadBoolean())
    | 'c' -> Exp_constant(deserialize_sconst reader)
    | 'd' -> Exp_abs(deserialize_binders reader, deserialize_exp reader)
    | 'e' -> Exp_app(deserialize_exp reader, deserialize_args reader)
    | 'f' ->
        let g (reader:Reader) =
            match (reader.ReadChar()) with
            | 'a' -> Some(deserialize_exp reader)
            | 'b' -> None
        
        let f reader = (deserialize_pat reader, g reader, deserialize_exp reader) in
        Exp_match(deserialize_exp reader, deserialize_list reader f)
    | 'g' -> Exp_ascribed(deserialize_exp reader, deserialize_typ reader)
    | 'h' -> Exp_let(deserialize_letbindings reader, deserialize_exp reader)
    | 'i' -> Exp_meta(deserialize_meta_e reader)

and deserialize_meta_e (reader:Reader) :meta_e =
    match (reader.ReadChar()) with
    | 'a' -> Meta_desugared(deserialize_exp reader, deserialize_meta_source_info reader)
  
and deserialize_meta_source_info (reader:Reader) :meta_source_info =
    match (reader.ReadChar()) with
    | 'a' -> Data_app
    | 'b' -> Sequence
    | 'c' -> Primop
    | 'd' -> MaskedEffect

and deserialize_exp (reader:Reader) :exp = deserialize_syntax reader deserialize_exp' mk_Typ_unknown

and deserialize_btvdef (reader:Reader) :btvdef = deserialize_bvdef reader

and deserialize_bvvdef (reader:Reader) :bvvdef = deserialize_bvdef reader

and deserialize_pat' (reader:Reader) :pat' = 
    match (reader.ReadChar()) with
    | 'a' -> Pat_disj(deserialize_list reader deserialize_pat)
    | 'b' -> Pat_constant(deserialize_sconst reader)
    | 'c' -> Pat_cons(deserialize_fvvar reader, deserialize_list reader deserialize_pat)
    | 'd' -> Pat_var(deserialize_bvvar reader, reader.ReadBoolean())
    | 'e' -> Pat_tvar(deserialize_btvar reader)
    | 'f' -> Pat_wild(deserialize_bvvar reader)
    | 'g' -> Pat_tvar(deserialize_btvar reader)
    | 'h' -> Pat_dot_term(deserialize_bvvar reader, deserialize_exp reader)
    | 'i' -> Pat_dot_typ(deserialize_btvar reader, deserialize_typ reader)

and deserialize_pat (reader:Reader) :pat = 
    deserialize_withinfo_t reader deserialize_pat' (fun r -> None)// deserialize_either r deserialize_knd deserialize_typ)

and deserialize_knd' (reader:Reader) :knd' = 
    match (reader.ReadChar()) with
    | 'a' -> Kind_type
    | 'b' -> Kind_effect
    | 'c' -> Kind_abbrev(deserialize_kabbrev reader, deserialize_knd reader)
    | 'd' -> Kind_arrow(deserialize_binders reader, deserialize_knd reader)
    | 'e' -> Kind_lam(deserialize_binders reader, deserialize_knd reader)
    | 'f' -> Kind_unknown

and deserialize_knd (reader:Reader) :knd = deserialize_syntax reader deserialize_knd' ()

and deserialize_kabbrev (reader:Reader) :kabbrev = (deserialize_lident reader, deserialize_args reader)

and deserialize_lbname (reader:Reader) :lbname = deserialize_either reader deserialize_bvvdef deserialize_lident

and deserialize_letbindings (reader:Reader) :letbindings = 
    let f reader = (deserialize_lbname reader, deserialize_typ reader, deserialize_exp reader) in
    (reader.ReadBoolean(), deserialize_list reader f)

and deserialize_fvar (reader:Reader) :fvar = deserialize_either reader deserialize_btvdef deserialize_bvvdef

and deserialize_btvar (reader:Reader) :btvar = deserialize_bvar reader deserialize_knd

and deserialize_bvvar (reader:Reader) :bvvar = deserialize_bvar reader deserialize_typ

and deserialize_ftvar (reader:Reader) :ftvar = deserialize_var reader deserialize_knd

and deserialize_fvvar (reader:Reader) :fvvar = deserialize_var reader deserialize_typ

(*type s_formula = s_typ

let serialize_formula (ast : formula) : s_formula = serialize_typ ast
let deserialize_formula (ast : s_formula) : formula = deserialize_typ ast*)

let serialize_formula = serialize_typ
let deserialize_formula = deserialize_typ

(* [<KnownType("KnownTypes")>] *)
(* type s_qualifier =  *)
(*     | (\* S_Private *\) A *)
(*     | (\* S_Public *\) B *)
(*     | (\* S_Assumption *\) C *)
(*     | (\* S_Definition *\) D *)
(*     | (\* S_Query *\) E *)
(*     | (\* S_Lemma *\) F *)
(*     | (\* S_Logic *\) G *)
(*     | (\* S_Opaque *\) H *)
(*     | (\* S_Discriminator *\) I of s_lident *)
(*     | (\* S_Projector *\) J of s_lident * s_either<s_btvdef, s_bvvdef> *)
(*     | (\* S_RecordType *\) K of array<s_ident> *)
(*     | (\* S_RecordConstructor *\) L of array<s_ident> *)
(*     | (\* S_ExceptionConstructor *\) M *)
(*     | (\* S_Effect *\) N *)
(*     static member KnownTypes() =  *)
(*         typeof<s_qualifier>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic)  *)
(*         |> Array.filter FSharpType.IsUnion *)

(* let serialize_qualifier (ast : qualifier) : s_qualifier =  *)
(*     match ast with *)
(*     | Private -> (\* S_Private *\) s_qualifier.A *)
(*     | Public -> (\* S_Public *\) s_qualifier.B *)
(*     | Assumption -> (\* S_Assumption *\) s_qualifier.C *)
(*     | Definition -> (\* S_Definition *\) s_qualifier.D *)
(*     | Query -> (\* S_Query *\) s_qualifier.E *)
(*     | Lemma -> (\* S_Lemma *\) s_qualifier.F *)
(*     | Logic -> (\* S_Logic *\) s_qualifier.G *)
(*     | Opaque -> (\* S_Opaque *\) s_qualifier.H *)
(*     | Discriminator(lid) -> (\* S_Discriminator *\) s_qualifier.I(serialize_lident lid) *)
(*     | Projector(lid, v) -> (\* S_Projector *\) s_qualifier.J(serialize_lident lid, serialize_either serialize_btvdef serialize_bvvdef v) *)
(*     | RecordType(l) -> (\* S_RecordType *\) s_qualifier.K(serialize_list serialize_ident l) *)
(*     | RecordConstructor(l) -> (\* S_RecordConstructor *\) s_qualifier.L(serialize_list serialize_ident l) *)
(*     | ExceptionConstructor -> (\* S_ExceptionConstructor *\) s_qualifier.M *)
(*     | Effect -> (\* S_Effect *\) s_qualifier.N *)

(* let deserialize_qualifier (ast : s_qualifier) : qualifier =  *)
(*     match ast with *)
(*     | (\* S_Private *\) s_qualifier.A -> Private *)
(*     | (\* S_Public *\)s_qualifier.B -> Public *)
(*     | (\* S_Assumption *\) s_qualifier.C -> Assumption *)
(*     | (\* S_Definition *\) s_qualifier.D -> Definition *)
(*     | (\* S_Query *\) s_qualifier.E -> Query *)
(*     | (\* S_Lemma *\) s_qualifier.F -> Lemma *)
(*     | (\* S_Logic *\) s_qualifier.G -> Logic *)
(*     | (\* S_Opaque *\) s_qualifier.H -> Opaque *)
(*     | (\* S_Discriminator *\) s_qualifier.I(lid) -> Discriminator(deserialize_lident lid) *)
(*     | (\* S_Projector *\) s_qualifier.J(lid, v) ->  *)
(*         Projector(deserialize_lident lid, deserialize_either deserialize_btvdef deserialize_bvvdef v) *)
(*     | (\* S_RecordType *\) s_qualifier.K(l) -> RecordType(deserialize_list deserialize_ident l) *)
(*     | (\* S_RecordConstructor *\) s_qualifier.L(l) -> RecordConstructor(deserialize_list deserialize_ident l) *)
(*     | (\* S_ExceptionConstructor *\) s_qualifier.M -> ExceptionConstructor *)
(*     | (\* S_Effect *\) s_qualifier.N -> Effect *)

let serialize_qualifier (writer:Writer)(ast:qualifier) :unit =
    match ast with
    | Private -> writer.Write('a')
    | Public -> writer.Write('b')
    | Assumption -> writer.Write('c')
    | Definition -> writer.Write('d')
    | Query -> writer.Write('e')
    | Lemma -> writer.Write('f')
    | Logic -> writer.Write('g')
    | Opaque -> writer.Write('h')
    | Discriminator(lid) -> writer.Write('i'); serialize_lident writer lid
    | Projector(lid, v) -> writer.Write('j'); serialize_lident writer lid; serialize_either writer serialize_btvdef serialize_bvvdef v
    | RecordType(l) -> writer.Write('k'); serialize_list writer serialize_ident l
    | RecordConstructor(l) -> writer.Write('l'); serialize_list writer serialize_ident l
    | ExceptionConstructor -> writer.Write('m')
    | Effect -> writer.Write('n')

let deserialize_qualifier (reader:Reader) :qualifier =
    match (reader.ReadChar()) with
    | 'a' -> Private
    | 'b' -> Public
    | 'c' -> Assumption
    | 'd' -> Definition
    | 'e' -> Query
    | 'f' -> Lemma
    | 'g' -> Logic
    | 'h' -> Opaque
    | 'i' -> Discriminator(deserialize_lident reader)
    | 'j' -> Projector(deserialize_lident reader, deserialize_either reader deserialize_btvdef deserialize_bvvdef)
    | 'k' -> RecordType(deserialize_list reader deserialize_ident)
    | 'l' -> RecordConstructor(deserialize_list reader deserialize_ident)
    | 'm' -> ExceptionConstructor
    | 'n' -> Effect

(*type s_tycon = s_lident * s_binders * s_knd
let serialize_tycon ((lid, bs, k): tycon) :s_tycon = (serialize_lident lid, serialize_binders bs, serialize_knd k)
let deserialize_tycon ((lid, bs, k):s_tycon) :tycon = (deserialize_lident lid, deserialize_binders bs, deserialize_knd k)*)

let serialize_tycon (writer:Writer) ((lid, bs, k): tycon) :unit = serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k
let deserialize_tycon (reader:Reader) :tycon = (deserialize_lident reader, deserialize_binders reader, deserialize_knd reader)

(*type s_monad_abbrev = 
    { m : s_lident (* mabbrev *)
      p : s_binders (* parms *)
      d : s_typ (* def *)}

let serialize_monad_abbrev (ast : monad_abbrev) : s_monad_abbrev = 
    { m = serialize_lident ast.mabbrev
      p = serialize_binders ast.parms
      d = serialize_typ ast.def }

let deserialize_monad_abbrev (ast : s_monad_abbrev) : monad_abbrev = 
    { mabbrev = deserialize_lident ast.m
      parms = deserialize_binders ast.p
      def = deserialize_typ ast.d }*)

let serialize_monad_abbrev (writer:Writer) (ast : monad_abbrev) :unit = 
    serialize_lident writer ast.mabbrev;
    serialize_binders writer ast.parms;
    serialize_typ writer ast.def

let deserialize_monad_abbrev (reader:Reader) :monad_abbrev = 
    { mabbrev = deserialize_lident reader
      parms = deserialize_binders reader
      def = deserialize_typ reader }

(*type s_monad_order = 
    { s : s_lident (* source *)
      t : s_lident (* target *)
      l : s_typ (* lift *) }

let serialize_monad_order (ast : monad_order) : s_monad_order = 
    { s = serialize_lident ast.source
      t = serialize_lident ast.target
      l = serialize_typ ast.lift }

let deserialize_monad_order (ast : s_monad_order) : monad_order = 
    { source = deserialize_lident ast.s
      target = deserialize_lident ast.t
      lift = deserialize_typ ast.l }*)

let serialize_monad_order (writer:Writer) (ast:monad_order) :unit =
    serialize_lident writer ast.source;
    serialize_lident writer ast.target;
    serialize_typ writer ast.lift

let deserialize_monad_order (reader:Reader) :monad_order = 
    { source = deserialize_lident reader
      target = deserialize_lident reader
      lift = deserialize_typ reader }

(*type s_monad_lat = array<s_monad_order>

let serialize_monad_lat (ast : monad_lat) : s_monad_lat = serialize_list serialize_monad_order ast
let deserialize_monad_lat (ast : s_monad_lat) : monad_lat = deserialize_list deserialize_monad_order ast*)

let serialize_monad_lat (writer:Writer) (ast:monad_lat) :unit = serialize_list writer serialize_monad_order ast
let deserialize_monad_lat (reader:Reader) :monad_lat = deserialize_list reader deserialize_monad_order

(* type s_monad_decl =  *)
(*     { mname : s_lident *)
(*       total : bool *)
(*       signature : s_knd *)
(*       ret : s_typ *)
(*       bind_wp : s_typ *)
(*       bind_wlp : s_typ *)
(*       if_then_else : s_typ *)
(*       ite_wp : s_typ *)
(*       ite_wlp : s_typ *)
(*       wp_binop : s_typ *)
(*       wp_as_type : s_typ *)
(*       close_wp : s_typ *)
(*       close_wp_t : s_typ *)
(*       assert_p : s_typ *)
(*       assume_p : s_typ *)
(*       null_wp : s_typ *)
(*       trivial : s_typ *)
(*       abbrevs : array<s_sigelt> *)
(*       kind_abbrevs: array<s_lident * array<s_either<s_btvdef, s_bvvdef>> * s_knd> *)
(*       default_monad: option<s_lident> } *)

(* and [<KnownType("KnownTypes")>] s_sigelt =  *)
(*     | (\* S_Sig_tycon *\) A of s_lident * s_binders * s_knd * array<s_lident> * array<s_lident> * array<s_qualifier> *)
(*     | (\* S_Sig_typ_abbrev *\) B of s_lident * s_binders * s_knd * s_typ * array<s_qualifier> *)
(*     | (\* S_Sig_datacon *\) C of s_lident * s_typ * s_tycon * array<s_qualifier> *)
(*     | (\* S_Sig_val_decl *\) D of s_lident * s_typ * array<s_qualifier> *)
(*     | (\* S_Sig_assume *\) E of s_lident * s_formula * array<s_qualifier> *)
(*     | (\* S_Sig_let *\) F of s_letbindings * array<s_lident> * bool *)
(*     | (\* S_Sig_main *\) G of s_exp *)
(*     | (\* S_Sig_bundle *\) H of array<s_sigelt> * array<s_lident> *)
(*     | (\* S_Sig_monads *\) I of array<s_monad_decl> * s_monad_lat * array<s_lident> *)
(*     static member KnownTypes() =  *)
(*         typeof<s_sigelt>.GetNestedTypes(BindingFlags.Public ||| BindingFlags.NonPublic)  *)
(*         |> Array.filter FSharpType.IsUnion *)

(* let rec serialize_monad_decl (ast : monad_decl) : s_monad_decl =  *)
(*     { mname = serialize_lident ast.mname *)
(*       total = ast.total *)
(*       signature = serialize_knd ast.signature *)
(*       ret = serialize_typ ast.ret *)
(*       bind_wp = serialize_typ ast.bind_wp *)
(*       bind_wlp = serialize_typ ast.bind_wlp *)
(*       if_then_else = serialize_typ ast.if_then_else *)
(*       ite_wp = serialize_typ ast.ite_wp *)
(*       ite_wlp = serialize_typ ast.ite_wlp *)
(*       wp_binop = serialize_typ ast.wp_binop *)
(*       wp_as_type = serialize_typ ast.wp_as_type *)
(*       close_wp = serialize_typ ast.close_wp *)
(*       close_wp_t = serialize_typ ast.close_wp_t *)
(*       assert_p = serialize_typ ast.assert_p *)
(*       assume_p = serialize_typ ast.assume_p *)
(*       null_wp = serialize_typ ast.null_wp *)
(*       trivial = serialize_typ ast.trivial *)
(*       abbrevs = serialize_list serialize_sigelt ast.abbrevs *)
(*       kind_abbrevs =  *)
(*           serialize_list  *)
(*               (fun (lid, l, k) ->  *)
(*               serialize_lident lid,  *)
(*               serialize_list (fun vdef -> serialize_either serialize_btvdef serialize_bvvdef vdef) l, serialize_knd k)  *)
(*               ast.kind_abbrevs *)
(*       default_monad =  *)
(*           match ast.default_monad with *)
(*           | None -> None *)
(*           | Some(lid) -> Some(serialize_lident lid) } *)

(* and serialize_sigelt (ast : sigelt) : s_sigelt =  *)
(*     match ast with *)
(*     | Sig_tycon(lid, bs, k, l1, l2, qs, _) ->  *)
(*         (\* S_Sig_tycon *\) s_sigelt.A (serialize_lident lid, serialize_binders bs, serialize_knd k, serialize_list serialize_lident l1,  *)
(*                                       serialize_list serialize_lident l2, serialize_list serialize_qualifier qs) *)
(*     | Sig_typ_abbrev(lid, bs, k, t, qs, _) ->  *)
(*         (\* S_Sig_typ_abbrev *\) s_sigelt.B (serialize_lident lid, serialize_binders bs, serialize_knd k, serialize_typ t,  *)
(*                                            serialize_list serialize_qualifier qs) *)
(*     | Sig_datacon(lid1, t, tyc, qs, _) -> *)
(*       let t' = *)
(*         match Util.function_formals t with  *)
(*         | Some (f, c) -> mk_Typ_fun (f, Syntax.mk_Total  (Util.comp_result c)) None dummyRange *)
(*         | None -> t *)
(*       in *)
(*       (\*S_Sig_datacon *\) s_sigelt.C(serialize_lident lid1, serialize_typ t', serialize_tycon tyc, serialize_list serialize_qualifier qs) *)
(*     | Sig_val_decl(lid, t, qs, _) ->  *)
(*         (\* S_Sig_val_decl *\) s_sigelt.D(serialize_lident lid, serialize_typ t, serialize_list serialize_qualifier qs) *)
(*     | Sig_assume(lid, fml, qs, _) ->  *)
(*         (\* S_Sig_assume *\) s_sigelt.E(serialize_lident lid, serialize_formula fml, serialize_list serialize_qualifier qs) *)
(*     | Sig_let(lbs, _, l, b) -> (\* S_Sig_let *\) s_sigelt.F(serialize_letbindings lbs, serialize_list serialize_lident l, b) *)
(*     | Sig_main(e, _) -> (\* S_Sig_main *\) s_sigelt.G(serialize_exp e) *)
(*     | Sig_bundle(l, _, lids) -> (\* S_Sig_bundle *\) s_sigelt.H(serialize_list serialize_sigelt l, serialize_list serialize_lident lids) *)
(*     | Sig_monads(l, lat, _, lids) ->  *)
(*         (\* S_Sig_monads *\) s_sigelt.I(serialize_list serialize_monad_decl l, serialize_monad_lat lat, serialize_list serialize_lident lids) *)

let rec serialize_monad_decl (writer:Writer) (ast:monad_decl) :unit =
    serialize_lident writer ast.mname;
    writer.Write(ast.total);
    serialize_knd writer ast.signature;
    serialize_typ writer ast.ret;
    serialize_typ writer ast.bind_wp;
    serialize_typ writer ast.bind_wlp;
    serialize_typ writer ast.if_then_else;
    serialize_typ writer ast.ite_wp;
    serialize_typ writer ast.ite_wlp;
    serialize_typ writer ast.wp_binop;
    serialize_typ writer ast.wp_as_type;
    serialize_typ writer ast.close_wp;
    serialize_typ writer ast.close_wp_t;
    serialize_typ writer ast.assert_p;
    serialize_typ writer ast.assume_p;
    serialize_typ writer ast.null_wp;
    serialize_typ writer ast.trivial;
    serialize_list writer serialize_sigelt ast.abbrevs;
    (serialize_list writer
              (fun writer (lid, l, k) ->
               serialize_lident writer lid;
               serialize_list writer (fun writer vdef -> serialize_either writer serialize_btvdef serialize_bvvdef vdef) l;
               serialize_knd writer k)
               ast.kind_abbrevs);
    (match ast.default_monad with
     | None -> writer.Write('a')
     | Some(lid) -> writer.Write('b'); serialize_lident writer lid)

and serialize_sigelt (writer:Writer) (ast:sigelt) :unit =
    match ast with
    | Sig_tycon(lid, bs, k, l1, l2, qs, _) ->
        writer.Write('a');
        serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k;
        serialize_list writer serialize_lident l1; serialize_list writer serialize_lident l2;
        serialize_list writer serialize_qualifier qs
    | Sig_typ_abbrev(lid, bs, k, t, qs, _) ->
        writer.Write('b');
        serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k;
        serialize_typ writer t; serialize_list writer serialize_qualifier qs
    | Sig_datacon(lid1, t, tyc, qs, _) ->
      let t' =
        match Util.function_formals t with 
        | Some (f, c) -> mk_Typ_fun (f, Syntax.mk_Total  (Util.comp_result c)) None dummyRange
        | None -> t
      in
      writer.Write('c');
      serialize_lident writer lid1; serialize_typ writer t'; serialize_tycon writer tyc;
      serialize_list writer serialize_qualifier qs
    | Sig_val_decl(lid, t, qs, _) -> 
        writer.Write('d');
        serialize_lident writer lid; serialize_typ writer t; serialize_list writer serialize_qualifier qs
    | Sig_assume(lid, fml, qs, _) ->
        writer.Write('e');
        serialize_lident writer lid; serialize_formula writer fml; serialize_list writer serialize_qualifier qs
    | Sig_let(lbs, _, l, b) ->
        Util.fprint1 (">>>>>>Serializing %s\n") (Print.sigelt_to_string_short ast);
        writer.Write('f');
        serialize_letbindings writer lbs; serialize_list writer serialize_lident l; writer.Write(b)
    | Sig_main(e, _) -> writer.Write('g'); serialize_exp writer e
    | Sig_bundle(l, _, lids) ->
        writer.Write('h');
        serialize_list writer serialize_sigelt l; serialize_list writer serialize_lident lids
    | Sig_monads(l, lat, _, lids) ->
        writer.Write('i');
        serialize_list writer serialize_monad_decl l; serialize_monad_lat writer lat;
        serialize_list writer serialize_lident lids

(* let rec deserialize_monad_decl (ast : s_monad_decl) : monad_decl =  *)
(*     { mname = deserialize_lident ast.mname *)
(*       total = ast.total *)
(*       signature = deserialize_knd ast.signature *)
(*       ret = deserialize_typ ast.ret *)
(*       bind_wp = deserialize_typ ast.bind_wp *)
(*       bind_wlp = deserialize_typ ast.bind_wlp *)
(*       if_then_else = deserialize_typ ast.if_then_else *)
(*       ite_wp = deserialize_typ ast.ite_wp *)
(*       ite_wlp = deserialize_typ ast.ite_wlp *)
(*       wp_binop = deserialize_typ ast.wp_binop *)
(*       wp_as_type = deserialize_typ ast.wp_as_type *)
(*       close_wp = deserialize_typ ast.close_wp *)
(*       close_wp_t = deserialize_typ ast.close_wp_t *)
(*       assert_p = deserialize_typ ast.assert_p *)
(*       assume_p = deserialize_typ ast.assume_p *)
(*       null_wp = deserialize_typ ast.null_wp *)
(*       trivial = deserialize_typ ast.trivial *)
(*       abbrevs = deserialize_list deserialize_sigelt ast.abbrevs *)
(*       kind_abbrevs =  *)
(*           deserialize_list  *)
(*               (fun (lid, l, k) ->  *)
(*               deserialize_lident lid,  *)
(*               deserialize_list (fun vdef -> deserialize_either deserialize_btvdef deserialize_bvvdef vdef) l,  *)
(*               deserialize_knd k) ast.kind_abbrevs *)
(*       default_monad =  *)
(*           match ast.default_monad with *)
(*           | None -> None *)
(*           | Some(lid) -> Some(deserialize_lident lid) } *)


(* and deserialize_sigelt (ast : s_sigelt) : sigelt =  *)
(*     match ast with *)
(*     | (\* S_Sig_tycon *\) s_sigelt.A(lid, bs, k, l1, l2, qs) ->  *)
(*         Sig_tycon *)
(*             (deserialize_lident lid, deserialize_binders bs, deserialize_knd k, deserialize_list deserialize_lident l1,  *)
(*              deserialize_list deserialize_lident l2, deserialize_list deserialize_qualifier qs, dummyRange) *)
(*     | (\* S_Sig_typ_abbrev *\) s_sigelt.B(lid, bs, k, t, qs) ->  *)
(*         Sig_typ_abbrev *)
(*             (deserialize_lident lid, deserialize_binders bs, deserialize_knd k, deserialize_typ t,  *)
(*              deserialize_list deserialize_qualifier qs, dummyRange) *)
(*     | (\* S_Sig_datacon *\) s_sigelt.C(lid1, t, tyc, qs) ->  *)
(*         Sig_datacon *)
(*             (deserialize_lident lid1, deserialize_typ t, deserialize_tycon tyc, deserialize_list deserialize_qualifier qs,  *)
(*              dummyRange) *)
(*     | (\* S_Sig_val_decl *\) s_sigelt.D(lid, t, qs) ->  *)
(*         Sig_val_decl(deserialize_lident lid, deserialize_typ t, deserialize_list deserialize_qualifier qs, dummyRange) *)
(*     | (\* S_Sig_assume *\) s_sigelt.E(lid, fml, qs) ->  *)
(*         Sig_assume(deserialize_lident lid, deserialize_formula fml, deserialize_list deserialize_qualifier qs, dummyRange) *)
(*     | (\* S_Sig_let *\) s_sigelt.F(lbs, l, b) -> Sig_let(deserialize_letbindings lbs, dummyRange, deserialize_list deserialize_lident l, b) *)
(*     | (\* S_Sig_main *\) s_sigelt.G(e) -> Sig_main(deserialize_exp e, dummyRange) *)
(*     | (\* S_Sig_bundle *\) s_sigelt.H(l, lids) -> Sig_bundle(deserialize_list deserialize_sigelt l, dummyRange, deserialize_list deserialize_lident lids) *)
(*     | (\* S_Sig_monads *\) s_sigelt.I(l, lat, lids) ->  *)
(*         Sig_monads *)
(*             (deserialize_list deserialize_monad_decl l, deserialize_monad_lat lat, dummyRange, deserialize_list deserialize_lident lids) *)

let rec deserialize_monad_decl (reader:Reader) :monad_decl =
    { mname = deserialize_lident reader
      total = reader.ReadBoolean()
      signature = deserialize_knd reader
      ret = deserialize_typ reader
      bind_wp = deserialize_typ reader
      bind_wlp = deserialize_typ reader
      if_then_else = deserialize_typ reader
      ite_wp = deserialize_typ reader
      ite_wlp = deserialize_typ reader
      wp_binop = deserialize_typ reader
      wp_as_type = deserialize_typ reader
      close_wp = deserialize_typ reader
      close_wp_t = deserialize_typ reader
      assert_p = deserialize_typ reader
      assume_p = deserialize_typ reader
      null_wp = deserialize_typ reader
      trivial = deserialize_typ reader
      abbrevs = deserialize_list reader deserialize_sigelt
      kind_abbrevs = 
          deserialize_list reader
              (fun reader -> 
               deserialize_lident reader,
               deserialize_list reader (fun reader -> deserialize_either reader deserialize_btvdef deserialize_bvvdef),
               deserialize_knd reader)
      default_monad = 
          match (reader.ReadChar()) with
          | 'a' -> None
          | 'b' -> Some(deserialize_lident reader) }

and deserialize_sigelt (reader:Reader) :sigelt =
    match (reader.ReadChar()) with
    | 'a' ->
        Sig_tycon
            (deserialize_lident reader, deserialize_binders reader, deserialize_knd reader, deserialize_list reader deserialize_lident, 
             deserialize_list reader deserialize_lident, deserialize_list reader deserialize_qualifier, dummyRange)
    | 'b' ->
        Sig_typ_abbrev
            (deserialize_lident reader, deserialize_binders reader, deserialize_knd reader, deserialize_typ reader,
             deserialize_list reader deserialize_qualifier, dummyRange)
    | 'c' -> 
        Sig_datacon
            (deserialize_lident reader, deserialize_typ reader, deserialize_tycon reader, deserialize_list reader deserialize_qualifier, dummyRange)
    | 'd' -> 
        Sig_val_decl(deserialize_lident reader, deserialize_typ reader, deserialize_list reader deserialize_qualifier, dummyRange)
    | 'e' -> 
        Sig_assume(deserialize_lident reader, deserialize_formula reader, deserialize_list reader deserialize_qualifier, dummyRange)
    | 'f' -> Sig_let(deserialize_letbindings reader, dummyRange, deserialize_list reader deserialize_lident, reader.ReadBoolean())
    | 'g' -> Sig_main(deserialize_exp reader, dummyRange)
    | 'h' -> Sig_bundle(deserialize_list reader deserialize_sigelt, dummyRange, deserialize_list reader deserialize_lident)
    | 'i' -> 
        Sig_monads
            (deserialize_list reader deserialize_monad_decl, deserialize_monad_lat reader, dummyRange, deserialize_list reader deserialize_lident)

(* type s_sigelts = array<s_sigelt> *)

(* let serialize_sigelts (ast : sigelts) : s_sigelts = serialize_list serialize_sigelt ast *)
(* let deserialize_sigelts (ast : s_sigelts) : sigelts = deserialize_list deserialize_sigelt ast *)

let serialize_sigelts (writer:Writer) (ast:sigelts) :unit = serialize_list writer serialize_sigelt ast
let deserialize_sigelts (reader:Reader) :sigelts = deserialize_list reader deserialize_sigelt

(* type s_modul =  *)
(*     { n : s_lident (\* name *\) *)
(*       d : s_sigelts (\* declarations *\) *)
(*       e : s_sigelts (\* exports *\) *)
(*       i : bool (\* is_interface *\) } *)

(* let serialize_modul (ast : modul) : s_modul =  *)
(*     { n = serialize_lident ast.name *)
(*       d = serialize_sigelts ast.declarations *)
(*       e = serialize_sigelts (\*[]*\) ast.exports *)
(*       i = ast.is_interface } *)

(* let deserialize_modul (ast : s_modul) : modul =  *)
(*     { name = deserialize_lident ast.n *)
(*       declarations = deserialize_sigelts ast.d *)
(*       exports = deserialize_sigelts (\*[||]*\) ast.e *)
(*       is_interface = ast.i *)
(*       is_deserialized = true } *)

let serialize_modul (writer:Writer) (ast:modul) :unit =
    serialize_lident writer ast.name;
    serialize_sigelts writer [];//ast.declarations;
    serialize_sigelts writer ast.exports;
    writer.Write(ast.is_interface)

let deserialize_modul (reader) :modul =
    let m = { name = deserialize_lident reader;
      declarations = deserialize_sigelts reader;
      exports = deserialize_sigelts (*[||]*) reader;
      is_interface = reader.ReadBoolean();
      is_deserialized = true } in
    {m with declarations=m.exports}//; exports=[]}

let serialize_modul_ext (file:string) (ast:modul) :unit = serialize_modul (new BinaryWriter(File.Open(file, FileMode.Create))) ast

let deserialize_modul_ext (file:string) :modul = deserialize_modul (new BinaryReader(File.Open(file, FileMode.Open)))