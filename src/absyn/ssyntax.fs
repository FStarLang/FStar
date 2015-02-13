module Microsoft.FStar.Absyn.SSyntax

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open System.IO

exception Err of string

let parse_error () = failwith "Parse error: ill-formed cache"

type Writer = BinaryWriter

type Reader = BinaryReader

(* AST for serialization of modules *)

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
    
let serialize_ident (writer: Writer) (ast:ident) :unit = writer.Write(ast.idText)
let deserialize_ident (reader: Reader) :ident = mk_ident (reader.ReadString(), dummyRange)

let serialize_LongIdent (writer:Writer) (ast:LongIdent) :unit =
    serialize_list writer serialize_ident ast.ns;
    serialize_ident writer ast.ident

let deserialize_LongIdent (reader:Reader) :LongIdent =
    lid_of_ids (deserialize_list reader deserialize_ident @ [ deserialize_ident reader ])

let serialize_lident = serialize_LongIdent
let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t (writer: Writer) (s_v:Writer -> 'a -> unit) (s_sort:Writer -> 't -> unit) (ast:withinfo_t<'a, 't>) :unit =
    s_v writer ast.v;
    s_sort writer ast.sort

let deserialize_withinfo_t (reader:Reader) (ds_v:Reader -> 'a) (ds_sort:Reader -> 't) :withinfo_t<'a, 't> =
    { v = ds_v reader;
      sort = ds_sort reader;
      p = dummyRange}

let serialize_var (writer:Writer) (s_sort:Writer -> 't -> unit) (ast:var<'t>) :unit =
    serialize_withinfo_t writer serialize_lident s_sort ast

let deserialize_var (reader:Reader) (ds_sort:Reader -> 't) :var<'t> =
    deserialize_withinfo_t reader deserialize_lident ds_sort

let serialize_bvdef (writer:Writer) (ast:bvdef<'a>) :unit =
    serialize_ident writer ast.ppname;
    serialize_ident writer ast.realname

let deserialize_bvdef (reader:Reader) :bvdef<'a> =
    { ppname = deserialize_ident reader;
      realname = deserialize_ident reader}

let serialize_bvar (writer:Writer) (s_sort:Writer -> 't -> unit) (ast:bvar<'a, 't>) :unit =
    serialize_withinfo_t writer serialize_bvdef s_sort ast

let deserialize_bvar (reader:Reader) (ds_sort:Reader -> 't) :bvar<'a, 't> =
    deserialize_withinfo_t reader deserialize_bvdef ds_sort

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
    |  _  -> parse_error()

let serialize_either (writer:Writer) (s_l:Writer -> 'a -> unit) (s_r:Writer -> 'b -> unit) (ast:either<'a, 'b>) :unit =
    match ast with
    | Inl(v) -> writer.Write('a'); s_l writer v
    | Inr(v) -> writer.Write('b'); s_r writer v

let deserialize_either (reader:Reader) (ds_l:Reader -> 'a) (ds_r: Reader -> 'b) :either<'a, 'b> =
    match (reader.ReadChar()) with
    | 'a' -> Inl(ds_l reader)
    | 'b' -> Inr(ds_r reader)
    |  _ -> raise (Err "Unknown tag in either datatype")

let serialize_syntax (writer:Writer) (s_a:Writer -> 'a -> unit) (ast:syntax<'a, 'b>) :unit = s_a writer ast.n

let deserialize_syntax (reader:Reader) (ds_a:Reader -> 'a) (ds_b:'b) :syntax<'a, 'b> =
    { n = ds_a reader
      tk = Util.mk_ref None
      pos = dummyRange
      fvs = ref None
      uvs = ref None}


let rec serialize_typ' (writer:Writer) (ast:typ') :unit = 
    match ast with
    | Typ_btvar(v) -> writer.Write('a'); serialize_btvar writer v
    | Typ_const(v) -> writer.Write('b'); serialize_ftvar writer v
    | Typ_fun(bs, c) -> writer.Write('c'); serialize_binders writer bs; serialize_comp writer c
    | Typ_refine(v, t) -> writer.Write('d'); serialize_bvvar writer v; serialize_typ writer t
    | Typ_app(t, ars) ->
        writer.Write('e'); serialize_typ writer t; serialize_args writer ars;
        if !Options.debug <> []
        then begin match t.n with
                | Typ_lam (_, _) -> print_string "type application node with lam\n"
                | _ -> ()
        end
    | Typ_lam(bs, t) -> writer.Write('f'); serialize_binders writer bs; serialize_typ writer t
    | Typ_ascribed(t, k) -> writer.Write('g'); serialize_typ writer t; serialize_knd writer k
    | Typ_meta(m) -> writer.Write('h'); serialize_meta_t writer m
    | Typ_unknown -> writer.Write('i') //raise (Err "Typ_unknown") TODO: fail on Typ_unknown
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
    | Kind_unknown -> writer.Write('f') //raise (Err "Kind_unknown") TODO: fail here
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
    | 'i' -> Typ_unknown //TODO: fail on Typ_unknown
    |  _  -> parse_error()

and deserialize_meta_t (reader:Reader) :meta_t = 
    match (reader.ReadChar()) with
    | 'a' -> Meta_pattern(deserialize_typ reader, deserialize_list reader deserialize_arg)
    | 'b' -> Meta_named(deserialize_typ reader, deserialize_lident reader)
    | 'c' -> Meta_labeled(deserialize_typ reader, reader.ReadString(), reader.ReadBoolean())
    |  _  -> parse_error()

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
    |  _  -> parse_error()

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
    |  _  -> parse_error()

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
            |  _  -> parse_error() in
        
        let f reader = (deserialize_pat reader, g reader, deserialize_exp reader) in
        Exp_match(deserialize_exp reader, deserialize_list reader f)
    | 'g' -> Exp_ascribed(deserialize_exp reader, deserialize_typ reader)
    | 'h' -> Exp_let(deserialize_letbindings reader, deserialize_exp reader)
    | 'i' -> Exp_meta(deserialize_meta_e reader)
    |  _  -> parse_error()

and deserialize_meta_e (reader:Reader) :meta_e =
    match (reader.ReadChar()) with
    | 'a' -> Meta_desugared(deserialize_exp reader, deserialize_meta_source_info reader)
    |  _  -> parse_error()
  
and deserialize_meta_source_info (reader:Reader) :meta_source_info =
    match (reader.ReadChar()) with
    | 'a' -> Data_app
    | 'b' -> Sequence
    | 'c' -> Primop
    | 'd' -> MaskedEffect
    |  _  -> parse_error()

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
    | 'g' -> Pat_twild(deserialize_btvar reader)
    | 'h' -> Pat_dot_term(deserialize_bvvar reader, deserialize_exp reader)
    | 'i' -> Pat_dot_typ(deserialize_btvar reader, deserialize_typ reader)
    | _   -> parse_error ()

and deserialize_pat (reader:Reader) :pat = 
    deserialize_withinfo_t reader deserialize_pat' (fun r -> None)// deserialize_either r deserialize_knd deserialize_typ)

and deserialize_knd' (reader:Reader) :knd' = 
    match (reader.ReadChar()) with
    | 'a' -> Kind_type
    | 'b' -> Kind_effect
    | 'c' -> Kind_abbrev(deserialize_kabbrev reader, deserialize_knd reader)
    | 'd' -> Kind_arrow(deserialize_binders reader, deserialize_knd reader)
    | 'e' -> Kind_lam(deserialize_binders reader, deserialize_knd reader)
    | 'f' -> Kind_unknown //TODO: should not allow this
    |  _  -> parse_error()

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

let serialize_formula = serialize_typ
let deserialize_formula = deserialize_typ

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
    |  _  -> parse_error()

let serialize_tycon (writer:Writer) ((lid, bs, k): tycon) :unit = serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k
let deserialize_tycon (reader:Reader) :tycon = (deserialize_lident reader, deserialize_binders reader, deserialize_knd reader)

let serialize_monad_abbrev (writer:Writer) (ast : monad_abbrev) :unit = 
    serialize_lident writer ast.mabbrev;
    serialize_binders writer ast.parms;
    serialize_typ writer ast.def

let deserialize_monad_abbrev (reader:Reader) :monad_abbrev = 
    { mabbrev = deserialize_lident reader
      parms = deserialize_binders reader
      def = deserialize_typ reader }

let serialize_monad_order (writer:Writer) (ast:monad_order) :unit =
    serialize_lident writer ast.source;
    serialize_lident writer ast.target;
    serialize_typ writer ast.lift

let deserialize_monad_order (reader:Reader) :monad_order = 
    { source = deserialize_lident reader
      target = deserialize_lident reader
      lift = deserialize_typ reader }

let serialize_monad_lat (writer:Writer) (ast:monad_lat) :unit = serialize_list writer serialize_monad_order ast
let deserialize_monad_lat (reader:Reader) :monad_lat = deserialize_list reader deserialize_monad_order

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
          | 'b' -> Some(deserialize_lident reader)
          |  _  -> parse_error() }
 

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
    |  _  -> parse_error()

let serialize_sigelts (writer:Writer) (ast:sigelts) :unit = serialize_list writer serialize_sigelt ast
let deserialize_sigelts (reader:Reader) :sigelts = deserialize_list reader deserialize_sigelt 

let serialize_modul (writer:Writer) (ast:modul) :unit =
    serialize_lident writer ast.name;
    serialize_sigelts writer [];
    serialize_sigelts writer ast.exports;
    writer.Write(ast.is_interface)

let deserialize_modul (reader) :modul =
    let m = { name = deserialize_lident reader;
      declarations = deserialize_sigelts reader;
      exports = deserialize_sigelts (*[||]*) reader;
      is_interface = reader.ReadBoolean();
      is_deserialized = true } in
    {m with declarations=m.exports}

let serialize_modul_ext (file:string) (ast:modul) :unit = serialize_modul (new BinaryWriter(File.Open(file, FileMode.Create))) ast

let deserialize_modul_ext (file:string) :modul = deserialize_modul (new BinaryReader(File.Open(file, FileMode.Open)))