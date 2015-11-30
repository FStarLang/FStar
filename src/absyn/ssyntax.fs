module FStar.Absyn.SSyntax

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util

exception Err of string

let parse_error () = failwith "Parse error: ill-formed cache"

type Writer = Util.oWriter

type Reader = Util.oReader

let serialize_option (writer:Writer) (f:Writer -> 'a -> unit) (l:option<'a>) :unit =
    match l with
        | None -> writer.write_char 'n'
        | Some l -> writer.write_char 's'; f writer l

let deserialize_option (reader:Reader) (f:Reader -> 'a) : option<'a> =
    let n = reader.read_char () in
    if n='n' then None
    else Some (f reader)

let serialize_list (writer:Writer) (f:Writer -> 'a -> unit) (l:list<'a>) :unit =
    writer.write_int (List.length l);
    List.iter (fun elt -> f writer elt) (List.rev_append l [])

let deserialize_list (reader: Reader) (f:Reader -> 'a) :list<'a> =
    let n = reader.read_int () in
    let rec helper (accum:list<'a>) (n:int) :list<'a> =
        if n = 0 then accum
        else
            helper ((f reader)::accum) (n - 1)
    in
    helper [] n

let serialize_ident (writer: Writer) (ast:ident) :unit = writer.write_string ast.idText
let deserialize_ident (reader: Reader) :ident = mk_ident (reader.read_string (), dummyRange)

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

(*
 * the ghost param below is to bind 'a in the return type
 * is there another way to bind type parameters that works for F* and F#
 *)
let deserialize_bvdef (ghost:option<'a>) (reader:Reader) :bvdef<'a> =
    { ppname = deserialize_ident reader;
      realname = deserialize_ident reader}

let serialize_bvar (writer:Writer) (s_sort:Writer -> 't -> unit) (ast:bvar<'a, 't>) :unit =
    serialize_withinfo_t writer serialize_bvdef s_sort ast

let deserialize_bvar (ghost:option<'a>) (reader:Reader) (ds_sort:Reader -> 't) :bvar<'a, 't> =
    deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort

let serialize_sconst (writer:Writer) (ast:sconst) :unit =
    match ast with
    | Const_unit -> writer.write_char 'a'
    | Const_uint8(v) -> writer.write_char 'b'; writer.write_byte v
    | Const_bool(v) -> writer.write_char 'c'; writer.write_bool v
    | Const_int32(v) -> writer.write_char 'd'; writer.write_int32 v
    | Const_int64(v) -> writer.write_char 'e'; writer.write_int64 v
    | Const_char(v) -> writer.write_char 'f'; writer.write_char v
    | Const_float(v) -> writer.write_char 'g'; writer.write_double v
    | Const_bytearray(v, _) -> writer.write_char 'h'; writer.write_bytearray v
    | Const_string(v, _) -> writer.write_char 'i'; writer.write_bytearray v
    | Const_int(v) -> writer.write_char 'j'; writer.write_string v

let deserialize_sconst (reader:Reader) :sconst =
    match (reader.read_char()) with
    | 'a' -> Const_unit
    | 'b' -> Const_uint8(reader.read_byte ())
    | 'c' -> Const_bool(reader.read_bool ())
    | 'd' -> Const_int32(reader.read_int32 ())
    | 'e' -> Const_int64(reader.read_int64 ())
    | 'f' -> Const_char(reader.read_char ())
    | 'g' -> Const_float(reader.read_double ())
    | 'h' -> Const_bytearray(reader.read_bytearray (), dummyRange)
    | 'i' -> Const_string(reader.read_bytearray (), dummyRange)
    | 'j' -> Const_int(reader.read_string ())
    |  _  -> parse_error()

let serialize_either (writer:Writer) (s_l:Writer -> 'a -> unit) (s_r:Writer -> 'b -> unit) (ast:either<'a, 'b>) :unit =
    match ast with
    | Inl(v) -> writer.write_char 'a'; s_l writer v
    | Inr(v) -> writer.write_char 'b'; s_r writer v

let deserialize_either (reader:Reader) (ds_l:Reader -> 'a) (ds_r: Reader -> 'b) :either<'a, 'b> =
    match (reader.read_char ()) with
    | 'a' -> Inl(ds_l reader)
    | 'b' -> Inr(ds_r reader)
    |  _ -> parse_error()

let serialize_syntax (writer:Writer) (s_a:Writer -> 'a -> unit) (ast:syntax<'a, 'b>) :unit = s_a writer ast.n

let deserialize_syntax (reader:Reader) (ds_a:Reader -> 'a) (ds_b:'b) :syntax<'a, 'b> =
    { n = ds_a reader;
      tk = Util.mk_ref None;
      pos = dummyRange;
      fvs = Util.mk_ref None;
      uvs = Util.mk_ref None}

let rec serialize_typ' (writer:Writer) (ast:typ') :unit =
    match ast with
    | Typ_btvar(v) -> writer.write_char 'a'; serialize_btvar writer v
    | Typ_const(v) -> writer.write_char 'b'; serialize_ftvar writer v
    | Typ_fun(bs, c) -> writer.write_char 'c'; serialize_binders writer bs; serialize_comp writer c
    | Typ_refine(v, t) -> writer.write_char 'd'; serialize_bvvar writer v; serialize_typ writer t
    | Typ_app(t, ars) ->
        writer.write_char 'e'; serialize_typ writer t; serialize_args writer ars;
        if !Options.debug <> []
        then begin match t.n with
                | Typ_lam (_, _) -> print_string "type application node with lam\n"
                | _ -> ()
        end
    | Typ_lam(bs, t) -> writer.write_char 'f'; serialize_binders writer bs; serialize_typ writer t
    | Typ_ascribed(t, k) -> writer.write_char 'g'; serialize_typ writer t; serialize_knd writer k
    | Typ_meta(m) -> writer.write_char 'h'; serialize_meta_t writer m
    | Typ_unknown -> writer.write_char 'i' //raise (Err "Typ_unknown") TODO: fail on Typ_unknown
    | Typ_uvar(_, _) -> raise (Err "typ not impl:1")
    | Typ_delayed(_, _) -> raise (Err "typ not impl:2")

and serialize_meta_t (writer:Writer) (ast:meta_t) :unit =
    match ast with
    | Meta_pattern(t, l) -> writer.write_char 'a'; serialize_typ writer t; serialize_list writer (fun w -> serialize_list w serialize_arg) l
    | Meta_named(t, lid) -> writer.write_char 'b'; serialize_typ writer t; serialize_lident writer lid
    | Meta_labeled(t, s, _, b) -> writer.write_char 'c'; serialize_typ writer t; writer.write_string s; writer.write_bool b
    | _ -> raise (Err "unimplemented meta_t")

and serialize_arg (writer:Writer) (ast:arg) :unit = serialize_either writer serialize_typ serialize_exp (fst ast); writer.write_bool (is_implicit <| snd ast)//TODO: Generalize

and serialize_args (writer:Writer) (ast:args) :unit = serialize_list writer serialize_arg ast

and serialize_binder (writer:Writer) (ast:binder) :unit = serialize_either writer serialize_btvar serialize_bvvar (fst ast); writer.write_bool (is_implicit <| snd ast)//TODO: Generalize

and serialize_binders (writer:Writer) (ast:binders) :unit = serialize_list writer serialize_binder ast

and serialize_typ (writer:Writer) (ast:typ) :unit = serialize_syntax writer serialize_typ' (Util.compress_typ ast)

and serialize_comp_typ (writer:Writer) (ast:comp_typ) :unit =
    serialize_lident writer ast.effect_name;
    serialize_typ writer ast.result_typ;
    serialize_args writer ast.effect_args;
    serialize_list writer serialize_cflags ast.flags

and serialize_comp' (writer:Writer) (ast:comp') :unit =
    match ast with
    | Total(t) -> writer.write_char 'a'; serialize_typ writer t
    | Comp(c) -> writer.write_char 'b'; serialize_comp_typ writer c

and serialize_comp (writer:Writer) (ast:comp) :unit = serialize_syntax writer serialize_comp' ast

and serialize_cflags (writer:Writer) (ast:cflags) :unit =
    match ast with
    | TOTAL -> writer.write_char 'a'
    | MLEFFECT -> writer.write_char 'b'
    | RETURN -> writer.write_char 'c'
    | PARTIAL_RETURN -> writer.write_char 'd'
    | SOMETRIVIAL -> writer.write_char 'e'
    | LEMMA -> writer.write_char 'f'
    | DECREASES e -> writer.write_char 'g'; serialize_exp writer e

and serialize_exp' (writer:Writer) (ast:exp') :unit =
    match ast with
    | Exp_bvar(v) -> writer.write_char 'a'; serialize_bvvar writer v
    | Exp_fvar(v, b) -> writer.write_char 'b'; serialize_fvvar writer v; writer.write_bool false//NS: FIXME!
    | Exp_constant(c) -> writer.write_char 'c'; serialize_sconst writer c
    | Exp_abs(bs, e) -> writer.write_char 'd'; serialize_binders writer bs; serialize_exp writer e
    | Exp_app(e, ars) -> writer.write_char 'e'; serialize_exp writer e; serialize_args writer ars
    | Exp_match(e, l) ->
        let g (writer:Writer) eopt =
            match eopt with
            | Some(e1) -> writer.write_char 'a'; serialize_exp writer e1
            | None -> writer.write_char 'b'
        in
        let f writer (p, eopt, e) = serialize_pat writer p; g writer eopt; serialize_exp writer e in
        writer.write_char 'f'; serialize_exp writer e; serialize_list writer f l
    | Exp_ascribed(e, t, l) -> writer.write_char 'g'; serialize_exp writer e; serialize_typ writer t; serialize_option writer serialize_lident l
    | Exp_let(lbs, e) -> writer.write_char 'h'; serialize_letbindings writer lbs; serialize_exp writer e
    | Exp_meta(m) -> writer.write_char 'i'; serialize_meta_e writer m
    | _ -> raise (Err "unimplemented exp'")

and serialize_meta_e (writer:Writer) (ast:meta_e) :unit =
    match ast with
    | Meta_desugared(e, s) -> writer.write_char 'a'; serialize_exp writer  e; serialize_meta_source_info writer s


and serialize_meta_source_info (writer:Writer) (ast:meta_source_info) :unit =
    match ast with
    | Data_app -> writer.write_char 'a'
    | Sequence -> writer.write_char 'b'
    | Primop -> writer.write_char 'c'
    | Masked_effect -> writer.write_char 'd'
    | Meta_smt_pat ->  writer.write_char 'e'

and serialize_exp (writer:Writer) (ast:exp) :unit = serialize_syntax writer serialize_exp' (Util.compress_exp ast)

and serialize_btvdef (writer:Writer) (ast:btvdef) :unit = serialize_bvdef writer ast

and serialize_bvvdef (writer:Writer) (ast:bvvdef) :unit = serialize_bvdef writer ast

and serialize_pat' (writer:Writer) (ast:pat') :unit =
    match ast with
    | Pat_disj(l) -> writer.write_char 'a'; serialize_list writer serialize_pat l
    | Pat_constant(c) -> writer.write_char 'b'; serialize_sconst writer c
    | Pat_cons(v, _, l) -> writer.write_char 'c'; serialize_fvvar writer v; serialize_list writer (fun w (p,b) -> serialize_pat w p; w.write_bool b) l
    | Pat_var v -> writer.write_char 'd'; serialize_bvvar writer v
    | Pat_tvar(v) -> writer.write_char 'e'; serialize_btvar writer v
    | Pat_wild(v) -> writer.write_char 'f';  serialize_bvvar writer v
    | Pat_twild(v) -> writer.write_char 'g';  serialize_btvar writer v
    | Pat_dot_term(v, e) -> writer.write_char 'h'; serialize_bvvar writer v; serialize_exp writer e
    | Pat_dot_typ(v, t) -> writer.write_char 'i'; serialize_btvar writer v; serialize_typ writer t

and serialize_pat (writer:Writer) (ast:pat) :unit =
    serialize_withinfo_t writer serialize_pat' (fun w kt -> () (* serialize_either w serialize_knd serialize_typ kt*)) ast

and serialize_knd' (writer:Writer) (ast:knd') :unit =
    match ast with
    | Kind_type -> writer.write_char 'a'
    | Kind_effect -> writer.write_char 'b'
    | Kind_abbrev(ka, k) -> writer.write_char 'c'; serialize_kabbrev writer ka; serialize_knd writer k
    | Kind_arrow(bs, k) -> writer.write_char 'd'; serialize_binders writer bs; serialize_knd writer k
    | Kind_lam(bs, k) -> writer.write_char 'e'; serialize_binders writer bs; serialize_knd writer k
    | Kind_unknown -> writer.write_char 'f' //raise (Err "Kind_unknown") TODO: fail here
    | Kind_uvar(uv, args) -> raise (Err "knd' serialization unimplemented:1")
    | Kind_delayed(_, _, _) -> raise (Err "knd' serialization unimplemented:2")

and serialize_knd (writer:Writer) (ast:knd) :unit = serialize_syntax writer serialize_knd' (Util.compress_kind ast)

and serialize_kabbrev (writer:Writer) (ast:kabbrev) :unit = serialize_lident writer (fst ast); serialize_args writer (snd ast)

and serialize_lbname (writer:Writer) (ast:lbname) :unit = serialize_either writer serialize_bvvdef serialize_lident ast

and serialize_letbindings (writer:Writer) (ast:letbindings) :unit =
    let f writer lb = serialize_lbname writer lb.lbname; serialize_lident writer lb.lbeff; serialize_typ writer lb.lbtyp; serialize_exp writer lb.lbdef in
    writer.write_bool (fst ast); serialize_list writer f (snd ast)

and serialize_fvar (writer:Writer) (ast:Syntax.fvar) :unit = serialize_either writer serialize_btvdef serialize_bvvdef ast

and serialize_btvar (writer:Writer) (ast:btvar) :unit = serialize_bvar writer serialize_knd ast

and serialize_bvvar (writer:Writer) (ast:bvvar) :unit = serialize_bvar writer serialize_typ ast

and serialize_ftvar (writer:Writer) (ast:ftvar) :unit = serialize_var writer serialize_knd ast

and serialize_fvvar (writer:Writer) (ast:fvvar) :unit = serialize_var writer serialize_typ ast

let rec deserialize_typ' (reader:Reader) :typ' =
    match (reader.read_char ()) with
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
    match (reader.read_char ()) with
    | 'a' -> Meta_pattern(deserialize_typ reader, deserialize_list reader (fun r -> deserialize_list r deserialize_arg))
    | 'b' -> Meta_named(deserialize_typ reader, deserialize_lident reader)
    | 'c' -> Meta_labeled(deserialize_typ reader, reader.read_string (), dummyRange, reader.read_bool ())
    |  _  -> parse_error()

and deserialize_arg (reader:Reader) :arg = (deserialize_either reader deserialize_typ deserialize_exp, as_implicit <| reader.read_bool ())//TODO: Generalize

and deserialize_args (reader:Reader) :args = deserialize_list reader deserialize_arg

and deserialize_binder (reader:Reader) :binder =
    (deserialize_either reader deserialize_btvar deserialize_bvvar, as_implicit <| reader.read_bool ())//TODO: Generalize

and deserialize_binders (reader:Reader) :binders = deserialize_list reader deserialize_binder

and deserialize_typ (reader:Reader) :typ = deserialize_syntax reader deserialize_typ' mk_Kind_unknown

and deserialize_comp_typ (reader:Reader) :comp_typ =
    { effect_name = deserialize_lident reader;
      result_typ = deserialize_typ reader;
      effect_args = deserialize_args reader;
      flags = deserialize_list reader deserialize_cflags }

and deserialize_comp' (reader:Reader) :comp' =
    match (reader.read_char ()) with
    | 'a' -> Total(deserialize_typ reader)
    | 'b' -> Comp(deserialize_comp_typ reader)
    |  _  -> parse_error()

and deserialize_comp (reader:Reader) :comp = deserialize_syntax reader deserialize_comp' ()

and deserialize_cflags (reader:Reader) :cflags =
    match (reader.read_char ()) with
    | 'a' -> TOTAL
    | 'b' -> MLEFFECT
    | 'c' -> RETURN
    | 'd' -> PARTIAL_RETURN
    | 'e' -> SOMETRIVIAL
    | 'f' -> LEMMA
    | 'g' -> DECREASES(deserialize_exp reader)
    |  _  -> parse_error()

and deserialize_exp' (reader:Reader) :exp' =
    match (reader.read_char ()) with
    | 'a' -> Exp_bvar(deserialize_bvvar reader)
    | 'b' -> Exp_fvar(deserialize_fvvar reader, (ignore <| reader.read_bool (); None)) //FIXME
    | 'c' -> Exp_constant(deserialize_sconst reader)
    | 'd' -> Exp_abs(deserialize_binders reader, deserialize_exp reader)
    | 'e' -> Exp_app(deserialize_exp reader, deserialize_args reader)
    | 'f' ->
        let g (reader:Reader) =
            match (reader.read_char ()) with
            | 'a' -> Some(deserialize_exp reader)
            | 'b' -> None
            |  _  -> parse_error() in

        let f reader = (deserialize_pat reader, g reader, deserialize_exp reader) in
        Exp_match(deserialize_exp reader, deserialize_list reader f)
    | 'g' -> Exp_ascribed(deserialize_exp reader, deserialize_typ reader, deserialize_option reader deserialize_lident)
    | 'h' -> Exp_let(deserialize_letbindings reader, deserialize_exp reader)
    | 'i' -> Exp_meta(deserialize_meta_e reader)
    |  _  -> parse_error()

and deserialize_meta_e (reader:Reader) :meta_e =
    match (reader.read_char ()) with
    | 'a' -> Meta_desugared(deserialize_exp reader, deserialize_meta_source_info reader)
    |  _  -> parse_error()

and deserialize_meta_source_info (reader:Reader) :meta_source_info =
    match (reader.read_char ()) with
    | 'a' -> Data_app
    | 'b' -> Sequence
    | 'c' -> Primop
    | 'd' -> Masked_effect
    |  _  -> parse_error()

and deserialize_exp (reader:Reader) :exp = deserialize_syntax reader deserialize_exp' mk_Typ_unknown

and deserialize_btvdef (reader:Reader) :btvdef = deserialize_bvdef None reader

and deserialize_bvvdef (reader:Reader) :bvvdef = deserialize_bvdef None reader

and deserialize_pat' (reader:Reader) :pat' =
    match (reader.read_char ()) with
    | 'a' -> Pat_disj(deserialize_list reader deserialize_pat)
    | 'b' -> Pat_constant(deserialize_sconst reader)
    | 'c' -> Pat_cons(deserialize_fvvar reader, None(* fixme *), deserialize_list reader (fun r -> (deserialize_pat r, r.read_bool ())))
    | 'd' -> Pat_var(deserialize_bvvar reader)
    | 'e' -> Pat_tvar(deserialize_btvar reader)
    | 'f' -> Pat_wild(deserialize_bvvar reader)
    | 'g' -> Pat_twild(deserialize_btvar reader)
    | 'h' -> Pat_dot_term(deserialize_bvvar reader, deserialize_exp reader)
    | 'i' -> Pat_dot_typ(deserialize_btvar reader, deserialize_typ reader)
    | _   -> parse_error ()

and deserialize_pat (reader:Reader) :pat =
    deserialize_withinfo_t reader deserialize_pat' (fun r -> None)// deserialize_either r deserialize_knd deserialize_typ)

and deserialize_knd' (reader:Reader) :knd' =
    match (reader.read_char ()) with
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
    let f reader = {lbname=deserialize_lbname reader;
                    lbeff=deserialize_lident reader;
                    lbtyp=deserialize_typ reader;
                    lbdef=deserialize_exp reader} in
    (reader.read_bool (), deserialize_list reader f)

and deserialize_fvar (reader:Reader) :Syntax.fvar = deserialize_either reader deserialize_btvdef deserialize_bvvdef

and deserialize_btvar (reader:Reader) :btvar = deserialize_bvar None reader deserialize_knd

and deserialize_bvvar (reader:Reader) :bvvar = deserialize_bvar None reader deserialize_typ

and deserialize_ftvar (reader:Reader) :ftvar = deserialize_var reader deserialize_knd

and deserialize_fvvar (reader:Reader) :fvvar = deserialize_var reader deserialize_typ

let serialize_formula = serialize_typ
let deserialize_formula = deserialize_typ

let serialize_qualifier (writer:Writer)(ast:qualifier) :unit =
    match ast with
    | Private -> writer.write_char 'a'
    | Assumption -> writer.write_char 'c'
    | Logic -> writer.write_char 'g'
    | Opaque -> writer.write_char 'h'
    | Discriminator(lid) -> writer.write_char 'i'; serialize_lident writer lid
    | Projector(lid, v) -> writer.write_char 'j'; serialize_lident writer lid; serialize_either writer serialize_btvdef serialize_bvvdef v
    | RecordType(l) -> writer.write_char 'k'; serialize_list writer serialize_lident l
    | RecordConstructor(l) -> writer.write_char 'l'; serialize_list writer serialize_lident l
    | ExceptionConstructor -> writer.write_char 'm'
    | HasMaskedEffect -> writer.write_char 'o'
    | DefaultEffect l -> writer.write_char 'p'; serialize_option writer serialize_lident l
    | TotalEffect -> writer.write_char 'q'
    | _ -> failwith "Unexpected qualifier"

let deserialize_qualifier (reader:Reader) :qualifier =
    match reader.read_char () with
    | 'a' -> Private
    | 'c' -> Assumption
    | 'g' -> Logic
    | 'h' -> Opaque
    | 'i' -> Discriminator(deserialize_lident reader)
    | 'j' -> Projector(deserialize_lident reader, deserialize_either reader deserialize_btvdef deserialize_bvvdef)
    | 'k' -> RecordType(deserialize_list reader deserialize_lident)
    | 'l' -> RecordConstructor(deserialize_list reader deserialize_lident)
    | 'm' -> ExceptionConstructor
    | 'o' -> HasMaskedEffect
    | 'p' -> deserialize_option reader deserialize_lident |> DefaultEffect
    | 'q' -> TotalEffect
    |  _  -> parse_error()

let serialize_tycon (writer:Writer) ((lid, bs, k): tycon) :unit = serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k
let deserialize_tycon (reader:Reader) :tycon = (deserialize_lident reader, deserialize_binders reader, deserialize_knd reader)

let serialize_monad_abbrev (writer:Writer) (ast : monad_abbrev) :unit =
    serialize_lident writer ast.mabbrev;
    serialize_binders writer ast.parms;
    serialize_typ writer ast.def

let deserialize_monad_abbrev (reader:Reader) :monad_abbrev =
    { mabbrev = deserialize_lident reader;
      parms = deserialize_binders reader;
      def = deserialize_typ reader }

let serialize_sub_effect (writer:Writer) (ast:sub_eff) :unit =
    serialize_lident writer ast.source;
    serialize_lident writer ast.target;
    serialize_typ writer ast.lift

let deserialize_sub_effect (reader:Reader) : sub_eff  =
    { source = deserialize_lident reader;
      target = deserialize_lident reader;
      lift = deserialize_typ reader }

let rec serialize_new_effect (writer:Writer) (ast:eff_decl) :unit =
    serialize_lident writer ast.mname;
    serialize_list writer serialize_binder ast.binders;
    serialize_list writer serialize_qualifier ast.qualifiers;
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
    serialize_typ writer ast.trivial

and serialize_sigelt (writer:Writer) (ast:sigelt) :unit =
    match ast with
    | Sig_pragma _ -> failwith "NYI"
    | Sig_tycon(lid, bs, k, l1, l2, qs, _) ->
        writer.write_char 'a';
        serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k;
        serialize_list writer serialize_lident l1; serialize_list writer serialize_lident l2;
        serialize_list writer serialize_qualifier qs
    | Sig_typ_abbrev(lid, bs, k, t, qs, _) ->
        writer.write_char 'b';
        serialize_lident writer lid; serialize_binders writer bs; serialize_knd writer k;
        serialize_typ writer t; serialize_list writer serialize_qualifier qs
    | Sig_datacon(lid1, t, tyc, qs, mutuals, _) ->
      let t' =
        match Util.function_formals t with
        | Some (f, c) -> mk_Typ_fun (f, Syntax.mk_Total  (Util.comp_result c)) None dummyRange
        | None -> t
      in
      writer.write_char 'c';
      serialize_lident writer lid1; serialize_typ writer t'; serialize_tycon writer tyc;
      serialize_list writer serialize_qualifier qs;
      serialize_list writer serialize_lident mutuals
    | Sig_val_decl(lid, t, qs, _) ->
        writer.write_char 'd';
        serialize_lident writer lid; serialize_typ writer t; serialize_list writer serialize_qualifier qs
    | Sig_assume(lid, fml, qs, _) ->
        writer.write_char 'e';
        serialize_lident writer lid; serialize_formula writer fml; serialize_list writer serialize_qualifier qs
    | Sig_let(lbs, _, l, quals) ->
        writer.write_char 'f';
        serialize_letbindings writer lbs; serialize_list writer serialize_lident l; writer.write_bool (quals |> Util.for_some (function HasMaskedEffect -> true | _ -> false)) //TODO: Generalize
    | Sig_main(e, _) -> writer.write_char 'g'; serialize_exp writer e
    | Sig_bundle(l, qs, lids, _) ->
        writer.write_char 'h';
        serialize_list writer serialize_sigelt l;
        serialize_list writer serialize_qualifier qs;
        serialize_list writer serialize_lident lids
    | Sig_new_effect (n, _) ->
        writer.write_char 'i';
        serialize_new_effect writer n
    | Sig_effect_abbrev(lid, bs, c, qs, _) ->
        writer.write_char 'j';
        serialize_lident writer lid; serialize_binders writer bs;
        serialize_comp writer c; serialize_list writer serialize_qualifier qs
    | Sig_sub_effect(se, r) ->
        writer.write_char 'k';
        serialize_sub_effect writer se
    | Sig_kind_abbrev(l, binders, k, _) ->
        writer.write_char 'l';
        serialize_lident writer l;
        serialize_list writer serialize_binder binders;
        serialize_knd writer k

let rec deserialize_new_effect (reader:Reader) :eff_decl =
    {
      mname = deserialize_lident reader;
      binders= deserialize_list reader deserialize_binder;
      qualifiers = deserialize_list reader deserialize_qualifier;
      signature = deserialize_knd reader;
      ret = deserialize_typ reader;
      bind_wp = deserialize_typ reader;
      bind_wlp = deserialize_typ reader;
      if_then_else = deserialize_typ reader;
      ite_wp = deserialize_typ reader;
      ite_wlp = deserialize_typ reader;
      wp_binop = deserialize_typ reader;
      wp_as_type = deserialize_typ reader;
      close_wp = deserialize_typ reader;
      close_wp_t = deserialize_typ reader;
      assert_p = deserialize_typ reader;
      assume_p = deserialize_typ reader;
      null_wp = deserialize_typ reader;
      trivial = deserialize_typ reader;
     }

and deserialize_sigelt (reader:Reader) :sigelt =
    match (reader.read_char ()) with
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
            (deserialize_lident reader, deserialize_typ reader, deserialize_tycon reader, deserialize_list reader deserialize_qualifier,
            deserialize_list reader deserialize_lident, dummyRange)
    | 'd' ->
        Sig_val_decl(deserialize_lident reader, deserialize_typ reader, deserialize_list reader deserialize_qualifier, dummyRange)
    | 'e' ->
        Sig_assume(deserialize_lident reader, deserialize_formula reader, deserialize_list reader deserialize_qualifier, dummyRange)
    | 'f' -> Sig_let(deserialize_letbindings reader, dummyRange, deserialize_list reader deserialize_lident, (if reader.read_bool () then [HasMaskedEffect] else [])) //TODO: Generalize
    | 'g' -> Sig_main(deserialize_exp reader, dummyRange)
    | 'h' -> Sig_bundle(deserialize_list reader deserialize_sigelt, deserialize_list reader deserialize_qualifier, deserialize_list reader deserialize_lident, dummyRange)
    | 'i' -> Sig_new_effect(deserialize_new_effect reader, dummyRange)
    | 'j'
    | 'k'
    | 'l' -> failwith "TODO"
    |  _  -> parse_error()

let serialize_sigelts (writer:Writer) (ast:sigelts) :unit = serialize_list writer serialize_sigelt ast
let deserialize_sigelts (reader:Reader) :sigelts = deserialize_list reader deserialize_sigelt

let serialize_modul (writer:Writer) (ast:modul) :unit =
    serialize_lident writer ast.name;
    serialize_sigelts writer [];
    serialize_sigelts writer ast.exports;
    writer.write_bool ast.is_interface

let deserialize_modul (reader:Reader) :modul =
    let m = { name = deserialize_lident reader;
      declarations = deserialize_sigelts reader;
      exports = deserialize_sigelts (*[||]*) reader;
      is_interface = reader.read_bool ();
      is_deserialized = true } in
    {m with declarations=m.exports}