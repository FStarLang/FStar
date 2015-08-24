
exception Err of (string)

let is_Err = (fun ( _discr_ ) -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 = (fun ( projectee ) -> (match (projectee) with
| Err (_27_3) -> begin
_27_3
end))

let parse_error = (fun ( _27_4 ) -> (match (()) with
| () -> begin
(Support.All.failwith "Parse error: ill-formed cache")
end))

type l__Writer =
Support.Microsoft.FStar.Util.oWriter

type l__Reader =
Support.Microsoft.FStar.Util.oReader

let serialize_option = (fun ( writer ) ( f ) ( l ) -> (match (l) with
| None -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'n')
end
| Some (l) -> begin
(let _27_12 = (writer.Support.Microsoft.FStar.Util.write_char 's')
in (f writer l))
end))

let deserialize_option = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_char ())
in (match ((n = 'n')) with
| true -> begin
None
end
| false -> begin
(let _93_21 = (f reader)
in Some (_93_21))
end)))

let serialize_list = (fun ( writer ) ( f ) ( l ) -> (let _27_22 = (writer.Support.Microsoft.FStar.Util.write_int (Support.List.length l))
in (Support.List.iter (fun ( elt ) -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_int ())
in (let rec helper = (fun ( accum ) ( n ) -> (match ((n = 0)) with
| true -> begin
accum
end
| false -> begin
(let _93_42 = (let _93_41 = (f reader)
in (_93_41)::accum)
in (helper _93_42 (n - 1)))
end))
in (helper [] n))))

let serialize_ident = (fun ( writer ) ( ast ) -> (writer.Support.Microsoft.FStar.Util.write_string ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun ( reader ) -> (let _93_50 = (let _93_49 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (_93_49, Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _93_50)))

let serialize_LongIdent = (fun ( writer ) ( ast ) -> (let _27_37 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun ( reader ) -> (let _93_60 = (let _93_59 = (deserialize_list reader deserialize_ident)
in (let _93_58 = (let _93_57 = (deserialize_ident reader)
in (_93_57)::[])
in (Support.List.append _93_59 _93_58)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _93_60)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun ( writer ) ( s_v ) ( s_sort ) ( ast ) -> (let _27_46 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun ( reader ) ( ds_v ) ( ds_sort ) -> (let _93_90 = (ds_v reader)
in (let _93_89 = (ds_sort reader)
in {Microsoft_FStar_Absyn_Syntax.v = _93_90; Microsoft_FStar_Absyn_Syntax.sort = _93_89; Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun ( writer ) ( ast ) -> (let _27_63 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ( ghost ) ( reader ) -> (let _93_110 = (deserialize_ident reader)
in (let _93_109 = (deserialize_ident reader)
in {Microsoft_FStar_Absyn_Syntax.ppname = _93_110; Microsoft_FStar_Absyn_Syntax.realname = _93_109})))

let serialize_bvar = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

let deserialize_bvar = (fun ( ghost ) ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

let serialize_sconst = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (v) -> begin
(let _27_83 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (writer.Support.Microsoft.FStar.Util.write_byte v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (v) -> begin
(let _27_87 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (writer.Support.Microsoft.FStar.Util.write_bool v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (v) -> begin
(let _27_91 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (writer.Support.Microsoft.FStar.Util.write_int32 v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (v) -> begin
(let _27_95 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (writer.Support.Microsoft.FStar.Util.write_int64 v))
end
| Microsoft_FStar_Absyn_Syntax.Const_char (v) -> begin
(let _27_99 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (writer.Support.Microsoft.FStar.Util.write_char v))
end
| Microsoft_FStar_Absyn_Syntax.Const_float (v) -> begin
(let _27_103 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (writer.Support.Microsoft.FStar.Util.write_double v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((v, _27_107)) -> begin
(let _27_110 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (writer.Support.Microsoft.FStar.Util.write_bytearray v))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((v, _27_114)) -> begin
(let _27_117 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (writer.Support.Microsoft.FStar.Util.write_bytearray v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (v) -> begin
(let _27_121 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (writer.Support.Microsoft.FStar.Util.write_string v))
end))

let deserialize_sconst = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Const_unit
end
| 'b' -> begin
(let _93_132 = (reader.Support.Microsoft.FStar.Util.read_byte ())
in Microsoft_FStar_Absyn_Syntax.Const_uint8 (_93_132))
end
| 'c' -> begin
(let _93_133 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in Microsoft_FStar_Absyn_Syntax.Const_bool (_93_133))
end
| 'd' -> begin
(let _93_134 = (reader.Support.Microsoft.FStar.Util.read_int32 ())
in Microsoft_FStar_Absyn_Syntax.Const_int32 (_93_134))
end
| 'e' -> begin
(let _93_135 = (reader.Support.Microsoft.FStar.Util.read_int64 ())
in Microsoft_FStar_Absyn_Syntax.Const_int64 (_93_135))
end
| 'f' -> begin
(let _93_136 = (reader.Support.Microsoft.FStar.Util.read_char ())
in Microsoft_FStar_Absyn_Syntax.Const_char (_93_136))
end
| 'g' -> begin
(let _93_137 = (reader.Support.Microsoft.FStar.Util.read_double ())
in Microsoft_FStar_Absyn_Syntax.Const_float (_93_137))
end
| 'h' -> begin
(let _93_139 = (let _93_138 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_93_138, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_bytearray (_93_139))
end
| 'i' -> begin
(let _93_141 = (let _93_140 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_93_140, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_93_141))
end
| 'j' -> begin
(let _93_142 = (reader.Support.Microsoft.FStar.Util.read_string ())
in Microsoft_FStar_Absyn_Syntax.Const_int (_93_142))
end
| _27_135 -> begin
(parse_error ())
end))

let serialize_either = (fun ( writer ) ( s_l ) ( s_r ) ( ast ) -> (match (ast) with
| Support.Microsoft.FStar.Util.Inl (v) -> begin
(let _27_144 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (s_l writer v))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _27_148 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (s_r writer v))
end))

let deserialize_either = (fun ( reader ) ( ds_l ) ( ds_r ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_168 = (ds_l reader)
in Support.Microsoft.FStar.Util.Inl (_93_168))
end
| 'b' -> begin
(let _93_169 = (ds_r reader)
in Support.Microsoft.FStar.Util.Inr (_93_169))
end
| _27_158 -> begin
(parse_error ())
end))

let serialize_syntax = (fun ( writer ) ( s_a ) ( ast ) -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun ( reader ) ( ds_a ) ( ds_b ) -> (let _93_188 = (ds_a reader)
in (let _93_187 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _93_186 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _93_185 = (Support.Microsoft.FStar.Util.mk_ref None)
in {Microsoft_FStar_Absyn_Syntax.n = _93_188; Microsoft_FStar_Absyn_Syntax.tk = _93_187; Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = _93_186; Microsoft_FStar_Absyn_Syntax.uvs = _93_185})))))

let rec serialize_typ' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _27_173 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _27_177 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_ftvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _27_183 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_185 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((v, t)) -> begin
(let _27_191 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_193 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, ars)) -> begin
(let _27_199 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_201 = (serialize_typ writer t)
in (let _27_203 = (serialize_args writer ars)
in (match (((Support.ST.read Microsoft_FStar_Options.debug) <> [])) with
| true -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_27_206, _27_208)) -> begin
(Support.Microsoft.FStar.Util.print_string "type application node with lam\n")
end
| _27_212 -> begin
()
end)
end
| false -> begin
()
end))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _27_217 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _27_219 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(let _27_225 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (let _27_227 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _27_231 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (serialize_meta_t writer m))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'i')
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_27_235, _27_237)) -> begin
(raise (Err ("typ not impl:1")))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((_27_241, _27_243)) -> begin
(raise (Err ("typ not impl:2")))
end))
and serialize_meta_t = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, l)) -> begin
(let _27_252 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _27_254 = (serialize_typ writer t)
in (serialize_list writer serialize_arg l)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid)) -> begin
(let _27_260 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _27_262 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, s, _27_267, b)) -> begin
(let _27_271 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_273 = (serialize_typ writer t)
in (let _27_275 = (writer.Support.Microsoft.FStar.Util.write_string s)
in (writer.Support.Microsoft.FStar.Util.write_bool b))))
end
| _27_278 -> begin
(raise (Err ("unimplemented meta_t")))
end))
and serialize_arg = (fun ( writer ) ( ast ) -> (let _27_281 = (serialize_either writer serialize_typ serialize_exp (Support.Prims.fst ast))
in (let _93_255 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _93_255))))
and serialize_args = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun ( writer ) ( ast ) -> (let _27_287 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (let _93_260 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _93_260))))
and serialize_binders = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun ( writer ) ( ast ) -> (let _93_265 = (Microsoft_FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _93_265)))
and serialize_comp_typ = (fun ( writer ) ( ast ) -> (let _27_295 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _27_297 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _27_299 = (serialize_args writer ast.Microsoft_FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.Microsoft_FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _27_305 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_typ writer t))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let _27_309 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_comp_typ writer c))
end))
and serialize_comp = (fun ( writer ) ( ast ) -> (serialize_syntax writer serialize_comp' ast))
and serialize_cflags = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'b')
end
| Microsoft_FStar_Absyn_Syntax.RETURN -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'c')
end
| Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'd')
end
| Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'e')
end
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'f')
end
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _27_323 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _27_329 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, b)) -> begin
(let _27_335 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _27_337 = (serialize_fvvar writer v)
in (writer.Support.Microsoft.FStar.Util.write_bool false)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _27_341 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let _27_347 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_349 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, ars)) -> begin
(let _27_355 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_357 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, l)) -> begin
(let g = (fun ( writer ) ( eopt ) -> (match (eopt) with
| Some (e1) -> begin
(let _27_368 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'b')
end))
in (let f = (fun ( writer ) ( _27_376 ) -> (match (_27_376) with
| (p, eopt, e) -> begin
(let _27_377 = (serialize_pat writer p)
in (let _27_379 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _27_381 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _27_383 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, l)) -> begin
(let _27_390 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (let _27_392 = (serialize_exp writer e)
in (let _27_394 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _27_400 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _27_402 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _27_406 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _27_409 -> begin
(raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, s)) -> begin
(let _27_416 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _27_418 = (serialize_exp writer e)
in (serialize_meta_source_info writer s)))
end))
and serialize_meta_source_info = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Data_app -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.Sequence -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'b')
end
| Microsoft_FStar_Absyn_Syntax.Primop -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'c')
end
| Microsoft_FStar_Absyn_Syntax.MaskedEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'd')
end))
and serialize_exp = (fun ( writer ) ( ast ) -> (let _93_290 = (Microsoft_FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _93_290)))
and serialize_btvdef = (fun ( writer ) ( ast ) -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun ( writer ) ( ast ) -> (serialize_bvdef writer ast))
and serialize_pat' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _27_436 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _27_440 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((v, _27_444, l)) -> begin
(let _27_448 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_450 = (serialize_fvvar writer v)
in (serialize_list writer (fun ( w ) ( _27_455 ) -> (match (_27_455) with
| (p, b) -> begin
(let _27_456 = (serialize_pat w p)
in (w.Support.Microsoft.FStar.Util.write_bool b))
end)) l)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (v) -> begin
(let _27_460 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _27_464 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _27_468 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _27_472 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((v, e)) -> begin
(let _27_478 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _27_480 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((v, t)) -> begin
(let _27_486 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (let _27_488 = (serialize_btvar writer v)
in (serialize_typ writer t)))
end))
and serialize_pat = (fun ( writer ) ( ast ) -> (serialize_withinfo_t writer serialize_pat' (fun ( w ) ( kt ) -> ()) ast))
and serialize_knd' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.Kind_effect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'b')
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((ka, k)) -> begin
(let _27_502 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_504 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _27_510 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_512 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((bs, k)) -> begin
(let _27_518 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_520 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'f')
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(raise (Err ("knd\' serialization unimplemented:1")))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_27_528, _27_530, _27_532)) -> begin
(raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun ( writer ) ( ast ) -> (let _93_307 = (Microsoft_FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _93_307)))
and serialize_kabbrev = (fun ( writer ) ( ast ) -> (let _27_539 = (serialize_lident writer (Support.Prims.fst ast))
in (serialize_args writer (Support.Prims.snd ast))))
and serialize_lbname = (fun ( writer ) ( ast ) -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun ( writer ) ( ast ) -> (let f = (fun ( writer ) ( lb ) -> (let _27_548 = (serialize_lbname writer lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _27_550 = (serialize_lident writer lb.Microsoft_FStar_Absyn_Syntax.lbeff)
in (let _27_552 = (serialize_typ writer lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.Microsoft_FStar_Absyn_Syntax.lbdef)))))
in (let _27_554 = (writer.Support.Microsoft.FStar.Util.write_bool (Support.Prims.fst ast))
in (serialize_list writer f (Support.Prims.snd ast)))))
and serialize_fvar = (fun ( writer ) ( ast ) -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun ( writer ) ( ast ) -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun ( writer ) ( ast ) -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun ( writer ) ( ast ) -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun ( writer ) ( ast ) -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_358 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_btvar (_93_358))
end
| 'b' -> begin
(let _93_359 = (deserialize_ftvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_const (_93_359))
end
| 'c' -> begin
(let _93_362 = (let _93_361 = (deserialize_binders reader)
in (let _93_360 = (deserialize_comp reader)
in (_93_361, _93_360)))
in Microsoft_FStar_Absyn_Syntax.Typ_fun (_93_362))
end
| 'd' -> begin
(let _93_365 = (let _93_364 = (deserialize_bvvar reader)
in (let _93_363 = (deserialize_typ reader)
in (_93_364, _93_363)))
in Microsoft_FStar_Absyn_Syntax.Typ_refine (_93_365))
end
| 'e' -> begin
(let _93_368 = (let _93_367 = (deserialize_typ reader)
in (let _93_366 = (deserialize_args reader)
in (_93_367, _93_366)))
in Microsoft_FStar_Absyn_Syntax.Typ_app (_93_368))
end
| 'f' -> begin
(let _93_371 = (let _93_370 = (deserialize_binders reader)
in (let _93_369 = (deserialize_typ reader)
in (_93_370, _93_369)))
in Microsoft_FStar_Absyn_Syntax.Typ_lam (_93_371))
end
| 'g' -> begin
(let _93_374 = (let _93_373 = (deserialize_typ reader)
in (let _93_372 = (deserialize_knd reader)
in (_93_373, _93_372)))
in Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_93_374))
end
| 'h' -> begin
(let _93_375 = (deserialize_meta_t reader)
in Microsoft_FStar_Absyn_Syntax.Typ_meta (_93_375))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _27_577 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_379 = (let _93_378 = (deserialize_typ reader)
in (let _93_377 = (deserialize_list reader deserialize_arg)
in (_93_378, _93_377)))
in Microsoft_FStar_Absyn_Syntax.Meta_pattern (_93_379))
end
| 'b' -> begin
(let _93_382 = (let _93_381 = (deserialize_typ reader)
in (let _93_380 = (deserialize_lident reader)
in (_93_381, _93_380)))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_93_382))
end
| 'c' -> begin
(let _93_386 = (let _93_385 = (deserialize_typ reader)
in (let _93_384 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (let _93_383 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_93_385, _93_384, Microsoft_FStar_Absyn_Syntax.dummyRange, _93_383))))
in Microsoft_FStar_Absyn_Syntax.Meta_labeled (_93_386))
end
| _27_583 -> begin
(parse_error ())
end))
and deserialize_arg = (fun ( reader ) -> (let _93_390 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _93_389 = (let _93_388 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _93_388))
in (_93_390, _93_389))))
and deserialize_args = (fun ( reader ) -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun ( reader ) -> (let _93_395 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _93_394 = (let _93_393 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _93_393))
in (_93_395, _93_394))))
and deserialize_binders = (fun ( reader ) -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun ( reader ) -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun ( reader ) -> (let _93_402 = (deserialize_lident reader)
in (let _93_401 = (deserialize_typ reader)
in (let _93_400 = (deserialize_args reader)
in (let _93_399 = (deserialize_list reader deserialize_cflags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _93_402; Microsoft_FStar_Absyn_Syntax.result_typ = _93_401; Microsoft_FStar_Absyn_Syntax.effect_args = _93_400; Microsoft_FStar_Absyn_Syntax.flags = _93_399})))))
and deserialize_comp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_404 = (deserialize_typ reader)
in Microsoft_FStar_Absyn_Syntax.Total (_93_404))
end
| 'b' -> begin
(let _93_405 = (deserialize_comp_typ reader)
in Microsoft_FStar_Absyn_Syntax.Comp (_93_405))
end
| _27_594 -> begin
(parse_error ())
end))
and deserialize_comp = (fun ( reader ) -> (deserialize_syntax reader deserialize_comp' ()))
and deserialize_cflags = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.TOTAL
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.MLEFFECT
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.RETURN
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.LEMMA
end
| 'g' -> begin
(let _93_408 = (deserialize_exp reader)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_93_408))
end
| _27_605 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_410 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Exp_bvar (_93_410))
end
| 'b' -> begin
(let _93_414 = (let _93_413 = (deserialize_fvvar reader)
in (let _93_412 = (let _27_609 = (let _93_411 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Support.Prims.ignore _93_411))
in None)
in (_93_413, _93_412)))
in Microsoft_FStar_Absyn_Syntax.Exp_fvar (_93_414))
end
| 'c' -> begin
(let _93_415 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Exp_constant (_93_415))
end
| 'd' -> begin
(let _93_418 = (let _93_417 = (deserialize_binders reader)
in (let _93_416 = (deserialize_exp reader)
in (_93_417, _93_416)))
in Microsoft_FStar_Absyn_Syntax.Exp_abs (_93_418))
end
| 'e' -> begin
(let _93_421 = (let _93_420 = (deserialize_exp reader)
in (let _93_419 = (deserialize_args reader)
in (_93_420, _93_419)))
in Microsoft_FStar_Absyn_Syntax.Exp_app (_93_421))
end
| 'f' -> begin
(let g = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_424 = (deserialize_exp reader)
in Some (_93_424))
end
| 'b' -> begin
None
end
| _27_620 -> begin
(parse_error ())
end))
in (let f = (fun ( reader ) -> (let _93_429 = (deserialize_pat reader)
in (let _93_428 = (g reader)
in (let _93_427 = (deserialize_exp reader)
in (_93_429, _93_428, _93_427)))))
in (let _93_432 = (let _93_431 = (deserialize_exp reader)
in (let _93_430 = (deserialize_list reader f)
in (_93_431, _93_430)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (_93_432))))
end
| 'g' -> begin
(let _93_436 = (let _93_435 = (deserialize_exp reader)
in (let _93_434 = (deserialize_typ reader)
in (let _93_433 = (deserialize_option reader deserialize_lident)
in (_93_435, _93_434, _93_433))))
in Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_93_436))
end
| 'h' -> begin
(let _93_439 = (let _93_438 = (deserialize_letbindings reader)
in (let _93_437 = (deserialize_exp reader)
in (_93_438, _93_437)))
in Microsoft_FStar_Absyn_Syntax.Exp_let (_93_439))
end
| 'i' -> begin
(let _93_440 = (deserialize_meta_e reader)
in Microsoft_FStar_Absyn_Syntax.Exp_meta (_93_440))
end
| _27_627 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_444 = (let _93_443 = (deserialize_exp reader)
in (let _93_442 = (deserialize_meta_source_info reader)
in (_93_443, _93_442)))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_93_444))
end
| _27_631 -> begin
(parse_error ())
end))
and deserialize_meta_source_info = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Data_app
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Sequence
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Primop
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.MaskedEffect
end
| _27_638 -> begin
(parse_error ())
end))
and deserialize_exp = (fun ( reader ) -> (deserialize_syntax reader deserialize_exp' Microsoft_FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun ( reader ) -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun ( reader ) -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_450 = (deserialize_list reader deserialize_pat)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_93_450))
end
| 'b' -> begin
(let _93_451 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Pat_constant (_93_451))
end
| 'c' -> begin
(let _93_457 = (let _93_456 = (deserialize_fvvar reader)
in (let _93_455 = (deserialize_list reader (fun ( r ) -> (let _93_454 = (deserialize_pat r)
in (let _93_453 = (r.Support.Microsoft.FStar.Util.read_bool ())
in (_93_454, _93_453)))))
in (_93_456, None, _93_455)))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_93_457))
end
| 'd' -> begin
(let _93_458 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_var (_93_458))
end
| 'e' -> begin
(let _93_459 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_93_459))
end
| 'f' -> begin
(let _93_460 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_93_460))
end
| 'g' -> begin
(let _93_461 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_93_461))
end
| 'h' -> begin
(let _93_464 = (let _93_463 = (deserialize_bvvar reader)
in (let _93_462 = (deserialize_exp reader)
in (_93_463, _93_462)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_93_464))
end
| 'i' -> begin
(let _93_467 = (let _93_466 = (deserialize_btvar reader)
in (let _93_465 = (deserialize_typ reader)
in (_93_466, _93_465)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_93_467))
end
| _27_654 -> begin
(parse_error ())
end))
and deserialize_pat = (fun ( reader ) -> (deserialize_withinfo_t reader deserialize_pat' (fun ( r ) -> None)))
and deserialize_knd' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_type
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_effect
end
| 'c' -> begin
(let _93_473 = (let _93_472 = (deserialize_kabbrev reader)
in (let _93_471 = (deserialize_knd reader)
in (_93_472, _93_471)))
in Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_93_473))
end
| 'd' -> begin
(let _93_476 = (let _93_475 = (deserialize_binders reader)
in (let _93_474 = (deserialize_knd reader)
in (_93_475, _93_474)))
in Microsoft_FStar_Absyn_Syntax.Kind_arrow (_93_476))
end
| 'e' -> begin
(let _93_479 = (let _93_478 = (deserialize_binders reader)
in (let _93_477 = (deserialize_knd reader)
in (_93_478, _93_477)))
in Microsoft_FStar_Absyn_Syntax.Kind_lam (_93_479))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _27_665 -> begin
(parse_error ())
end))
and deserialize_knd = (fun ( reader ) -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun ( reader ) -> (let _93_483 = (deserialize_lident reader)
in (let _93_482 = (deserialize_args reader)
in (_93_483, _93_482))))
and deserialize_lbname = (fun ( reader ) -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun ( reader ) -> (let f = (fun ( reader ) -> (let _93_491 = (deserialize_lbname reader)
in (let _93_490 = (deserialize_typ reader)
in (let _93_489 = (deserialize_lident reader)
in (let _93_488 = (deserialize_exp reader)
in {Microsoft_FStar_Absyn_Syntax.lbname = _93_491; Microsoft_FStar_Absyn_Syntax.lbtyp = _93_490; Microsoft_FStar_Absyn_Syntax.lbeff = _93_489; Microsoft_FStar_Absyn_Syntax.lbdef = _93_488})))))
in (let _93_493 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (let _93_492 = (deserialize_list reader f)
in (_93_493, _93_492)))))
and deserialize_fvar = (fun ( reader ) -> (deserialize_either reader deserialize_btvdef deserialize_bvvdef))
and deserialize_btvar = (fun ( reader ) -> (deserialize_bvar None reader deserialize_knd))
and deserialize_bvvar = (fun ( reader ) -> (deserialize_bvar None reader deserialize_typ))
and deserialize_ftvar = (fun ( reader ) -> (deserialize_var reader deserialize_knd))
and deserialize_fvvar = (fun ( reader ) -> (deserialize_var reader deserialize_typ))

let serialize_formula = serialize_typ

let deserialize_formula = deserialize_typ

let serialize_qualifier = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Private -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'c')
end
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'g')
end
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'h')
end
| Microsoft_FStar_Absyn_Syntax.Discriminator (lid) -> begin
(let _27_685 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_lident writer lid))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((lid, v)) -> begin
(let _27_691 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (let _27_693 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| Microsoft_FStar_Absyn_Syntax.RecordType (l) -> begin
(let _27_697 = (writer.Support.Microsoft.FStar.Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _27_701 = (writer.Support.Microsoft.FStar.Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'm')
end
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'o')
end
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _27_707 = (writer.Support.Microsoft.FStar.Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.TotalEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'q')
end
| _27_711 -> begin
(Support.All.failwith "Unexpected qualifier")
end))

let deserialize_qualifier = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Private
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Assumption
end
| 'g' -> begin
Microsoft_FStar_Absyn_Syntax.Logic
end
| 'h' -> begin
Microsoft_FStar_Absyn_Syntax.Opaque
end
| 'i' -> begin
(let _93_508 = (deserialize_lident reader)
in Microsoft_FStar_Absyn_Syntax.Discriminator (_93_508))
end
| 'j' -> begin
(let _93_511 = (let _93_510 = (deserialize_lident reader)
in (let _93_509 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_93_510, _93_509)))
in Microsoft_FStar_Absyn_Syntax.Projector (_93_511))
end
| 'k' -> begin
(let _93_512 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordType (_93_512))
end
| 'l' -> begin
(let _93_513 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordConstructor (_93_513))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _93_515 = (deserialize_option reader deserialize_lident)
in (Support.All.pipe_right _93_515 (fun ( _93_514 ) -> Microsoft_FStar_Absyn_Syntax.DefaultEffect (_93_514))))
end
| 'q' -> begin
Microsoft_FStar_Absyn_Syntax.TotalEffect
end
| _27_726 -> begin
(parse_error ())
end))

let serialize_tycon = (fun ( writer ) ( _27_731 ) -> (match (_27_731) with
| (lid, bs, k) -> begin
(let _27_732 = (serialize_lident writer lid)
in (let _27_734 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun ( reader ) -> (let _93_524 = (deserialize_lident reader)
in (let _93_523 = (deserialize_binders reader)
in (let _93_522 = (deserialize_knd reader)
in (_93_524, _93_523, _93_522)))))

let serialize_monad_abbrev = (fun ( writer ) ( ast ) -> (let _27_739 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _27_741 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun ( reader ) -> (let _93_533 = (deserialize_lident reader)
in (let _93_532 = (deserialize_binders reader)
in (let _93_531 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mabbrev = _93_533; Microsoft_FStar_Absyn_Syntax.parms = _93_532; Microsoft_FStar_Absyn_Syntax.def = _93_531}))))

let serialize_sub_effect = (fun ( writer ) ( ast ) -> (let _27_746 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _27_748 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun ( reader ) -> (let _93_542 = (deserialize_lident reader)
in (let _93_541 = (deserialize_lident reader)
in (let _93_540 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.source = _93_542; Microsoft_FStar_Absyn_Syntax.target = _93_541; Microsoft_FStar_Absyn_Syntax.lift = _93_540}))))

let rec serialize_new_effect = (fun ( writer ) ( ast ) -> (let _27_753 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mname)
in (let _27_755 = (serialize_list writer serialize_binder ast.Microsoft_FStar_Absyn_Syntax.binders)
in (let _27_757 = (serialize_list writer serialize_qualifier ast.Microsoft_FStar_Absyn_Syntax.qualifiers)
in (let _27_759 = (serialize_knd writer ast.Microsoft_FStar_Absyn_Syntax.signature)
in (let _27_761 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ret)
in (let _27_763 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _27_765 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _27_767 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _27_769 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _27_771 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _27_773 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _27_775 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _27_777 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _27_779 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _27_781 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _27_783 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _27_785 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_27_790) -> begin
(Support.All.failwith "NYI")
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, bs, k, l1, l2, qs, _27_799)) -> begin
(let _27_802 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _27_804 = (serialize_lident writer lid)
in (let _27_806 = (serialize_binders writer bs)
in (let _27_808 = (serialize_knd writer k)
in (let _27_810 = (serialize_list writer serialize_lident l1)
in (let _27_812 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, bs, k, t, qs, _27_820)) -> begin
(let _27_823 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _27_825 = (serialize_lident writer lid)
in (let _27_827 = (serialize_binders writer bs)
in (let _27_829 = (serialize_knd writer k)
in (let _27_831 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid1, t, tyc, qs, mutuals, _27_839)) -> begin
(let t' = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(let _93_552 = (let _93_551 = (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))
in (f, _93_551))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _93_552 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _27_848 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_850 = (serialize_lident writer lid1)
in (let _27_852 = (serialize_typ writer t')
in (let _27_854 = (serialize_tycon writer tyc)
in (let _27_856 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, qs, _27_862)) -> begin
(let _27_865 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_867 = (serialize_lident writer lid)
in (let _27_869 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, fml, qs, _27_875)) -> begin
(let _27_878 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_880 = (serialize_lident writer lid)
in (let _27_882 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _27_886, l, quals)) -> begin
(let _27_891 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _27_893 = (serialize_letbindings writer lbs)
in (let _27_895 = (serialize_list writer serialize_lident l)
in (let _93_554 = (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _27_1 ) -> (match (_27_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _27_900 -> begin
false
end))))
in (writer.Support.Microsoft.FStar.Util.write_bool _93_554)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _27_903)) -> begin
(let _27_906 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_exp writer e))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((l, qs, lids, _27_912)) -> begin
(let _27_915 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _27_917 = (serialize_list writer serialize_sigelt l)
in (let _27_919 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _27_923)) -> begin
(let _27_926 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_new_effect writer n))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, bs, c, qs, _27_933)) -> begin
(let _27_936 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (let _27_938 = (serialize_lident writer lid)
in (let _27_940 = (serialize_binders writer bs)
in (let _27_942 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((se, r)) -> begin
(let _27_948 = (writer.Support.Microsoft.FStar.Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _27_954)) -> begin
(let _27_957 = (writer.Support.Microsoft.FStar.Util.write_char 'l')
in (let _27_959 = (serialize_lident writer l)
in (let _27_961 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun ( reader ) -> (let _93_575 = (deserialize_lident reader)
in (let _93_574 = (deserialize_list reader deserialize_binder)
in (let _93_573 = (deserialize_list reader deserialize_qualifier)
in (let _93_572 = (deserialize_knd reader)
in (let _93_571 = (deserialize_typ reader)
in (let _93_570 = (deserialize_typ reader)
in (let _93_569 = (deserialize_typ reader)
in (let _93_568 = (deserialize_typ reader)
in (let _93_567 = (deserialize_typ reader)
in (let _93_566 = (deserialize_typ reader)
in (let _93_565 = (deserialize_typ reader)
in (let _93_564 = (deserialize_typ reader)
in (let _93_563 = (deserialize_typ reader)
in (let _93_562 = (deserialize_typ reader)
in (let _93_561 = (deserialize_typ reader)
in (let _93_560 = (deserialize_typ reader)
in (let _93_559 = (deserialize_typ reader)
in (let _93_558 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mname = _93_575; Microsoft_FStar_Absyn_Syntax.binders = _93_574; Microsoft_FStar_Absyn_Syntax.qualifiers = _93_573; Microsoft_FStar_Absyn_Syntax.signature = _93_572; Microsoft_FStar_Absyn_Syntax.ret = _93_571; Microsoft_FStar_Absyn_Syntax.bind_wp = _93_570; Microsoft_FStar_Absyn_Syntax.bind_wlp = _93_569; Microsoft_FStar_Absyn_Syntax.if_then_else = _93_568; Microsoft_FStar_Absyn_Syntax.ite_wp = _93_567; Microsoft_FStar_Absyn_Syntax.ite_wlp = _93_566; Microsoft_FStar_Absyn_Syntax.wp_binop = _93_565; Microsoft_FStar_Absyn_Syntax.wp_as_type = _93_564; Microsoft_FStar_Absyn_Syntax.close_wp = _93_563; Microsoft_FStar_Absyn_Syntax.close_wp_t = _93_562; Microsoft_FStar_Absyn_Syntax.assert_p = _93_561; Microsoft_FStar_Absyn_Syntax.assume_p = _93_560; Microsoft_FStar_Absyn_Syntax.null_wp = _93_559; Microsoft_FStar_Absyn_Syntax.trivial = _93_558})))))))))))))))))))
and deserialize_sigelt = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _93_583 = (let _93_582 = (deserialize_lident reader)
in (let _93_581 = (deserialize_binders reader)
in (let _93_580 = (deserialize_knd reader)
in (let _93_579 = (deserialize_list reader deserialize_lident)
in (let _93_578 = (deserialize_list reader deserialize_lident)
in (let _93_577 = (deserialize_list reader deserialize_qualifier)
in (_93_582, _93_581, _93_580, _93_579, _93_578, _93_577, Microsoft_FStar_Absyn_Syntax.dummyRange)))))))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_93_583))
end
| 'b' -> begin
(let _93_589 = (let _93_588 = (deserialize_lident reader)
in (let _93_587 = (deserialize_binders reader)
in (let _93_586 = (deserialize_knd reader)
in (let _93_585 = (deserialize_typ reader)
in (let _93_584 = (deserialize_list reader deserialize_qualifier)
in (_93_588, _93_587, _93_586, _93_585, _93_584, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_93_589))
end
| 'c' -> begin
(let _93_595 = (let _93_594 = (deserialize_lident reader)
in (let _93_593 = (deserialize_typ reader)
in (let _93_592 = (deserialize_tycon reader)
in (let _93_591 = (deserialize_list reader deserialize_qualifier)
in (let _93_590 = (deserialize_list reader deserialize_lident)
in (_93_594, _93_593, _93_592, _93_591, _93_590, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_93_595))
end
| 'd' -> begin
(let _93_599 = (let _93_598 = (deserialize_lident reader)
in (let _93_597 = (deserialize_typ reader)
in (let _93_596 = (deserialize_list reader deserialize_qualifier)
in (_93_598, _93_597, _93_596, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_93_599))
end
| 'e' -> begin
(let _93_603 = (let _93_602 = (deserialize_lident reader)
in (let _93_601 = (deserialize_formula reader)
in (let _93_600 = (deserialize_list reader deserialize_qualifier)
in (_93_602, _93_601, _93_600, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_93_603))
end
| 'f' -> begin
(let _93_607 = (let _93_606 = (deserialize_letbindings reader)
in (let _93_605 = (deserialize_list reader deserialize_lident)
in (let _93_604 = (match ((reader.Support.Microsoft.FStar.Util.read_bool ())) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end
| false -> begin
[]
end)
in (_93_606, Microsoft_FStar_Absyn_Syntax.dummyRange, _93_605, _93_604))))
in Microsoft_FStar_Absyn_Syntax.Sig_let (_93_607))
end
| 'g' -> begin
(let _93_609 = (let _93_608 = (deserialize_exp reader)
in (_93_608, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_main (_93_609))
end
| 'h' -> begin
(let _93_613 = (let _93_612 = (deserialize_list reader deserialize_sigelt)
in (let _93_611 = (deserialize_list reader deserialize_qualifier)
in (let _93_610 = (deserialize_list reader deserialize_lident)
in (_93_612, _93_611, _93_610, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_93_613))
end
| 'i' -> begin
(let _93_615 = (let _93_614 = (deserialize_new_effect reader)
in (_93_614, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_93_615))
end
| ('j') | ('k') | ('l') -> begin
(Support.All.failwith "TODO")
end
| _27_978 -> begin
(parse_error ())
end))

let serialize_sigelts = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun ( reader ) -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun ( writer ) ( ast ) -> (let _27_984 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.name)
in (let _27_986 = (serialize_sigelts writer [])
in (let _27_988 = (serialize_sigelts writer ast.Microsoft_FStar_Absyn_Syntax.exports)
in (writer.Support.Microsoft.FStar.Util.write_bool ast.Microsoft_FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun ( reader ) -> (let m = (let _93_631 = (deserialize_lident reader)
in (let _93_630 = (deserialize_sigelts reader)
in (let _93_629 = (deserialize_sigelts reader)
in (let _93_628 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in {Microsoft_FStar_Absyn_Syntax.name = _93_631; Microsoft_FStar_Absyn_Syntax.declarations = _93_630; Microsoft_FStar_Absyn_Syntax.exports = _93_629; Microsoft_FStar_Absyn_Syntax.is_interface = _93_628; Microsoft_FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _27_992 = m
in {Microsoft_FStar_Absyn_Syntax.name = _27_992.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _27_992.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _27_992.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _27_992.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




