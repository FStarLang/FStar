
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
(let _70_11973 = (f reader)
in Some (_70_11973))
end)))

let serialize_list = (fun ( writer ) ( f ) ( l ) -> (let _27_22 = (writer.Support.Microsoft.FStar.Util.write_int (Support.List.length l))
in (Support.List.iter (fun ( elt ) -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_int ())
in (let rec helper = (fun ( accum ) ( n ) -> (match ((n = 0)) with
| true -> begin
accum
end
| false -> begin
(let _70_11994 = (let _70_11993 = (f reader)
in (_70_11993)::accum)
in (helper _70_11994 (n - 1)))
end))
in (helper [] n))))

let serialize_ident = (fun ( writer ) ( ast ) -> (writer.Support.Microsoft.FStar.Util.write_string ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun ( reader ) -> (let _70_12002 = (let _70_12001 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (_70_12001, Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _70_12002)))

let serialize_LongIdent = (fun ( writer ) ( ast ) -> (let _27_37 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun ( reader ) -> (let _70_12012 = (let _70_12011 = (deserialize_list reader deserialize_ident)
in (let _70_12010 = (let _70_12009 = (deserialize_ident reader)
in (_70_12009)::[])
in (Support.List.append _70_12011 _70_12010)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _70_12012)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun ( writer ) ( s_v ) ( s_sort ) ( ast ) -> (let _27_46 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun ( reader ) ( ds_v ) ( ds_sort ) -> (let _70_12042 = (ds_v reader)
in (let _70_12041 = (ds_sort reader)
in {Microsoft_FStar_Absyn_Syntax.v = _70_12042; Microsoft_FStar_Absyn_Syntax.sort = _70_12041; Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun ( writer ) ( ast ) -> (let _27_63 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ( ghost ) ( reader ) -> (let _70_12062 = (deserialize_ident reader)
in (let _70_12061 = (deserialize_ident reader)
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_12062; Microsoft_FStar_Absyn_Syntax.realname = _70_12061})))

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
(let _70_12084 = (reader.Support.Microsoft.FStar.Util.read_byte ())
in Microsoft_FStar_Absyn_Syntax.Const_uint8 (_70_12084))
end
| 'c' -> begin
(let _70_12085 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in Microsoft_FStar_Absyn_Syntax.Const_bool (_70_12085))
end
| 'd' -> begin
(let _70_12086 = (reader.Support.Microsoft.FStar.Util.read_int32 ())
in Microsoft_FStar_Absyn_Syntax.Const_int32 (_70_12086))
end
| 'e' -> begin
(let _70_12087 = (reader.Support.Microsoft.FStar.Util.read_int64 ())
in Microsoft_FStar_Absyn_Syntax.Const_int64 (_70_12087))
end
| 'f' -> begin
(let _70_12088 = (reader.Support.Microsoft.FStar.Util.read_char ())
in Microsoft_FStar_Absyn_Syntax.Const_char (_70_12088))
end
| 'g' -> begin
(let _70_12089 = (reader.Support.Microsoft.FStar.Util.read_double ())
in Microsoft_FStar_Absyn_Syntax.Const_float (_70_12089))
end
| 'h' -> begin
(let _70_12091 = (let _70_12090 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_70_12090, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_bytearray (_70_12091))
end
| 'i' -> begin
(let _70_12093 = (let _70_12092 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_70_12092, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_70_12093))
end
| 'j' -> begin
(let _70_12094 = (reader.Support.Microsoft.FStar.Util.read_string ())
in Microsoft_FStar_Absyn_Syntax.Const_int (_70_12094))
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
(let _70_12120 = (ds_l reader)
in Support.Microsoft.FStar.Util.Inl (_70_12120))
end
| 'b' -> begin
(let _70_12121 = (ds_r reader)
in Support.Microsoft.FStar.Util.Inr (_70_12121))
end
| _27_158 -> begin
(parse_error ())
end))

let serialize_syntax = (fun ( writer ) ( s_a ) ( ast ) -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun ( reader ) ( ds_a ) ( ds_b ) -> (let _70_12140 = (ds_a reader)
in (let _70_12139 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _70_12138 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _70_12137 = (Support.Microsoft.FStar.Util.mk_ref None)
in {Microsoft_FStar_Absyn_Syntax.n = _70_12140; Microsoft_FStar_Absyn_Syntax.tk = _70_12139; Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = _70_12138; Microsoft_FStar_Absyn_Syntax.uvs = _70_12137})))))

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
in (let _70_12207 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _70_12207))))
and serialize_args = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun ( writer ) ( ast ) -> (let _27_287 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (let _70_12212 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _70_12212))))
and serialize_binders = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun ( writer ) ( ast ) -> (let _70_12217 = (Microsoft_FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _70_12217)))
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
and serialize_exp = (fun ( writer ) ( ast ) -> (let _70_12242 = (Microsoft_FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _70_12242)))
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
and serialize_knd = (fun ( writer ) ( ast ) -> (let _70_12259 = (Microsoft_FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _70_12259)))
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
(let _70_12310 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_btvar (_70_12310))
end
| 'b' -> begin
(let _70_12311 = (deserialize_ftvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_const (_70_12311))
end
| 'c' -> begin
(let _70_12314 = (let _70_12313 = (deserialize_binders reader)
in (let _70_12312 = (deserialize_comp reader)
in (_70_12313, _70_12312)))
in Microsoft_FStar_Absyn_Syntax.Typ_fun (_70_12314))
end
| 'd' -> begin
(let _70_12317 = (let _70_12316 = (deserialize_bvvar reader)
in (let _70_12315 = (deserialize_typ reader)
in (_70_12316, _70_12315)))
in Microsoft_FStar_Absyn_Syntax.Typ_refine (_70_12317))
end
| 'e' -> begin
(let _70_12320 = (let _70_12319 = (deserialize_typ reader)
in (let _70_12318 = (deserialize_args reader)
in (_70_12319, _70_12318)))
in Microsoft_FStar_Absyn_Syntax.Typ_app (_70_12320))
end
| 'f' -> begin
(let _70_12323 = (let _70_12322 = (deserialize_binders reader)
in (let _70_12321 = (deserialize_typ reader)
in (_70_12322, _70_12321)))
in Microsoft_FStar_Absyn_Syntax.Typ_lam (_70_12323))
end
| 'g' -> begin
(let _70_12326 = (let _70_12325 = (deserialize_typ reader)
in (let _70_12324 = (deserialize_knd reader)
in (_70_12325, _70_12324)))
in Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_70_12326))
end
| 'h' -> begin
(let _70_12327 = (deserialize_meta_t reader)
in Microsoft_FStar_Absyn_Syntax.Typ_meta (_70_12327))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _27_577 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_12331 = (let _70_12330 = (deserialize_typ reader)
in (let _70_12329 = (deserialize_list reader deserialize_arg)
in (_70_12330, _70_12329)))
in Microsoft_FStar_Absyn_Syntax.Meta_pattern (_70_12331))
end
| 'b' -> begin
(let _70_12334 = (let _70_12333 = (deserialize_typ reader)
in (let _70_12332 = (deserialize_lident reader)
in (_70_12333, _70_12332)))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_70_12334))
end
| 'c' -> begin
(let _70_12338 = (let _70_12337 = (deserialize_typ reader)
in (let _70_12336 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (let _70_12335 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_70_12337, _70_12336, Microsoft_FStar_Absyn_Syntax.dummyRange, _70_12335))))
in Microsoft_FStar_Absyn_Syntax.Meta_labeled (_70_12338))
end
| _27_583 -> begin
(parse_error ())
end))
and deserialize_arg = (fun ( reader ) -> (let _70_12342 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _70_12341 = (let _70_12340 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _70_12340))
in (_70_12342, _70_12341))))
and deserialize_args = (fun ( reader ) -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun ( reader ) -> (let _70_12347 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _70_12346 = (let _70_12345 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _70_12345))
in (_70_12347, _70_12346))))
and deserialize_binders = (fun ( reader ) -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun ( reader ) -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun ( reader ) -> (let _70_12354 = (deserialize_lident reader)
in (let _70_12353 = (deserialize_typ reader)
in (let _70_12352 = (deserialize_args reader)
in (let _70_12351 = (deserialize_list reader deserialize_cflags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _70_12354; Microsoft_FStar_Absyn_Syntax.result_typ = _70_12353; Microsoft_FStar_Absyn_Syntax.effect_args = _70_12352; Microsoft_FStar_Absyn_Syntax.flags = _70_12351})))))
and deserialize_comp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_12356 = (deserialize_typ reader)
in Microsoft_FStar_Absyn_Syntax.Total (_70_12356))
end
| 'b' -> begin
(let _70_12357 = (deserialize_comp_typ reader)
in Microsoft_FStar_Absyn_Syntax.Comp (_70_12357))
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
(let _70_12360 = (deserialize_exp reader)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_70_12360))
end
| _27_605 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_12362 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Exp_bvar (_70_12362))
end
| 'b' -> begin
(let _70_12366 = (let _70_12365 = (deserialize_fvvar reader)
in (let _70_12364 = (let _27_609 = (let _70_12363 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Support.Prims.ignore _70_12363))
in None)
in (_70_12365, _70_12364)))
in Microsoft_FStar_Absyn_Syntax.Exp_fvar (_70_12366))
end
| 'c' -> begin
(let _70_12367 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Exp_constant (_70_12367))
end
| 'd' -> begin
(let _70_12370 = (let _70_12369 = (deserialize_binders reader)
in (let _70_12368 = (deserialize_exp reader)
in (_70_12369, _70_12368)))
in Microsoft_FStar_Absyn_Syntax.Exp_abs (_70_12370))
end
| 'e' -> begin
(let _70_12373 = (let _70_12372 = (deserialize_exp reader)
in (let _70_12371 = (deserialize_args reader)
in (_70_12372, _70_12371)))
in Microsoft_FStar_Absyn_Syntax.Exp_app (_70_12373))
end
| 'f' -> begin
(let g = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_12376 = (deserialize_exp reader)
in Some (_70_12376))
end
| 'b' -> begin
None
end
| _27_620 -> begin
(parse_error ())
end))
in (let f = (fun ( reader ) -> (let _70_12381 = (deserialize_pat reader)
in (let _70_12380 = (g reader)
in (let _70_12379 = (deserialize_exp reader)
in (_70_12381, _70_12380, _70_12379)))))
in (let _70_12384 = (let _70_12383 = (deserialize_exp reader)
in (let _70_12382 = (deserialize_list reader f)
in (_70_12383, _70_12382)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (_70_12384))))
end
| 'g' -> begin
(let _70_12388 = (let _70_12387 = (deserialize_exp reader)
in (let _70_12386 = (deserialize_typ reader)
in (let _70_12385 = (deserialize_option reader deserialize_lident)
in (_70_12387, _70_12386, _70_12385))))
in Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_70_12388))
end
| 'h' -> begin
(let _70_12391 = (let _70_12390 = (deserialize_letbindings reader)
in (let _70_12389 = (deserialize_exp reader)
in (_70_12390, _70_12389)))
in Microsoft_FStar_Absyn_Syntax.Exp_let (_70_12391))
end
| 'i' -> begin
(let _70_12392 = (deserialize_meta_e reader)
in Microsoft_FStar_Absyn_Syntax.Exp_meta (_70_12392))
end
| _27_627 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_12396 = (let _70_12395 = (deserialize_exp reader)
in (let _70_12394 = (deserialize_meta_source_info reader)
in (_70_12395, _70_12394)))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_12396))
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
(let _70_12402 = (deserialize_list reader deserialize_pat)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_70_12402))
end
| 'b' -> begin
(let _70_12403 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Pat_constant (_70_12403))
end
| 'c' -> begin
(let _70_12409 = (let _70_12408 = (deserialize_fvvar reader)
in (let _70_12407 = (deserialize_list reader (fun ( r ) -> (let _70_12406 = (deserialize_pat r)
in (let _70_12405 = (r.Support.Microsoft.FStar.Util.read_bool ())
in (_70_12406, _70_12405)))))
in (_70_12408, None, _70_12407)))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_12409))
end
| 'd' -> begin
(let _70_12410 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_var (_70_12410))
end
| 'e' -> begin
(let _70_12411 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_70_12411))
end
| 'f' -> begin
(let _70_12412 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_70_12412))
end
| 'g' -> begin
(let _70_12413 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_70_12413))
end
| 'h' -> begin
(let _70_12416 = (let _70_12415 = (deserialize_bvvar reader)
in (let _70_12414 = (deserialize_exp reader)
in (_70_12415, _70_12414)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_70_12416))
end
| 'i' -> begin
(let _70_12419 = (let _70_12418 = (deserialize_btvar reader)
in (let _70_12417 = (deserialize_typ reader)
in (_70_12418, _70_12417)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_70_12419))
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
(let _70_12425 = (let _70_12424 = (deserialize_kabbrev reader)
in (let _70_12423 = (deserialize_knd reader)
in (_70_12424, _70_12423)))
in Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_70_12425))
end
| 'd' -> begin
(let _70_12428 = (let _70_12427 = (deserialize_binders reader)
in (let _70_12426 = (deserialize_knd reader)
in (_70_12427, _70_12426)))
in Microsoft_FStar_Absyn_Syntax.Kind_arrow (_70_12428))
end
| 'e' -> begin
(let _70_12431 = (let _70_12430 = (deserialize_binders reader)
in (let _70_12429 = (deserialize_knd reader)
in (_70_12430, _70_12429)))
in Microsoft_FStar_Absyn_Syntax.Kind_lam (_70_12431))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _27_665 -> begin
(parse_error ())
end))
and deserialize_knd = (fun ( reader ) -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun ( reader ) -> (let _70_12435 = (deserialize_lident reader)
in (let _70_12434 = (deserialize_args reader)
in (_70_12435, _70_12434))))
and deserialize_lbname = (fun ( reader ) -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun ( reader ) -> (let f = (fun ( reader ) -> (let _70_12443 = (deserialize_lbname reader)
in (let _70_12442 = (deserialize_typ reader)
in (let _70_12441 = (deserialize_lident reader)
in (let _70_12440 = (deserialize_exp reader)
in {Microsoft_FStar_Absyn_Syntax.lbname = _70_12443; Microsoft_FStar_Absyn_Syntax.lbtyp = _70_12442; Microsoft_FStar_Absyn_Syntax.lbeff = _70_12441; Microsoft_FStar_Absyn_Syntax.lbdef = _70_12440})))))
in (let _70_12445 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (let _70_12444 = (deserialize_list reader f)
in (_70_12445, _70_12444)))))
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
(let _70_12460 = (deserialize_lident reader)
in Microsoft_FStar_Absyn_Syntax.Discriminator (_70_12460))
end
| 'j' -> begin
(let _70_12463 = (let _70_12462 = (deserialize_lident reader)
in (let _70_12461 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_70_12462, _70_12461)))
in Microsoft_FStar_Absyn_Syntax.Projector (_70_12463))
end
| 'k' -> begin
(let _70_12464 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordType (_70_12464))
end
| 'l' -> begin
(let _70_12465 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordConstructor (_70_12465))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _70_12467 = (deserialize_option reader deserialize_lident)
in (Support.All.pipe_right _70_12467 (fun ( _70_12466 ) -> Microsoft_FStar_Absyn_Syntax.DefaultEffect (_70_12466))))
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

let deserialize_tycon = (fun ( reader ) -> (let _70_12476 = (deserialize_lident reader)
in (let _70_12475 = (deserialize_binders reader)
in (let _70_12474 = (deserialize_knd reader)
in (_70_12476, _70_12475, _70_12474)))))

let serialize_monad_abbrev = (fun ( writer ) ( ast ) -> (let _27_739 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _27_741 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun ( reader ) -> (let _70_12485 = (deserialize_lident reader)
in (let _70_12484 = (deserialize_binders reader)
in (let _70_12483 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mabbrev = _70_12485; Microsoft_FStar_Absyn_Syntax.parms = _70_12484; Microsoft_FStar_Absyn_Syntax.def = _70_12483}))))

let serialize_sub_effect = (fun ( writer ) ( ast ) -> (let _27_746 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _27_748 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun ( reader ) -> (let _70_12494 = (deserialize_lident reader)
in (let _70_12493 = (deserialize_lident reader)
in (let _70_12492 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.source = _70_12494; Microsoft_FStar_Absyn_Syntax.target = _70_12493; Microsoft_FStar_Absyn_Syntax.lift = _70_12492}))))

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
(let _70_12504 = (let _70_12503 = (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))
in (f, _70_12503))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_12504 None Microsoft_FStar_Absyn_Syntax.dummyRange))
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
in (let _70_12506 = (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _27_1 ) -> (match (_27_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _27_900 -> begin
false
end))))
in (writer.Support.Microsoft.FStar.Util.write_bool _70_12506)))))
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

let rec deserialize_new_effect = (fun ( reader ) -> (let _70_12527 = (deserialize_lident reader)
in (let _70_12526 = (deserialize_list reader deserialize_binder)
in (let _70_12525 = (deserialize_list reader deserialize_qualifier)
in (let _70_12524 = (deserialize_knd reader)
in (let _70_12523 = (deserialize_typ reader)
in (let _70_12522 = (deserialize_typ reader)
in (let _70_12521 = (deserialize_typ reader)
in (let _70_12520 = (deserialize_typ reader)
in (let _70_12519 = (deserialize_typ reader)
in (let _70_12518 = (deserialize_typ reader)
in (let _70_12517 = (deserialize_typ reader)
in (let _70_12516 = (deserialize_typ reader)
in (let _70_12515 = (deserialize_typ reader)
in (let _70_12514 = (deserialize_typ reader)
in (let _70_12513 = (deserialize_typ reader)
in (let _70_12512 = (deserialize_typ reader)
in (let _70_12511 = (deserialize_typ reader)
in (let _70_12510 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mname = _70_12527; Microsoft_FStar_Absyn_Syntax.binders = _70_12526; Microsoft_FStar_Absyn_Syntax.qualifiers = _70_12525; Microsoft_FStar_Absyn_Syntax.signature = _70_12524; Microsoft_FStar_Absyn_Syntax.ret = _70_12523; Microsoft_FStar_Absyn_Syntax.bind_wp = _70_12522; Microsoft_FStar_Absyn_Syntax.bind_wlp = _70_12521; Microsoft_FStar_Absyn_Syntax.if_then_else = _70_12520; Microsoft_FStar_Absyn_Syntax.ite_wp = _70_12519; Microsoft_FStar_Absyn_Syntax.ite_wlp = _70_12518; Microsoft_FStar_Absyn_Syntax.wp_binop = _70_12517; Microsoft_FStar_Absyn_Syntax.wp_as_type = _70_12516; Microsoft_FStar_Absyn_Syntax.close_wp = _70_12515; Microsoft_FStar_Absyn_Syntax.close_wp_t = _70_12514; Microsoft_FStar_Absyn_Syntax.assert_p = _70_12513; Microsoft_FStar_Absyn_Syntax.assume_p = _70_12512; Microsoft_FStar_Absyn_Syntax.null_wp = _70_12511; Microsoft_FStar_Absyn_Syntax.trivial = _70_12510})))))))))))))))))))
and deserialize_sigelt = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_12535 = (let _70_12534 = (deserialize_lident reader)
in (let _70_12533 = (deserialize_binders reader)
in (let _70_12532 = (deserialize_knd reader)
in (let _70_12531 = (deserialize_list reader deserialize_lident)
in (let _70_12530 = (deserialize_list reader deserialize_lident)
in (let _70_12529 = (deserialize_list reader deserialize_qualifier)
in (_70_12534, _70_12533, _70_12532, _70_12531, _70_12530, _70_12529, Microsoft_FStar_Absyn_Syntax.dummyRange)))))))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_70_12535))
end
| 'b' -> begin
(let _70_12541 = (let _70_12540 = (deserialize_lident reader)
in (let _70_12539 = (deserialize_binders reader)
in (let _70_12538 = (deserialize_knd reader)
in (let _70_12537 = (deserialize_typ reader)
in (let _70_12536 = (deserialize_list reader deserialize_qualifier)
in (_70_12540, _70_12539, _70_12538, _70_12537, _70_12536, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_70_12541))
end
| 'c' -> begin
(let _70_12547 = (let _70_12546 = (deserialize_lident reader)
in (let _70_12545 = (deserialize_typ reader)
in (let _70_12544 = (deserialize_tycon reader)
in (let _70_12543 = (deserialize_list reader deserialize_qualifier)
in (let _70_12542 = (deserialize_list reader deserialize_lident)
in (_70_12546, _70_12545, _70_12544, _70_12543, _70_12542, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_70_12547))
end
| 'd' -> begin
(let _70_12551 = (let _70_12550 = (deserialize_lident reader)
in (let _70_12549 = (deserialize_typ reader)
in (let _70_12548 = (deserialize_list reader deserialize_qualifier)
in (_70_12550, _70_12549, _70_12548, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_12551))
end
| 'e' -> begin
(let _70_12555 = (let _70_12554 = (deserialize_lident reader)
in (let _70_12553 = (deserialize_formula reader)
in (let _70_12552 = (deserialize_list reader deserialize_qualifier)
in (_70_12554, _70_12553, _70_12552, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_70_12555))
end
| 'f' -> begin
(let _70_12559 = (let _70_12558 = (deserialize_letbindings reader)
in (let _70_12557 = (deserialize_list reader deserialize_lident)
in (let _70_12556 = (match ((reader.Support.Microsoft.FStar.Util.read_bool ())) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end
| false -> begin
[]
end)
in (_70_12558, Microsoft_FStar_Absyn_Syntax.dummyRange, _70_12557, _70_12556))))
in Microsoft_FStar_Absyn_Syntax.Sig_let (_70_12559))
end
| 'g' -> begin
(let _70_12561 = (let _70_12560 = (deserialize_exp reader)
in (_70_12560, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_main (_70_12561))
end
| 'h' -> begin
(let _70_12565 = (let _70_12564 = (deserialize_list reader deserialize_sigelt)
in (let _70_12563 = (deserialize_list reader deserialize_qualifier)
in (let _70_12562 = (deserialize_list reader deserialize_lident)
in (_70_12564, _70_12563, _70_12562, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_70_12565))
end
| 'i' -> begin
(let _70_12567 = (let _70_12566 = (deserialize_new_effect reader)
in (_70_12566, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_70_12567))
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

let deserialize_modul = (fun ( reader ) -> (let m = (let _70_12583 = (deserialize_lident reader)
in (let _70_12582 = (deserialize_sigelts reader)
in (let _70_12581 = (deserialize_sigelts reader)
in (let _70_12580 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in {Microsoft_FStar_Absyn_Syntax.name = _70_12583; Microsoft_FStar_Absyn_Syntax.declarations = _70_12582; Microsoft_FStar_Absyn_Syntax.exports = _70_12581; Microsoft_FStar_Absyn_Syntax.is_interface = _70_12580; Microsoft_FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _27_992 = m
in {Microsoft_FStar_Absyn_Syntax.name = _27_992.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _27_992.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _27_992.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _27_992.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




