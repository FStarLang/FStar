
exception Err of (string)

let is_Err = (fun ( _discr_ ) -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let parse_error = (fun ( _25_3 ) -> (match (()) with
| () -> begin
(failwith ("Parse error: ill-formed cache"))
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
(let _25_11 = (writer.Support.Microsoft.FStar.Util.write_char 's')
in (f writer l))
end))

let deserialize_option = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_char ())
in (match ((n = 'n')) with
| true -> begin
None
end
| false -> begin
(let _52_7063 = (f reader)
in Some (_52_7063))
end)))

let serialize_list = (fun ( writer ) ( f ) ( l ) -> (let _25_21 = (writer.Support.Microsoft.FStar.Util.write_int (Support.List.length l))
in (Support.List.iter (fun ( elt ) -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_int ())
in (let rec helper = (fun ( accum ) ( n ) -> (match ((n = 0)) with
| true -> begin
accum
end
| false -> begin
(let _52_7084 = (let _52_7083 = (f reader)
in (_52_7083)::accum)
in (helper _52_7084 (n - 1)))
end))
in (helper [] n))))

let serialize_ident = (fun ( writer ) ( ast ) -> (writer.Support.Microsoft.FStar.Util.write_string ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun ( reader ) -> (let _52_7092 = (let _52_7091 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (_52_7091, Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _52_7092)))

let serialize_LongIdent = (fun ( writer ) ( ast ) -> (let _25_36 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun ( reader ) -> (let _52_7102 = (let _52_7101 = (deserialize_list reader deserialize_ident)
in (let _52_7100 = (let _52_7099 = (deserialize_ident reader)
in (_52_7099)::[])
in (Support.List.append _52_7101 _52_7100)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _52_7102)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun ( writer ) ( s_v ) ( s_sort ) ( ast ) -> (let _25_45 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun ( reader ) ( ds_v ) ( ds_sort ) -> (let _52_7132 = (ds_v reader)
in (let _52_7131 = (ds_sort reader)
in {Microsoft_FStar_Absyn_Syntax.v = _52_7132; Microsoft_FStar_Absyn_Syntax.sort = _52_7131; Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun ( writer ) ( ast ) -> (let _25_62 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ( ghost ) ( reader ) -> (let _52_7152 = (deserialize_ident reader)
in (let _52_7151 = (deserialize_ident reader)
in {Microsoft_FStar_Absyn_Syntax.ppname = _52_7152; Microsoft_FStar_Absyn_Syntax.realname = _52_7151})))

let serialize_bvar = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

let deserialize_bvar = (fun ( ghost ) ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

let serialize_sconst = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (v) -> begin
(let _25_82 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (writer.Support.Microsoft.FStar.Util.write_byte v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (v) -> begin
(let _25_86 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (writer.Support.Microsoft.FStar.Util.write_bool v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (v) -> begin
(let _25_90 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (writer.Support.Microsoft.FStar.Util.write_int32 v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (v) -> begin
(let _25_94 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (writer.Support.Microsoft.FStar.Util.write_int64 v))
end
| Microsoft_FStar_Absyn_Syntax.Const_char (v) -> begin
(let _25_98 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (writer.Support.Microsoft.FStar.Util.write_char v))
end
| Microsoft_FStar_Absyn_Syntax.Const_float (v) -> begin
(let _25_102 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (writer.Support.Microsoft.FStar.Util.write_double v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((v, _)) -> begin
(let _25_109 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (writer.Support.Microsoft.FStar.Util.write_bytearray v))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((v, _)) -> begin
(let _25_116 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (writer.Support.Microsoft.FStar.Util.write_bytearray v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (v) -> begin
(let _25_120 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (writer.Support.Microsoft.FStar.Util.write_string v))
end))

let deserialize_sconst = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Const_unit
end
| 'b' -> begin
(let _52_7174 = (reader.Support.Microsoft.FStar.Util.read_byte ())
in Microsoft_FStar_Absyn_Syntax.Const_uint8 (_52_7174))
end
| 'c' -> begin
(let _52_7175 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in Microsoft_FStar_Absyn_Syntax.Const_bool (_52_7175))
end
| 'd' -> begin
(let _52_7176 = (reader.Support.Microsoft.FStar.Util.read_int32 ())
in Microsoft_FStar_Absyn_Syntax.Const_int32 (_52_7176))
end
| 'e' -> begin
(let _52_7177 = (reader.Support.Microsoft.FStar.Util.read_int64 ())
in Microsoft_FStar_Absyn_Syntax.Const_int64 (_52_7177))
end
| 'f' -> begin
(let _52_7178 = (reader.Support.Microsoft.FStar.Util.read_char ())
in Microsoft_FStar_Absyn_Syntax.Const_char (_52_7178))
end
| 'g' -> begin
(let _52_7179 = (reader.Support.Microsoft.FStar.Util.read_double ())
in Microsoft_FStar_Absyn_Syntax.Const_float (_52_7179))
end
| 'h' -> begin
(let _52_7181 = (let _52_7180 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_52_7180, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_bytearray (_52_7181))
end
| 'i' -> begin
(let _52_7183 = (let _52_7182 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_52_7182, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_52_7183))
end
| 'j' -> begin
(let _52_7184 = (reader.Support.Microsoft.FStar.Util.read_string ())
in Microsoft_FStar_Absyn_Syntax.Const_int (_52_7184))
end
| _ -> begin
(parse_error ())
end))

let serialize_either = (fun ( writer ) ( s_l ) ( s_r ) ( ast ) -> (match (ast) with
| Support.Microsoft.FStar.Util.Inl (v) -> begin
(let _25_143 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (s_l writer v))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _25_147 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (s_r writer v))
end))

let deserialize_either = (fun ( reader ) ( ds_l ) ( ds_r ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7210 = (ds_l reader)
in Support.Microsoft.FStar.Util.Inl (_52_7210))
end
| 'b' -> begin
(let _52_7211 = (ds_r reader)
in Support.Microsoft.FStar.Util.Inr (_52_7211))
end
| _ -> begin
(parse_error ())
end))

let serialize_syntax = (fun ( writer ) ( s_a ) ( ast ) -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun ( reader ) ( ds_a ) ( ds_b ) -> (let _52_7230 = (ds_a reader)
in (let _52_7229 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _52_7228 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _52_7227 = (Support.Microsoft.FStar.Util.mk_ref None)
in {Microsoft_FStar_Absyn_Syntax.n = _52_7230; Microsoft_FStar_Absyn_Syntax.tk = _52_7229; Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = _52_7228; Microsoft_FStar_Absyn_Syntax.uvs = _52_7227})))))

let rec serialize_typ' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _25_172 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _25_176 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_ftvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _25_182 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _25_184 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((v, t)) -> begin
(let _25_190 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _25_192 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, ars)) -> begin
(let _25_198 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _25_200 = (serialize_typ writer t)
in (let _25_202 = (serialize_args writer ars)
in (match ((let _52_7291 = (Support.ST.read Microsoft_FStar_Options.debug)
in (_52_7291 <> []))) with
| true -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, _)) -> begin
(Support.Microsoft.FStar.Util.print_string "type application node with lam\n")
end
| _ -> begin
()
end)
end
| false -> begin
()
end))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _25_216 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _25_218 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(let _25_224 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (let _25_226 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _25_230 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (serialize_meta_t writer m))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'i')
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_, _)) -> begin
(raise (Err ("typ not impl:1")))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((_, _)) -> begin
(raise (Err ("typ not impl:2")))
end))
and serialize_meta_t = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, l)) -> begin
(let _25_251 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _25_253 = (serialize_typ writer t)
in (serialize_list writer serialize_arg l)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid)) -> begin
(let _25_259 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _25_261 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, s, _, b)) -> begin
(let _25_270 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _25_272 = (serialize_typ writer t)
in (let _25_274 = (writer.Support.Microsoft.FStar.Util.write_string s)
in (writer.Support.Microsoft.FStar.Util.write_bool b))))
end
| _ -> begin
(raise (Err ("unimplemented meta_t")))
end))
and serialize_arg = (fun ( writer ) ( ast ) -> (let _25_280 = (serialize_either writer serialize_typ serialize_exp (Support.Prims.fst ast))
in (let _52_7296 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _52_7296))))
and serialize_args = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun ( writer ) ( ast ) -> (let _25_286 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (let _52_7301 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _52_7301))))
and serialize_binders = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun ( writer ) ( ast ) -> (let _52_7306 = (Microsoft_FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _52_7306)))
and serialize_comp_typ = (fun ( writer ) ( ast ) -> (let _25_294 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _25_296 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _25_298 = (serialize_args writer ast.Microsoft_FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.Microsoft_FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _25_304 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_typ writer t))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let _25_308 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
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
(let _25_322 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _25_328 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, b)) -> begin
(let _25_334 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _25_336 = (serialize_fvvar writer v)
in (writer.Support.Microsoft.FStar.Util.write_bool false)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _25_340 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let _25_346 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _25_348 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, ars)) -> begin
(let _25_354 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _25_356 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, l)) -> begin
(let g = (fun ( writer ) ( eopt ) -> (match (eopt) with
| Some (e1) -> begin
(let _25_367 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'b')
end))
in (let f = (fun ( writer ) ( _25_375 ) -> (match (_25_375) with
| (p, eopt, e) -> begin
(let _25_376 = (serialize_pat writer p)
in (let _25_378 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _25_380 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _25_382 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, l)) -> begin
(let _25_389 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (let _25_391 = (serialize_exp writer e)
in (let _25_393 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _25_399 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _25_401 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _25_405 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _ -> begin
(raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, s)) -> begin
(let _25_415 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _25_417 = (serialize_exp writer e)
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
and serialize_exp = (fun ( writer ) ( ast ) -> (let _52_7331 = (Microsoft_FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _52_7331)))
and serialize_btvdef = (fun ( writer ) ( ast ) -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun ( writer ) ( ast ) -> (serialize_bvdef writer ast))
and serialize_pat' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _25_435 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _25_439 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((v, _, l)) -> begin
(let _25_447 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _25_449 = (serialize_fvvar writer v)
in (serialize_list writer serialize_pat l)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((v, b)) -> begin
(let _25_455 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _25_457 = (serialize_bvvar writer v)
in (writer.Support.Microsoft.FStar.Util.write_bool b)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _25_461 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _25_465 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _25_469 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((v, e)) -> begin
(let _25_475 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _25_477 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((v, t)) -> begin
(let _25_483 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (let _25_485 = (serialize_btvar writer v)
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
(let _25_499 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _25_501 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _25_507 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _25_509 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((bs, k)) -> begin
(let _25_515 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _25_517 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'f')
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(raise (Err ("knd\' serialization unimplemented:1")))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_, _, _)) -> begin
(raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun ( writer ) ( ast ) -> (let _52_7346 = (Microsoft_FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _52_7346)))
and serialize_kabbrev = (fun ( writer ) ( ast ) -> (let _25_536 = (serialize_lident writer (Support.Prims.fst ast))
in (serialize_args writer (Support.Prims.snd ast))))
and serialize_lbname = (fun ( writer ) ( ast ) -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun ( writer ) ( ast ) -> (let f = (fun ( writer ) ( lb ) -> (let _25_545 = (serialize_lbname writer lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _25_547 = (serialize_lident writer lb.Microsoft_FStar_Absyn_Syntax.lbeff)
in (let _25_549 = (serialize_typ writer lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.Microsoft_FStar_Absyn_Syntax.lbdef)))))
in (let _25_551 = (writer.Support.Microsoft.FStar.Util.write_bool (Support.Prims.fst ast))
in (serialize_list writer f (Support.Prims.snd ast)))))
and serialize_fvar = (fun ( writer ) ( ast ) -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun ( writer ) ( ast ) -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun ( writer ) ( ast ) -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun ( writer ) ( ast ) -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun ( writer ) ( ast ) -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7397 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_btvar (_52_7397))
end
| 'b' -> begin
(let _52_7398 = (deserialize_ftvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_const (_52_7398))
end
| 'c' -> begin
(let _52_7401 = (let _52_7400 = (deserialize_binders reader)
in (let _52_7399 = (deserialize_comp reader)
in (_52_7400, _52_7399)))
in Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_7401))
end
| 'd' -> begin
(let _52_7404 = (let _52_7403 = (deserialize_bvvar reader)
in (let _52_7402 = (deserialize_typ reader)
in (_52_7403, _52_7402)))
in Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_7404))
end
| 'e' -> begin
(let _52_7407 = (let _52_7406 = (deserialize_typ reader)
in (let _52_7405 = (deserialize_args reader)
in (_52_7406, _52_7405)))
in Microsoft_FStar_Absyn_Syntax.Typ_app (_52_7407))
end
| 'f' -> begin
(let _52_7410 = (let _52_7409 = (deserialize_binders reader)
in (let _52_7408 = (deserialize_typ reader)
in (_52_7409, _52_7408)))
in Microsoft_FStar_Absyn_Syntax.Typ_lam (_52_7410))
end
| 'g' -> begin
(let _52_7413 = (let _52_7412 = (deserialize_typ reader)
in (let _52_7411 = (deserialize_knd reader)
in (_52_7412, _52_7411)))
in Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_52_7413))
end
| 'h' -> begin
(let _52_7414 = (deserialize_meta_t reader)
in Microsoft_FStar_Absyn_Syntax.Typ_meta (_52_7414))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7418 = (let _52_7417 = (deserialize_typ reader)
in (let _52_7416 = (deserialize_list reader deserialize_arg)
in (_52_7417, _52_7416)))
in Microsoft_FStar_Absyn_Syntax.Meta_pattern (_52_7418))
end
| 'b' -> begin
(let _52_7421 = (let _52_7420 = (deserialize_typ reader)
in (let _52_7419 = (deserialize_lident reader)
in (_52_7420, _52_7419)))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_52_7421))
end
| 'c' -> begin
(let _52_7425 = (let _52_7424 = (deserialize_typ reader)
in (let _52_7423 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (let _52_7422 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_52_7424, _52_7423, Microsoft_FStar_Absyn_Syntax.dummyRange, _52_7422))))
in Microsoft_FStar_Absyn_Syntax.Meta_labeled (_52_7425))
end
| _ -> begin
(parse_error ())
end))
and deserialize_arg = (fun ( reader ) -> (let _52_7429 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _52_7428 = (let _52_7427 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _52_7427))
in (_52_7429, _52_7428))))
and deserialize_args = (fun ( reader ) -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun ( reader ) -> (let _52_7434 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _52_7433 = (let _52_7432 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _52_7432))
in (_52_7434, _52_7433))))
and deserialize_binders = (fun ( reader ) -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun ( reader ) -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun ( reader ) -> (let _52_7441 = (deserialize_lident reader)
in (let _52_7440 = (deserialize_typ reader)
in (let _52_7439 = (deserialize_args reader)
in (let _52_7438 = (deserialize_list reader deserialize_cflags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _52_7441; Microsoft_FStar_Absyn_Syntax.result_typ = _52_7440; Microsoft_FStar_Absyn_Syntax.effect_args = _52_7439; Microsoft_FStar_Absyn_Syntax.flags = _52_7438})))))
and deserialize_comp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7443 = (deserialize_typ reader)
in Microsoft_FStar_Absyn_Syntax.Total (_52_7443))
end
| 'b' -> begin
(let _52_7444 = (deserialize_comp_typ reader)
in Microsoft_FStar_Absyn_Syntax.Comp (_52_7444))
end
| _ -> begin
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
(let _52_7447 = (deserialize_exp reader)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_52_7447))
end
| _ -> begin
(parse_error ())
end))
and deserialize_exp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7449 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Exp_bvar (_52_7449))
end
| 'b' -> begin
(let _52_7452 = (let _52_7451 = (deserialize_fvvar reader)
in (_52_7451, (let _25_606 = (let _52_7450 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Support.Prims.ignore _52_7450))
in None)))
in Microsoft_FStar_Absyn_Syntax.Exp_fvar (_52_7452))
end
| 'c' -> begin
(let _52_7453 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Exp_constant (_52_7453))
end
| 'd' -> begin
(let _52_7456 = (let _52_7455 = (deserialize_binders reader)
in (let _52_7454 = (deserialize_exp reader)
in (_52_7455, _52_7454)))
in Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_7456))
end
| 'e' -> begin
(let _52_7459 = (let _52_7458 = (deserialize_exp reader)
in (let _52_7457 = (deserialize_args reader)
in (_52_7458, _52_7457)))
in Microsoft_FStar_Absyn_Syntax.Exp_app (_52_7459))
end
| 'f' -> begin
(let g = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7462 = (deserialize_exp reader)
in Some (_52_7462))
end
| 'b' -> begin
None
end
| _ -> begin
(parse_error ())
end))
in (let f = (fun ( reader ) -> (let _52_7467 = (deserialize_pat reader)
in (let _52_7466 = (g reader)
in (let _52_7465 = (deserialize_exp reader)
in (_52_7467, _52_7466, _52_7465)))))
in (let _52_7470 = (let _52_7469 = (deserialize_exp reader)
in (let _52_7468 = (deserialize_list reader f)
in (_52_7469, _52_7468)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (_52_7470))))
end
| 'g' -> begin
(let _52_7474 = (let _52_7473 = (deserialize_exp reader)
in (let _52_7472 = (deserialize_typ reader)
in (let _52_7471 = (deserialize_option reader deserialize_lident)
in (_52_7473, _52_7472, _52_7471))))
in Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_52_7474))
end
| 'h' -> begin
(let _52_7477 = (let _52_7476 = (deserialize_letbindings reader)
in (let _52_7475 = (deserialize_exp reader)
in (_52_7476, _52_7475)))
in Microsoft_FStar_Absyn_Syntax.Exp_let (_52_7477))
end
| 'i' -> begin
(let _52_7478 = (deserialize_meta_e reader)
in Microsoft_FStar_Absyn_Syntax.Exp_meta (_52_7478))
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7482 = (let _52_7481 = (deserialize_exp reader)
in (let _52_7480 = (deserialize_meta_source_info reader)
in (_52_7481, _52_7480)))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_7482))
end
| _ -> begin
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
| _ -> begin
(parse_error ())
end))
and deserialize_exp = (fun ( reader ) -> (deserialize_syntax reader deserialize_exp' Microsoft_FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun ( reader ) -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun ( reader ) -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7488 = (deserialize_list reader deserialize_pat)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_7488))
end
| 'b' -> begin
(let _52_7489 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Pat_constant (_52_7489))
end
| 'c' -> begin
(let _52_7492 = (let _52_7491 = (deserialize_fvvar reader)
in (let _52_7490 = (deserialize_list reader deserialize_pat)
in (_52_7491, None, _52_7490)))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_7492))
end
| 'd' -> begin
(let _52_7495 = (let _52_7494 = (deserialize_bvvar reader)
in (let _52_7493 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_52_7494, _52_7493)))
in Microsoft_FStar_Absyn_Syntax.Pat_var (_52_7495))
end
| 'e' -> begin
(let _52_7496 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_52_7496))
end
| 'f' -> begin
(let _52_7497 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_52_7497))
end
| 'g' -> begin
(let _52_7498 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_52_7498))
end
| 'h' -> begin
(let _52_7501 = (let _52_7500 = (deserialize_bvvar reader)
in (let _52_7499 = (deserialize_exp reader)
in (_52_7500, _52_7499)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_52_7501))
end
| 'i' -> begin
(let _52_7504 = (let _52_7503 = (deserialize_btvar reader)
in (let _52_7502 = (deserialize_typ reader)
in (_52_7503, _52_7502)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_52_7504))
end
| _ -> begin
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
(let _52_7510 = (let _52_7509 = (deserialize_kabbrev reader)
in (let _52_7508 = (deserialize_knd reader)
in (_52_7509, _52_7508)))
in Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_52_7510))
end
| 'd' -> begin
(let _52_7513 = (let _52_7512 = (deserialize_binders reader)
in (let _52_7511 = (deserialize_knd reader)
in (_52_7512, _52_7511)))
in Microsoft_FStar_Absyn_Syntax.Kind_arrow (_52_7513))
end
| 'e' -> begin
(let _52_7516 = (let _52_7515 = (deserialize_binders reader)
in (let _52_7514 = (deserialize_knd reader)
in (_52_7515, _52_7514)))
in Microsoft_FStar_Absyn_Syntax.Kind_lam (_52_7516))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_knd = (fun ( reader ) -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun ( reader ) -> (let _52_7520 = (deserialize_lident reader)
in (let _52_7519 = (deserialize_args reader)
in (_52_7520, _52_7519))))
and deserialize_lbname = (fun ( reader ) -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun ( reader ) -> (let f = (fun ( reader ) -> (let _52_7528 = (deserialize_lbname reader)
in (let _52_7527 = (deserialize_typ reader)
in (let _52_7526 = (deserialize_lident reader)
in (let _52_7525 = (deserialize_exp reader)
in {Microsoft_FStar_Absyn_Syntax.lbname = _52_7528; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_7527; Microsoft_FStar_Absyn_Syntax.lbeff = _52_7526; Microsoft_FStar_Absyn_Syntax.lbdef = _52_7525})))))
in (let _52_7530 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (let _52_7529 = (deserialize_list reader f)
in (_52_7530, _52_7529)))))
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
(let _25_681 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_lident writer lid))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((lid, v)) -> begin
(let _25_687 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (let _25_689 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| Microsoft_FStar_Absyn_Syntax.RecordType (l) -> begin
(let _25_693 = (writer.Support.Microsoft.FStar.Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _25_697 = (writer.Support.Microsoft.FStar.Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'm')
end
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'o')
end
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _25_703 = (writer.Support.Microsoft.FStar.Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.TotalEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'q')
end
| _ -> begin
(failwith ("Unexpected qualifier"))
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
(let _52_7545 = (deserialize_lident reader)
in Microsoft_FStar_Absyn_Syntax.Discriminator (_52_7545))
end
| 'j' -> begin
(let _52_7548 = (let _52_7547 = (deserialize_lident reader)
in (let _52_7546 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_52_7547, _52_7546)))
in Microsoft_FStar_Absyn_Syntax.Projector (_52_7548))
end
| 'k' -> begin
(let _52_7549 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordType (_52_7549))
end
| 'l' -> begin
(let _52_7550 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordConstructor (_52_7550))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _52_7552 = (deserialize_option reader deserialize_lident)
in (Support.Prims.pipe_right _52_7552 (fun ( _52_7551 ) -> Microsoft_FStar_Absyn_Syntax.DefaultEffect (_52_7551))))
end
| 'q' -> begin
Microsoft_FStar_Absyn_Syntax.TotalEffect
end
| _ -> begin
(parse_error ())
end))

let serialize_tycon = (fun ( writer ) ( _25_727 ) -> (match (_25_727) with
| (lid, bs, k) -> begin
(let _25_728 = (serialize_lident writer lid)
in (let _25_730 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun ( reader ) -> (let _52_7561 = (deserialize_lident reader)
in (let _52_7560 = (deserialize_binders reader)
in (let _52_7559 = (deserialize_knd reader)
in (_52_7561, _52_7560, _52_7559)))))

let serialize_monad_abbrev = (fun ( writer ) ( ast ) -> (let _25_735 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _25_737 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun ( reader ) -> (let _52_7570 = (deserialize_lident reader)
in (let _52_7569 = (deserialize_binders reader)
in (let _52_7568 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mabbrev = _52_7570; Microsoft_FStar_Absyn_Syntax.parms = _52_7569; Microsoft_FStar_Absyn_Syntax.def = _52_7568}))))

let serialize_sub_effect = (fun ( writer ) ( ast ) -> (let _25_742 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _25_744 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun ( reader ) -> (let _52_7579 = (deserialize_lident reader)
in (let _52_7578 = (deserialize_lident reader)
in (let _52_7577 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.source = _52_7579; Microsoft_FStar_Absyn_Syntax.target = _52_7578; Microsoft_FStar_Absyn_Syntax.lift = _52_7577}))))

let rec serialize_new_effect = (fun ( writer ) ( ast ) -> (let _25_749 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mname)
in (let _25_751 = (serialize_list writer serialize_binder ast.Microsoft_FStar_Absyn_Syntax.binders)
in (let _25_753 = (serialize_list writer serialize_qualifier ast.Microsoft_FStar_Absyn_Syntax.qualifiers)
in (let _25_755 = (serialize_knd writer ast.Microsoft_FStar_Absyn_Syntax.signature)
in (let _25_757 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ret)
in (let _25_759 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _25_761 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _25_763 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _25_765 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _25_767 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _25_769 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _25_771 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _25_773 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _25_775 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _25_777 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _25_779 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _25_781 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_) -> begin
(failwith ("NYI"))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, bs, k, l1, l2, qs, _)) -> begin
(let _25_798 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _25_800 = (serialize_lident writer lid)
in (let _25_802 = (serialize_binders writer bs)
in (let _25_804 = (serialize_knd writer k)
in (let _25_806 = (serialize_list writer serialize_lident l1)
in (let _25_808 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, bs, k, t, qs, _)) -> begin
(let _25_819 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _25_821 = (serialize_lident writer lid)
in (let _25_823 = (serialize_binders writer bs)
in (let _25_825 = (serialize_knd writer k)
in (let _25_827 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid1, t, tyc, qs, mutuals, _)) -> begin
(let t' = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(let _52_7589 = (let _52_7588 = (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))
in (f, _52_7588))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_7589 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _25_844 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _25_846 = (serialize_lident writer lid1)
in (let _25_848 = (serialize_typ writer t')
in (let _25_850 = (serialize_tycon writer tyc)
in (let _25_852 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, qs, _)) -> begin
(let _25_861 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _25_863 = (serialize_lident writer lid)
in (let _25_865 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, fml, qs, _)) -> begin
(let _25_874 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _25_876 = (serialize_lident writer lid)
in (let _25_878 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _, l, quals)) -> begin
(let _25_887 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _25_889 = (serialize_letbindings writer lbs)
in (let _25_891 = (serialize_list writer serialize_lident l)
in (let _52_7591 = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _25_1 ) -> (match (_25_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))))
in (writer.Support.Microsoft.FStar.Util.write_bool _52_7591)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _)) -> begin
(let _25_902 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_exp writer e))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((l, qs, lids, _)) -> begin
(let _25_911 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _25_913 = (serialize_list writer serialize_sigelt l)
in (let _25_915 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _)) -> begin
(let _25_922 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_new_effect writer n))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, bs, c, qs, _)) -> begin
(let _25_932 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (let _25_934 = (serialize_lident writer lid)
in (let _25_936 = (serialize_binders writer bs)
in (let _25_938 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((se, r)) -> begin
(let _25_944 = (writer.Support.Microsoft.FStar.Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _)) -> begin
(let _25_953 = (writer.Support.Microsoft.FStar.Util.write_char 'l')
in (let _25_955 = (serialize_lident writer l)
in (let _25_957 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun ( reader ) -> (let _52_7612 = (deserialize_lident reader)
in (let _52_7611 = (deserialize_list reader deserialize_binder)
in (let _52_7610 = (deserialize_list reader deserialize_qualifier)
in (let _52_7609 = (deserialize_knd reader)
in (let _52_7608 = (deserialize_typ reader)
in (let _52_7607 = (deserialize_typ reader)
in (let _52_7606 = (deserialize_typ reader)
in (let _52_7605 = (deserialize_typ reader)
in (let _52_7604 = (deserialize_typ reader)
in (let _52_7603 = (deserialize_typ reader)
in (let _52_7602 = (deserialize_typ reader)
in (let _52_7601 = (deserialize_typ reader)
in (let _52_7600 = (deserialize_typ reader)
in (let _52_7599 = (deserialize_typ reader)
in (let _52_7598 = (deserialize_typ reader)
in (let _52_7597 = (deserialize_typ reader)
in (let _52_7596 = (deserialize_typ reader)
in (let _52_7595 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mname = _52_7612; Microsoft_FStar_Absyn_Syntax.binders = _52_7611; Microsoft_FStar_Absyn_Syntax.qualifiers = _52_7610; Microsoft_FStar_Absyn_Syntax.signature = _52_7609; Microsoft_FStar_Absyn_Syntax.ret = _52_7608; Microsoft_FStar_Absyn_Syntax.bind_wp = _52_7607; Microsoft_FStar_Absyn_Syntax.bind_wlp = _52_7606; Microsoft_FStar_Absyn_Syntax.if_then_else = _52_7605; Microsoft_FStar_Absyn_Syntax.ite_wp = _52_7604; Microsoft_FStar_Absyn_Syntax.ite_wlp = _52_7603; Microsoft_FStar_Absyn_Syntax.wp_binop = _52_7602; Microsoft_FStar_Absyn_Syntax.wp_as_type = _52_7601; Microsoft_FStar_Absyn_Syntax.close_wp = _52_7600; Microsoft_FStar_Absyn_Syntax.close_wp_t = _52_7599; Microsoft_FStar_Absyn_Syntax.assert_p = _52_7598; Microsoft_FStar_Absyn_Syntax.assume_p = _52_7597; Microsoft_FStar_Absyn_Syntax.null_wp = _52_7596; Microsoft_FStar_Absyn_Syntax.trivial = _52_7595})))))))))))))))))))
and deserialize_sigelt = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _52_7620 = (let _52_7619 = (deserialize_lident reader)
in (let _52_7618 = (deserialize_binders reader)
in (let _52_7617 = (deserialize_knd reader)
in (let _52_7616 = (deserialize_list reader deserialize_lident)
in (let _52_7615 = (deserialize_list reader deserialize_lident)
in (let _52_7614 = (deserialize_list reader deserialize_qualifier)
in (_52_7619, _52_7618, _52_7617, _52_7616, _52_7615, _52_7614, Microsoft_FStar_Absyn_Syntax.dummyRange)))))))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_52_7620))
end
| 'b' -> begin
(let _52_7626 = (let _52_7625 = (deserialize_lident reader)
in (let _52_7624 = (deserialize_binders reader)
in (let _52_7623 = (deserialize_knd reader)
in (let _52_7622 = (deserialize_typ reader)
in (let _52_7621 = (deserialize_list reader deserialize_qualifier)
in (_52_7625, _52_7624, _52_7623, _52_7622, _52_7621, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_52_7626))
end
| 'c' -> begin
(let _52_7632 = (let _52_7631 = (deserialize_lident reader)
in (let _52_7630 = (deserialize_typ reader)
in (let _52_7629 = (deserialize_tycon reader)
in (let _52_7628 = (deserialize_list reader deserialize_qualifier)
in (let _52_7627 = (deserialize_list reader deserialize_lident)
in (_52_7631, _52_7630, _52_7629, _52_7628, _52_7627, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_52_7632))
end
| 'd' -> begin
(let _52_7636 = (let _52_7635 = (deserialize_lident reader)
in (let _52_7634 = (deserialize_typ reader)
in (let _52_7633 = (deserialize_list reader deserialize_qualifier)
in (_52_7635, _52_7634, _52_7633, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_52_7636))
end
| 'e' -> begin
(let _52_7640 = (let _52_7639 = (deserialize_lident reader)
in (let _52_7638 = (deserialize_formula reader)
in (let _52_7637 = (deserialize_list reader deserialize_qualifier)
in (_52_7639, _52_7638, _52_7637, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_52_7640))
end
| 'f' -> begin
(let _52_7644 = (let _52_7643 = (deserialize_letbindings reader)
in (let _52_7642 = (deserialize_list reader deserialize_lident)
in (let _52_7641 = (match ((reader.Support.Microsoft.FStar.Util.read_bool ())) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end
| false -> begin
[]
end)
in (_52_7643, Microsoft_FStar_Absyn_Syntax.dummyRange, _52_7642, _52_7641))))
in Microsoft_FStar_Absyn_Syntax.Sig_let (_52_7644))
end
| 'g' -> begin
(let _52_7646 = (let _52_7645 = (deserialize_exp reader)
in (_52_7645, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_main (_52_7646))
end
| 'h' -> begin
(let _52_7650 = (let _52_7649 = (deserialize_list reader deserialize_sigelt)
in (let _52_7648 = (deserialize_list reader deserialize_qualifier)
in (let _52_7647 = (deserialize_list reader deserialize_lident)
in (_52_7649, _52_7648, _52_7647, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_52_7650))
end
| 'i' -> begin
(let _52_7652 = (let _52_7651 = (deserialize_new_effect reader)
in (_52_7651, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_52_7652))
end
| ('j') | ('k') | ('l') -> begin
(failwith ("TODO"))
end
| _ -> begin
(parse_error ())
end))

let serialize_sigelts = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun ( reader ) -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun ( writer ) ( ast ) -> (let _25_980 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.name)
in (let _25_982 = (serialize_sigelts writer [])
in (let _25_984 = (serialize_sigelts writer ast.Microsoft_FStar_Absyn_Syntax.exports)
in (writer.Support.Microsoft.FStar.Util.write_bool ast.Microsoft_FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun ( reader ) -> (let m = (let _52_7668 = (deserialize_lident reader)
in (let _52_7667 = (deserialize_sigelts reader)
in (let _52_7666 = (deserialize_sigelts reader)
in (let _52_7665 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in {Microsoft_FStar_Absyn_Syntax.name = _52_7668; Microsoft_FStar_Absyn_Syntax.declarations = _52_7667; Microsoft_FStar_Absyn_Syntax.exports = _52_7666; Microsoft_FStar_Absyn_Syntax.is_interface = _52_7665; Microsoft_FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _25_988 = m
in {Microsoft_FStar_Absyn_Syntax.name = _25_988.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _25_988.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _25_988.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _25_988.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




