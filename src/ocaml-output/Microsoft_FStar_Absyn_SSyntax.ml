
exception Err of (string)

let is_Err = (fun ( _discr_ ) -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let parse_error = (fun ( _27_3 ) -> (match (()) with
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
(let _27_11 = (writer.Support.Microsoft.FStar.Util.write_char 's')
in (f writer l))
end))

let deserialize_option = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_char ())
in (match ((n = 'n')) with
| true -> begin
None
end
| false -> begin
(let _70_10634 = (f reader)
in Some (_70_10634))
end)))

let serialize_list = (fun ( writer ) ( f ) ( l ) -> (let _27_21 = (writer.Support.Microsoft.FStar.Util.write_int (Support.List.length l))
in (Support.List.iter (fun ( elt ) -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_int ())
in (let rec helper = (fun ( accum ) ( n ) -> (match ((n = 0)) with
| true -> begin
accum
end
| false -> begin
(let _70_10655 = (let _70_10654 = (f reader)
in (_70_10654)::accum)
in (helper _70_10655 (n - 1)))
end))
in (helper [] n))))

let serialize_ident = (fun ( writer ) ( ast ) -> (writer.Support.Microsoft.FStar.Util.write_string ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun ( reader ) -> (let _70_10663 = (let _70_10662 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (_70_10662, Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _70_10663)))

let serialize_LongIdent = (fun ( writer ) ( ast ) -> (let _27_36 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun ( reader ) -> (let _70_10673 = (let _70_10672 = (deserialize_list reader deserialize_ident)
in (let _70_10671 = (let _70_10670 = (deserialize_ident reader)
in (_70_10670)::[])
in (Support.List.append _70_10672 _70_10671)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _70_10673)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun ( writer ) ( s_v ) ( s_sort ) ( ast ) -> (let _27_45 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun ( reader ) ( ds_v ) ( ds_sort ) -> (let _70_10703 = (ds_v reader)
in (let _70_10702 = (ds_sort reader)
in {Microsoft_FStar_Absyn_Syntax.v = _70_10703; Microsoft_FStar_Absyn_Syntax.sort = _70_10702; Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun ( writer ) ( ast ) -> (let _27_62 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ( ghost ) ( reader ) -> (let _70_10723 = (deserialize_ident reader)
in (let _70_10722 = (deserialize_ident reader)
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_10723; Microsoft_FStar_Absyn_Syntax.realname = _70_10722})))

let serialize_bvar = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

let deserialize_bvar = (fun ( ghost ) ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

let serialize_sconst = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'a')
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (v) -> begin
(let _27_82 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (writer.Support.Microsoft.FStar.Util.write_byte v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (v) -> begin
(let _27_86 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (writer.Support.Microsoft.FStar.Util.write_bool v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (v) -> begin
(let _27_90 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (writer.Support.Microsoft.FStar.Util.write_int32 v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (v) -> begin
(let _27_94 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (writer.Support.Microsoft.FStar.Util.write_int64 v))
end
| Microsoft_FStar_Absyn_Syntax.Const_char (v) -> begin
(let _27_98 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (writer.Support.Microsoft.FStar.Util.write_char v))
end
| Microsoft_FStar_Absyn_Syntax.Const_float (v) -> begin
(let _27_102 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (writer.Support.Microsoft.FStar.Util.write_double v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((v, _27_106)) -> begin
(let _27_109 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (writer.Support.Microsoft.FStar.Util.write_bytearray v))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((v, _27_113)) -> begin
(let _27_116 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (writer.Support.Microsoft.FStar.Util.write_bytearray v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (v) -> begin
(let _27_120 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (writer.Support.Microsoft.FStar.Util.write_string v))
end))

let deserialize_sconst = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Const_unit
end
| 'b' -> begin
(let _70_10745 = (reader.Support.Microsoft.FStar.Util.read_byte ())
in Microsoft_FStar_Absyn_Syntax.Const_uint8 (_70_10745))
end
| 'c' -> begin
(let _70_10746 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in Microsoft_FStar_Absyn_Syntax.Const_bool (_70_10746))
end
| 'd' -> begin
(let _70_10747 = (reader.Support.Microsoft.FStar.Util.read_int32 ())
in Microsoft_FStar_Absyn_Syntax.Const_int32 (_70_10747))
end
| 'e' -> begin
(let _70_10748 = (reader.Support.Microsoft.FStar.Util.read_int64 ())
in Microsoft_FStar_Absyn_Syntax.Const_int64 (_70_10748))
end
| 'f' -> begin
(let _70_10749 = (reader.Support.Microsoft.FStar.Util.read_char ())
in Microsoft_FStar_Absyn_Syntax.Const_char (_70_10749))
end
| 'g' -> begin
(let _70_10750 = (reader.Support.Microsoft.FStar.Util.read_double ())
in Microsoft_FStar_Absyn_Syntax.Const_float (_70_10750))
end
| 'h' -> begin
(let _70_10752 = (let _70_10751 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_70_10751, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_bytearray (_70_10752))
end
| 'i' -> begin
(let _70_10754 = (let _70_10753 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_70_10753, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_70_10754))
end
| 'j' -> begin
(let _70_10755 = (reader.Support.Microsoft.FStar.Util.read_string ())
in Microsoft_FStar_Absyn_Syntax.Const_int (_70_10755))
end
| _27_134 -> begin
(parse_error ())
end))

let serialize_either = (fun ( writer ) ( s_l ) ( s_r ) ( ast ) -> (match (ast) with
| Support.Microsoft.FStar.Util.Inl (v) -> begin
(let _27_143 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (s_l writer v))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _27_147 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (s_r writer v))
end))

let deserialize_either = (fun ( reader ) ( ds_l ) ( ds_r ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_10781 = (ds_l reader)
in Support.Microsoft.FStar.Util.Inl (_70_10781))
end
| 'b' -> begin
(let _70_10782 = (ds_r reader)
in Support.Microsoft.FStar.Util.Inr (_70_10782))
end
| _27_157 -> begin
(parse_error ())
end))

let serialize_syntax = (fun ( writer ) ( s_a ) ( ast ) -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun ( reader ) ( ds_a ) ( ds_b ) -> (let _70_10801 = (ds_a reader)
in (let _70_10800 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _70_10799 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _70_10798 = (Support.Microsoft.FStar.Util.mk_ref None)
in {Microsoft_FStar_Absyn_Syntax.n = _70_10801; Microsoft_FStar_Absyn_Syntax.tk = _70_10800; Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = _70_10799; Microsoft_FStar_Absyn_Syntax.uvs = _70_10798})))))

let rec serialize_typ' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _27_172 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _27_176 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_ftvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _27_182 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_184 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((v, t)) -> begin
(let _27_190 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_192 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, ars)) -> begin
(let _27_198 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_200 = (serialize_typ writer t)
in (let _27_202 = (serialize_args writer ars)
in (match (((Support.ST.read Microsoft_FStar_Options.debug) <> [])) with
| true -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_27_205, _27_207)) -> begin
(Support.Microsoft.FStar.Util.print_string "type application node with lam\n")
end
| _27_211 -> begin
()
end)
end
| false -> begin
()
end))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _27_216 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _27_218 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(let _27_224 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (let _27_226 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _27_230 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (serialize_meta_t writer m))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'i')
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_27_234, _27_236)) -> begin
(raise (Err ("typ not impl:1")))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((_27_240, _27_242)) -> begin
(raise (Err ("typ not impl:2")))
end))
and serialize_meta_t = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, l)) -> begin
(let _27_251 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _27_253 = (serialize_typ writer t)
in (serialize_list writer serialize_arg l)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid)) -> begin
(let _27_259 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _27_261 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, s, _27_266, b)) -> begin
(let _27_270 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_272 = (serialize_typ writer t)
in (let _27_274 = (writer.Support.Microsoft.FStar.Util.write_string s)
in (writer.Support.Microsoft.FStar.Util.write_bool b))))
end
| _27_277 -> begin
(raise (Err ("unimplemented meta_t")))
end))
and serialize_arg = (fun ( writer ) ( ast ) -> (let _27_280 = (serialize_either writer serialize_typ serialize_exp (Support.Prims.fst ast))
in (let _70_10868 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _70_10868))))
and serialize_args = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun ( writer ) ( ast ) -> (let _27_286 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (let _70_10873 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _70_10873))))
and serialize_binders = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun ( writer ) ( ast ) -> (let _70_10878 = (Microsoft_FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _70_10878)))
and serialize_comp_typ = (fun ( writer ) ( ast ) -> (let _27_294 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _27_296 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _27_298 = (serialize_args writer ast.Microsoft_FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.Microsoft_FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _27_304 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_typ writer t))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let _27_308 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
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
(let _27_322 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _27_328 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, b)) -> begin
(let _27_334 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _27_336 = (serialize_fvvar writer v)
in (writer.Support.Microsoft.FStar.Util.write_bool false)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _27_340 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let _27_346 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_348 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, ars)) -> begin
(let _27_354 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_356 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, l)) -> begin
(let g = (fun ( writer ) ( eopt ) -> (match (eopt) with
| Some (e1) -> begin
(let _27_367 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'b')
end))
in (let f = (fun ( writer ) ( _27_375 ) -> (match (_27_375) with
| (p, eopt, e) -> begin
(let _27_376 = (serialize_pat writer p)
in (let _27_378 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _27_380 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _27_382 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, l)) -> begin
(let _27_389 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (let _27_391 = (serialize_exp writer e)
in (let _27_393 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _27_399 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _27_401 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _27_405 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _27_408 -> begin
(raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, s)) -> begin
(let _27_415 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _27_417 = (serialize_exp writer e)
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
and serialize_exp = (fun ( writer ) ( ast ) -> (let _70_10903 = (Microsoft_FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _70_10903)))
and serialize_btvdef = (fun ( writer ) ( ast ) -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun ( writer ) ( ast ) -> (serialize_bvdef writer ast))
and serialize_pat' = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _27_435 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _27_439 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((v, _27_443, l)) -> begin
(let _27_447 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_449 = (serialize_fvvar writer v)
in (serialize_list writer serialize_pat l)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((v, b)) -> begin
(let _27_455 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_457 = (serialize_bvvar writer v)
in (writer.Support.Microsoft.FStar.Util.write_bool b)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _27_461 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _27_465 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _27_469 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((v, e)) -> begin
(let _27_475 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _27_477 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((v, t)) -> begin
(let _27_483 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (let _27_485 = (serialize_btvar writer v)
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
(let _27_499 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_501 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _27_507 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_509 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((bs, k)) -> begin
(let _27_515 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_517 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'f')
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(raise (Err ("knd\' serialization unimplemented:1")))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_27_525, _27_527, _27_529)) -> begin
(raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun ( writer ) ( ast ) -> (let _70_10918 = (Microsoft_FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _70_10918)))
and serialize_kabbrev = (fun ( writer ) ( ast ) -> (let _27_536 = (serialize_lident writer (Support.Prims.fst ast))
in (serialize_args writer (Support.Prims.snd ast))))
and serialize_lbname = (fun ( writer ) ( ast ) -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun ( writer ) ( ast ) -> (let f = (fun ( writer ) ( lb ) -> (let _27_545 = (serialize_lbname writer lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _27_547 = (serialize_lident writer lb.Microsoft_FStar_Absyn_Syntax.lbeff)
in (let _27_549 = (serialize_typ writer lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.Microsoft_FStar_Absyn_Syntax.lbdef)))))
in (let _27_551 = (writer.Support.Microsoft.FStar.Util.write_bool (Support.Prims.fst ast))
in (serialize_list writer f (Support.Prims.snd ast)))))
and serialize_fvar = (fun ( writer ) ( ast ) -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun ( writer ) ( ast ) -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun ( writer ) ( ast ) -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun ( writer ) ( ast ) -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun ( writer ) ( ast ) -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_10969 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_btvar (_70_10969))
end
| 'b' -> begin
(let _70_10970 = (deserialize_ftvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_const (_70_10970))
end
| 'c' -> begin
(let _70_10973 = (let _70_10972 = (deserialize_binders reader)
in (let _70_10971 = (deserialize_comp reader)
in (_70_10972, _70_10971)))
in Microsoft_FStar_Absyn_Syntax.Typ_fun (_70_10973))
end
| 'd' -> begin
(let _70_10976 = (let _70_10975 = (deserialize_bvvar reader)
in (let _70_10974 = (deserialize_typ reader)
in (_70_10975, _70_10974)))
in Microsoft_FStar_Absyn_Syntax.Typ_refine (_70_10976))
end
| 'e' -> begin
(let _70_10979 = (let _70_10978 = (deserialize_typ reader)
in (let _70_10977 = (deserialize_args reader)
in (_70_10978, _70_10977)))
in Microsoft_FStar_Absyn_Syntax.Typ_app (_70_10979))
end
| 'f' -> begin
(let _70_10982 = (let _70_10981 = (deserialize_binders reader)
in (let _70_10980 = (deserialize_typ reader)
in (_70_10981, _70_10980)))
in Microsoft_FStar_Absyn_Syntax.Typ_lam (_70_10982))
end
| 'g' -> begin
(let _70_10985 = (let _70_10984 = (deserialize_typ reader)
in (let _70_10983 = (deserialize_knd reader)
in (_70_10984, _70_10983)))
in Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_70_10985))
end
| 'h' -> begin
(let _70_10986 = (deserialize_meta_t reader)
in Microsoft_FStar_Absyn_Syntax.Typ_meta (_70_10986))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _27_574 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_10990 = (let _70_10989 = (deserialize_typ reader)
in (let _70_10988 = (deserialize_list reader deserialize_arg)
in (_70_10989, _70_10988)))
in Microsoft_FStar_Absyn_Syntax.Meta_pattern (_70_10990))
end
| 'b' -> begin
(let _70_10993 = (let _70_10992 = (deserialize_typ reader)
in (let _70_10991 = (deserialize_lident reader)
in (_70_10992, _70_10991)))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_70_10993))
end
| 'c' -> begin
(let _70_10997 = (let _70_10996 = (deserialize_typ reader)
in (let _70_10995 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (let _70_10994 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_70_10996, _70_10995, Microsoft_FStar_Absyn_Syntax.dummyRange, _70_10994))))
in Microsoft_FStar_Absyn_Syntax.Meta_labeled (_70_10997))
end
| _27_580 -> begin
(parse_error ())
end))
and deserialize_arg = (fun ( reader ) -> (let _70_11001 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _70_11000 = (let _70_10999 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _70_10999))
in (_70_11001, _70_11000))))
and deserialize_args = (fun ( reader ) -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun ( reader ) -> (let _70_11006 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _70_11005 = (let _70_11004 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _70_11004))
in (_70_11006, _70_11005))))
and deserialize_binders = (fun ( reader ) -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun ( reader ) -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun ( reader ) -> (let _70_11013 = (deserialize_lident reader)
in (let _70_11012 = (deserialize_typ reader)
in (let _70_11011 = (deserialize_args reader)
in (let _70_11010 = (deserialize_list reader deserialize_cflags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _70_11013; Microsoft_FStar_Absyn_Syntax.result_typ = _70_11012; Microsoft_FStar_Absyn_Syntax.effect_args = _70_11011; Microsoft_FStar_Absyn_Syntax.flags = _70_11010})))))
and deserialize_comp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_11015 = (deserialize_typ reader)
in Microsoft_FStar_Absyn_Syntax.Total (_70_11015))
end
| 'b' -> begin
(let _70_11016 = (deserialize_comp_typ reader)
in Microsoft_FStar_Absyn_Syntax.Comp (_70_11016))
end
| _27_591 -> begin
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
(let _70_11019 = (deserialize_exp reader)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_70_11019))
end
| _27_602 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_11021 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Exp_bvar (_70_11021))
end
| 'b' -> begin
(let _70_11025 = (let _70_11024 = (deserialize_fvvar reader)
in (let _70_11023 = (let _27_606 = (let _70_11022 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.All.pipe_left Support.Prims.ignore _70_11022))
in None)
in (_70_11024, _70_11023)))
in Microsoft_FStar_Absyn_Syntax.Exp_fvar (_70_11025))
end
| 'c' -> begin
(let _70_11026 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Exp_constant (_70_11026))
end
| 'd' -> begin
(let _70_11029 = (let _70_11028 = (deserialize_binders reader)
in (let _70_11027 = (deserialize_exp reader)
in (_70_11028, _70_11027)))
in Microsoft_FStar_Absyn_Syntax.Exp_abs (_70_11029))
end
| 'e' -> begin
(let _70_11032 = (let _70_11031 = (deserialize_exp reader)
in (let _70_11030 = (deserialize_args reader)
in (_70_11031, _70_11030)))
in Microsoft_FStar_Absyn_Syntax.Exp_app (_70_11032))
end
| 'f' -> begin
(let g = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_11035 = (deserialize_exp reader)
in Some (_70_11035))
end
| 'b' -> begin
None
end
| _27_617 -> begin
(parse_error ())
end))
in (let f = (fun ( reader ) -> (let _70_11040 = (deserialize_pat reader)
in (let _70_11039 = (g reader)
in (let _70_11038 = (deserialize_exp reader)
in (_70_11040, _70_11039, _70_11038)))))
in (let _70_11043 = (let _70_11042 = (deserialize_exp reader)
in (let _70_11041 = (deserialize_list reader f)
in (_70_11042, _70_11041)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (_70_11043))))
end
| 'g' -> begin
(let _70_11047 = (let _70_11046 = (deserialize_exp reader)
in (let _70_11045 = (deserialize_typ reader)
in (let _70_11044 = (deserialize_option reader deserialize_lident)
in (_70_11046, _70_11045, _70_11044))))
in Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_70_11047))
end
| 'h' -> begin
(let _70_11050 = (let _70_11049 = (deserialize_letbindings reader)
in (let _70_11048 = (deserialize_exp reader)
in (_70_11049, _70_11048)))
in Microsoft_FStar_Absyn_Syntax.Exp_let (_70_11050))
end
| 'i' -> begin
(let _70_11051 = (deserialize_meta_e reader)
in Microsoft_FStar_Absyn_Syntax.Exp_meta (_70_11051))
end
| _27_624 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_11055 = (let _70_11054 = (deserialize_exp reader)
in (let _70_11053 = (deserialize_meta_source_info reader)
in (_70_11054, _70_11053)))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_11055))
end
| _27_628 -> begin
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
| _27_635 -> begin
(parse_error ())
end))
and deserialize_exp = (fun ( reader ) -> (deserialize_syntax reader deserialize_exp' Microsoft_FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun ( reader ) -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun ( reader ) -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_11061 = (deserialize_list reader deserialize_pat)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_70_11061))
end
| 'b' -> begin
(let _70_11062 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Pat_constant (_70_11062))
end
| 'c' -> begin
(let _70_11065 = (let _70_11064 = (deserialize_fvvar reader)
in (let _70_11063 = (deserialize_list reader deserialize_pat)
in (_70_11064, None, _70_11063)))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_11065))
end
| 'd' -> begin
(let _70_11068 = (let _70_11067 = (deserialize_bvvar reader)
in (let _70_11066 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_70_11067, _70_11066)))
in Microsoft_FStar_Absyn_Syntax.Pat_var (_70_11068))
end
| 'e' -> begin
(let _70_11069 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_70_11069))
end
| 'f' -> begin
(let _70_11070 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_70_11070))
end
| 'g' -> begin
(let _70_11071 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_70_11071))
end
| 'h' -> begin
(let _70_11074 = (let _70_11073 = (deserialize_bvvar reader)
in (let _70_11072 = (deserialize_exp reader)
in (_70_11073, _70_11072)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_70_11074))
end
| 'i' -> begin
(let _70_11077 = (let _70_11076 = (deserialize_btvar reader)
in (let _70_11075 = (deserialize_typ reader)
in (_70_11076, _70_11075)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_70_11077))
end
| _27_650 -> begin
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
(let _70_11083 = (let _70_11082 = (deserialize_kabbrev reader)
in (let _70_11081 = (deserialize_knd reader)
in (_70_11082, _70_11081)))
in Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_70_11083))
end
| 'd' -> begin
(let _70_11086 = (let _70_11085 = (deserialize_binders reader)
in (let _70_11084 = (deserialize_knd reader)
in (_70_11085, _70_11084)))
in Microsoft_FStar_Absyn_Syntax.Kind_arrow (_70_11086))
end
| 'e' -> begin
(let _70_11089 = (let _70_11088 = (deserialize_binders reader)
in (let _70_11087 = (deserialize_knd reader)
in (_70_11088, _70_11087)))
in Microsoft_FStar_Absyn_Syntax.Kind_lam (_70_11089))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _27_661 -> begin
(parse_error ())
end))
and deserialize_knd = (fun ( reader ) -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun ( reader ) -> (let _70_11093 = (deserialize_lident reader)
in (let _70_11092 = (deserialize_args reader)
in (_70_11093, _70_11092))))
and deserialize_lbname = (fun ( reader ) -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun ( reader ) -> (let f = (fun ( reader ) -> (let _70_11101 = (deserialize_lbname reader)
in (let _70_11100 = (deserialize_typ reader)
in (let _70_11099 = (deserialize_lident reader)
in (let _70_11098 = (deserialize_exp reader)
in {Microsoft_FStar_Absyn_Syntax.lbname = _70_11101; Microsoft_FStar_Absyn_Syntax.lbtyp = _70_11100; Microsoft_FStar_Absyn_Syntax.lbeff = _70_11099; Microsoft_FStar_Absyn_Syntax.lbdef = _70_11098})))))
in (let _70_11103 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (let _70_11102 = (deserialize_list reader f)
in (_70_11103, _70_11102)))))
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
(let _27_681 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_lident writer lid))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((lid, v)) -> begin
(let _27_687 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (let _27_689 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| Microsoft_FStar_Absyn_Syntax.RecordType (l) -> begin
(let _27_693 = (writer.Support.Microsoft.FStar.Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _27_697 = (writer.Support.Microsoft.FStar.Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'm')
end
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'o')
end
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _27_703 = (writer.Support.Microsoft.FStar.Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.TotalEffect -> begin
(writer.Support.Microsoft.FStar.Util.write_char 'q')
end
| _27_707 -> begin
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
(let _70_11118 = (deserialize_lident reader)
in Microsoft_FStar_Absyn_Syntax.Discriminator (_70_11118))
end
| 'j' -> begin
(let _70_11121 = (let _70_11120 = (deserialize_lident reader)
in (let _70_11119 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_70_11120, _70_11119)))
in Microsoft_FStar_Absyn_Syntax.Projector (_70_11121))
end
| 'k' -> begin
(let _70_11122 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordType (_70_11122))
end
| 'l' -> begin
(let _70_11123 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordConstructor (_70_11123))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _70_11125 = (deserialize_option reader deserialize_lident)
in (Support.All.pipe_right _70_11125 (fun ( _70_11124 ) -> Microsoft_FStar_Absyn_Syntax.DefaultEffect (_70_11124))))
end
| 'q' -> begin
Microsoft_FStar_Absyn_Syntax.TotalEffect
end
| _27_722 -> begin
(parse_error ())
end))

let serialize_tycon = (fun ( writer ) ( _27_727 ) -> (match (_27_727) with
| (lid, bs, k) -> begin
(let _27_728 = (serialize_lident writer lid)
in (let _27_730 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun ( reader ) -> (let _70_11134 = (deserialize_lident reader)
in (let _70_11133 = (deserialize_binders reader)
in (let _70_11132 = (deserialize_knd reader)
in (_70_11134, _70_11133, _70_11132)))))

let serialize_monad_abbrev = (fun ( writer ) ( ast ) -> (let _27_735 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _27_737 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun ( reader ) -> (let _70_11143 = (deserialize_lident reader)
in (let _70_11142 = (deserialize_binders reader)
in (let _70_11141 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mabbrev = _70_11143; Microsoft_FStar_Absyn_Syntax.parms = _70_11142; Microsoft_FStar_Absyn_Syntax.def = _70_11141}))))

let serialize_sub_effect = (fun ( writer ) ( ast ) -> (let _27_742 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _27_744 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun ( reader ) -> (let _70_11152 = (deserialize_lident reader)
in (let _70_11151 = (deserialize_lident reader)
in (let _70_11150 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.source = _70_11152; Microsoft_FStar_Absyn_Syntax.target = _70_11151; Microsoft_FStar_Absyn_Syntax.lift = _70_11150}))))

let rec serialize_new_effect = (fun ( writer ) ( ast ) -> (let _27_749 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mname)
in (let _27_751 = (serialize_list writer serialize_binder ast.Microsoft_FStar_Absyn_Syntax.binders)
in (let _27_753 = (serialize_list writer serialize_qualifier ast.Microsoft_FStar_Absyn_Syntax.qualifiers)
in (let _27_755 = (serialize_knd writer ast.Microsoft_FStar_Absyn_Syntax.signature)
in (let _27_757 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ret)
in (let _27_759 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _27_761 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _27_763 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _27_765 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _27_767 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _27_769 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _27_771 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _27_773 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _27_775 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _27_777 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _27_779 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _27_781 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun ( writer ) ( ast ) -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_27_786) -> begin
(Support.All.failwith "NYI")
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, bs, k, l1, l2, qs, _27_795)) -> begin
(let _27_798 = (writer.Support.Microsoft.FStar.Util.write_char 'a')
in (let _27_800 = (serialize_lident writer lid)
in (let _27_802 = (serialize_binders writer bs)
in (let _27_804 = (serialize_knd writer k)
in (let _27_806 = (serialize_list writer serialize_lident l1)
in (let _27_808 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, bs, k, t, qs, _27_816)) -> begin
(let _27_819 = (writer.Support.Microsoft.FStar.Util.write_char 'b')
in (let _27_821 = (serialize_lident writer lid)
in (let _27_823 = (serialize_binders writer bs)
in (let _27_825 = (serialize_knd writer k)
in (let _27_827 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid1, t, tyc, qs, mutuals, _27_835)) -> begin
(let t' = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(let _70_11162 = (let _70_11161 = (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))
in (f, _70_11161))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_11162 None Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _27_844 = (writer.Support.Microsoft.FStar.Util.write_char 'c')
in (let _27_846 = (serialize_lident writer lid1)
in (let _27_848 = (serialize_typ writer t')
in (let _27_850 = (serialize_tycon writer tyc)
in (let _27_852 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, qs, _27_858)) -> begin
(let _27_861 = (writer.Support.Microsoft.FStar.Util.write_char 'd')
in (let _27_863 = (serialize_lident writer lid)
in (let _27_865 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, fml, qs, _27_871)) -> begin
(let _27_874 = (writer.Support.Microsoft.FStar.Util.write_char 'e')
in (let _27_876 = (serialize_lident writer lid)
in (let _27_878 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _27_882, l, quals)) -> begin
(let _27_887 = (writer.Support.Microsoft.FStar.Util.write_char 'f')
in (let _27_889 = (serialize_letbindings writer lbs)
in (let _27_891 = (serialize_list writer serialize_lident l)
in (let _70_11164 = (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _27_1 ) -> (match (_27_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _27_896 -> begin
false
end))))
in (writer.Support.Microsoft.FStar.Util.write_bool _70_11164)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _27_899)) -> begin
(let _27_902 = (writer.Support.Microsoft.FStar.Util.write_char 'g')
in (serialize_exp writer e))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((l, qs, lids, _27_908)) -> begin
(let _27_911 = (writer.Support.Microsoft.FStar.Util.write_char 'h')
in (let _27_913 = (serialize_list writer serialize_sigelt l)
in (let _27_915 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _27_919)) -> begin
(let _27_922 = (writer.Support.Microsoft.FStar.Util.write_char 'i')
in (serialize_new_effect writer n))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, bs, c, qs, _27_929)) -> begin
(let _27_932 = (writer.Support.Microsoft.FStar.Util.write_char 'j')
in (let _27_934 = (serialize_lident writer lid)
in (let _27_936 = (serialize_binders writer bs)
in (let _27_938 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((se, r)) -> begin
(let _27_944 = (writer.Support.Microsoft.FStar.Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _27_950)) -> begin
(let _27_953 = (writer.Support.Microsoft.FStar.Util.write_char 'l')
in (let _27_955 = (serialize_lident writer l)
in (let _27_957 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun ( reader ) -> (let _70_11185 = (deserialize_lident reader)
in (let _70_11184 = (deserialize_list reader deserialize_binder)
in (let _70_11183 = (deserialize_list reader deserialize_qualifier)
in (let _70_11182 = (deserialize_knd reader)
in (let _70_11181 = (deserialize_typ reader)
in (let _70_11180 = (deserialize_typ reader)
in (let _70_11179 = (deserialize_typ reader)
in (let _70_11178 = (deserialize_typ reader)
in (let _70_11177 = (deserialize_typ reader)
in (let _70_11176 = (deserialize_typ reader)
in (let _70_11175 = (deserialize_typ reader)
in (let _70_11174 = (deserialize_typ reader)
in (let _70_11173 = (deserialize_typ reader)
in (let _70_11172 = (deserialize_typ reader)
in (let _70_11171 = (deserialize_typ reader)
in (let _70_11170 = (deserialize_typ reader)
in (let _70_11169 = (deserialize_typ reader)
in (let _70_11168 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mname = _70_11185; Microsoft_FStar_Absyn_Syntax.binders = _70_11184; Microsoft_FStar_Absyn_Syntax.qualifiers = _70_11183; Microsoft_FStar_Absyn_Syntax.signature = _70_11182; Microsoft_FStar_Absyn_Syntax.ret = _70_11181; Microsoft_FStar_Absyn_Syntax.bind_wp = _70_11180; Microsoft_FStar_Absyn_Syntax.bind_wlp = _70_11179; Microsoft_FStar_Absyn_Syntax.if_then_else = _70_11178; Microsoft_FStar_Absyn_Syntax.ite_wp = _70_11177; Microsoft_FStar_Absyn_Syntax.ite_wlp = _70_11176; Microsoft_FStar_Absyn_Syntax.wp_binop = _70_11175; Microsoft_FStar_Absyn_Syntax.wp_as_type = _70_11174; Microsoft_FStar_Absyn_Syntax.close_wp = _70_11173; Microsoft_FStar_Absyn_Syntax.close_wp_t = _70_11172; Microsoft_FStar_Absyn_Syntax.assert_p = _70_11171; Microsoft_FStar_Absyn_Syntax.assume_p = _70_11170; Microsoft_FStar_Absyn_Syntax.null_wp = _70_11169; Microsoft_FStar_Absyn_Syntax.trivial = _70_11168})))))))))))))))))))
and deserialize_sigelt = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _70_11193 = (let _70_11192 = (deserialize_lident reader)
in (let _70_11191 = (deserialize_binders reader)
in (let _70_11190 = (deserialize_knd reader)
in (let _70_11189 = (deserialize_list reader deserialize_lident)
in (let _70_11188 = (deserialize_list reader deserialize_lident)
in (let _70_11187 = (deserialize_list reader deserialize_qualifier)
in (_70_11192, _70_11191, _70_11190, _70_11189, _70_11188, _70_11187, Microsoft_FStar_Absyn_Syntax.dummyRange)))))))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_70_11193))
end
| 'b' -> begin
(let _70_11199 = (let _70_11198 = (deserialize_lident reader)
in (let _70_11197 = (deserialize_binders reader)
in (let _70_11196 = (deserialize_knd reader)
in (let _70_11195 = (deserialize_typ reader)
in (let _70_11194 = (deserialize_list reader deserialize_qualifier)
in (_70_11198, _70_11197, _70_11196, _70_11195, _70_11194, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_70_11199))
end
| 'c' -> begin
(let _70_11205 = (let _70_11204 = (deserialize_lident reader)
in (let _70_11203 = (deserialize_typ reader)
in (let _70_11202 = (deserialize_tycon reader)
in (let _70_11201 = (deserialize_list reader deserialize_qualifier)
in (let _70_11200 = (deserialize_list reader deserialize_lident)
in (_70_11204, _70_11203, _70_11202, _70_11201, _70_11200, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_70_11205))
end
| 'd' -> begin
(let _70_11209 = (let _70_11208 = (deserialize_lident reader)
in (let _70_11207 = (deserialize_typ reader)
in (let _70_11206 = (deserialize_list reader deserialize_qualifier)
in (_70_11208, _70_11207, _70_11206, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_70_11209))
end
| 'e' -> begin
(let _70_11213 = (let _70_11212 = (deserialize_lident reader)
in (let _70_11211 = (deserialize_formula reader)
in (let _70_11210 = (deserialize_list reader deserialize_qualifier)
in (_70_11212, _70_11211, _70_11210, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_70_11213))
end
| 'f' -> begin
(let _70_11217 = (let _70_11216 = (deserialize_letbindings reader)
in (let _70_11215 = (deserialize_list reader deserialize_lident)
in (let _70_11214 = (match ((reader.Support.Microsoft.FStar.Util.read_bool ())) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end
| false -> begin
[]
end)
in (_70_11216, Microsoft_FStar_Absyn_Syntax.dummyRange, _70_11215, _70_11214))))
in Microsoft_FStar_Absyn_Syntax.Sig_let (_70_11217))
end
| 'g' -> begin
(let _70_11219 = (let _70_11218 = (deserialize_exp reader)
in (_70_11218, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_main (_70_11219))
end
| 'h' -> begin
(let _70_11223 = (let _70_11222 = (deserialize_list reader deserialize_sigelt)
in (let _70_11221 = (deserialize_list reader deserialize_qualifier)
in (let _70_11220 = (deserialize_list reader deserialize_lident)
in (_70_11222, _70_11221, _70_11220, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_70_11223))
end
| 'i' -> begin
(let _70_11225 = (let _70_11224 = (deserialize_new_effect reader)
in (_70_11224, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_70_11225))
end
| ('j') | ('k') | ('l') -> begin
(Support.All.failwith "TODO")
end
| _27_974 -> begin
(parse_error ())
end))

let serialize_sigelts = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun ( reader ) -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun ( writer ) ( ast ) -> (let _27_980 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.name)
in (let _27_982 = (serialize_sigelts writer [])
in (let _27_984 = (serialize_sigelts writer ast.Microsoft_FStar_Absyn_Syntax.exports)
in (writer.Support.Microsoft.FStar.Util.write_bool ast.Microsoft_FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun ( reader ) -> (let m = (let _70_11241 = (deserialize_lident reader)
in (let _70_11240 = (deserialize_sigelts reader)
in (let _70_11239 = (deserialize_sigelts reader)
in (let _70_11238 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in {Microsoft_FStar_Absyn_Syntax.name = _70_11241; Microsoft_FStar_Absyn_Syntax.declarations = _70_11240; Microsoft_FStar_Absyn_Syntax.exports = _70_11239; Microsoft_FStar_Absyn_Syntax.is_interface = _70_11238; Microsoft_FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _27_988 = m
in {Microsoft_FStar_Absyn_Syntax.name = _27_988.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _27_988.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _27_988.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _27_988.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




