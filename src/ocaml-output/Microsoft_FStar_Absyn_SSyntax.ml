
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
(let _65_10486 = (f reader)
in Some (_65_10486))
end)))

let serialize_list = (fun ( writer ) ( f ) ( l ) -> (let _25_21 = (writer.Support.Microsoft.FStar.Util.write_int (Support.List.length l))
in (Support.List.iter (fun ( elt ) -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_int ())
in (let rec helper = (fun ( accum ) ( n ) -> (match ((n = 0)) with
| true -> begin
accum
end
| false -> begin
(let _65_10507 = (let _65_10506 = (f reader)
in (_65_10506)::accum)
in (helper _65_10507 (n - 1)))
end))
in (helper [] n))))

let serialize_ident = (fun ( writer ) ( ast ) -> (writer.Support.Microsoft.FStar.Util.write_string ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun ( reader ) -> (let _65_10515 = (let _65_10514 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (_65_10514, Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _65_10515)))

let serialize_LongIdent = (fun ( writer ) ( ast ) -> (let _25_36 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun ( reader ) -> (let _65_10525 = (let _65_10524 = (deserialize_list reader deserialize_ident)
in (let _65_10523 = (let _65_10522 = (deserialize_ident reader)
in (_65_10522)::[])
in (Support.List.append _65_10524 _65_10523)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _65_10525)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun ( writer ) ( s_v ) ( s_sort ) ( ast ) -> (let _25_45 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun ( reader ) ( ds_v ) ( ds_sort ) -> (let _65_10555 = (ds_v reader)
in (let _65_10554 = (ds_sort reader)
in {Microsoft_FStar_Absyn_Syntax.v = _65_10555; Microsoft_FStar_Absyn_Syntax.sort = _65_10554; Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun ( writer ) ( ast ) -> (let _25_62 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ( ghost ) ( reader ) -> (let _65_10575 = (deserialize_ident reader)
in (let _65_10574 = (deserialize_ident reader)
in {Microsoft_FStar_Absyn_Syntax.ppname = _65_10575; Microsoft_FStar_Absyn_Syntax.realname = _65_10574})))

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
(let _65_10597 = (reader.Support.Microsoft.FStar.Util.read_byte ())
in Microsoft_FStar_Absyn_Syntax.Const_uint8 (_65_10597))
end
| 'c' -> begin
(let _65_10598 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in Microsoft_FStar_Absyn_Syntax.Const_bool (_65_10598))
end
| 'd' -> begin
(let _65_10599 = (reader.Support.Microsoft.FStar.Util.read_int32 ())
in Microsoft_FStar_Absyn_Syntax.Const_int32 (_65_10599))
end
| 'e' -> begin
(let _65_10600 = (reader.Support.Microsoft.FStar.Util.read_int64 ())
in Microsoft_FStar_Absyn_Syntax.Const_int64 (_65_10600))
end
| 'f' -> begin
(let _65_10601 = (reader.Support.Microsoft.FStar.Util.read_char ())
in Microsoft_FStar_Absyn_Syntax.Const_char (_65_10601))
end
| 'g' -> begin
(let _65_10602 = (reader.Support.Microsoft.FStar.Util.read_double ())
in Microsoft_FStar_Absyn_Syntax.Const_float (_65_10602))
end
| 'h' -> begin
(let _65_10604 = (let _65_10603 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_65_10603, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_bytearray (_65_10604))
end
| 'i' -> begin
(let _65_10606 = (let _65_10605 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_65_10605, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_65_10606))
end
| 'j' -> begin
(let _65_10607 = (reader.Support.Microsoft.FStar.Util.read_string ())
in Microsoft_FStar_Absyn_Syntax.Const_int (_65_10607))
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
(let _65_10633 = (ds_l reader)
in Support.Microsoft.FStar.Util.Inl (_65_10633))
end
| 'b' -> begin
(let _65_10634 = (ds_r reader)
in Support.Microsoft.FStar.Util.Inr (_65_10634))
end
| _ -> begin
(parse_error ())
end))

let serialize_syntax = (fun ( writer ) ( s_a ) ( ast ) -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun ( reader ) ( ds_a ) ( ds_b ) -> (let _65_10653 = (ds_a reader)
in (let _65_10652 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _65_10651 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _65_10650 = (Support.Microsoft.FStar.Util.mk_ref None)
in {Microsoft_FStar_Absyn_Syntax.n = _65_10653; Microsoft_FStar_Absyn_Syntax.tk = _65_10652; Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = _65_10651; Microsoft_FStar_Absyn_Syntax.uvs = _65_10650})))))

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
in (match (((Support.ST.read Microsoft_FStar_Options.debug) <> [])) with
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
in (let _65_10718 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _65_10718))))
and serialize_args = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun ( writer ) ( ast ) -> (let _25_286 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (let _65_10723 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _65_10723))))
and serialize_binders = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun ( writer ) ( ast ) -> (let _65_10728 = (Microsoft_FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _65_10728)))
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
and serialize_exp = (fun ( writer ) ( ast ) -> (let _65_10753 = (Microsoft_FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _65_10753)))
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
and serialize_knd = (fun ( writer ) ( ast ) -> (let _65_10768 = (Microsoft_FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _65_10768)))
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
(let _65_10819 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_btvar (_65_10819))
end
| 'b' -> begin
(let _65_10820 = (deserialize_ftvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_const (_65_10820))
end
| 'c' -> begin
(let _65_10823 = (let _65_10822 = (deserialize_binders reader)
in (let _65_10821 = (deserialize_comp reader)
in (_65_10822, _65_10821)))
in Microsoft_FStar_Absyn_Syntax.Typ_fun (_65_10823))
end
| 'd' -> begin
(let _65_10826 = (let _65_10825 = (deserialize_bvvar reader)
in (let _65_10824 = (deserialize_typ reader)
in (_65_10825, _65_10824)))
in Microsoft_FStar_Absyn_Syntax.Typ_refine (_65_10826))
end
| 'e' -> begin
(let _65_10829 = (let _65_10828 = (deserialize_typ reader)
in (let _65_10827 = (deserialize_args reader)
in (_65_10828, _65_10827)))
in Microsoft_FStar_Absyn_Syntax.Typ_app (_65_10829))
end
| 'f' -> begin
(let _65_10832 = (let _65_10831 = (deserialize_binders reader)
in (let _65_10830 = (deserialize_typ reader)
in (_65_10831, _65_10830)))
in Microsoft_FStar_Absyn_Syntax.Typ_lam (_65_10832))
end
| 'g' -> begin
(let _65_10835 = (let _65_10834 = (deserialize_typ reader)
in (let _65_10833 = (deserialize_knd reader)
in (_65_10834, _65_10833)))
in Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_65_10835))
end
| 'h' -> begin
(let _65_10836 = (deserialize_meta_t reader)
in Microsoft_FStar_Absyn_Syntax.Typ_meta (_65_10836))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _65_10840 = (let _65_10839 = (deserialize_typ reader)
in (let _65_10838 = (deserialize_list reader deserialize_arg)
in (_65_10839, _65_10838)))
in Microsoft_FStar_Absyn_Syntax.Meta_pattern (_65_10840))
end
| 'b' -> begin
(let _65_10843 = (let _65_10842 = (deserialize_typ reader)
in (let _65_10841 = (deserialize_lident reader)
in (_65_10842, _65_10841)))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_65_10843))
end
| 'c' -> begin
(let _65_10847 = (let _65_10846 = (deserialize_typ reader)
in (let _65_10845 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (let _65_10844 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_65_10846, _65_10845, Microsoft_FStar_Absyn_Syntax.dummyRange, _65_10844))))
in Microsoft_FStar_Absyn_Syntax.Meta_labeled (_65_10847))
end
| _ -> begin
(parse_error ())
end))
and deserialize_arg = (fun ( reader ) -> (let _65_10851 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _65_10850 = (let _65_10849 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _65_10849))
in (_65_10851, _65_10850))))
and deserialize_args = (fun ( reader ) -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun ( reader ) -> (let _65_10856 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _65_10855 = (let _65_10854 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _65_10854))
in (_65_10856, _65_10855))))
and deserialize_binders = (fun ( reader ) -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun ( reader ) -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun ( reader ) -> (let _65_10863 = (deserialize_lident reader)
in (let _65_10862 = (deserialize_typ reader)
in (let _65_10861 = (deserialize_args reader)
in (let _65_10860 = (deserialize_list reader deserialize_cflags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _65_10863; Microsoft_FStar_Absyn_Syntax.result_typ = _65_10862; Microsoft_FStar_Absyn_Syntax.effect_args = _65_10861; Microsoft_FStar_Absyn_Syntax.flags = _65_10860})))))
and deserialize_comp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _65_10865 = (deserialize_typ reader)
in Microsoft_FStar_Absyn_Syntax.Total (_65_10865))
end
| 'b' -> begin
(let _65_10866 = (deserialize_comp_typ reader)
in Microsoft_FStar_Absyn_Syntax.Comp (_65_10866))
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
(let _65_10869 = (deserialize_exp reader)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_65_10869))
end
| _ -> begin
(parse_error ())
end))
and deserialize_exp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _65_10871 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Exp_bvar (_65_10871))
end
| 'b' -> begin
(let _65_10874 = (let _65_10873 = (deserialize_fvvar reader)
in (_65_10873, (let _25_606 = (let _65_10872 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Support.Prims.ignore _65_10872))
in None)))
in Microsoft_FStar_Absyn_Syntax.Exp_fvar (_65_10874))
end
| 'c' -> begin
(let _65_10875 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Exp_constant (_65_10875))
end
| 'd' -> begin
(let _65_10878 = (let _65_10877 = (deserialize_binders reader)
in (let _65_10876 = (deserialize_exp reader)
in (_65_10877, _65_10876)))
in Microsoft_FStar_Absyn_Syntax.Exp_abs (_65_10878))
end
| 'e' -> begin
(let _65_10881 = (let _65_10880 = (deserialize_exp reader)
in (let _65_10879 = (deserialize_args reader)
in (_65_10880, _65_10879)))
in Microsoft_FStar_Absyn_Syntax.Exp_app (_65_10881))
end
| 'f' -> begin
(let g = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _65_10884 = (deserialize_exp reader)
in Some (_65_10884))
end
| 'b' -> begin
None
end
| _ -> begin
(parse_error ())
end))
in (let f = (fun ( reader ) -> (let _65_10889 = (deserialize_pat reader)
in (let _65_10888 = (g reader)
in (let _65_10887 = (deserialize_exp reader)
in (_65_10889, _65_10888, _65_10887)))))
in (let _65_10892 = (let _65_10891 = (deserialize_exp reader)
in (let _65_10890 = (deserialize_list reader f)
in (_65_10891, _65_10890)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (_65_10892))))
end
| 'g' -> begin
(let _65_10896 = (let _65_10895 = (deserialize_exp reader)
in (let _65_10894 = (deserialize_typ reader)
in (let _65_10893 = (deserialize_option reader deserialize_lident)
in (_65_10895, _65_10894, _65_10893))))
in Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_65_10896))
end
| 'h' -> begin
(let _65_10899 = (let _65_10898 = (deserialize_letbindings reader)
in (let _65_10897 = (deserialize_exp reader)
in (_65_10898, _65_10897)))
in Microsoft_FStar_Absyn_Syntax.Exp_let (_65_10899))
end
| 'i' -> begin
(let _65_10900 = (deserialize_meta_e reader)
in Microsoft_FStar_Absyn_Syntax.Exp_meta (_65_10900))
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _65_10904 = (let _65_10903 = (deserialize_exp reader)
in (let _65_10902 = (deserialize_meta_source_info reader)
in (_65_10903, _65_10902)))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_65_10904))
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
(let _65_10910 = (deserialize_list reader deserialize_pat)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_65_10910))
end
| 'b' -> begin
(let _65_10911 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Pat_constant (_65_10911))
end
| 'c' -> begin
(let _65_10914 = (let _65_10913 = (deserialize_fvvar reader)
in (let _65_10912 = (deserialize_list reader deserialize_pat)
in (_65_10913, None, _65_10912)))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_65_10914))
end
| 'd' -> begin
(let _65_10917 = (let _65_10916 = (deserialize_bvvar reader)
in (let _65_10915 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_65_10916, _65_10915)))
in Microsoft_FStar_Absyn_Syntax.Pat_var (_65_10917))
end
| 'e' -> begin
(let _65_10918 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_65_10918))
end
| 'f' -> begin
(let _65_10919 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_65_10919))
end
| 'g' -> begin
(let _65_10920 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_65_10920))
end
| 'h' -> begin
(let _65_10923 = (let _65_10922 = (deserialize_bvvar reader)
in (let _65_10921 = (deserialize_exp reader)
in (_65_10922, _65_10921)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_65_10923))
end
| 'i' -> begin
(let _65_10926 = (let _65_10925 = (deserialize_btvar reader)
in (let _65_10924 = (deserialize_typ reader)
in (_65_10925, _65_10924)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_65_10926))
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
(let _65_10932 = (let _65_10931 = (deserialize_kabbrev reader)
in (let _65_10930 = (deserialize_knd reader)
in (_65_10931, _65_10930)))
in Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_65_10932))
end
| 'd' -> begin
(let _65_10935 = (let _65_10934 = (deserialize_binders reader)
in (let _65_10933 = (deserialize_knd reader)
in (_65_10934, _65_10933)))
in Microsoft_FStar_Absyn_Syntax.Kind_arrow (_65_10935))
end
| 'e' -> begin
(let _65_10938 = (let _65_10937 = (deserialize_binders reader)
in (let _65_10936 = (deserialize_knd reader)
in (_65_10937, _65_10936)))
in Microsoft_FStar_Absyn_Syntax.Kind_lam (_65_10938))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_knd = (fun ( reader ) -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun ( reader ) -> (let _65_10942 = (deserialize_lident reader)
in (let _65_10941 = (deserialize_args reader)
in (_65_10942, _65_10941))))
and deserialize_lbname = (fun ( reader ) -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun ( reader ) -> (let f = (fun ( reader ) -> (let _65_10950 = (deserialize_lbname reader)
in (let _65_10949 = (deserialize_typ reader)
in (let _65_10948 = (deserialize_lident reader)
in (let _65_10947 = (deserialize_exp reader)
in {Microsoft_FStar_Absyn_Syntax.lbname = _65_10950; Microsoft_FStar_Absyn_Syntax.lbtyp = _65_10949; Microsoft_FStar_Absyn_Syntax.lbeff = _65_10948; Microsoft_FStar_Absyn_Syntax.lbdef = _65_10947})))))
in (let _65_10952 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (let _65_10951 = (deserialize_list reader f)
in (_65_10952, _65_10951)))))
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
(let _65_10967 = (deserialize_lident reader)
in Microsoft_FStar_Absyn_Syntax.Discriminator (_65_10967))
end
| 'j' -> begin
(let _65_10970 = (let _65_10969 = (deserialize_lident reader)
in (let _65_10968 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_65_10969, _65_10968)))
in Microsoft_FStar_Absyn_Syntax.Projector (_65_10970))
end
| 'k' -> begin
(let _65_10971 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordType (_65_10971))
end
| 'l' -> begin
(let _65_10972 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordConstructor (_65_10972))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _65_10974 = (deserialize_option reader deserialize_lident)
in (Support.Prims.pipe_right _65_10974 (fun ( _65_10973 ) -> Microsoft_FStar_Absyn_Syntax.DefaultEffect (_65_10973))))
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

let deserialize_tycon = (fun ( reader ) -> (let _65_10983 = (deserialize_lident reader)
in (let _65_10982 = (deserialize_binders reader)
in (let _65_10981 = (deserialize_knd reader)
in (_65_10983, _65_10982, _65_10981)))))

let serialize_monad_abbrev = (fun ( writer ) ( ast ) -> (let _25_735 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _25_737 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun ( reader ) -> (let _65_10992 = (deserialize_lident reader)
in (let _65_10991 = (deserialize_binders reader)
in (let _65_10990 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mabbrev = _65_10992; Microsoft_FStar_Absyn_Syntax.parms = _65_10991; Microsoft_FStar_Absyn_Syntax.def = _65_10990}))))

let serialize_sub_effect = (fun ( writer ) ( ast ) -> (let _25_742 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _25_744 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun ( reader ) -> (let _65_11001 = (deserialize_lident reader)
in (let _65_11000 = (deserialize_lident reader)
in (let _65_10999 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.source = _65_11001; Microsoft_FStar_Absyn_Syntax.target = _65_11000; Microsoft_FStar_Absyn_Syntax.lift = _65_10999}))))

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
(let _65_11011 = (let _65_11010 = (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))
in (f, _65_11010))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _65_11011 None Microsoft_FStar_Absyn_Syntax.dummyRange))
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
in (let _65_11013 = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _25_1 ) -> (match (_25_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))))
in (writer.Support.Microsoft.FStar.Util.write_bool _65_11013)))))
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

let rec deserialize_new_effect = (fun ( reader ) -> (let _65_11034 = (deserialize_lident reader)
in (let _65_11033 = (deserialize_list reader deserialize_binder)
in (let _65_11032 = (deserialize_list reader deserialize_qualifier)
in (let _65_11031 = (deserialize_knd reader)
in (let _65_11030 = (deserialize_typ reader)
in (let _65_11029 = (deserialize_typ reader)
in (let _65_11028 = (deserialize_typ reader)
in (let _65_11027 = (deserialize_typ reader)
in (let _65_11026 = (deserialize_typ reader)
in (let _65_11025 = (deserialize_typ reader)
in (let _65_11024 = (deserialize_typ reader)
in (let _65_11023 = (deserialize_typ reader)
in (let _65_11022 = (deserialize_typ reader)
in (let _65_11021 = (deserialize_typ reader)
in (let _65_11020 = (deserialize_typ reader)
in (let _65_11019 = (deserialize_typ reader)
in (let _65_11018 = (deserialize_typ reader)
in (let _65_11017 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mname = _65_11034; Microsoft_FStar_Absyn_Syntax.binders = _65_11033; Microsoft_FStar_Absyn_Syntax.qualifiers = _65_11032; Microsoft_FStar_Absyn_Syntax.signature = _65_11031; Microsoft_FStar_Absyn_Syntax.ret = _65_11030; Microsoft_FStar_Absyn_Syntax.bind_wp = _65_11029; Microsoft_FStar_Absyn_Syntax.bind_wlp = _65_11028; Microsoft_FStar_Absyn_Syntax.if_then_else = _65_11027; Microsoft_FStar_Absyn_Syntax.ite_wp = _65_11026; Microsoft_FStar_Absyn_Syntax.ite_wlp = _65_11025; Microsoft_FStar_Absyn_Syntax.wp_binop = _65_11024; Microsoft_FStar_Absyn_Syntax.wp_as_type = _65_11023; Microsoft_FStar_Absyn_Syntax.close_wp = _65_11022; Microsoft_FStar_Absyn_Syntax.close_wp_t = _65_11021; Microsoft_FStar_Absyn_Syntax.assert_p = _65_11020; Microsoft_FStar_Absyn_Syntax.assume_p = _65_11019; Microsoft_FStar_Absyn_Syntax.null_wp = _65_11018; Microsoft_FStar_Absyn_Syntax.trivial = _65_11017})))))))))))))))))))
and deserialize_sigelt = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _65_11042 = (let _65_11041 = (deserialize_lident reader)
in (let _65_11040 = (deserialize_binders reader)
in (let _65_11039 = (deserialize_knd reader)
in (let _65_11038 = (deserialize_list reader deserialize_lident)
in (let _65_11037 = (deserialize_list reader deserialize_lident)
in (let _65_11036 = (deserialize_list reader deserialize_qualifier)
in (_65_11041, _65_11040, _65_11039, _65_11038, _65_11037, _65_11036, Microsoft_FStar_Absyn_Syntax.dummyRange)))))))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_65_11042))
end
| 'b' -> begin
(let _65_11048 = (let _65_11047 = (deserialize_lident reader)
in (let _65_11046 = (deserialize_binders reader)
in (let _65_11045 = (deserialize_knd reader)
in (let _65_11044 = (deserialize_typ reader)
in (let _65_11043 = (deserialize_list reader deserialize_qualifier)
in (_65_11047, _65_11046, _65_11045, _65_11044, _65_11043, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_65_11048))
end
| 'c' -> begin
(let _65_11054 = (let _65_11053 = (deserialize_lident reader)
in (let _65_11052 = (deserialize_typ reader)
in (let _65_11051 = (deserialize_tycon reader)
in (let _65_11050 = (deserialize_list reader deserialize_qualifier)
in (let _65_11049 = (deserialize_list reader deserialize_lident)
in (_65_11053, _65_11052, _65_11051, _65_11050, _65_11049, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_65_11054))
end
| 'd' -> begin
(let _65_11058 = (let _65_11057 = (deserialize_lident reader)
in (let _65_11056 = (deserialize_typ reader)
in (let _65_11055 = (deserialize_list reader deserialize_qualifier)
in (_65_11057, _65_11056, _65_11055, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_65_11058))
end
| 'e' -> begin
(let _65_11062 = (let _65_11061 = (deserialize_lident reader)
in (let _65_11060 = (deserialize_formula reader)
in (let _65_11059 = (deserialize_list reader deserialize_qualifier)
in (_65_11061, _65_11060, _65_11059, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_65_11062))
end
| 'f' -> begin
(let _65_11066 = (let _65_11065 = (deserialize_letbindings reader)
in (let _65_11064 = (deserialize_list reader deserialize_lident)
in (let _65_11063 = (match ((reader.Support.Microsoft.FStar.Util.read_bool ())) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end
| false -> begin
[]
end)
in (_65_11065, Microsoft_FStar_Absyn_Syntax.dummyRange, _65_11064, _65_11063))))
in Microsoft_FStar_Absyn_Syntax.Sig_let (_65_11066))
end
| 'g' -> begin
(let _65_11068 = (let _65_11067 = (deserialize_exp reader)
in (_65_11067, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_main (_65_11068))
end
| 'h' -> begin
(let _65_11072 = (let _65_11071 = (deserialize_list reader deserialize_sigelt)
in (let _65_11070 = (deserialize_list reader deserialize_qualifier)
in (let _65_11069 = (deserialize_list reader deserialize_lident)
in (_65_11071, _65_11070, _65_11069, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_65_11072))
end
| 'i' -> begin
(let _65_11074 = (let _65_11073 = (deserialize_new_effect reader)
in (_65_11073, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_65_11074))
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

let deserialize_modul = (fun ( reader ) -> (let m = (let _65_11090 = (deserialize_lident reader)
in (let _65_11089 = (deserialize_sigelts reader)
in (let _65_11088 = (deserialize_sigelts reader)
in (let _65_11087 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in {Microsoft_FStar_Absyn_Syntax.name = _65_11090; Microsoft_FStar_Absyn_Syntax.declarations = _65_11089; Microsoft_FStar_Absyn_Syntax.exports = _65_11088; Microsoft_FStar_Absyn_Syntax.is_interface = _65_11087; Microsoft_FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _25_988 = m
in {Microsoft_FStar_Absyn_Syntax.name = _25_988.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _25_988.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _25_988.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _25_988.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




