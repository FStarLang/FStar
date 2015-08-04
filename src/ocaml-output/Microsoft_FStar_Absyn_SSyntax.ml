
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
(let _68_10493 = (f reader)
in Some (_68_10493))
end)))

let serialize_list = (fun ( writer ) ( f ) ( l ) -> (let _25_21 = (writer.Support.Microsoft.FStar.Util.write_int (Support.List.length l))
in (Support.List.iter (fun ( elt ) -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun ( reader ) ( f ) -> (let n = (reader.Support.Microsoft.FStar.Util.read_int ())
in (let rec helper = (fun ( accum ) ( n ) -> (match ((n = 0)) with
| true -> begin
accum
end
| false -> begin
(let _68_10514 = (let _68_10513 = (f reader)
in (_68_10513)::accum)
in (helper _68_10514 (n - 1)))
end))
in (helper [] n))))

let serialize_ident = (fun ( writer ) ( ast ) -> (writer.Support.Microsoft.FStar.Util.write_string ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun ( reader ) -> (let _68_10522 = (let _68_10521 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (_68_10521, Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _68_10522)))

let serialize_LongIdent = (fun ( writer ) ( ast ) -> (let _25_36 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun ( reader ) -> (let _68_10532 = (let _68_10531 = (deserialize_list reader deserialize_ident)
in (let _68_10530 = (let _68_10529 = (deserialize_ident reader)
in (_68_10529)::[])
in (Support.List.append _68_10531 _68_10530)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _68_10532)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun ( writer ) ( s_v ) ( s_sort ) ( ast ) -> (let _25_45 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun ( reader ) ( ds_v ) ( ds_sort ) -> (let _68_10562 = (ds_v reader)
in (let _68_10561 = (ds_sort reader)
in {Microsoft_FStar_Absyn_Syntax.v = _68_10562; Microsoft_FStar_Absyn_Syntax.sort = _68_10561; Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun ( writer ) ( s_sort ) ( ast ) -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun ( reader ) ( ds_sort ) -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun ( writer ) ( ast ) -> (let _25_62 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ( ghost ) ( reader ) -> (let _68_10582 = (deserialize_ident reader)
in (let _68_10581 = (deserialize_ident reader)
in {Microsoft_FStar_Absyn_Syntax.ppname = _68_10582; Microsoft_FStar_Absyn_Syntax.realname = _68_10581})))

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
(let _68_10604 = (reader.Support.Microsoft.FStar.Util.read_byte ())
in Microsoft_FStar_Absyn_Syntax.Const_uint8 (_68_10604))
end
| 'c' -> begin
(let _68_10605 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in Microsoft_FStar_Absyn_Syntax.Const_bool (_68_10605))
end
| 'd' -> begin
(let _68_10606 = (reader.Support.Microsoft.FStar.Util.read_int32 ())
in Microsoft_FStar_Absyn_Syntax.Const_int32 (_68_10606))
end
| 'e' -> begin
(let _68_10607 = (reader.Support.Microsoft.FStar.Util.read_int64 ())
in Microsoft_FStar_Absyn_Syntax.Const_int64 (_68_10607))
end
| 'f' -> begin
(let _68_10608 = (reader.Support.Microsoft.FStar.Util.read_char ())
in Microsoft_FStar_Absyn_Syntax.Const_char (_68_10608))
end
| 'g' -> begin
(let _68_10609 = (reader.Support.Microsoft.FStar.Util.read_double ())
in Microsoft_FStar_Absyn_Syntax.Const_float (_68_10609))
end
| 'h' -> begin
(let _68_10611 = (let _68_10610 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_68_10610, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_bytearray (_68_10611))
end
| 'i' -> begin
(let _68_10613 = (let _68_10612 = (reader.Support.Microsoft.FStar.Util.read_bytearray ())
in (_68_10612, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Const_string (_68_10613))
end
| 'j' -> begin
(let _68_10614 = (reader.Support.Microsoft.FStar.Util.read_string ())
in Microsoft_FStar_Absyn_Syntax.Const_int (_68_10614))
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
(let _68_10640 = (ds_l reader)
in Support.Microsoft.FStar.Util.Inl (_68_10640))
end
| 'b' -> begin
(let _68_10641 = (ds_r reader)
in Support.Microsoft.FStar.Util.Inr (_68_10641))
end
| _ -> begin
(parse_error ())
end))

let serialize_syntax = (fun ( writer ) ( s_a ) ( ast ) -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun ( reader ) ( ds_a ) ( ds_b ) -> (let _68_10660 = (ds_a reader)
in (let _68_10659 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _68_10658 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _68_10657 = (Support.Microsoft.FStar.Util.mk_ref None)
in {Microsoft_FStar_Absyn_Syntax.n = _68_10660; Microsoft_FStar_Absyn_Syntax.tk = _68_10659; Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = _68_10658; Microsoft_FStar_Absyn_Syntax.uvs = _68_10657})))))

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
in (let _68_10725 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _68_10725))))
and serialize_args = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun ( writer ) ( ast ) -> (let _25_286 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (let _68_10730 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast))
in (writer.Support.Microsoft.FStar.Util.write_bool _68_10730))))
and serialize_binders = (fun ( writer ) ( ast ) -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun ( writer ) ( ast ) -> (let _68_10735 = (Microsoft_FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _68_10735)))
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
and serialize_exp = (fun ( writer ) ( ast ) -> (let _68_10760 = (Microsoft_FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _68_10760)))
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
and serialize_knd = (fun ( writer ) ( ast ) -> (let _68_10775 = (Microsoft_FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _68_10775)))
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
(let _68_10826 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_btvar (_68_10826))
end
| 'b' -> begin
(let _68_10827 = (deserialize_ftvar reader)
in Microsoft_FStar_Absyn_Syntax.Typ_const (_68_10827))
end
| 'c' -> begin
(let _68_10830 = (let _68_10829 = (deserialize_binders reader)
in (let _68_10828 = (deserialize_comp reader)
in (_68_10829, _68_10828)))
in Microsoft_FStar_Absyn_Syntax.Typ_fun (_68_10830))
end
| 'd' -> begin
(let _68_10833 = (let _68_10832 = (deserialize_bvvar reader)
in (let _68_10831 = (deserialize_typ reader)
in (_68_10832, _68_10831)))
in Microsoft_FStar_Absyn_Syntax.Typ_refine (_68_10833))
end
| 'e' -> begin
(let _68_10836 = (let _68_10835 = (deserialize_typ reader)
in (let _68_10834 = (deserialize_args reader)
in (_68_10835, _68_10834)))
in Microsoft_FStar_Absyn_Syntax.Typ_app (_68_10836))
end
| 'f' -> begin
(let _68_10839 = (let _68_10838 = (deserialize_binders reader)
in (let _68_10837 = (deserialize_typ reader)
in (_68_10838, _68_10837)))
in Microsoft_FStar_Absyn_Syntax.Typ_lam (_68_10839))
end
| 'g' -> begin
(let _68_10842 = (let _68_10841 = (deserialize_typ reader)
in (let _68_10840 = (deserialize_knd reader)
in (_68_10841, _68_10840)))
in Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_68_10842))
end
| 'h' -> begin
(let _68_10843 = (deserialize_meta_t reader)
in Microsoft_FStar_Absyn_Syntax.Typ_meta (_68_10843))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _68_10847 = (let _68_10846 = (deserialize_typ reader)
in (let _68_10845 = (deserialize_list reader deserialize_arg)
in (_68_10846, _68_10845)))
in Microsoft_FStar_Absyn_Syntax.Meta_pattern (_68_10847))
end
| 'b' -> begin
(let _68_10850 = (let _68_10849 = (deserialize_typ reader)
in (let _68_10848 = (deserialize_lident reader)
in (_68_10849, _68_10848)))
in Microsoft_FStar_Absyn_Syntax.Meta_named (_68_10850))
end
| 'c' -> begin
(let _68_10854 = (let _68_10853 = (deserialize_typ reader)
in (let _68_10852 = (reader.Support.Microsoft.FStar.Util.read_string ())
in (let _68_10851 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_68_10853, _68_10852, Microsoft_FStar_Absyn_Syntax.dummyRange, _68_10851))))
in Microsoft_FStar_Absyn_Syntax.Meta_labeled (_68_10854))
end
| _ -> begin
(parse_error ())
end))
and deserialize_arg = (fun ( reader ) -> (let _68_10858 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _68_10857 = (let _68_10856 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _68_10856))
in (_68_10858, _68_10857))))
and deserialize_args = (fun ( reader ) -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun ( reader ) -> (let _68_10863 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _68_10862 = (let _68_10861 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.as_implicit _68_10861))
in (_68_10863, _68_10862))))
and deserialize_binders = (fun ( reader ) -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun ( reader ) -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun ( reader ) -> (let _68_10870 = (deserialize_lident reader)
in (let _68_10869 = (deserialize_typ reader)
in (let _68_10868 = (deserialize_args reader)
in (let _68_10867 = (deserialize_list reader deserialize_cflags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _68_10870; Microsoft_FStar_Absyn_Syntax.result_typ = _68_10869; Microsoft_FStar_Absyn_Syntax.effect_args = _68_10868; Microsoft_FStar_Absyn_Syntax.flags = _68_10867})))))
and deserialize_comp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _68_10872 = (deserialize_typ reader)
in Microsoft_FStar_Absyn_Syntax.Total (_68_10872))
end
| 'b' -> begin
(let _68_10873 = (deserialize_comp_typ reader)
in Microsoft_FStar_Absyn_Syntax.Comp (_68_10873))
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
(let _68_10876 = (deserialize_exp reader)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_68_10876))
end
| _ -> begin
(parse_error ())
end))
and deserialize_exp' = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _68_10878 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Exp_bvar (_68_10878))
end
| 'b' -> begin
(let _68_10882 = (let _68_10881 = (deserialize_fvvar reader)
in (let _68_10880 = (let _25_606 = (let _68_10879 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (Support.Prims.pipe_left Support.Prims.ignore _68_10879))
in None)
in (_68_10881, _68_10880)))
in Microsoft_FStar_Absyn_Syntax.Exp_fvar (_68_10882))
end
| 'c' -> begin
(let _68_10883 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Exp_constant (_68_10883))
end
| 'd' -> begin
(let _68_10886 = (let _68_10885 = (deserialize_binders reader)
in (let _68_10884 = (deserialize_exp reader)
in (_68_10885, _68_10884)))
in Microsoft_FStar_Absyn_Syntax.Exp_abs (_68_10886))
end
| 'e' -> begin
(let _68_10889 = (let _68_10888 = (deserialize_exp reader)
in (let _68_10887 = (deserialize_args reader)
in (_68_10888, _68_10887)))
in Microsoft_FStar_Absyn_Syntax.Exp_app (_68_10889))
end
| 'f' -> begin
(let g = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _68_10892 = (deserialize_exp reader)
in Some (_68_10892))
end
| 'b' -> begin
None
end
| _ -> begin
(parse_error ())
end))
in (let f = (fun ( reader ) -> (let _68_10897 = (deserialize_pat reader)
in (let _68_10896 = (g reader)
in (let _68_10895 = (deserialize_exp reader)
in (_68_10897, _68_10896, _68_10895)))))
in (let _68_10900 = (let _68_10899 = (deserialize_exp reader)
in (let _68_10898 = (deserialize_list reader f)
in (_68_10899, _68_10898)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (_68_10900))))
end
| 'g' -> begin
(let _68_10904 = (let _68_10903 = (deserialize_exp reader)
in (let _68_10902 = (deserialize_typ reader)
in (let _68_10901 = (deserialize_option reader deserialize_lident)
in (_68_10903, _68_10902, _68_10901))))
in Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_68_10904))
end
| 'h' -> begin
(let _68_10907 = (let _68_10906 = (deserialize_letbindings reader)
in (let _68_10905 = (deserialize_exp reader)
in (_68_10906, _68_10905)))
in Microsoft_FStar_Absyn_Syntax.Exp_let (_68_10907))
end
| 'i' -> begin
(let _68_10908 = (deserialize_meta_e reader)
in Microsoft_FStar_Absyn_Syntax.Exp_meta (_68_10908))
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _68_10912 = (let _68_10911 = (deserialize_exp reader)
in (let _68_10910 = (deserialize_meta_source_info reader)
in (_68_10911, _68_10910)))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_10912))
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
(let _68_10918 = (deserialize_list reader deserialize_pat)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_68_10918))
end
| 'b' -> begin
(let _68_10919 = (deserialize_sconst reader)
in Microsoft_FStar_Absyn_Syntax.Pat_constant (_68_10919))
end
| 'c' -> begin
(let _68_10922 = (let _68_10921 = (deserialize_fvvar reader)
in (let _68_10920 = (deserialize_list reader deserialize_pat)
in (_68_10921, None, _68_10920)))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_68_10922))
end
| 'd' -> begin
(let _68_10925 = (let _68_10924 = (deserialize_bvvar reader)
in (let _68_10923 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (_68_10924, _68_10923)))
in Microsoft_FStar_Absyn_Syntax.Pat_var (_68_10925))
end
| 'e' -> begin
(let _68_10926 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_68_10926))
end
| 'f' -> begin
(let _68_10927 = (deserialize_bvvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_68_10927))
end
| 'g' -> begin
(let _68_10928 = (deserialize_btvar reader)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_68_10928))
end
| 'h' -> begin
(let _68_10931 = (let _68_10930 = (deserialize_bvvar reader)
in (let _68_10929 = (deserialize_exp reader)
in (_68_10930, _68_10929)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_68_10931))
end
| 'i' -> begin
(let _68_10934 = (let _68_10933 = (deserialize_btvar reader)
in (let _68_10932 = (deserialize_typ reader)
in (_68_10933, _68_10932)))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_68_10934))
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
(let _68_10940 = (let _68_10939 = (deserialize_kabbrev reader)
in (let _68_10938 = (deserialize_knd reader)
in (_68_10939, _68_10938)))
in Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_68_10940))
end
| 'd' -> begin
(let _68_10943 = (let _68_10942 = (deserialize_binders reader)
in (let _68_10941 = (deserialize_knd reader)
in (_68_10942, _68_10941)))
in Microsoft_FStar_Absyn_Syntax.Kind_arrow (_68_10943))
end
| 'e' -> begin
(let _68_10946 = (let _68_10945 = (deserialize_binders reader)
in (let _68_10944 = (deserialize_knd reader)
in (_68_10945, _68_10944)))
in Microsoft_FStar_Absyn_Syntax.Kind_lam (_68_10946))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_knd = (fun ( reader ) -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun ( reader ) -> (let _68_10950 = (deserialize_lident reader)
in (let _68_10949 = (deserialize_args reader)
in (_68_10950, _68_10949))))
and deserialize_lbname = (fun ( reader ) -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun ( reader ) -> (let f = (fun ( reader ) -> (let _68_10958 = (deserialize_lbname reader)
in (let _68_10957 = (deserialize_typ reader)
in (let _68_10956 = (deserialize_lident reader)
in (let _68_10955 = (deserialize_exp reader)
in {Microsoft_FStar_Absyn_Syntax.lbname = _68_10958; Microsoft_FStar_Absyn_Syntax.lbtyp = _68_10957; Microsoft_FStar_Absyn_Syntax.lbeff = _68_10956; Microsoft_FStar_Absyn_Syntax.lbdef = _68_10955})))))
in (let _68_10960 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in (let _68_10959 = (deserialize_list reader f)
in (_68_10960, _68_10959)))))
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
(let _68_10975 = (deserialize_lident reader)
in Microsoft_FStar_Absyn_Syntax.Discriminator (_68_10975))
end
| 'j' -> begin
(let _68_10978 = (let _68_10977 = (deserialize_lident reader)
in (let _68_10976 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_68_10977, _68_10976)))
in Microsoft_FStar_Absyn_Syntax.Projector (_68_10978))
end
| 'k' -> begin
(let _68_10979 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordType (_68_10979))
end
| 'l' -> begin
(let _68_10980 = (deserialize_list reader deserialize_lident)
in Microsoft_FStar_Absyn_Syntax.RecordConstructor (_68_10980))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _68_10982 = (deserialize_option reader deserialize_lident)
in (Support.Prims.pipe_right _68_10982 (fun ( _68_10981 ) -> Microsoft_FStar_Absyn_Syntax.DefaultEffect (_68_10981))))
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

let deserialize_tycon = (fun ( reader ) -> (let _68_10991 = (deserialize_lident reader)
in (let _68_10990 = (deserialize_binders reader)
in (let _68_10989 = (deserialize_knd reader)
in (_68_10991, _68_10990, _68_10989)))))

let serialize_monad_abbrev = (fun ( writer ) ( ast ) -> (let _25_735 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _25_737 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun ( reader ) -> (let _68_11000 = (deserialize_lident reader)
in (let _68_10999 = (deserialize_binders reader)
in (let _68_10998 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mabbrev = _68_11000; Microsoft_FStar_Absyn_Syntax.parms = _68_10999; Microsoft_FStar_Absyn_Syntax.def = _68_10998}))))

let serialize_sub_effect = (fun ( writer ) ( ast ) -> (let _25_742 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _25_744 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun ( reader ) -> (let _68_11009 = (deserialize_lident reader)
in (let _68_11008 = (deserialize_lident reader)
in (let _68_11007 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.source = _68_11009; Microsoft_FStar_Absyn_Syntax.target = _68_11008; Microsoft_FStar_Absyn_Syntax.lift = _68_11007}))))

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
(let _68_11019 = (let _68_11018 = (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))
in (f, _68_11018))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_11019 None Microsoft_FStar_Absyn_Syntax.dummyRange))
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
in (let _68_11021 = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _25_1 ) -> (match (_25_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))))
in (writer.Support.Microsoft.FStar.Util.write_bool _68_11021)))))
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

let rec deserialize_new_effect = (fun ( reader ) -> (let _68_11042 = (deserialize_lident reader)
in (let _68_11041 = (deserialize_list reader deserialize_binder)
in (let _68_11040 = (deserialize_list reader deserialize_qualifier)
in (let _68_11039 = (deserialize_knd reader)
in (let _68_11038 = (deserialize_typ reader)
in (let _68_11037 = (deserialize_typ reader)
in (let _68_11036 = (deserialize_typ reader)
in (let _68_11035 = (deserialize_typ reader)
in (let _68_11034 = (deserialize_typ reader)
in (let _68_11033 = (deserialize_typ reader)
in (let _68_11032 = (deserialize_typ reader)
in (let _68_11031 = (deserialize_typ reader)
in (let _68_11030 = (deserialize_typ reader)
in (let _68_11029 = (deserialize_typ reader)
in (let _68_11028 = (deserialize_typ reader)
in (let _68_11027 = (deserialize_typ reader)
in (let _68_11026 = (deserialize_typ reader)
in (let _68_11025 = (deserialize_typ reader)
in {Microsoft_FStar_Absyn_Syntax.mname = _68_11042; Microsoft_FStar_Absyn_Syntax.binders = _68_11041; Microsoft_FStar_Absyn_Syntax.qualifiers = _68_11040; Microsoft_FStar_Absyn_Syntax.signature = _68_11039; Microsoft_FStar_Absyn_Syntax.ret = _68_11038; Microsoft_FStar_Absyn_Syntax.bind_wp = _68_11037; Microsoft_FStar_Absyn_Syntax.bind_wlp = _68_11036; Microsoft_FStar_Absyn_Syntax.if_then_else = _68_11035; Microsoft_FStar_Absyn_Syntax.ite_wp = _68_11034; Microsoft_FStar_Absyn_Syntax.ite_wlp = _68_11033; Microsoft_FStar_Absyn_Syntax.wp_binop = _68_11032; Microsoft_FStar_Absyn_Syntax.wp_as_type = _68_11031; Microsoft_FStar_Absyn_Syntax.close_wp = _68_11030; Microsoft_FStar_Absyn_Syntax.close_wp_t = _68_11029; Microsoft_FStar_Absyn_Syntax.assert_p = _68_11028; Microsoft_FStar_Absyn_Syntax.assume_p = _68_11027; Microsoft_FStar_Absyn_Syntax.null_wp = _68_11026; Microsoft_FStar_Absyn_Syntax.trivial = _68_11025})))))))))))))))))))
and deserialize_sigelt = (fun ( reader ) -> (match ((reader.Support.Microsoft.FStar.Util.read_char ())) with
| 'a' -> begin
(let _68_11050 = (let _68_11049 = (deserialize_lident reader)
in (let _68_11048 = (deserialize_binders reader)
in (let _68_11047 = (deserialize_knd reader)
in (let _68_11046 = (deserialize_list reader deserialize_lident)
in (let _68_11045 = (deserialize_list reader deserialize_lident)
in (let _68_11044 = (deserialize_list reader deserialize_qualifier)
in (_68_11049, _68_11048, _68_11047, _68_11046, _68_11045, _68_11044, Microsoft_FStar_Absyn_Syntax.dummyRange)))))))
in Microsoft_FStar_Absyn_Syntax.Sig_tycon (_68_11050))
end
| 'b' -> begin
(let _68_11056 = (let _68_11055 = (deserialize_lident reader)
in (let _68_11054 = (deserialize_binders reader)
in (let _68_11053 = (deserialize_knd reader)
in (let _68_11052 = (deserialize_typ reader)
in (let _68_11051 = (deserialize_list reader deserialize_qualifier)
in (_68_11055, _68_11054, _68_11053, _68_11052, _68_11051, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_68_11056))
end
| 'c' -> begin
(let _68_11062 = (let _68_11061 = (deserialize_lident reader)
in (let _68_11060 = (deserialize_typ reader)
in (let _68_11059 = (deserialize_tycon reader)
in (let _68_11058 = (deserialize_list reader deserialize_qualifier)
in (let _68_11057 = (deserialize_list reader deserialize_lident)
in (_68_11061, _68_11060, _68_11059, _68_11058, _68_11057, Microsoft_FStar_Absyn_Syntax.dummyRange))))))
in Microsoft_FStar_Absyn_Syntax.Sig_datacon (_68_11062))
end
| 'd' -> begin
(let _68_11066 = (let _68_11065 = (deserialize_lident reader)
in (let _68_11064 = (deserialize_typ reader)
in (let _68_11063 = (deserialize_list reader deserialize_qualifier)
in (_68_11065, _68_11064, _68_11063, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_68_11066))
end
| 'e' -> begin
(let _68_11070 = (let _68_11069 = (deserialize_lident reader)
in (let _68_11068 = (deserialize_formula reader)
in (let _68_11067 = (deserialize_list reader deserialize_qualifier)
in (_68_11069, _68_11068, _68_11067, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_assume (_68_11070))
end
| 'f' -> begin
(let _68_11074 = (let _68_11073 = (deserialize_letbindings reader)
in (let _68_11072 = (deserialize_list reader deserialize_lident)
in (let _68_11071 = (match ((reader.Support.Microsoft.FStar.Util.read_bool ())) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end
| false -> begin
[]
end)
in (_68_11073, Microsoft_FStar_Absyn_Syntax.dummyRange, _68_11072, _68_11071))))
in Microsoft_FStar_Absyn_Syntax.Sig_let (_68_11074))
end
| 'g' -> begin
(let _68_11076 = (let _68_11075 = (deserialize_exp reader)
in (_68_11075, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_main (_68_11076))
end
| 'h' -> begin
(let _68_11080 = (let _68_11079 = (deserialize_list reader deserialize_sigelt)
in (let _68_11078 = (deserialize_list reader deserialize_qualifier)
in (let _68_11077 = (deserialize_list reader deserialize_lident)
in (_68_11079, _68_11078, _68_11077, Microsoft_FStar_Absyn_Syntax.dummyRange))))
in Microsoft_FStar_Absyn_Syntax.Sig_bundle (_68_11080))
end
| 'i' -> begin
(let _68_11082 = (let _68_11081 = (deserialize_new_effect reader)
in (_68_11081, Microsoft_FStar_Absyn_Syntax.dummyRange))
in Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_68_11082))
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

let deserialize_modul = (fun ( reader ) -> (let m = (let _68_11098 = (deserialize_lident reader)
in (let _68_11097 = (deserialize_sigelts reader)
in (let _68_11096 = (deserialize_sigelts reader)
in (let _68_11095 = (reader.Support.Microsoft.FStar.Util.read_bool ())
in {Microsoft_FStar_Absyn_Syntax.name = _68_11098; Microsoft_FStar_Absyn_Syntax.declarations = _68_11097; Microsoft_FStar_Absyn_Syntax.exports = _68_11096; Microsoft_FStar_Absyn_Syntax.is_interface = _68_11095; Microsoft_FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _25_988 = m
in {Microsoft_FStar_Absyn_Syntax.name = _25_988.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _25_988.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _25_988.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _25_988.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




