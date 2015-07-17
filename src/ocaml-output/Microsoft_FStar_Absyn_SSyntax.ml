
exception Err of (string)

let parse_error = (fun _20_3 -> (match (_20_3) with
| () -> begin
(failwith "Parse error: ill-formed cache")
end))

type l__Writer =
Support.Microsoft.FStar.Util.oWriter

type l__Reader =
Support.Microsoft.FStar.Util.oReader

let serialize_option = (fun writer f l -> (match (l) with
| None -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'n')
end
| Some (l) -> begin
(let _20_11 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 's')
in (f writer l))
end))

let deserialize_option = (fun reader f -> (let n = (Support.Microsoft.FStar.Util.MkoReader.read_char reader ())
in if (n = 'n') then begin
None
end else begin
Some ((f reader))
end))

let serialize_list = (fun writer f l -> (let _20_21 = (Support.Microsoft.FStar.Util.MkoWriter.write_int writer (Support.List.length l))
in (Support.List.iter (fun elt -> (f writer elt)) (Support.List.rev_append l []))))

let deserialize_list = (fun reader f -> (let n = (Support.Microsoft.FStar.Util.MkoReader.read_int reader ())
in (let rec helper = (fun accum n -> if (n = 0) then begin
accum
end else begin
(helper (((f reader))::accum) (n - 1))
end)
in (helper [] n))))

let serialize_ident = (fun writer ast -> (Support.Microsoft.FStar.Util.MkoWriter.write_string writer ast.Microsoft_FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun reader -> (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.Microsoft.FStar.Util.MkoReader.read_string reader ()), Microsoft_FStar_Absyn_Syntax.dummyRange)))

let serialize_LongIdent = (fun writer ast -> (let _20_36 = (serialize_list writer serialize_ident ast.Microsoft_FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun reader -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (deserialize_list reader deserialize_ident) (((deserialize_ident reader))::[]))))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun writer s_v s_sort ast -> (let _20_45 = (s_v writer ast.Microsoft_FStar_Absyn_Syntax.v)
in (s_sort writer ast.Microsoft_FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun reader ds_v ds_sort -> {Microsoft_FStar_Absyn_Syntax.v = (ds_v reader); Microsoft_FStar_Absyn_Syntax.sort = (ds_sort reader); Microsoft_FStar_Absyn_Syntax.p = Microsoft_FStar_Absyn_Syntax.dummyRange})

let serialize_var = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun reader ds_sort -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun writer ast -> (let _20_62 = (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.Microsoft_FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ghost reader -> {Microsoft_FStar_Absyn_Syntax.ppname = (deserialize_ident reader); Microsoft_FStar_Absyn_Syntax.realname = (deserialize_ident reader)})

let serialize_bvar = (fun writer s_sort ast -> (serialize_withinfo_t writer (serialize_bvdef) s_sort ast))

let deserialize_bvar = (fun ghost reader ds_sort -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

let serialize_sconst = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (v) -> begin
(let _20_82 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (Support.Microsoft.FStar.Util.MkoWriter.write_byte writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (v) -> begin
(let _20_86 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (v) -> begin
(let _20_90 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
in (Support.Microsoft.FStar.Util.MkoWriter.write_int32 writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (v) -> begin
(let _20_94 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
in (Support.Microsoft.FStar.Util.MkoWriter.write_int64 writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_char (v) -> begin
(let _20_98 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
in (Support.Microsoft.FStar.Util.MkoWriter.write_char writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_float (v) -> begin
(let _20_102 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
in (Support.Microsoft.FStar.Util.MkoWriter.write_double writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((v, _)) -> begin
(let _20_109 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'h')
in (Support.Microsoft.FStar.Util.MkoWriter.write_bytearray writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((v, _)) -> begin
(let _20_116 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'i')
in (Support.Microsoft.FStar.Util.MkoWriter.write_bytearray writer v))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (v) -> begin
(let _20_120 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'j')
in (Support.Microsoft.FStar.Util.MkoWriter.write_string writer v))
end))

let deserialize_sconst = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Const_unit
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Const_uint8 ((Support.Microsoft.FStar.Util.MkoReader.read_byte reader ()))
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Const_bool ((Support.Microsoft.FStar.Util.MkoReader.read_bool reader ()))
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.Const_int32 ((Support.Microsoft.FStar.Util.MkoReader.read_int32 reader ()))
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.Const_int64 ((Support.Microsoft.FStar.Util.MkoReader.read_int64 reader ()))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Const_char ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ()))
end
| 'g' -> begin
Microsoft_FStar_Absyn_Syntax.Const_float ((Support.Microsoft.FStar.Util.MkoReader.read_double reader ()))
end
| 'h' -> begin
Microsoft_FStar_Absyn_Syntax.Const_bytearray (((Support.Microsoft.FStar.Util.MkoReader.read_bytearray reader ()), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Const_string (((Support.Microsoft.FStar.Util.MkoReader.read_bytearray reader ()), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'j' -> begin
Microsoft_FStar_Absyn_Syntax.Const_int ((Support.Microsoft.FStar.Util.MkoReader.read_string reader ()))
end
| _ -> begin
(parse_error ())
end))

let serialize_either = (fun writer s_l s_r ast -> (match (ast) with
| Support.Microsoft.FStar.Util.Inl (v) -> begin
(let _20_143 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (s_l writer v))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _20_147 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (s_r writer v))
end))

let deserialize_either = (fun reader ds_l ds_r -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Support.Microsoft.FStar.Util.Inl ((ds_l reader))
end
| 'b' -> begin
Support.Microsoft.FStar.Util.Inr ((ds_r reader))
end
| _ -> begin
(parse_error ())
end))

let serialize_syntax = (fun writer s_a ast -> (s_a writer ast.Microsoft_FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun reader ds_a ds_b -> {Microsoft_FStar_Absyn_Syntax.n = (ds_a reader); Microsoft_FStar_Absyn_Syntax.tk = (Support.Microsoft.FStar.Util.mk_ref None); Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange; Microsoft_FStar_Absyn_Syntax.fvs = (Support.Microsoft.FStar.Util.mk_ref None); Microsoft_FStar_Absyn_Syntax.uvs = (Support.Microsoft.FStar.Util.mk_ref None)})

let rec serialize_typ' = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _20_172 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _20_176 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (serialize_ftvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _20_182 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (let _20_184 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((v, t)) -> begin
(let _20_190 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
in (let _20_192 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, ars)) -> begin
(let _20_198 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
in (let _20_200 = (serialize_typ writer t)
in (let _20_202 = (serialize_args writer ars)
in if ((! (Microsoft_FStar_Options.debug)) <> []) then begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, _)) -> begin
(Support.Microsoft.FStar.Util.print_string "type application node with lam\n")
end
| _ -> begin
()
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _20_216 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
in (let _20_218 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(let _20_224 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
in (let _20_226 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _20_230 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'h')
in (serialize_meta_t writer m))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'i')
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_, _)) -> begin
(raise (Err ("typ not impl:1")))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((_, _)) -> begin
(raise (Err ("typ not impl:2")))
end))
and serialize_meta_t = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, l)) -> begin
(let _20_251 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (let _20_253 = (serialize_typ writer t)
in (serialize_list writer serialize_arg l)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid)) -> begin
(let _20_259 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (let _20_261 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, s, _, b)) -> begin
(let _20_270 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (let _20_272 = (serialize_typ writer t)
in (let _20_274 = (Support.Microsoft.FStar.Util.MkoWriter.write_string writer s)
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer b))))
end
| _ -> begin
(raise (Err ("unimplemented meta\x5ft")))
end))
and serialize_arg = (fun writer ast -> (let _20_280 = (serialize_either writer serialize_typ serialize_exp (Support.Prims.fst ast))
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer (Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast)))))
and serialize_args = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun writer ast -> (let _20_286 = (serialize_either writer serialize_btvar serialize_bvvar (Support.Prims.fst ast))
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer (Microsoft_FStar_Absyn_Syntax.is_implicit (Support.Prims.snd ast)))))
and serialize_binders = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun writer ast -> (serialize_syntax writer serialize_typ' (Microsoft_FStar_Absyn_Util.compress_typ ast)))
and serialize_comp_typ = (fun writer ast -> (let _20_294 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _20_296 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _20_298 = (serialize_args writer ast.Microsoft_FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.Microsoft_FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _20_304 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (serialize_typ writer t))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let _20_308 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (serialize_comp_typ writer c))
end))
and serialize_comp = (fun writer ast -> (serialize_syntax writer serialize_comp' ast))
and serialize_cflags = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
end
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
end
| Microsoft_FStar_Absyn_Syntax.RETURN -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
end
| Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
end
| Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
end
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
end
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _20_322 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _20_328 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, b)) -> begin
(let _20_334 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (let _20_336 = (serialize_fvvar writer v)
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer b)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _20_340 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let _20_346 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
in (let _20_348 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, ars)) -> begin
(let _20_354 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
in (let _20_356 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, l)) -> begin
(let g = (fun writer eopt -> (match (eopt) with
| Some (e1) -> begin
(let _20_367 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (serialize_exp writer e1))
end
| None -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
end))
in (let f = (fun writer _20_375 -> (match (_20_375) with
| (p, eopt, e) -> begin
(let _20_376 = (serialize_pat writer p)
in (let _20_378 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _20_380 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
in (let _20_382 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(let _20_388 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
in (let _20_390 = (serialize_exp writer e)
in (serialize_typ writer t)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _20_396 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'h')
in (let _20_398 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _20_402 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'i')
in (serialize_meta_e writer m))
end
| _ -> begin
(raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, s)) -> begin
(let _20_412 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (let _20_414 = (serialize_exp writer e)
in (serialize_meta_source_info writer s)))
end))
and serialize_meta_source_info = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Data_app -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
end
| Microsoft_FStar_Absyn_Syntax.Sequence -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
end
| Microsoft_FStar_Absyn_Syntax.Primop -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
end
| Microsoft_FStar_Absyn_Syntax.MaskedEffect -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
end))
and serialize_exp = (fun writer ast -> (serialize_syntax writer serialize_exp' (Microsoft_FStar_Absyn_Util.compress_exp ast)))
and serialize_btvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_pat' = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _20_432 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (serialize_list writer serialize_pat l))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _20_436 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (serialize_sconst writer c))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((v, l)) -> begin
(let _20_442 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (let _20_444 = (serialize_fvvar writer v)
in (serialize_list writer serialize_pat l)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((v, b)) -> begin
(let _20_450 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
in (let _20_452 = (serialize_bvvar writer v)
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer b)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _20_456 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _20_460 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
in (serialize_bvvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _20_464 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
in (serialize_btvar writer v))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((v, e)) -> begin
(let _20_470 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'h')
in (let _20_472 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((v, t)) -> begin
(let _20_478 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'i')
in (let _20_480 = (serialize_btvar writer v)
in (serialize_typ writer t)))
end))
and serialize_pat = (fun writer ast -> (serialize_withinfo_t writer serialize_pat' (fun w kt -> ()) ast))
and serialize_knd' = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
end
| Microsoft_FStar_Absyn_Syntax.Kind_effect -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((ka, k)) -> begin
(let _20_494 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (let _20_496 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _20_502 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
in (let _20_504 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((bs, k)) -> begin
(let _20_510 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
in (let _20_512 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(raise (Err ("knd\' serialization unimplemented:1")))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_, _, _)) -> begin
(raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun writer ast -> (serialize_syntax writer serialize_knd' (Microsoft_FStar_Absyn_Util.compress_kind ast)))
and serialize_kabbrev = (fun writer ast -> (let _20_531 = (serialize_lident writer (Support.Prims.fst ast))
in (serialize_args writer (Support.Prims.snd ast))))
and serialize_lbname = (fun writer ast -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun writer ast -> (let f = (fun writer lb -> (let _20_540 = (serialize_lbname writer lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _20_542 = (serialize_lident writer lb.Microsoft_FStar_Absyn_Syntax.lbeff)
in (let _20_544 = (serialize_typ writer lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.Microsoft_FStar_Absyn_Syntax.lbdef)))))
in (let _20_546 = (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer (Support.Prims.fst ast))
in (serialize_list writer f (Support.Prims.snd ast)))))
and serialize_fvar = (fun writer ast -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun writer ast -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun writer ast -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun writer ast -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun writer ast -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_btvar ((deserialize_btvar reader))
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_const ((deserialize_ftvar reader))
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_fun (((deserialize_binders reader), (deserialize_comp reader)))
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_refine (((deserialize_bvvar reader), (deserialize_typ reader)))
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_app (((deserialize_typ reader), (deserialize_args reader)))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_lam (((deserialize_binders reader), (deserialize_typ reader)))
end
| 'g' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_ascribed (((deserialize_typ reader), (deserialize_knd reader)))
end
| 'h' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_meta ((deserialize_meta_t reader))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Typ_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Meta_pattern (((deserialize_typ reader), (deserialize_list reader deserialize_arg)))
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Meta_named (((deserialize_typ reader), (deserialize_lident reader)))
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Meta_labeled (((deserialize_typ reader), (Support.Microsoft.FStar.Util.MkoReader.read_string reader ()), Microsoft_FStar_Absyn_Syntax.dummyRange, (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ())))
end
| _ -> begin
(parse_error ())
end))
and deserialize_arg = (fun reader -> ((deserialize_either reader deserialize_typ deserialize_exp), (Microsoft_FStar_Absyn_Syntax.as_implicit (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ()))))
and deserialize_args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun reader -> ((deserialize_either reader deserialize_btvar deserialize_bvvar), (Microsoft_FStar_Absyn_Syntax.as_implicit (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ()))))
and deserialize_binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun reader -> (deserialize_syntax reader deserialize_typ' Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun reader -> {Microsoft_FStar_Absyn_Syntax.effect_name = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.result_typ = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.effect_args = (deserialize_args reader); Microsoft_FStar_Absyn_Syntax.flags = (deserialize_list reader deserialize_cflags)})
and deserialize_comp' = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Total ((deserialize_typ reader))
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Comp ((deserialize_comp_typ reader))
end
| _ -> begin
(parse_error ())
end))
and deserialize_comp = (fun reader -> (deserialize_syntax reader deserialize_comp' ()))
and deserialize_cflags = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
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
Microsoft_FStar_Absyn_Syntax.DECREASES ((deserialize_exp reader))
end
| _ -> begin
(parse_error ())
end))
and deserialize_exp' = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_bvar ((deserialize_bvvar reader))
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_fvar (((deserialize_fvvar reader), (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ())))
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_constant ((deserialize_sconst reader))
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_abs (((deserialize_binders reader), (deserialize_exp reader)))
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_app (((deserialize_exp reader), (deserialize_args reader)))
end
| 'f' -> begin
(let g = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Some ((deserialize_exp reader))
end
| 'b' -> begin
None
end
| _ -> begin
(parse_error ())
end))
in (let f = (fun reader -> ((deserialize_pat reader), (g reader), (deserialize_exp reader)))
in Microsoft_FStar_Absyn_Syntax.Exp_match (((deserialize_exp reader), (deserialize_list reader f)))))
end
| 'g' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_ascribed (((deserialize_exp reader), (deserialize_typ reader)))
end
| 'h' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_let (((deserialize_letbindings reader), (deserialize_exp reader)))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Exp_meta ((deserialize_meta_e reader))
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Meta_desugared (((deserialize_exp reader), (deserialize_meta_source_info reader)))
end
| _ -> begin
(parse_error ())
end))
and deserialize_meta_source_info = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
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
and deserialize_exp = (fun reader -> (deserialize_syntax reader deserialize_exp' Microsoft_FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_disj ((deserialize_list reader deserialize_pat))
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_constant ((deserialize_sconst reader))
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_cons (((deserialize_fvvar reader), (deserialize_list reader deserialize_pat)))
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_var (((deserialize_bvvar reader), (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ())))
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_tvar ((deserialize_btvar reader))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_wild ((deserialize_bvvar reader))
end
| 'g' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_twild ((deserialize_btvar reader))
end
| 'h' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_dot_term (((deserialize_bvvar reader), (deserialize_exp reader)))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (((deserialize_btvar reader), (deserialize_typ reader)))
end
| _ -> begin
(parse_error ())
end))
and deserialize_pat = (fun reader -> (deserialize_withinfo_t reader deserialize_pat' (fun r -> None)))
and deserialize_knd' = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_type
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_effect
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((deserialize_kabbrev reader), (deserialize_knd reader)))
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_arrow (((deserialize_binders reader), (deserialize_knd reader)))
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_lam (((deserialize_binders reader), (deserialize_knd reader)))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Kind_unknown
end
| _ -> begin
(parse_error ())
end))
and deserialize_knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun reader -> ((deserialize_lident reader), (deserialize_args reader)))
and deserialize_lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun reader -> (let f = (fun reader -> {Microsoft_FStar_Absyn_Syntax.lbname = (deserialize_lbname reader); Microsoft_FStar_Absyn_Syntax.lbtyp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.lbeff = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.lbdef = (deserialize_exp reader)})
in ((Support.Microsoft.FStar.Util.MkoReader.read_bool reader ()), (deserialize_list reader f))))
and deserialize_fvar = (fun reader -> (deserialize_either reader deserialize_btvdef deserialize_bvvdef))
and deserialize_btvar = (fun reader -> (deserialize_bvar None reader deserialize_knd))
and deserialize_bvvar = (fun reader -> (deserialize_bvar None reader deserialize_typ))
and deserialize_ftvar = (fun reader -> (deserialize_var reader deserialize_knd))
and deserialize_fvvar = (fun reader -> (deserialize_var reader deserialize_typ))

let serialize_formula = serialize_typ

let deserialize_formula = deserialize_typ

let serialize_qualifier = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Private -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
end
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
end
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
end
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'h')
end
| Microsoft_FStar_Absyn_Syntax.Discriminator (lid) -> begin
(let _20_674 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'i')
in (serialize_lident writer lid))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((lid, v)) -> begin
(let _20_680 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'j')
in (let _20_682 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| Microsoft_FStar_Absyn_Syntax.RecordType (l) -> begin
(let _20_686 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'k')
in (serialize_list writer serialize_ident l))
end
| Microsoft_FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _20_690 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'l')
in (serialize_list writer serialize_ident l))
end
| Microsoft_FStar_Absyn_Syntax.ExceptionConstructor -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'm')
end
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'o')
end
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _20_696 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'p')
in (serialize_option writer serialize_lident l))
end
| Microsoft_FStar_Absyn_Syntax.TotalEffect -> begin
(Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'q')
end
| _ -> begin
(failwith "Unexpected qualifier")
end))

let deserialize_qualifier = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
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
Microsoft_FStar_Absyn_Syntax.Discriminator ((deserialize_lident reader))
end
| 'j' -> begin
Microsoft_FStar_Absyn_Syntax.Projector (((deserialize_lident reader), (deserialize_either reader deserialize_btvdef deserialize_bvvdef)))
end
| 'k' -> begin
Microsoft_FStar_Absyn_Syntax.RecordType ((deserialize_list reader deserialize_ident))
end
| 'l' -> begin
Microsoft_FStar_Absyn_Syntax.RecordConstructor ((deserialize_list reader deserialize_ident))
end
| 'm' -> begin
Microsoft_FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
Microsoft_FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
Microsoft_FStar_Absyn_Syntax.DefaultEffect ((deserialize_option reader deserialize_lident))
end
| 'q' -> begin
Microsoft_FStar_Absyn_Syntax.TotalEffect
end
| _ -> begin
(parse_error ())
end))

let serialize_tycon = (fun writer _20_720 -> (match (_20_720) with
| (lid, bs, k) -> begin
(let _20_721 = (serialize_lident writer lid)
in (let _20_723 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun reader -> ((deserialize_lident reader), (deserialize_binders reader), (deserialize_knd reader)))

let serialize_monad_abbrev = (fun writer ast -> (let _20_728 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mabbrev)
in (let _20_730 = (serialize_binders writer ast.Microsoft_FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun reader -> {Microsoft_FStar_Absyn_Syntax.mabbrev = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.parms = (deserialize_binders reader); Microsoft_FStar_Absyn_Syntax.def = (deserialize_typ reader)})

let serialize_sub_effect = (fun writer ast -> (let _20_735 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.source)
in (let _20_737 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun reader -> {Microsoft_FStar_Absyn_Syntax.source = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.target = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.lift = (deserialize_typ reader)})

let rec serialize_new_effect = (fun writer ast -> (let _20_742 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.mname)
in (let _20_744 = (serialize_list writer serialize_binder ast.Microsoft_FStar_Absyn_Syntax.binders)
in (let _20_746 = (serialize_list writer serialize_qualifier ast.Microsoft_FStar_Absyn_Syntax.qualifiers)
in (let _20_748 = (serialize_knd writer ast.Microsoft_FStar_Absyn_Syntax.signature)
in (let _20_750 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ret)
in (let _20_752 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wp)
in (let _20_754 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.bind_wlp)
in (let _20_756 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.if_then_else)
in (let _20_758 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wp)
in (let _20_760 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.ite_wlp)
in (let _20_762 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_binop)
in (let _20_764 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.wp_as_type)
in (let _20_766 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp)
in (let _20_768 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.close_wp_t)
in (let _20_770 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assert_p)
in (let _20_772 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.assume_p)
in (let _20_774 = (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.Microsoft_FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun writer ast -> (match (ast) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_) -> begin
(failwith "NYI")
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, bs, k, l1, l2, qs, _)) -> begin
(let _20_791 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'a')
in (let _20_793 = (serialize_lident writer lid)
in (let _20_795 = (serialize_binders writer bs)
in (let _20_797 = (serialize_knd writer k)
in (let _20_799 = (serialize_list writer serialize_lident l1)
in (let _20_801 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, bs, k, t, qs, _)) -> begin
(let _20_812 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'b')
in (let _20_814 = (serialize_lident writer lid)
in (let _20_816 = (serialize_binders writer bs)
in (let _20_818 = (serialize_knd writer k)
in (let _20_820 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid1, t, tyc, qs, mutuals, _)) -> begin
(let t' = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (f, (Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Util.comp_result c))) None Microsoft_FStar_Absyn_Syntax.dummyRange)
end
| None -> begin
t
end)
in (let _20_837 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'c')
in (let _20_839 = (serialize_lident writer lid1)
in (let _20_841 = (serialize_typ writer t')
in (let _20_843 = (serialize_tycon writer tyc)
in (let _20_845 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, qs, _)) -> begin
(let _20_854 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'd')
in (let _20_856 = (serialize_lident writer lid)
in (let _20_858 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, fml, qs, _)) -> begin
(let _20_867 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'e')
in (let _20_869 = (serialize_lident writer lid)
in (let _20_871 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _, l, quals)) -> begin
(let _20_880 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'f')
in (let _20_882 = (serialize_letbindings writer lbs)
in (let _20_884 = (serialize_list writer serialize_lident l)
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer ((Support.Microsoft.FStar.Util.for_some (fun _20_1 -> (match (_20_1) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))) quals)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _)) -> begin
(let _20_895 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'g')
in (serialize_exp writer e))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((l, qs, lids, _)) -> begin
(let _20_904 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'h')
in (let _20_906 = (serialize_list writer serialize_sigelt l)
in (let _20_908 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _)) -> begin
(let _20_915 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'i')
in (serialize_new_effect writer n))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, bs, c, qs, _)) -> begin
(let _20_925 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'j')
in (let _20_927 = (serialize_lident writer lid)
in (let _20_929 = (serialize_binders writer bs)
in (let _20_931 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((se, r)) -> begin
(let _20_937 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'k')
in (serialize_sub_effect writer se))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _)) -> begin
(let _20_946 = (Support.Microsoft.FStar.Util.MkoWriter.write_char writer 'l')
in (let _20_948 = (serialize_lident writer l)
in (let _20_950 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun reader -> {Microsoft_FStar_Absyn_Syntax.mname = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.binders = (deserialize_list reader deserialize_binder); Microsoft_FStar_Absyn_Syntax.qualifiers = (deserialize_list reader deserialize_qualifier); Microsoft_FStar_Absyn_Syntax.signature = (deserialize_knd reader); Microsoft_FStar_Absyn_Syntax.ret = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.bind_wp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.bind_wlp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.if_then_else = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.ite_wp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.ite_wlp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.wp_binop = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.wp_as_type = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.close_wp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.close_wp_t = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.assert_p = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.assume_p = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.null_wp = (deserialize_typ reader); Microsoft_FStar_Absyn_Syntax.trivial = (deserialize_typ reader)})
and deserialize_sigelt = (fun reader -> (match ((Support.Microsoft.FStar.Util.MkoReader.read_char reader ())) with
| 'a' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_tycon (((deserialize_lident reader), (deserialize_binders reader), (deserialize_knd reader), (deserialize_list reader deserialize_lident), (deserialize_list reader deserialize_lident), (deserialize_list reader deserialize_qualifier), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'b' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (((deserialize_lident reader), (deserialize_binders reader), (deserialize_knd reader), (deserialize_typ reader), (deserialize_list reader deserialize_qualifier), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'c' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_datacon (((deserialize_lident reader), (deserialize_typ reader), (deserialize_tycon reader), (deserialize_list reader deserialize_qualifier), (deserialize_list reader deserialize_lident), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'd' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_val_decl (((deserialize_lident reader), (deserialize_typ reader), (deserialize_list reader deserialize_qualifier), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'e' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_assume (((deserialize_lident reader), (deserialize_formula reader), (deserialize_list reader deserialize_qualifier), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'f' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_let (((deserialize_letbindings reader), Microsoft_FStar_Absyn_Syntax.dummyRange, (deserialize_list reader deserialize_lident), if (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ()) then begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end))
end
| 'g' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_main (((deserialize_exp reader), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'h' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_bundle (((deserialize_list reader deserialize_sigelt), (deserialize_list reader deserialize_qualifier), (deserialize_list reader deserialize_lident), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| 'i' -> begin
Microsoft_FStar_Absyn_Syntax.Sig_new_effect (((deserialize_new_effect reader), Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| ('j') | ('k') | ('l') -> begin
(failwith "TODO")
end
| _ -> begin
(parse_error ())
end))

let serialize_sigelts = (fun writer ast -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun reader -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun writer ast -> (let _20_973 = (serialize_lident writer ast.Microsoft_FStar_Absyn_Syntax.name)
in (let _20_975 = (serialize_sigelts writer [])
in (let _20_977 = (serialize_sigelts writer ast.Microsoft_FStar_Absyn_Syntax.exports)
in (Support.Microsoft.FStar.Util.MkoWriter.write_bool writer ast.Microsoft_FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun reader -> (let m = {Microsoft_FStar_Absyn_Syntax.name = (deserialize_lident reader); Microsoft_FStar_Absyn_Syntax.declarations = (deserialize_sigelts reader); Microsoft_FStar_Absyn_Syntax.exports = (deserialize_sigelts reader); Microsoft_FStar_Absyn_Syntax.is_interface = (Support.Microsoft.FStar.Util.MkoReader.read_bool reader ()); Microsoft_FStar_Absyn_Syntax.is_deserialized = true}
in (let _20_981 = m
in {Microsoft_FStar_Absyn_Syntax.name = _20_981.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = m.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.exports = _20_981.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _20_981.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _20_981.Microsoft_FStar_Absyn_Syntax.is_deserialized})))




