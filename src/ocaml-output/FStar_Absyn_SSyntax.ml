
open Prims
exception Err of (Prims.string)

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_28_3) -> begin
_28_3
end))

let parse_error = (fun _28_4 -> (match (()) with
| () -> begin
(FStar_All.failwith "Parse error: ill-formed cache")
end))

type l__Writer =
FStar_Util.oWriter

type l__Reader =
FStar_Util.oReader

let serialize_option = (fun writer f l -> (match (l) with
| None -> begin
(writer.FStar_Util.write_char 'n')
end
| Some (l) -> begin
(let _28_12 = (writer.FStar_Util.write_char 's')
in (f writer l))
end))

let deserialize_option = (fun reader f -> (let n = (reader.FStar_Util.read_char ())
in if (n = 'n') then begin
None
end else begin
(let _94_21 = (f reader)
in Some (_94_21))
end))

let serialize_list = (fun writer f l -> (let _28_22 = (writer.FStar_Util.write_int (FStar_List.length l))
in (FStar_List.iter (fun elt -> (f writer elt)) (FStar_List.rev_append l []))))

let deserialize_list = (fun reader f -> (let n = (reader.FStar_Util.read_int ())
in (let rec helper = (fun accum n -> if (n = 0) then begin
accum
end else begin
(let _94_42 = (let _94_41 = (f reader)
in (_94_41)::accum)
in (helper _94_42 (n - 1)))
end)
in (helper [] n))))

let serialize_ident = (fun writer ast -> (writer.FStar_Util.write_string ast.FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun reader -> (let _94_50 = (let _94_49 = (reader.FStar_Util.read_string ())
in (_94_49, FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_ident _94_50)))

let serialize_LongIdent = (fun writer ast -> (let _28_37 = (serialize_list writer serialize_ident ast.FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun reader -> (let _94_60 = (let _94_59 = (deserialize_list reader deserialize_ident)
in (let _94_58 = (let _94_57 = (deserialize_ident reader)
in (_94_57)::[])
in (FStar_List.append _94_59 _94_58)))
in (FStar_Absyn_Syntax.lid_of_ids _94_60)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun writer s_v s_sort ast -> (let _28_46 = (s_v writer ast.FStar_Absyn_Syntax.v)
in (s_sort writer ast.FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun reader ds_v ds_sort -> (let _94_90 = (ds_v reader)
in (let _94_89 = (ds_sort reader)
in {FStar_Absyn_Syntax.v = _94_90; FStar_Absyn_Syntax.sort = _94_89; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun reader ds_sort -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun writer ast -> (let _28_63 = (serialize_ident writer ast.FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ghost reader -> (let _94_110 = (deserialize_ident reader)
in (let _94_109 = (deserialize_ident reader)
in {FStar_Absyn_Syntax.ppname = _94_110; FStar_Absyn_Syntax.realname = _94_109})))

let serialize_bvar = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

let deserialize_bvar = (fun ghost reader ds_sort -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

let serialize_sconst = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Const_unit -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Absyn_Syntax.Const_uint8 (v) -> begin
(let _28_83 = (writer.FStar_Util.write_char 'b')
in (writer.FStar_Util.write_byte v))
end
| FStar_Absyn_Syntax.Const_bool (v) -> begin
(let _28_87 = (writer.FStar_Util.write_char 'c')
in (writer.FStar_Util.write_bool v))
end
| FStar_Absyn_Syntax.Const_int32 (v) -> begin
(let _28_91 = (writer.FStar_Util.write_char 'd')
in (writer.FStar_Util.write_int32 v))
end
| FStar_Absyn_Syntax.Const_int64 (v) -> begin
(let _28_95 = (writer.FStar_Util.write_char 'e')
in (writer.FStar_Util.write_int64 v))
end
| FStar_Absyn_Syntax.Const_char (v) -> begin
(let _28_99 = (writer.FStar_Util.write_char 'f')
in (writer.FStar_Util.write_char v))
end
| FStar_Absyn_Syntax.Const_float (v) -> begin
(let _28_103 = (writer.FStar_Util.write_char 'g')
in (writer.FStar_Util.write_double v))
end
| FStar_Absyn_Syntax.Const_bytearray (v, _28_107) -> begin
(let _28_110 = (writer.FStar_Util.write_char 'h')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Absyn_Syntax.Const_string (v, _28_114) -> begin
(let _28_117 = (writer.FStar_Util.write_char 'i')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Absyn_Syntax.Const_int (v) -> begin
(let _28_121 = (writer.FStar_Util.write_char 'j')
in (writer.FStar_Util.write_string v))
end))

let deserialize_sconst = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
FStar_Absyn_Syntax.Const_unit
end
| 'b' -> begin
(let _94_132 = (reader.FStar_Util.read_byte ())
in FStar_Absyn_Syntax.Const_uint8 (_94_132))
end
| 'c' -> begin
(let _94_133 = (reader.FStar_Util.read_bool ())
in FStar_Absyn_Syntax.Const_bool (_94_133))
end
| 'd' -> begin
(let _94_134 = (reader.FStar_Util.read_int32 ())
in FStar_Absyn_Syntax.Const_int32 (_94_134))
end
| 'e' -> begin
(let _94_135 = (reader.FStar_Util.read_int64 ())
in FStar_Absyn_Syntax.Const_int64 (_94_135))
end
| 'f' -> begin
(let _94_136 = (reader.FStar_Util.read_char ())
in FStar_Absyn_Syntax.Const_char (_94_136))
end
| 'g' -> begin
(let _94_137 = (reader.FStar_Util.read_double ())
in FStar_Absyn_Syntax.Const_float (_94_137))
end
| 'h' -> begin
(let _94_139 = (let _94_138 = (reader.FStar_Util.read_bytearray ())
in (_94_138, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Const_bytearray (_94_139))
end
| 'i' -> begin
(let _94_141 = (let _94_140 = (reader.FStar_Util.read_bytearray ())
in (_94_140, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Const_string (_94_141))
end
| 'j' -> begin
(let _94_142 = (reader.FStar_Util.read_string ())
in FStar_Absyn_Syntax.Const_int (_94_142))
end
| _28_135 -> begin
(parse_error ())
end))

let serialize_either = (fun writer s_l s_r ast -> (match (ast) with
| FStar_Util.Inl (v) -> begin
(let _28_144 = (writer.FStar_Util.write_char 'a')
in (s_l writer v))
end
| FStar_Util.Inr (v) -> begin
(let _28_148 = (writer.FStar_Util.write_char 'b')
in (s_r writer v))
end))

let deserialize_either = (fun reader ds_l ds_r -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_168 = (ds_l reader)
in FStar_Util.Inl (_94_168))
end
| 'b' -> begin
(let _94_169 = (ds_r reader)
in FStar_Util.Inr (_94_169))
end
| _28_158 -> begin
(parse_error ())
end))

let serialize_syntax = (fun writer s_a ast -> (s_a writer ast.FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun reader ds_a ds_b -> (let _94_188 = (ds_a reader)
in (let _94_187 = (FStar_Util.mk_ref None)
in (let _94_186 = (FStar_Util.mk_ref None)
in (let _94_185 = (FStar_Util.mk_ref None)
in {FStar_Absyn_Syntax.n = _94_188; FStar_Absyn_Syntax.tk = _94_187; FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange; FStar_Absyn_Syntax.fvs = _94_186; FStar_Absyn_Syntax.uvs = _94_185})))))

let rec serialize_typ' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _28_173 = (writer.FStar_Util.write_char 'a')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _28_177 = (writer.FStar_Util.write_char 'b')
in (serialize_ftvar writer v))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _28_183 = (writer.FStar_Util.write_char 'c')
in (let _28_185 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| FStar_Absyn_Syntax.Typ_refine (v, t) -> begin
(let _28_191 = (writer.FStar_Util.write_char 'd')
in (let _28_193 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_app (t, ars) -> begin
(let _28_199 = (writer.FStar_Util.write_char 'e')
in (let _28_201 = (serialize_typ writer t)
in (let _28_203 = (serialize_args writer ars)
in if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (_28_206, _28_208) -> begin
(FStar_Util.print_string "type application node with lam\n")
end
| _28_212 -> begin
()
end)
end else begin
()
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _28_217 = (writer.FStar_Util.write_char 'f')
in (let _28_219 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _28_225 = (writer.FStar_Util.write_char 'g')
in (let _28_227 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _28_231 = (writer.FStar_Util.write_char 'h')
in (serialize_meta_t writer m))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(writer.FStar_Util.write_char 'i')
end
| FStar_Absyn_Syntax.Typ_uvar (_28_235, _28_237) -> begin
(Prims.raise (Err ("typ not impl:1")))
end
| FStar_Absyn_Syntax.Typ_delayed (_28_241, _28_243) -> begin
(Prims.raise (Err ("typ not impl:2")))
end))
and serialize_meta_t = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_pattern (t, l) -> begin
(let _28_252 = (writer.FStar_Util.write_char 'a')
in (let _28_254 = (serialize_typ writer t)
in (serialize_list writer (fun w -> (serialize_list w serialize_arg)) l)))
end
| FStar_Absyn_Syntax.Meta_named (t, lid) -> begin
(let _28_261 = (writer.FStar_Util.write_char 'b')
in (let _28_263 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| FStar_Absyn_Syntax.Meta_labeled (t, s, _28_268, b) -> begin
(let _28_272 = (writer.FStar_Util.write_char 'c')
in (let _28_274 = (serialize_typ writer t)
in (let _28_276 = (writer.FStar_Util.write_string s)
in (writer.FStar_Util.write_bool b))))
end
| _28_279 -> begin
(Prims.raise (Err ("unimplemented meta_t")))
end))
and serialize_arg = (fun writer ast -> (let _28_282 = (serialize_either writer serialize_typ serialize_exp (Prims.fst ast))
in (let _94_257 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _94_257))))
and serialize_args = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun writer ast -> (let _28_288 = (serialize_either writer serialize_btvar serialize_bvvar (Prims.fst ast))
in (let _94_262 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _94_262))))
and serialize_binders = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun writer ast -> (let _94_267 = (FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _94_267)))
and serialize_comp_typ = (fun writer ast -> (let _28_296 = (serialize_lident writer ast.FStar_Absyn_Syntax.effect_name)
in (let _28_298 = (serialize_typ writer ast.FStar_Absyn_Syntax.result_typ)
in (let _28_300 = (serialize_args writer ast.FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _28_306 = (writer.FStar_Util.write_char 'a')
in (serialize_typ writer t))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let _28_310 = (writer.FStar_Util.write_char 'b')
in (serialize_comp_typ writer c))
end))
and serialize_comp = (fun writer ast -> (serialize_syntax writer serialize_comp' ast))
and serialize_cflags = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.TOTAL -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Absyn_Syntax.MLEFFECT -> begin
(writer.FStar_Util.write_char 'b')
end
| FStar_Absyn_Syntax.RETURN -> begin
(writer.FStar_Util.write_char 'c')
end
| FStar_Absyn_Syntax.PARTIAL_RETURN -> begin
(writer.FStar_Util.write_char 'd')
end
| FStar_Absyn_Syntax.SOMETRIVIAL -> begin
(writer.FStar_Util.write_char 'e')
end
| FStar_Absyn_Syntax.LEMMA -> begin
(writer.FStar_Util.write_char 'f')
end
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _28_324 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _28_330 = (writer.FStar_Util.write_char 'a')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Exp_fvar (v, b) -> begin
(let _28_336 = (writer.FStar_Util.write_char 'b')
in (let _28_338 = (serialize_fvvar writer v)
in (writer.FStar_Util.write_bool false)))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _28_342 = (writer.FStar_Util.write_char 'c')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _28_348 = (writer.FStar_Util.write_char 'd')
in (let _28_350 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_app (e, ars) -> begin
(let _28_356 = (writer.FStar_Util.write_char 'e')
in (let _28_358 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| FStar_Absyn_Syntax.Exp_match (e, l) -> begin
(let g = (fun writer eopt -> (match (eopt) with
| Some (e1) -> begin
(let _28_369 = (writer.FStar_Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.FStar_Util.write_char 'b')
end))
in (let f = (fun writer _28_377 -> (match (_28_377) with
| (p, eopt, e) -> begin
(let _28_378 = (serialize_pat writer p)
in (let _28_380 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _28_382 = (writer.FStar_Util.write_char 'f')
in (let _28_384 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let _28_391 = (writer.FStar_Util.write_char 'g')
in (let _28_393 = (serialize_exp writer e)
in (let _28_395 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _28_401 = (writer.FStar_Util.write_char 'h')
in (let _28_403 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _28_407 = (writer.FStar_Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _28_410 -> begin
(Prims.raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_desugared (e, s) -> begin
(let _28_417 = (writer.FStar_Util.write_char 'a')
in (let _28_419 = (serialize_exp writer e)
in (serialize_meta_source_info writer s)))
end))
and serialize_meta_source_info = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Data_app -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Absyn_Syntax.Sequence -> begin
(writer.FStar_Util.write_char 'b')
end
| FStar_Absyn_Syntax.Primop -> begin
(writer.FStar_Util.write_char 'c')
end
| FStar_Absyn_Syntax.Masked_effect -> begin
(writer.FStar_Util.write_char 'd')
end
| FStar_Absyn_Syntax.Meta_smt_pat -> begin
(writer.FStar_Util.write_char 'e')
end))
and serialize_exp = (fun writer ast -> (let _94_292 = (FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _94_292)))
and serialize_btvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_pat' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _28_438 = (writer.FStar_Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _28_442 = (writer.FStar_Util.write_char 'b')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Pat_cons (v, _28_446, l) -> begin
(let _28_450 = (writer.FStar_Util.write_char 'c')
in (let _28_452 = (serialize_fvvar writer v)
in (serialize_list writer (fun w _28_457 -> (match (_28_457) with
| (p, b) -> begin
(let _28_458 = (serialize_pat w p)
in (w.FStar_Util.write_bool b))
end)) l)))
end
| FStar_Absyn_Syntax.Pat_var (v) -> begin
(let _28_462 = (writer.FStar_Util.write_char 'd')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _28_466 = (writer.FStar_Util.write_char 'e')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _28_470 = (writer.FStar_Util.write_char 'f')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _28_474 = (writer.FStar_Util.write_char 'g')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_dot_term (v, e) -> begin
(let _28_480 = (writer.FStar_Util.write_char 'h')
in (let _28_482 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (v, t) -> begin
(let _28_488 = (writer.FStar_Util.write_char 'i')
in (let _28_490 = (serialize_btvar writer v)
in (serialize_typ writer t)))
end))
and serialize_pat = (fun writer ast -> (serialize_withinfo_t writer serialize_pat' (fun w kt -> ()) ast))
and serialize_knd' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Kind_type -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Absyn_Syntax.Kind_effect -> begin
(writer.FStar_Util.write_char 'b')
end
| FStar_Absyn_Syntax.Kind_abbrev (ka, k) -> begin
(let _28_504 = (writer.FStar_Util.write_char 'c')
in (let _28_506 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _28_512 = (writer.FStar_Util.write_char 'd')
in (let _28_514 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_lam (bs, k) -> begin
(let _28_520 = (writer.FStar_Util.write_char 'e')
in (let _28_522 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.FStar_Util.write_char 'f')
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:1")))
end
| FStar_Absyn_Syntax.Kind_delayed (_28_530, _28_532, _28_534) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun writer ast -> (let _94_309 = (FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _94_309)))
and serialize_kabbrev = (fun writer ast -> (let _28_541 = (serialize_lident writer (Prims.fst ast))
in (serialize_args writer (Prims.snd ast))))
and serialize_lbname = (fun writer ast -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun writer ast -> (let f = (fun writer lb -> (let _28_550 = (serialize_lbname writer lb.FStar_Absyn_Syntax.lbname)
in (let _28_552 = (serialize_lident writer lb.FStar_Absyn_Syntax.lbeff)
in (let _28_554 = (serialize_typ writer lb.FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.FStar_Absyn_Syntax.lbdef)))))
in (let _28_556 = (writer.FStar_Util.write_bool (Prims.fst ast))
in (serialize_list writer f (Prims.snd ast)))))
and serialize_fvar = (fun writer ast -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun writer ast -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun writer ast -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun writer ast -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun writer ast -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_360 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Typ_btvar (_94_360))
end
| 'b' -> begin
(let _94_361 = (deserialize_ftvar reader)
in FStar_Absyn_Syntax.Typ_const (_94_361))
end
| 'c' -> begin
(let _94_364 = (let _94_363 = (deserialize_binders reader)
in (let _94_362 = (deserialize_comp reader)
in (_94_363, _94_362)))
in FStar_Absyn_Syntax.Typ_fun (_94_364))
end
| 'd' -> begin
(let _94_367 = (let _94_366 = (deserialize_bvvar reader)
in (let _94_365 = (deserialize_typ reader)
in (_94_366, _94_365)))
in FStar_Absyn_Syntax.Typ_refine (_94_367))
end
| 'e' -> begin
(let _94_370 = (let _94_369 = (deserialize_typ reader)
in (let _94_368 = (deserialize_args reader)
in (_94_369, _94_368)))
in FStar_Absyn_Syntax.Typ_app (_94_370))
end
| 'f' -> begin
(let _94_373 = (let _94_372 = (deserialize_binders reader)
in (let _94_371 = (deserialize_typ reader)
in (_94_372, _94_371)))
in FStar_Absyn_Syntax.Typ_lam (_94_373))
end
| 'g' -> begin
(let _94_376 = (let _94_375 = (deserialize_typ reader)
in (let _94_374 = (deserialize_knd reader)
in (_94_375, _94_374)))
in FStar_Absyn_Syntax.Typ_ascribed (_94_376))
end
| 'h' -> begin
(let _94_377 = (deserialize_meta_t reader)
in FStar_Absyn_Syntax.Typ_meta (_94_377))
end
| 'i' -> begin
FStar_Absyn_Syntax.Typ_unknown
end
| _28_579 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_382 = (let _94_381 = (deserialize_typ reader)
in (let _94_380 = (deserialize_list reader (fun r -> (deserialize_list r deserialize_arg)))
in (_94_381, _94_380)))
in FStar_Absyn_Syntax.Meta_pattern (_94_382))
end
| 'b' -> begin
(let _94_385 = (let _94_384 = (deserialize_typ reader)
in (let _94_383 = (deserialize_lident reader)
in (_94_384, _94_383)))
in FStar_Absyn_Syntax.Meta_named (_94_385))
end
| 'c' -> begin
(let _94_389 = (let _94_388 = (deserialize_typ reader)
in (let _94_387 = (reader.FStar_Util.read_string ())
in (let _94_386 = (reader.FStar_Util.read_bool ())
in (_94_388, _94_387, FStar_Absyn_Syntax.dummyRange, _94_386))))
in FStar_Absyn_Syntax.Meta_labeled (_94_389))
end
| _28_586 -> begin
(parse_error ())
end))
and deserialize_arg = (fun reader -> (let _94_393 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _94_392 = (let _94_391 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _94_391))
in (_94_393, _94_392))))
and deserialize_args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun reader -> (let _94_398 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _94_397 = (let _94_396 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _94_396))
in (_94_398, _94_397))))
and deserialize_binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun reader -> (deserialize_syntax reader deserialize_typ' FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun reader -> (let _94_405 = (deserialize_lident reader)
in (let _94_404 = (deserialize_typ reader)
in (let _94_403 = (deserialize_args reader)
in (let _94_402 = (deserialize_list reader deserialize_cflags)
in {FStar_Absyn_Syntax.effect_name = _94_405; FStar_Absyn_Syntax.result_typ = _94_404; FStar_Absyn_Syntax.effect_args = _94_403; FStar_Absyn_Syntax.flags = _94_402})))))
and deserialize_comp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_407 = (deserialize_typ reader)
in FStar_Absyn_Syntax.Total (_94_407))
end
| 'b' -> begin
(let _94_408 = (deserialize_comp_typ reader)
in FStar_Absyn_Syntax.Comp (_94_408))
end
| _28_597 -> begin
(parse_error ())
end))
and deserialize_comp = (fun reader -> (deserialize_syntax reader deserialize_comp' ()))
and deserialize_cflags = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
FStar_Absyn_Syntax.TOTAL
end
| 'b' -> begin
FStar_Absyn_Syntax.MLEFFECT
end
| 'c' -> begin
FStar_Absyn_Syntax.RETURN
end
| 'd' -> begin
FStar_Absyn_Syntax.PARTIAL_RETURN
end
| 'e' -> begin
FStar_Absyn_Syntax.SOMETRIVIAL
end
| 'f' -> begin
FStar_Absyn_Syntax.LEMMA
end
| 'g' -> begin
(let _94_411 = (deserialize_exp reader)
in FStar_Absyn_Syntax.DECREASES (_94_411))
end
| _28_608 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_413 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Exp_bvar (_94_413))
end
| 'b' -> begin
(let _94_417 = (let _94_416 = (deserialize_fvvar reader)
in (let _94_415 = (let _28_612 = (let _94_414 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left Prims.ignore _94_414))
in None)
in (_94_416, _94_415)))
in FStar_Absyn_Syntax.Exp_fvar (_94_417))
end
| 'c' -> begin
(let _94_418 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Exp_constant (_94_418))
end
| 'd' -> begin
(let _94_421 = (let _94_420 = (deserialize_binders reader)
in (let _94_419 = (deserialize_exp reader)
in (_94_420, _94_419)))
in FStar_Absyn_Syntax.Exp_abs (_94_421))
end
| 'e' -> begin
(let _94_424 = (let _94_423 = (deserialize_exp reader)
in (let _94_422 = (deserialize_args reader)
in (_94_423, _94_422)))
in FStar_Absyn_Syntax.Exp_app (_94_424))
end
| 'f' -> begin
(let g = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_427 = (deserialize_exp reader)
in Some (_94_427))
end
| 'b' -> begin
None
end
| _28_623 -> begin
(parse_error ())
end))
in (let f = (fun reader -> (let _94_432 = (deserialize_pat reader)
in (let _94_431 = (g reader)
in (let _94_430 = (deserialize_exp reader)
in (_94_432, _94_431, _94_430)))))
in (let _94_435 = (let _94_434 = (deserialize_exp reader)
in (let _94_433 = (deserialize_list reader f)
in (_94_434, _94_433)))
in FStar_Absyn_Syntax.Exp_match (_94_435))))
end
| 'g' -> begin
(let _94_439 = (let _94_438 = (deserialize_exp reader)
in (let _94_437 = (deserialize_typ reader)
in (let _94_436 = (deserialize_option reader deserialize_lident)
in (_94_438, _94_437, _94_436))))
in FStar_Absyn_Syntax.Exp_ascribed (_94_439))
end
| 'h' -> begin
(let _94_442 = (let _94_441 = (deserialize_letbindings reader)
in (let _94_440 = (deserialize_exp reader)
in (_94_441, _94_440)))
in FStar_Absyn_Syntax.Exp_let (_94_442))
end
| 'i' -> begin
(let _94_443 = (deserialize_meta_e reader)
in FStar_Absyn_Syntax.Exp_meta (_94_443))
end
| _28_630 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_447 = (let _94_446 = (deserialize_exp reader)
in (let _94_445 = (deserialize_meta_source_info reader)
in (_94_446, _94_445)))
in FStar_Absyn_Syntax.Meta_desugared (_94_447))
end
| _28_634 -> begin
(parse_error ())
end))
and deserialize_meta_source_info = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
FStar_Absyn_Syntax.Data_app
end
| 'b' -> begin
FStar_Absyn_Syntax.Sequence
end
| 'c' -> begin
FStar_Absyn_Syntax.Primop
end
| 'd' -> begin
FStar_Absyn_Syntax.Masked_effect
end
| _28_641 -> begin
(parse_error ())
end))
and deserialize_exp = (fun reader -> (deserialize_syntax reader deserialize_exp' FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_453 = (deserialize_list reader deserialize_pat)
in FStar_Absyn_Syntax.Pat_disj (_94_453))
end
| 'b' -> begin
(let _94_454 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Pat_constant (_94_454))
end
| 'c' -> begin
(let _94_460 = (let _94_459 = (deserialize_fvvar reader)
in (let _94_458 = (deserialize_list reader (fun r -> (let _94_457 = (deserialize_pat r)
in (let _94_456 = (r.FStar_Util.read_bool ())
in (_94_457, _94_456)))))
in (_94_459, None, _94_458)))
in FStar_Absyn_Syntax.Pat_cons (_94_460))
end
| 'd' -> begin
(let _94_461 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_var (_94_461))
end
| 'e' -> begin
(let _94_462 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_tvar (_94_462))
end
| 'f' -> begin
(let _94_463 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_wild (_94_463))
end
| 'g' -> begin
(let _94_464 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_twild (_94_464))
end
| 'h' -> begin
(let _94_467 = (let _94_466 = (deserialize_bvvar reader)
in (let _94_465 = (deserialize_exp reader)
in (_94_466, _94_465)))
in FStar_Absyn_Syntax.Pat_dot_term (_94_467))
end
| 'i' -> begin
(let _94_470 = (let _94_469 = (deserialize_btvar reader)
in (let _94_468 = (deserialize_typ reader)
in (_94_469, _94_468)))
in FStar_Absyn_Syntax.Pat_dot_typ (_94_470))
end
| _28_657 -> begin
(parse_error ())
end))
and deserialize_pat = (fun reader -> (deserialize_withinfo_t reader deserialize_pat' (fun r -> None)))
and deserialize_knd' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
FStar_Absyn_Syntax.Kind_type
end
| 'b' -> begin
FStar_Absyn_Syntax.Kind_effect
end
| 'c' -> begin
(let _94_476 = (let _94_475 = (deserialize_kabbrev reader)
in (let _94_474 = (deserialize_knd reader)
in (_94_475, _94_474)))
in FStar_Absyn_Syntax.Kind_abbrev (_94_476))
end
| 'd' -> begin
(let _94_479 = (let _94_478 = (deserialize_binders reader)
in (let _94_477 = (deserialize_knd reader)
in (_94_478, _94_477)))
in FStar_Absyn_Syntax.Kind_arrow (_94_479))
end
| 'e' -> begin
(let _94_482 = (let _94_481 = (deserialize_binders reader)
in (let _94_480 = (deserialize_knd reader)
in (_94_481, _94_480)))
in FStar_Absyn_Syntax.Kind_lam (_94_482))
end
| 'f' -> begin
FStar_Absyn_Syntax.Kind_unknown
end
| _28_668 -> begin
(parse_error ())
end))
and deserialize_knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun reader -> (let _94_486 = (deserialize_lident reader)
in (let _94_485 = (deserialize_args reader)
in (_94_486, _94_485))))
and deserialize_lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun reader -> (let f = (fun reader -> (let _94_494 = (deserialize_lbname reader)
in (let _94_493 = (deserialize_typ reader)
in (let _94_492 = (deserialize_lident reader)
in (let _94_491 = (deserialize_exp reader)
in {FStar_Absyn_Syntax.lbname = _94_494; FStar_Absyn_Syntax.lbtyp = _94_493; FStar_Absyn_Syntax.lbeff = _94_492; FStar_Absyn_Syntax.lbdef = _94_491})))))
in (let _94_496 = (reader.FStar_Util.read_bool ())
in (let _94_495 = (deserialize_list reader f)
in (_94_496, _94_495)))))
and deserialize_fvar = (fun reader -> (deserialize_either reader deserialize_btvdef deserialize_bvvdef))
and deserialize_btvar = (fun reader -> (deserialize_bvar None reader deserialize_knd))
and deserialize_bvvar = (fun reader -> (deserialize_bvar None reader deserialize_typ))
and deserialize_ftvar = (fun reader -> (deserialize_var reader deserialize_knd))
and deserialize_fvvar = (fun reader -> (deserialize_var reader deserialize_typ))

let serialize_formula = serialize_typ

let deserialize_formula = deserialize_typ

let serialize_qualifier = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Private -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Absyn_Syntax.Assumption -> begin
(writer.FStar_Util.write_char 'c')
end
| FStar_Absyn_Syntax.Logic -> begin
(writer.FStar_Util.write_char 'g')
end
| FStar_Absyn_Syntax.Opaque -> begin
(writer.FStar_Util.write_char 'h')
end
| FStar_Absyn_Syntax.Discriminator (lid) -> begin
(let _28_688 = (writer.FStar_Util.write_char 'i')
in (serialize_lident writer lid))
end
| FStar_Absyn_Syntax.Projector (lid, v) -> begin
(let _28_694 = (writer.FStar_Util.write_char 'j')
in (let _28_696 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| FStar_Absyn_Syntax.RecordType (l) -> begin
(let _28_700 = (writer.FStar_Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _28_704 = (writer.FStar_Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.FStar_Util.write_char 'm')
end
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.FStar_Util.write_char 'o')
end
| FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _28_710 = (writer.FStar_Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| FStar_Absyn_Syntax.TotalEffect -> begin
(writer.FStar_Util.write_char 'q')
end
| _28_714 -> begin
(FStar_All.failwith "Unexpected qualifier")
end))

let deserialize_qualifier = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
FStar_Absyn_Syntax.Private
end
| 'c' -> begin
FStar_Absyn_Syntax.Assumption
end
| 'g' -> begin
FStar_Absyn_Syntax.Logic
end
| 'h' -> begin
FStar_Absyn_Syntax.Opaque
end
| 'i' -> begin
(let _94_511 = (deserialize_lident reader)
in FStar_Absyn_Syntax.Discriminator (_94_511))
end
| 'j' -> begin
(let _94_514 = (let _94_513 = (deserialize_lident reader)
in (let _94_512 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_94_513, _94_512)))
in FStar_Absyn_Syntax.Projector (_94_514))
end
| 'k' -> begin
(let _94_515 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordType (_94_515))
end
| 'l' -> begin
(let _94_516 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordConstructor (_94_516))
end
| 'm' -> begin
FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _94_518 = (deserialize_option reader deserialize_lident)
in (FStar_All.pipe_right _94_518 (fun _94_517 -> FStar_Absyn_Syntax.DefaultEffect (_94_517))))
end
| 'q' -> begin
FStar_Absyn_Syntax.TotalEffect
end
| _28_729 -> begin
(parse_error ())
end))

let serialize_tycon = (fun writer _28_734 -> (match (_28_734) with
| (lid, bs, k) -> begin
(let _28_735 = (serialize_lident writer lid)
in (let _28_737 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun reader -> (let _94_527 = (deserialize_lident reader)
in (let _94_526 = (deserialize_binders reader)
in (let _94_525 = (deserialize_knd reader)
in (_94_527, _94_526, _94_525)))))

let serialize_monad_abbrev = (fun writer ast -> (let _28_742 = (serialize_lident writer ast.FStar_Absyn_Syntax.mabbrev)
in (let _28_744 = (serialize_binders writer ast.FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun reader -> (let _94_536 = (deserialize_lident reader)
in (let _94_535 = (deserialize_binders reader)
in (let _94_534 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mabbrev = _94_536; FStar_Absyn_Syntax.parms = _94_535; FStar_Absyn_Syntax.def = _94_534}))))

let serialize_sub_effect = (fun writer ast -> (let _28_749 = (serialize_lident writer ast.FStar_Absyn_Syntax.source)
in (let _28_751 = (serialize_lident writer ast.FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun reader -> (let _94_545 = (deserialize_lident reader)
in (let _94_544 = (deserialize_lident reader)
in (let _94_543 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.source = _94_545; FStar_Absyn_Syntax.target = _94_544; FStar_Absyn_Syntax.lift = _94_543}))))

let rec serialize_new_effect = (fun writer ast -> (let _28_756 = (serialize_lident writer ast.FStar_Absyn_Syntax.mname)
in (let _28_758 = (serialize_list writer serialize_binder ast.FStar_Absyn_Syntax.binders)
in (let _28_760 = (serialize_list writer serialize_qualifier ast.FStar_Absyn_Syntax.qualifiers)
in (let _28_762 = (serialize_knd writer ast.FStar_Absyn_Syntax.signature)
in (let _28_764 = (serialize_typ writer ast.FStar_Absyn_Syntax.ret)
in (let _28_766 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wp)
in (let _28_768 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wlp)
in (let _28_770 = (serialize_typ writer ast.FStar_Absyn_Syntax.if_then_else)
in (let _28_772 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wp)
in (let _28_774 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wlp)
in (let _28_776 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_binop)
in (let _28_778 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_as_type)
in (let _28_780 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp)
in (let _28_782 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp_t)
in (let _28_784 = (serialize_typ writer ast.FStar_Absyn_Syntax.assert_p)
in (let _28_786 = (serialize_typ writer ast.FStar_Absyn_Syntax.assume_p)
in (let _28_788 = (serialize_typ writer ast.FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Sig_pragma (_28_793) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Absyn_Syntax.Sig_tycon (lid, bs, k, l1, l2, qs, _28_802) -> begin
(let _28_805 = (writer.FStar_Util.write_char 'a')
in (let _28_807 = (serialize_lident writer lid)
in (let _28_809 = (serialize_binders writer bs)
in (let _28_811 = (serialize_knd writer k)
in (let _28_813 = (serialize_list writer serialize_lident l1)
in (let _28_815 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, bs, k, t, qs, _28_823) -> begin
(let _28_826 = (writer.FStar_Util.write_char 'b')
in (let _28_828 = (serialize_lident writer lid)
in (let _28_830 = (serialize_binders writer bs)
in (let _28_832 = (serialize_knd writer k)
in (let _28_834 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid1, t, tyc, qs, mutuals, _28_842) -> begin
(let t' = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(let _94_555 = (let _94_554 = (FStar_Absyn_Syntax.mk_Total (FStar_Absyn_Util.comp_result c))
in (f, _94_554))
in (FStar_Absyn_Syntax.mk_Typ_fun _94_555 None FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _28_851 = (writer.FStar_Util.write_char 'c')
in (let _28_853 = (serialize_lident writer lid1)
in (let _28_855 = (serialize_typ writer t')
in (let _28_857 = (serialize_tycon writer tyc)
in (let _28_859 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, qs, _28_865) -> begin
(let _28_868 = (writer.FStar_Util.write_char 'd')
in (let _28_870 = (serialize_lident writer lid)
in (let _28_872 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, fml, qs, _28_878) -> begin
(let _28_881 = (writer.FStar_Util.write_char 'e')
in (let _28_883 = (serialize_lident writer lid)
in (let _28_885 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _28_889, l, quals) -> begin
(let _28_894 = (writer.FStar_Util.write_char 'f')
in (let _28_896 = (serialize_letbindings writer lbs)
in (let _28_898 = (serialize_list writer serialize_lident l)
in (let _94_557 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _28_1 -> (match (_28_1) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _28_903 -> begin
false
end))))
in (writer.FStar_Util.write_bool _94_557)))))
end
| FStar_Absyn_Syntax.Sig_main (e, _28_906) -> begin
(let _28_909 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end
| FStar_Absyn_Syntax.Sig_bundle (l, qs, lids, _28_915) -> begin
(let _28_918 = (writer.FStar_Util.write_char 'h')
in (let _28_920 = (serialize_list writer serialize_sigelt l)
in (let _28_922 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _28_926) -> begin
(let _28_929 = (writer.FStar_Util.write_char 'i')
in (serialize_new_effect writer n))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, bs, c, qs, _28_936) -> begin
(let _28_939 = (writer.FStar_Util.write_char 'j')
in (let _28_941 = (serialize_lident writer lid)
in (let _28_943 = (serialize_binders writer bs)
in (let _28_945 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (se, r) -> begin
(let _28_951 = (writer.FStar_Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _28_957) -> begin
(let _28_960 = (writer.FStar_Util.write_char 'l')
in (let _28_962 = (serialize_lident writer l)
in (let _28_964 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun reader -> (let _94_578 = (deserialize_lident reader)
in (let _94_577 = (deserialize_list reader deserialize_binder)
in (let _94_576 = (deserialize_list reader deserialize_qualifier)
in (let _94_575 = (deserialize_knd reader)
in (let _94_574 = (deserialize_typ reader)
in (let _94_573 = (deserialize_typ reader)
in (let _94_572 = (deserialize_typ reader)
in (let _94_571 = (deserialize_typ reader)
in (let _94_570 = (deserialize_typ reader)
in (let _94_569 = (deserialize_typ reader)
in (let _94_568 = (deserialize_typ reader)
in (let _94_567 = (deserialize_typ reader)
in (let _94_566 = (deserialize_typ reader)
in (let _94_565 = (deserialize_typ reader)
in (let _94_564 = (deserialize_typ reader)
in (let _94_563 = (deserialize_typ reader)
in (let _94_562 = (deserialize_typ reader)
in (let _94_561 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mname = _94_578; FStar_Absyn_Syntax.binders = _94_577; FStar_Absyn_Syntax.qualifiers = _94_576; FStar_Absyn_Syntax.signature = _94_575; FStar_Absyn_Syntax.ret = _94_574; FStar_Absyn_Syntax.bind_wp = _94_573; FStar_Absyn_Syntax.bind_wlp = _94_572; FStar_Absyn_Syntax.if_then_else = _94_571; FStar_Absyn_Syntax.ite_wp = _94_570; FStar_Absyn_Syntax.ite_wlp = _94_569; FStar_Absyn_Syntax.wp_binop = _94_568; FStar_Absyn_Syntax.wp_as_type = _94_567; FStar_Absyn_Syntax.close_wp = _94_566; FStar_Absyn_Syntax.close_wp_t = _94_565; FStar_Absyn_Syntax.assert_p = _94_564; FStar_Absyn_Syntax.assume_p = _94_563; FStar_Absyn_Syntax.null_wp = _94_562; FStar_Absyn_Syntax.trivial = _94_561})))))))))))))))))))
and deserialize_sigelt = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_586 = (let _94_585 = (deserialize_lident reader)
in (let _94_584 = (deserialize_binders reader)
in (let _94_583 = (deserialize_knd reader)
in (let _94_582 = (deserialize_list reader deserialize_lident)
in (let _94_581 = (deserialize_list reader deserialize_lident)
in (let _94_580 = (deserialize_list reader deserialize_qualifier)
in (_94_585, _94_584, _94_583, _94_582, _94_581, _94_580, FStar_Absyn_Syntax.dummyRange)))))))
in FStar_Absyn_Syntax.Sig_tycon (_94_586))
end
| 'b' -> begin
(let _94_592 = (let _94_591 = (deserialize_lident reader)
in (let _94_590 = (deserialize_binders reader)
in (let _94_589 = (deserialize_knd reader)
in (let _94_588 = (deserialize_typ reader)
in (let _94_587 = (deserialize_list reader deserialize_qualifier)
in (_94_591, _94_590, _94_589, _94_588, _94_587, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_94_592))
end
| 'c' -> begin
(let _94_598 = (let _94_597 = (deserialize_lident reader)
in (let _94_596 = (deserialize_typ reader)
in (let _94_595 = (deserialize_tycon reader)
in (let _94_594 = (deserialize_list reader deserialize_qualifier)
in (let _94_593 = (deserialize_list reader deserialize_lident)
in (_94_597, _94_596, _94_595, _94_594, _94_593, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_datacon (_94_598))
end
| 'd' -> begin
(let _94_602 = (let _94_601 = (deserialize_lident reader)
in (let _94_600 = (deserialize_typ reader)
in (let _94_599 = (deserialize_list reader deserialize_qualifier)
in (_94_601, _94_600, _94_599, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_val_decl (_94_602))
end
| 'e' -> begin
(let _94_606 = (let _94_605 = (deserialize_lident reader)
in (let _94_604 = (deserialize_formula reader)
in (let _94_603 = (deserialize_list reader deserialize_qualifier)
in (_94_605, _94_604, _94_603, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_assume (_94_606))
end
| 'f' -> begin
(let _94_610 = (let _94_609 = (deserialize_letbindings reader)
in (let _94_608 = (deserialize_list reader deserialize_lident)
in (let _94_607 = if (reader.FStar_Util.read_bool ()) then begin
(FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end
in (_94_609, FStar_Absyn_Syntax.dummyRange, _94_608, _94_607))))
in FStar_Absyn_Syntax.Sig_let (_94_610))
end
| 'g' -> begin
(let _94_612 = (let _94_611 = (deserialize_exp reader)
in (_94_611, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_main (_94_612))
end
| 'h' -> begin
(let _94_616 = (let _94_615 = (deserialize_list reader deserialize_sigelt)
in (let _94_614 = (deserialize_list reader deserialize_qualifier)
in (let _94_613 = (deserialize_list reader deserialize_lident)
in (_94_615, _94_614, _94_613, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_bundle (_94_616))
end
| 'i' -> begin
(let _94_618 = (let _94_617 = (deserialize_new_effect reader)
in (_94_617, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_new_effect (_94_618))
end
| ('j') | ('k') | ('l') -> begin
(FStar_All.failwith "TODO")
end
| _28_981 -> begin
(parse_error ())
end))

let serialize_sigelts = (fun writer ast -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun reader -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun writer ast -> (let _28_987 = (serialize_lident writer ast.FStar_Absyn_Syntax.name)
in (let _28_989 = (serialize_sigelts writer [])
in (let _28_991 = (serialize_sigelts writer ast.FStar_Absyn_Syntax.exports)
in (writer.FStar_Util.write_bool ast.FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun reader -> (let m = (let _94_634 = (deserialize_lident reader)
in (let _94_633 = (deserialize_sigelts reader)
in (let _94_632 = (deserialize_sigelts reader)
in (let _94_631 = (reader.FStar_Util.read_bool ())
in {FStar_Absyn_Syntax.name = _94_634; FStar_Absyn_Syntax.declarations = _94_633; FStar_Absyn_Syntax.exports = _94_632; FStar_Absyn_Syntax.is_interface = _94_631; FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _28_995 = m
in {FStar_Absyn_Syntax.name = _28_995.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = m.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.exports = _28_995.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _28_995.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _28_995.FStar_Absyn_Syntax.is_deserialized})))




