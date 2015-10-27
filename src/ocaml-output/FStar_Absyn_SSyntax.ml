
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
(let _93_21 = (f reader)
in Some (_93_21))
end))

let serialize_list = (fun writer f l -> (let _28_22 = (writer.FStar_Util.write_int (FStar_List.length l))
in (FStar_List.iter (fun elt -> (f writer elt)) (FStar_List.rev_append l []))))

let deserialize_list = (fun reader f -> (let n = (reader.FStar_Util.read_int ())
in (let rec helper = (fun accum n -> if (n = 0) then begin
accum
end else begin
(let _93_42 = (let _93_41 = (f reader)
in (_93_41)::accum)
in (helper _93_42 (n - 1)))
end)
in (helper [] n))))

let serialize_ident = (fun writer ast -> (writer.FStar_Util.write_string ast.FStar_Absyn_Syntax.idText))

let deserialize_ident = (fun reader -> (let _93_50 = (let _93_49 = (reader.FStar_Util.read_string ())
in (_93_49, FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_ident _93_50)))

let serialize_LongIdent = (fun writer ast -> (let _28_37 = (serialize_list writer serialize_ident ast.FStar_Absyn_Syntax.ns)
in (serialize_ident writer ast.FStar_Absyn_Syntax.ident)))

let deserialize_LongIdent = (fun reader -> (let _93_60 = (let _93_59 = (deserialize_list reader deserialize_ident)
in (let _93_58 = (let _93_57 = (deserialize_ident reader)
in (_93_57)::[])
in (FStar_List.append _93_59 _93_58)))
in (FStar_Absyn_Syntax.lid_of_ids _93_60)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun writer s_v s_sort ast -> (let _28_46 = (s_v writer ast.FStar_Absyn_Syntax.v)
in (s_sort writer ast.FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun reader ds_v ds_sort -> (let _93_90 = (ds_v reader)
in (let _93_89 = (ds_sort reader)
in {FStar_Absyn_Syntax.v = _93_90; FStar_Absyn_Syntax.sort = _93_89; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun reader ds_sort -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun writer ast -> (let _28_63 = (serialize_ident writer ast.FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ghost reader -> (let _93_110 = (deserialize_ident reader)
in (let _93_109 = (deserialize_ident reader)
in {FStar_Absyn_Syntax.ppname = _93_110; FStar_Absyn_Syntax.realname = _93_109})))

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
(let _93_132 = (reader.FStar_Util.read_byte ())
in FStar_Absyn_Syntax.Const_uint8 (_93_132))
end
| 'c' -> begin
(let _93_133 = (reader.FStar_Util.read_bool ())
in FStar_Absyn_Syntax.Const_bool (_93_133))
end
| 'd' -> begin
(let _93_134 = (reader.FStar_Util.read_int32 ())
in FStar_Absyn_Syntax.Const_int32 (_93_134))
end
| 'e' -> begin
(let _93_135 = (reader.FStar_Util.read_int64 ())
in FStar_Absyn_Syntax.Const_int64 (_93_135))
end
| 'f' -> begin
(let _93_136 = (reader.FStar_Util.read_char ())
in FStar_Absyn_Syntax.Const_char (_93_136))
end
| 'g' -> begin
(let _93_137 = (reader.FStar_Util.read_double ())
in FStar_Absyn_Syntax.Const_float (_93_137))
end
| 'h' -> begin
(let _93_139 = (let _93_138 = (reader.FStar_Util.read_bytearray ())
in (_93_138, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Const_bytearray (_93_139))
end
| 'i' -> begin
(let _93_141 = (let _93_140 = (reader.FStar_Util.read_bytearray ())
in (_93_140, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Const_string (_93_141))
end
| 'j' -> begin
(let _93_142 = (reader.FStar_Util.read_string ())
in FStar_Absyn_Syntax.Const_int (_93_142))
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
(let _93_168 = (ds_l reader)
in FStar_Util.Inl (_93_168))
end
| 'b' -> begin
(let _93_169 = (ds_r reader)
in FStar_Util.Inr (_93_169))
end
| _28_158 -> begin
(parse_error ())
end))

let serialize_syntax = (fun writer s_a ast -> (s_a writer ast.FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun reader ds_a ds_b -> (let _93_188 = (ds_a reader)
in (let _93_187 = (FStar_Util.mk_ref None)
in (let _93_186 = (FStar_Util.mk_ref None)
in (let _93_185 = (FStar_Util.mk_ref None)
in {FStar_Absyn_Syntax.n = _93_188; FStar_Absyn_Syntax.tk = _93_187; FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange; FStar_Absyn_Syntax.fvs = _93_186; FStar_Absyn_Syntax.uvs = _93_185})))))

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
in (let _93_257 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _93_257))))
and serialize_args = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun writer ast -> (let _28_288 = (serialize_either writer serialize_btvar serialize_bvvar (Prims.fst ast))
in (let _93_262 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _93_262))))
and serialize_binders = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun writer ast -> (let _93_267 = (FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _93_267)))
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
and serialize_exp = (fun writer ast -> (let _93_292 = (FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _93_292)))
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
and serialize_knd = (fun writer ast -> (let _93_309 = (FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _93_309)))
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
(let _93_360 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Typ_btvar (_93_360))
end
| 'b' -> begin
(let _93_361 = (deserialize_ftvar reader)
in FStar_Absyn_Syntax.Typ_const (_93_361))
end
| 'c' -> begin
(let _93_364 = (let _93_363 = (deserialize_binders reader)
in (let _93_362 = (deserialize_comp reader)
in (_93_363, _93_362)))
in FStar_Absyn_Syntax.Typ_fun (_93_364))
end
| 'd' -> begin
(let _93_367 = (let _93_366 = (deserialize_bvvar reader)
in (let _93_365 = (deserialize_typ reader)
in (_93_366, _93_365)))
in FStar_Absyn_Syntax.Typ_refine (_93_367))
end
| 'e' -> begin
(let _93_370 = (let _93_369 = (deserialize_typ reader)
in (let _93_368 = (deserialize_args reader)
in (_93_369, _93_368)))
in FStar_Absyn_Syntax.Typ_app (_93_370))
end
| 'f' -> begin
(let _93_373 = (let _93_372 = (deserialize_binders reader)
in (let _93_371 = (deserialize_typ reader)
in (_93_372, _93_371)))
in FStar_Absyn_Syntax.Typ_lam (_93_373))
end
| 'g' -> begin
(let _93_376 = (let _93_375 = (deserialize_typ reader)
in (let _93_374 = (deserialize_knd reader)
in (_93_375, _93_374)))
in FStar_Absyn_Syntax.Typ_ascribed (_93_376))
end
| 'h' -> begin
(let _93_377 = (deserialize_meta_t reader)
in FStar_Absyn_Syntax.Typ_meta (_93_377))
end
| 'i' -> begin
FStar_Absyn_Syntax.Typ_unknown
end
| _28_579 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _93_382 = (let _93_381 = (deserialize_typ reader)
in (let _93_380 = (deserialize_list reader (fun r -> (deserialize_list r deserialize_arg)))
in (_93_381, _93_380)))
in FStar_Absyn_Syntax.Meta_pattern (_93_382))
end
| 'b' -> begin
(let _93_385 = (let _93_384 = (deserialize_typ reader)
in (let _93_383 = (deserialize_lident reader)
in (_93_384, _93_383)))
in FStar_Absyn_Syntax.Meta_named (_93_385))
end
| 'c' -> begin
(let _93_389 = (let _93_388 = (deserialize_typ reader)
in (let _93_387 = (reader.FStar_Util.read_string ())
in (let _93_386 = (reader.FStar_Util.read_bool ())
in (_93_388, _93_387, FStar_Absyn_Syntax.dummyRange, _93_386))))
in FStar_Absyn_Syntax.Meta_labeled (_93_389))
end
| _28_586 -> begin
(parse_error ())
end))
and deserialize_arg = (fun reader -> (let _93_393 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _93_392 = (let _93_391 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _93_391))
in (_93_393, _93_392))))
and deserialize_args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun reader -> (let _93_398 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _93_397 = (let _93_396 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _93_396))
in (_93_398, _93_397))))
and deserialize_binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun reader -> (deserialize_syntax reader deserialize_typ' FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun reader -> (let _93_405 = (deserialize_lident reader)
in (let _93_404 = (deserialize_typ reader)
in (let _93_403 = (deserialize_args reader)
in (let _93_402 = (deserialize_list reader deserialize_cflags)
in {FStar_Absyn_Syntax.effect_name = _93_405; FStar_Absyn_Syntax.result_typ = _93_404; FStar_Absyn_Syntax.effect_args = _93_403; FStar_Absyn_Syntax.flags = _93_402})))))
and deserialize_comp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _93_407 = (deserialize_typ reader)
in FStar_Absyn_Syntax.Total (_93_407))
end
| 'b' -> begin
(let _93_408 = (deserialize_comp_typ reader)
in FStar_Absyn_Syntax.Comp (_93_408))
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
(let _93_411 = (deserialize_exp reader)
in FStar_Absyn_Syntax.DECREASES (_93_411))
end
| _28_608 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _93_413 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Exp_bvar (_93_413))
end
| 'b' -> begin
(let _93_417 = (let _93_416 = (deserialize_fvvar reader)
in (let _93_415 = (let _28_612 = (let _93_414 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left Prims.ignore _93_414))
in None)
in (_93_416, _93_415)))
in FStar_Absyn_Syntax.Exp_fvar (_93_417))
end
| 'c' -> begin
(let _93_418 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Exp_constant (_93_418))
end
| 'd' -> begin
(let _93_421 = (let _93_420 = (deserialize_binders reader)
in (let _93_419 = (deserialize_exp reader)
in (_93_420, _93_419)))
in FStar_Absyn_Syntax.Exp_abs (_93_421))
end
| 'e' -> begin
(let _93_424 = (let _93_423 = (deserialize_exp reader)
in (let _93_422 = (deserialize_args reader)
in (_93_423, _93_422)))
in FStar_Absyn_Syntax.Exp_app (_93_424))
end
| 'f' -> begin
(let g = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _93_427 = (deserialize_exp reader)
in Some (_93_427))
end
| 'b' -> begin
None
end
| _28_623 -> begin
(parse_error ())
end))
in (let f = (fun reader -> (let _93_432 = (deserialize_pat reader)
in (let _93_431 = (g reader)
in (let _93_430 = (deserialize_exp reader)
in (_93_432, _93_431, _93_430)))))
in (let _93_435 = (let _93_434 = (deserialize_exp reader)
in (let _93_433 = (deserialize_list reader f)
in (_93_434, _93_433)))
in FStar_Absyn_Syntax.Exp_match (_93_435))))
end
| 'g' -> begin
(let _93_439 = (let _93_438 = (deserialize_exp reader)
in (let _93_437 = (deserialize_typ reader)
in (let _93_436 = (deserialize_option reader deserialize_lident)
in (_93_438, _93_437, _93_436))))
in FStar_Absyn_Syntax.Exp_ascribed (_93_439))
end
| 'h' -> begin
(let _93_442 = (let _93_441 = (deserialize_letbindings reader)
in (let _93_440 = (deserialize_exp reader)
in (_93_441, _93_440)))
in FStar_Absyn_Syntax.Exp_let (_93_442))
end
| 'i' -> begin
(let _93_443 = (deserialize_meta_e reader)
in FStar_Absyn_Syntax.Exp_meta (_93_443))
end
| _28_630 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _93_447 = (let _93_446 = (deserialize_exp reader)
in (let _93_445 = (deserialize_meta_source_info reader)
in (_93_446, _93_445)))
in FStar_Absyn_Syntax.Meta_desugared (_93_447))
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
(let _93_453 = (deserialize_list reader deserialize_pat)
in FStar_Absyn_Syntax.Pat_disj (_93_453))
end
| 'b' -> begin
(let _93_454 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Pat_constant (_93_454))
end
| 'c' -> begin
(let _93_460 = (let _93_459 = (deserialize_fvvar reader)
in (let _93_458 = (deserialize_list reader (fun r -> (let _93_457 = (deserialize_pat r)
in (let _93_456 = (r.FStar_Util.read_bool ())
in (_93_457, _93_456)))))
in (_93_459, None, _93_458)))
in FStar_Absyn_Syntax.Pat_cons (_93_460))
end
| 'd' -> begin
(let _93_461 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_var (_93_461))
end
| 'e' -> begin
(let _93_462 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_tvar (_93_462))
end
| 'f' -> begin
(let _93_463 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_wild (_93_463))
end
| 'g' -> begin
(let _93_464 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_twild (_93_464))
end
| 'h' -> begin
(let _93_467 = (let _93_466 = (deserialize_bvvar reader)
in (let _93_465 = (deserialize_exp reader)
in (_93_466, _93_465)))
in FStar_Absyn_Syntax.Pat_dot_term (_93_467))
end
| 'i' -> begin
(let _93_470 = (let _93_469 = (deserialize_btvar reader)
in (let _93_468 = (deserialize_typ reader)
in (_93_469, _93_468)))
in FStar_Absyn_Syntax.Pat_dot_typ (_93_470))
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
(let _93_476 = (let _93_475 = (deserialize_kabbrev reader)
in (let _93_474 = (deserialize_knd reader)
in (_93_475, _93_474)))
in FStar_Absyn_Syntax.Kind_abbrev (_93_476))
end
| 'd' -> begin
(let _93_479 = (let _93_478 = (deserialize_binders reader)
in (let _93_477 = (deserialize_knd reader)
in (_93_478, _93_477)))
in FStar_Absyn_Syntax.Kind_arrow (_93_479))
end
| 'e' -> begin
(let _93_482 = (let _93_481 = (deserialize_binders reader)
in (let _93_480 = (deserialize_knd reader)
in (_93_481, _93_480)))
in FStar_Absyn_Syntax.Kind_lam (_93_482))
end
| 'f' -> begin
FStar_Absyn_Syntax.Kind_unknown
end
| _28_668 -> begin
(parse_error ())
end))
and deserialize_knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun reader -> (let _93_486 = (deserialize_lident reader)
in (let _93_485 = (deserialize_args reader)
in (_93_486, _93_485))))
and deserialize_lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun reader -> (let f = (fun reader -> (let _93_494 = (deserialize_lbname reader)
in (let _93_493 = (deserialize_typ reader)
in (let _93_492 = (deserialize_lident reader)
in (let _93_491 = (deserialize_exp reader)
in {FStar_Absyn_Syntax.lbname = _93_494; FStar_Absyn_Syntax.lbtyp = _93_493; FStar_Absyn_Syntax.lbeff = _93_492; FStar_Absyn_Syntax.lbdef = _93_491})))))
in (let _93_496 = (reader.FStar_Util.read_bool ())
in (let _93_495 = (deserialize_list reader f)
in (_93_496, _93_495)))))
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
(let _93_511 = (deserialize_lident reader)
in FStar_Absyn_Syntax.Discriminator (_93_511))
end
| 'j' -> begin
(let _93_514 = (let _93_513 = (deserialize_lident reader)
in (let _93_512 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_93_513, _93_512)))
in FStar_Absyn_Syntax.Projector (_93_514))
end
| 'k' -> begin
(let _93_515 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordType (_93_515))
end
| 'l' -> begin
(let _93_516 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordConstructor (_93_516))
end
| 'm' -> begin
FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _93_518 = (deserialize_option reader deserialize_lident)
in (FStar_All.pipe_right _93_518 (fun _93_517 -> FStar_Absyn_Syntax.DefaultEffect (_93_517))))
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

let deserialize_tycon = (fun reader -> (let _93_527 = (deserialize_lident reader)
in (let _93_526 = (deserialize_binders reader)
in (let _93_525 = (deserialize_knd reader)
in (_93_527, _93_526, _93_525)))))

let serialize_monad_abbrev = (fun writer ast -> (let _28_742 = (serialize_lident writer ast.FStar_Absyn_Syntax.mabbrev)
in (let _28_744 = (serialize_binders writer ast.FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun reader -> (let _93_536 = (deserialize_lident reader)
in (let _93_535 = (deserialize_binders reader)
in (let _93_534 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mabbrev = _93_536; FStar_Absyn_Syntax.parms = _93_535; FStar_Absyn_Syntax.def = _93_534}))))

let serialize_sub_effect = (fun writer ast -> (let _28_749 = (serialize_lident writer ast.FStar_Absyn_Syntax.source)
in (let _28_751 = (serialize_lident writer ast.FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun reader -> (let _93_545 = (deserialize_lident reader)
in (let _93_544 = (deserialize_lident reader)
in (let _93_543 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.source = _93_545; FStar_Absyn_Syntax.target = _93_544; FStar_Absyn_Syntax.lift = _93_543}))))

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
(let _93_555 = (let _93_554 = (FStar_Absyn_Syntax.mk_Total (FStar_Absyn_Util.comp_result c))
in (f, _93_554))
in (FStar_Absyn_Syntax.mk_Typ_fun _93_555 None FStar_Absyn_Syntax.dummyRange))
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
in (let _93_557 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _28_1 -> (match (_28_1) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _28_903 -> begin
false
end))))
in (writer.FStar_Util.write_bool _93_557)))))
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

let rec deserialize_new_effect = (fun reader -> (let _93_578 = (deserialize_lident reader)
in (let _93_577 = (deserialize_list reader deserialize_binder)
in (let _93_576 = (deserialize_list reader deserialize_qualifier)
in (let _93_575 = (deserialize_knd reader)
in (let _93_574 = (deserialize_typ reader)
in (let _93_573 = (deserialize_typ reader)
in (let _93_572 = (deserialize_typ reader)
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
in {FStar_Absyn_Syntax.mname = _93_578; FStar_Absyn_Syntax.binders = _93_577; FStar_Absyn_Syntax.qualifiers = _93_576; FStar_Absyn_Syntax.signature = _93_575; FStar_Absyn_Syntax.ret = _93_574; FStar_Absyn_Syntax.bind_wp = _93_573; FStar_Absyn_Syntax.bind_wlp = _93_572; FStar_Absyn_Syntax.if_then_else = _93_571; FStar_Absyn_Syntax.ite_wp = _93_570; FStar_Absyn_Syntax.ite_wlp = _93_569; FStar_Absyn_Syntax.wp_binop = _93_568; FStar_Absyn_Syntax.wp_as_type = _93_567; FStar_Absyn_Syntax.close_wp = _93_566; FStar_Absyn_Syntax.close_wp_t = _93_565; FStar_Absyn_Syntax.assert_p = _93_564; FStar_Absyn_Syntax.assume_p = _93_563; FStar_Absyn_Syntax.null_wp = _93_562; FStar_Absyn_Syntax.trivial = _93_561})))))))))))))))))))
and deserialize_sigelt = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _93_586 = (let _93_585 = (deserialize_lident reader)
in (let _93_584 = (deserialize_binders reader)
in (let _93_583 = (deserialize_knd reader)
in (let _93_582 = (deserialize_list reader deserialize_lident)
in (let _93_581 = (deserialize_list reader deserialize_lident)
in (let _93_580 = (deserialize_list reader deserialize_qualifier)
in (_93_585, _93_584, _93_583, _93_582, _93_581, _93_580, FStar_Absyn_Syntax.dummyRange)))))))
in FStar_Absyn_Syntax.Sig_tycon (_93_586))
end
| 'b' -> begin
(let _93_592 = (let _93_591 = (deserialize_lident reader)
in (let _93_590 = (deserialize_binders reader)
in (let _93_589 = (deserialize_knd reader)
in (let _93_588 = (deserialize_typ reader)
in (let _93_587 = (deserialize_list reader deserialize_qualifier)
in (_93_591, _93_590, _93_589, _93_588, _93_587, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_93_592))
end
| 'c' -> begin
(let _93_598 = (let _93_597 = (deserialize_lident reader)
in (let _93_596 = (deserialize_typ reader)
in (let _93_595 = (deserialize_tycon reader)
in (let _93_594 = (deserialize_list reader deserialize_qualifier)
in (let _93_593 = (deserialize_list reader deserialize_lident)
in (_93_597, _93_596, _93_595, _93_594, _93_593, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_datacon (_93_598))
end
| 'd' -> begin
(let _93_602 = (let _93_601 = (deserialize_lident reader)
in (let _93_600 = (deserialize_typ reader)
in (let _93_599 = (deserialize_list reader deserialize_qualifier)
in (_93_601, _93_600, _93_599, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_val_decl (_93_602))
end
| 'e' -> begin
(let _93_606 = (let _93_605 = (deserialize_lident reader)
in (let _93_604 = (deserialize_formula reader)
in (let _93_603 = (deserialize_list reader deserialize_qualifier)
in (_93_605, _93_604, _93_603, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_assume (_93_606))
end
| 'f' -> begin
(let _93_610 = (let _93_609 = (deserialize_letbindings reader)
in (let _93_608 = (deserialize_list reader deserialize_lident)
in (let _93_607 = if (reader.FStar_Util.read_bool ()) then begin
(FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end
in (_93_609, FStar_Absyn_Syntax.dummyRange, _93_608, _93_607))))
in FStar_Absyn_Syntax.Sig_let (_93_610))
end
| 'g' -> begin
(let _93_612 = (let _93_611 = (deserialize_exp reader)
in (_93_611, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_main (_93_612))
end
| 'h' -> begin
(let _93_616 = (let _93_615 = (deserialize_list reader deserialize_sigelt)
in (let _93_614 = (deserialize_list reader deserialize_qualifier)
in (let _93_613 = (deserialize_list reader deserialize_lident)
in (_93_615, _93_614, _93_613, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_bundle (_93_616))
end
| 'i' -> begin
(let _93_618 = (let _93_617 = (deserialize_new_effect reader)
in (_93_617, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_new_effect (_93_618))
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

let deserialize_modul = (fun reader -> (let m = (let _93_634 = (deserialize_lident reader)
in (let _93_633 = (deserialize_sigelts reader)
in (let _93_632 = (deserialize_sigelts reader)
in (let _93_631 = (reader.FStar_Util.read_bool ())
in {FStar_Absyn_Syntax.name = _93_634; FStar_Absyn_Syntax.declarations = _93_633; FStar_Absyn_Syntax.exports = _93_632; FStar_Absyn_Syntax.is_interface = _93_631; FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _28_995 = m
in {FStar_Absyn_Syntax.name = _28_995.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = m.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.exports = _28_995.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _28_995.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _28_995.FStar_Absyn_Syntax.is_deserialized})))




