
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
| Err (_29_3) -> begin
_29_3
end))

let parse_error = (fun _29_4 -> (match (()) with
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
(let _29_12 = (writer.FStar_Util.write_char 's')
in (f writer l))
end))

let deserialize_option = (fun reader f -> (let n = (reader.FStar_Util.read_char ())
in if (n = 'n') then begin
None
end else begin
(let _59_21 = (f reader)
in Some (_59_21))
end))

let serialize_list = (fun writer f l -> (let _29_22 = (writer.FStar_Util.write_int (FStar_List.length l))
in (FStar_List.iter (fun elt -> (f writer elt)) (FStar_List.rev_append l []))))

let deserialize_list = (fun reader f -> (let n = (reader.FStar_Util.read_int ())
in (let rec helper = (fun accum n -> if (n = 0) then begin
accum
end else begin
(let _59_42 = (let _59_41 = (f reader)
in (_59_41)::accum)
in (helper _59_42 (n - 1)))
end)
in (helper [] n))))

let serialize_ident = (fun writer ast -> (writer.FStar_Util.write_string ast.FStar_Ident.idText))

let deserialize_ident = (fun reader -> (let _59_50 = (let _59_49 = (reader.FStar_Util.read_string ())
in (_59_49, FStar_Absyn_Syntax.dummyRange))
in (FStar_Ident.mk_ident _59_50)))

let serialize_LongIdent = (fun writer ast -> (let _29_37 = (serialize_list writer serialize_ident ast.FStar_Ident.ns)
in (serialize_ident writer ast.FStar_Ident.ident)))

let deserialize_LongIdent = (fun reader -> (let _59_60 = (let _59_59 = (deserialize_list reader deserialize_ident)
in (let _59_58 = (let _59_57 = (deserialize_ident reader)
in (_59_57)::[])
in (FStar_List.append _59_59 _59_58)))
in (FStar_Ident.lid_of_ids _59_60)))

let serialize_lident = serialize_LongIdent

let deserialize_lident = deserialize_LongIdent

let serialize_withinfo_t = (fun writer s_v s_sort ast -> (let _29_46 = (s_v writer ast.FStar_Absyn_Syntax.v)
in (s_sort writer ast.FStar_Absyn_Syntax.sort)))

let deserialize_withinfo_t = (fun reader ds_v ds_sort -> (let _59_90 = (ds_v reader)
in (let _59_89 = (ds_sort reader)
in {FStar_Absyn_Syntax.v = _59_90; FStar_Absyn_Syntax.sort = _59_89; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange})))

let serialize_var = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_lident s_sort ast))

let deserialize_var = (fun reader ds_sort -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

let serialize_bvdef = (fun writer ast -> (let _29_63 = (serialize_ident writer ast.FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.FStar_Absyn_Syntax.realname)))

let deserialize_bvdef = (fun ghost reader -> (let _59_110 = (deserialize_ident reader)
in (let _59_109 = (deserialize_ident reader)
in {FStar_Absyn_Syntax.ppname = _59_110; FStar_Absyn_Syntax.realname = _59_109})))

let serialize_bvar = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

let deserialize_bvar = (fun ghost reader ds_sort -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

let serialize_sconst = (fun writer ast -> (match (ast) with
| FStar_Const.Const_effect -> begin
(writer.FStar_Util.write_char '_')
end
| FStar_Const.Const_unit -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Const.Const_uint8 (v) -> begin
(let _29_84 = (writer.FStar_Util.write_char 'b')
in (writer.FStar_Util.write_byte v))
end
| FStar_Const.Const_bool (v) -> begin
(let _29_88 = (writer.FStar_Util.write_char 'c')
in (writer.FStar_Util.write_bool v))
end
| FStar_Const.Const_int32 (v) -> begin
(let _29_92 = (writer.FStar_Util.write_char 'd')
in (writer.FStar_Util.write_int32 v))
end
| FStar_Const.Const_int64 (v) -> begin
(let _29_96 = (writer.FStar_Util.write_char 'e')
in (writer.FStar_Util.write_int64 v))
end
| FStar_Const.Const_char (v) -> begin
(let _29_100 = (writer.FStar_Util.write_char 'f')
in (writer.FStar_Util.write_char v))
end
| FStar_Const.Const_float (v) -> begin
(let _29_104 = (writer.FStar_Util.write_char 'g')
in (writer.FStar_Util.write_double v))
end
| FStar_Const.Const_bytearray (v, _29_108) -> begin
(let _29_111 = (writer.FStar_Util.write_char 'h')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Const.Const_string (v, _29_115) -> begin
(let _29_118 = (writer.FStar_Util.write_char 'i')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Const.Const_int (v) -> begin
(let _29_122 = (writer.FStar_Util.write_char 'j')
in (writer.FStar_Util.write_string v))
end))

let deserialize_sconst = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| '_' -> begin
FStar_Const.Const_effect
end
| 'a' -> begin
FStar_Const.Const_unit
end
| 'b' -> begin
(let _59_132 = (reader.FStar_Util.read_byte ())
in FStar_Const.Const_uint8 (_59_132))
end
| 'c' -> begin
(let _59_133 = (reader.FStar_Util.read_bool ())
in FStar_Const.Const_bool (_59_133))
end
| 'd' -> begin
(let _59_134 = (reader.FStar_Util.read_int32 ())
in FStar_Const.Const_int32 (_59_134))
end
| 'e' -> begin
(let _59_135 = (reader.FStar_Util.read_int64 ())
in FStar_Const.Const_int64 (_59_135))
end
| 'f' -> begin
(let _59_136 = (reader.FStar_Util.read_char ())
in FStar_Const.Const_char (_59_136))
end
| 'g' -> begin
(let _59_137 = (reader.FStar_Util.read_double ())
in FStar_Const.Const_float (_59_137))
end
| 'h' -> begin
(let _59_139 = (let _59_138 = (reader.FStar_Util.read_bytearray ())
in (_59_138, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_bytearray (_59_139))
end
| 'i' -> begin
(let _59_141 = (let _59_140 = (reader.FStar_Util.read_bytearray ())
in (_59_140, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_59_141))
end
| 'j' -> begin
(let _59_142 = (reader.FStar_Util.read_string ())
in FStar_Const.Const_int (_59_142))
end
| _29_137 -> begin
(parse_error ())
end))

let serialize_either = (fun writer s_l s_r ast -> (match (ast) with
| FStar_Util.Inl (v) -> begin
(let _29_146 = (writer.FStar_Util.write_char 'a')
in (s_l writer v))
end
| FStar_Util.Inr (v) -> begin
(let _29_150 = (writer.FStar_Util.write_char 'b')
in (s_r writer v))
end))

let deserialize_either = (fun reader ds_l ds_r -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_168 = (ds_l reader)
in FStar_Util.Inl (_59_168))
end
| 'b' -> begin
(let _59_169 = (ds_r reader)
in FStar_Util.Inr (_59_169))
end
| _29_160 -> begin
(parse_error ())
end))

let serialize_syntax = (fun writer s_a ast -> (s_a writer ast.FStar_Absyn_Syntax.n))

let deserialize_syntax = (fun reader ds_a ds_b -> (let _59_188 = (ds_a reader)
in (let _59_187 = (FStar_Util.mk_ref None)
in (let _59_186 = (FStar_Util.mk_ref None)
in (let _59_185 = (FStar_Util.mk_ref None)
in {FStar_Absyn_Syntax.n = _59_188; FStar_Absyn_Syntax.tk = _59_187; FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange; FStar_Absyn_Syntax.fvs = _59_186; FStar_Absyn_Syntax.uvs = _59_185})))))

let rec serialize_typ' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _29_175 = (writer.FStar_Util.write_char 'a')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _29_179 = (writer.FStar_Util.write_char 'b')
in (serialize_ftvar writer v))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _29_185 = (writer.FStar_Util.write_char 'c')
in (let _29_187 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| FStar_Absyn_Syntax.Typ_refine (v, t) -> begin
(let _29_193 = (writer.FStar_Util.write_char 'd')
in (let _29_195 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_app (t, ars) -> begin
(let _29_201 = (writer.FStar_Util.write_char 'e')
in (let _29_203 = (serialize_typ writer t)
in (let _29_205 = (serialize_args writer ars)
in if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (_29_208, _29_210) -> begin
(FStar_Util.print_string "type application node with lam\n")
end
| _29_214 -> begin
()
end)
end else begin
()
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _29_219 = (writer.FStar_Util.write_char 'f')
in (let _29_221 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _29_227 = (writer.FStar_Util.write_char 'g')
in (let _29_229 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _29_233 = (writer.FStar_Util.write_char 'h')
in (serialize_meta_t writer m))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(writer.FStar_Util.write_char 'i')
end
| FStar_Absyn_Syntax.Typ_uvar (_29_237, _29_239) -> begin
(Prims.raise (Err ("typ not impl:1")))
end
| FStar_Absyn_Syntax.Typ_delayed (_29_243, _29_245) -> begin
(Prims.raise (Err ("typ not impl:2")))
end))
and serialize_meta_t = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_pattern (t, l) -> begin
(let _29_254 = (writer.FStar_Util.write_char 'a')
in (let _29_256 = (serialize_typ writer t)
in (serialize_list writer (fun w -> (serialize_list w serialize_arg)) l)))
end
| FStar_Absyn_Syntax.Meta_named (t, lid) -> begin
(let _29_263 = (writer.FStar_Util.write_char 'b')
in (let _29_265 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| FStar_Absyn_Syntax.Meta_labeled (t, s, _29_270, b) -> begin
(let _29_274 = (writer.FStar_Util.write_char 'c')
in (let _29_276 = (serialize_typ writer t)
in (let _29_278 = (writer.FStar_Util.write_string s)
in (writer.FStar_Util.write_bool b))))
end
| _29_281 -> begin
(Prims.raise (Err ("unimplemented meta_t")))
end))
and serialize_arg = (fun writer ast -> (let _29_284 = (serialize_either writer serialize_typ serialize_exp (Prims.fst ast))
in (let _59_257 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _59_257))))
and serialize_args = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun writer ast -> (let _29_290 = (serialize_either writer serialize_btvar serialize_bvvar (Prims.fst ast))
in (let _59_262 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _59_262))))
and serialize_binders = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun writer ast -> (let _59_267 = (FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _59_267)))
and serialize_comp_typ = (fun writer ast -> (let _29_298 = (serialize_lident writer ast.FStar_Absyn_Syntax.effect_name)
in (let _29_300 = (serialize_typ writer ast.FStar_Absyn_Syntax.result_typ)
in (let _29_302 = (serialize_args writer ast.FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _29_308 = (writer.FStar_Util.write_char 'a')
in (serialize_typ writer t))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let _29_312 = (writer.FStar_Util.write_char 'b')
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
(let _29_326 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _29_332 = (writer.FStar_Util.write_char 'a')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Exp_fvar (v, b) -> begin
(let _29_338 = (writer.FStar_Util.write_char 'b')
in (let _29_340 = (serialize_fvvar writer v)
in (writer.FStar_Util.write_bool false)))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _29_344 = (writer.FStar_Util.write_char 'c')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _29_350 = (writer.FStar_Util.write_char 'd')
in (let _29_352 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_app (e, ars) -> begin
(let _29_358 = (writer.FStar_Util.write_char 'e')
in (let _29_360 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| FStar_Absyn_Syntax.Exp_match (e, l) -> begin
(let g = (fun writer eopt -> (match (eopt) with
| Some (e1) -> begin
(let _29_371 = (writer.FStar_Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.FStar_Util.write_char 'b')
end))
in (let f = (fun writer _29_379 -> (match (_29_379) with
| (p, eopt, e) -> begin
(let _29_380 = (serialize_pat writer p)
in (let _29_382 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _29_384 = (writer.FStar_Util.write_char 'f')
in (let _29_386 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let _29_393 = (writer.FStar_Util.write_char 'g')
in (let _29_395 = (serialize_exp writer e)
in (let _29_397 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _29_403 = (writer.FStar_Util.write_char 'h')
in (let _29_405 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _29_409 = (writer.FStar_Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _29_412 -> begin
(Prims.raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_desugared (e, s) -> begin
(let _29_419 = (writer.FStar_Util.write_char 'a')
in (let _29_421 = (serialize_exp writer e)
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
and serialize_exp = (fun writer ast -> (let _59_292 = (FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _59_292)))
and serialize_btvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_pat' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _29_440 = (writer.FStar_Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _29_444 = (writer.FStar_Util.write_char 'b')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Pat_cons (v, _29_448, l) -> begin
(let _29_452 = (writer.FStar_Util.write_char 'c')
in (let _29_454 = (serialize_fvvar writer v)
in (serialize_list writer (fun w _29_459 -> (match (_29_459) with
| (p, b) -> begin
(let _29_460 = (serialize_pat w p)
in (w.FStar_Util.write_bool b))
end)) l)))
end
| FStar_Absyn_Syntax.Pat_var (v) -> begin
(let _29_464 = (writer.FStar_Util.write_char 'd')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _29_468 = (writer.FStar_Util.write_char 'e')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _29_472 = (writer.FStar_Util.write_char 'f')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _29_476 = (writer.FStar_Util.write_char 'g')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_dot_term (v, e) -> begin
(let _29_482 = (writer.FStar_Util.write_char 'h')
in (let _29_484 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (v, t) -> begin
(let _29_490 = (writer.FStar_Util.write_char 'i')
in (let _29_492 = (serialize_btvar writer v)
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
(let _29_506 = (writer.FStar_Util.write_char 'c')
in (let _29_508 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _29_514 = (writer.FStar_Util.write_char 'd')
in (let _29_516 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_lam (bs, k) -> begin
(let _29_522 = (writer.FStar_Util.write_char 'e')
in (let _29_524 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.FStar_Util.write_char 'f')
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:1")))
end
| FStar_Absyn_Syntax.Kind_delayed (_29_532, _29_534, _29_536) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun writer ast -> (let _59_309 = (FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _59_309)))
and serialize_kabbrev = (fun writer ast -> (let _29_543 = (serialize_lident writer (Prims.fst ast))
in (serialize_args writer (Prims.snd ast))))
and serialize_lbname = (fun writer ast -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun writer ast -> (let f = (fun writer lb -> (let _29_552 = (serialize_lbname writer lb.FStar_Absyn_Syntax.lbname)
in (let _29_554 = (serialize_lident writer lb.FStar_Absyn_Syntax.lbeff)
in (let _29_556 = (serialize_typ writer lb.FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.FStar_Absyn_Syntax.lbdef)))))
in (let _29_558 = (writer.FStar_Util.write_bool (Prims.fst ast))
in (serialize_list writer f (Prims.snd ast)))))
and serialize_fvar = (fun writer ast -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun writer ast -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun writer ast -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun writer ast -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun writer ast -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_360 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Typ_btvar (_59_360))
end
| 'b' -> begin
(let _59_361 = (deserialize_ftvar reader)
in FStar_Absyn_Syntax.Typ_const (_59_361))
end
| 'c' -> begin
(let _59_364 = (let _59_363 = (deserialize_binders reader)
in (let _59_362 = (deserialize_comp reader)
in (_59_363, _59_362)))
in FStar_Absyn_Syntax.Typ_fun (_59_364))
end
| 'd' -> begin
(let _59_367 = (let _59_366 = (deserialize_bvvar reader)
in (let _59_365 = (deserialize_typ reader)
in (_59_366, _59_365)))
in FStar_Absyn_Syntax.Typ_refine (_59_367))
end
| 'e' -> begin
(let _59_370 = (let _59_369 = (deserialize_typ reader)
in (let _59_368 = (deserialize_args reader)
in (_59_369, _59_368)))
in FStar_Absyn_Syntax.Typ_app (_59_370))
end
| 'f' -> begin
(let _59_373 = (let _59_372 = (deserialize_binders reader)
in (let _59_371 = (deserialize_typ reader)
in (_59_372, _59_371)))
in FStar_Absyn_Syntax.Typ_lam (_59_373))
end
| 'g' -> begin
(let _59_376 = (let _59_375 = (deserialize_typ reader)
in (let _59_374 = (deserialize_knd reader)
in (_59_375, _59_374)))
in FStar_Absyn_Syntax.Typ_ascribed (_59_376))
end
| 'h' -> begin
(let _59_377 = (deserialize_meta_t reader)
in FStar_Absyn_Syntax.Typ_meta (_59_377))
end
| 'i' -> begin
FStar_Absyn_Syntax.Typ_unknown
end
| _29_581 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_382 = (let _59_381 = (deserialize_typ reader)
in (let _59_380 = (deserialize_list reader (fun r -> (deserialize_list r deserialize_arg)))
in (_59_381, _59_380)))
in FStar_Absyn_Syntax.Meta_pattern (_59_382))
end
| 'b' -> begin
(let _59_385 = (let _59_384 = (deserialize_typ reader)
in (let _59_383 = (deserialize_lident reader)
in (_59_384, _59_383)))
in FStar_Absyn_Syntax.Meta_named (_59_385))
end
| 'c' -> begin
(let _59_389 = (let _59_388 = (deserialize_typ reader)
in (let _59_387 = (reader.FStar_Util.read_string ())
in (let _59_386 = (reader.FStar_Util.read_bool ())
in (_59_388, _59_387, FStar_Absyn_Syntax.dummyRange, _59_386))))
in FStar_Absyn_Syntax.Meta_labeled (_59_389))
end
| _29_588 -> begin
(parse_error ())
end))
and deserialize_arg = (fun reader -> (let _59_393 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _59_392 = (let _59_391 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _59_391))
in (_59_393, _59_392))))
and deserialize_args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun reader -> (let _59_398 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _59_397 = (let _59_396 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _59_396))
in (_59_398, _59_397))))
and deserialize_binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun reader -> (deserialize_syntax reader deserialize_typ' FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun reader -> (let _59_405 = (deserialize_lident reader)
in (let _59_404 = (deserialize_typ reader)
in (let _59_403 = (deserialize_args reader)
in (let _59_402 = (deserialize_list reader deserialize_cflags)
in {FStar_Absyn_Syntax.effect_name = _59_405; FStar_Absyn_Syntax.result_typ = _59_404; FStar_Absyn_Syntax.effect_args = _59_403; FStar_Absyn_Syntax.flags = _59_402})))))
and deserialize_comp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_407 = (deserialize_typ reader)
in FStar_Absyn_Syntax.Total (_59_407))
end
| 'b' -> begin
(let _59_408 = (deserialize_comp_typ reader)
in FStar_Absyn_Syntax.Comp (_59_408))
end
| _29_599 -> begin
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
(let _59_411 = (deserialize_exp reader)
in FStar_Absyn_Syntax.DECREASES (_59_411))
end
| _29_610 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_413 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Exp_bvar (_59_413))
end
| 'b' -> begin
(let _59_417 = (let _59_416 = (deserialize_fvvar reader)
in (let _59_415 = (let _29_614 = (let _59_414 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left Prims.ignore _59_414))
in None)
in (_59_416, _59_415)))
in FStar_Absyn_Syntax.Exp_fvar (_59_417))
end
| 'c' -> begin
(let _59_418 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Exp_constant (_59_418))
end
| 'd' -> begin
(let _59_421 = (let _59_420 = (deserialize_binders reader)
in (let _59_419 = (deserialize_exp reader)
in (_59_420, _59_419)))
in FStar_Absyn_Syntax.Exp_abs (_59_421))
end
| 'e' -> begin
(let _59_424 = (let _59_423 = (deserialize_exp reader)
in (let _59_422 = (deserialize_args reader)
in (_59_423, _59_422)))
in FStar_Absyn_Syntax.Exp_app (_59_424))
end
| 'f' -> begin
(let g = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_427 = (deserialize_exp reader)
in Some (_59_427))
end
| 'b' -> begin
None
end
| _29_625 -> begin
(parse_error ())
end))
in (let f = (fun reader -> (let _59_432 = (deserialize_pat reader)
in (let _59_431 = (g reader)
in (let _59_430 = (deserialize_exp reader)
in (_59_432, _59_431, _59_430)))))
in (let _59_435 = (let _59_434 = (deserialize_exp reader)
in (let _59_433 = (deserialize_list reader f)
in (_59_434, _59_433)))
in FStar_Absyn_Syntax.Exp_match (_59_435))))
end
| 'g' -> begin
(let _59_439 = (let _59_438 = (deserialize_exp reader)
in (let _59_437 = (deserialize_typ reader)
in (let _59_436 = (deserialize_option reader deserialize_lident)
in (_59_438, _59_437, _59_436))))
in FStar_Absyn_Syntax.Exp_ascribed (_59_439))
end
| 'h' -> begin
(let _59_442 = (let _59_441 = (deserialize_letbindings reader)
in (let _59_440 = (deserialize_exp reader)
in (_59_441, _59_440)))
in FStar_Absyn_Syntax.Exp_let (_59_442))
end
| 'i' -> begin
(let _59_443 = (deserialize_meta_e reader)
in FStar_Absyn_Syntax.Exp_meta (_59_443))
end
| _29_632 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_447 = (let _59_446 = (deserialize_exp reader)
in (let _59_445 = (deserialize_meta_source_info reader)
in (_59_446, _59_445)))
in FStar_Absyn_Syntax.Meta_desugared (_59_447))
end
| _29_636 -> begin
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
| _29_643 -> begin
(parse_error ())
end))
and deserialize_exp = (fun reader -> (deserialize_syntax reader deserialize_exp' FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_453 = (deserialize_list reader deserialize_pat)
in FStar_Absyn_Syntax.Pat_disj (_59_453))
end
| 'b' -> begin
(let _59_454 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Pat_constant (_59_454))
end
| 'c' -> begin
(let _59_460 = (let _59_459 = (deserialize_fvvar reader)
in (let _59_458 = (deserialize_list reader (fun r -> (let _59_457 = (deserialize_pat r)
in (let _59_456 = (r.FStar_Util.read_bool ())
in (_59_457, _59_456)))))
in (_59_459, None, _59_458)))
in FStar_Absyn_Syntax.Pat_cons (_59_460))
end
| 'd' -> begin
(let _59_461 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_var (_59_461))
end
| 'e' -> begin
(let _59_462 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_tvar (_59_462))
end
| 'f' -> begin
(let _59_463 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_wild (_59_463))
end
| 'g' -> begin
(let _59_464 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_twild (_59_464))
end
| 'h' -> begin
(let _59_467 = (let _59_466 = (deserialize_bvvar reader)
in (let _59_465 = (deserialize_exp reader)
in (_59_466, _59_465)))
in FStar_Absyn_Syntax.Pat_dot_term (_59_467))
end
| 'i' -> begin
(let _59_470 = (let _59_469 = (deserialize_btvar reader)
in (let _59_468 = (deserialize_typ reader)
in (_59_469, _59_468)))
in FStar_Absyn_Syntax.Pat_dot_typ (_59_470))
end
| _29_659 -> begin
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
(let _59_476 = (let _59_475 = (deserialize_kabbrev reader)
in (let _59_474 = (deserialize_knd reader)
in (_59_475, _59_474)))
in FStar_Absyn_Syntax.Kind_abbrev (_59_476))
end
| 'd' -> begin
(let _59_479 = (let _59_478 = (deserialize_binders reader)
in (let _59_477 = (deserialize_knd reader)
in (_59_478, _59_477)))
in FStar_Absyn_Syntax.Kind_arrow (_59_479))
end
| 'e' -> begin
(let _59_482 = (let _59_481 = (deserialize_binders reader)
in (let _59_480 = (deserialize_knd reader)
in (_59_481, _59_480)))
in FStar_Absyn_Syntax.Kind_lam (_59_482))
end
| 'f' -> begin
FStar_Absyn_Syntax.Kind_unknown
end
| _29_670 -> begin
(parse_error ())
end))
and deserialize_knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun reader -> (let _59_486 = (deserialize_lident reader)
in (let _59_485 = (deserialize_args reader)
in (_59_486, _59_485))))
and deserialize_lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun reader -> (let f = (fun reader -> (let _59_494 = (deserialize_lbname reader)
in (let _59_493 = (deserialize_typ reader)
in (let _59_492 = (deserialize_lident reader)
in (let _59_491 = (deserialize_exp reader)
in {FStar_Absyn_Syntax.lbname = _59_494; FStar_Absyn_Syntax.lbtyp = _59_493; FStar_Absyn_Syntax.lbeff = _59_492; FStar_Absyn_Syntax.lbdef = _59_491})))))
in (let _59_496 = (reader.FStar_Util.read_bool ())
in (let _59_495 = (deserialize_list reader f)
in (_59_496, _59_495)))))
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
(let _29_690 = (writer.FStar_Util.write_char 'i')
in (serialize_lident writer lid))
end
| FStar_Absyn_Syntax.Projector (lid, v) -> begin
(let _29_696 = (writer.FStar_Util.write_char 'j')
in (let _29_698 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| FStar_Absyn_Syntax.RecordType (l) -> begin
(let _29_702 = (writer.FStar_Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _29_706 = (writer.FStar_Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.FStar_Util.write_char 'm')
end
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.FStar_Util.write_char 'o')
end
| FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _29_712 = (writer.FStar_Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| FStar_Absyn_Syntax.TotalEffect -> begin
(writer.FStar_Util.write_char 'q')
end
| _29_716 -> begin
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
(let _59_511 = (deserialize_lident reader)
in FStar_Absyn_Syntax.Discriminator (_59_511))
end
| 'j' -> begin
(let _59_514 = (let _59_513 = (deserialize_lident reader)
in (let _59_512 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_59_513, _59_512)))
in FStar_Absyn_Syntax.Projector (_59_514))
end
| 'k' -> begin
(let _59_515 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordType (_59_515))
end
| 'l' -> begin
(let _59_516 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordConstructor (_59_516))
end
| 'm' -> begin
FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _59_518 = (deserialize_option reader deserialize_lident)
in (FStar_All.pipe_right _59_518 (fun _59_517 -> FStar_Absyn_Syntax.DefaultEffect (_59_517))))
end
| 'q' -> begin
FStar_Absyn_Syntax.TotalEffect
end
| _29_731 -> begin
(parse_error ())
end))

let serialize_tycon = (fun writer _29_736 -> (match (_29_736) with
| (lid, bs, k) -> begin
(let _29_737 = (serialize_lident writer lid)
in (let _29_739 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun reader -> (let _59_527 = (deserialize_lident reader)
in (let _59_526 = (deserialize_binders reader)
in (let _59_525 = (deserialize_knd reader)
in (_59_527, _59_526, _59_525)))))

let serialize_monad_abbrev = (fun writer ast -> (let _29_744 = (serialize_lident writer ast.FStar_Absyn_Syntax.mabbrev)
in (let _29_746 = (serialize_binders writer ast.FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun reader -> (let _59_536 = (deserialize_lident reader)
in (let _59_535 = (deserialize_binders reader)
in (let _59_534 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mabbrev = _59_536; FStar_Absyn_Syntax.parms = _59_535; FStar_Absyn_Syntax.def = _59_534}))))

let serialize_sub_effect = (fun writer ast -> (let _29_751 = (serialize_lident writer ast.FStar_Absyn_Syntax.source)
in (let _29_753 = (serialize_lident writer ast.FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun reader -> (let _59_545 = (deserialize_lident reader)
in (let _59_544 = (deserialize_lident reader)
in (let _59_543 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.source = _59_545; FStar_Absyn_Syntax.target = _59_544; FStar_Absyn_Syntax.lift = _59_543}))))

let rec serialize_new_effect = (fun writer ast -> (let _29_758 = (serialize_lident writer ast.FStar_Absyn_Syntax.mname)
in (let _29_760 = (serialize_list writer serialize_binder ast.FStar_Absyn_Syntax.binders)
in (let _29_762 = (serialize_list writer serialize_qualifier ast.FStar_Absyn_Syntax.qualifiers)
in (let _29_764 = (serialize_knd writer ast.FStar_Absyn_Syntax.signature)
in (let _29_766 = (serialize_typ writer ast.FStar_Absyn_Syntax.ret)
in (let _29_768 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wp)
in (let _29_770 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wlp)
in (let _29_772 = (serialize_typ writer ast.FStar_Absyn_Syntax.if_then_else)
in (let _29_774 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wp)
in (let _29_776 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wlp)
in (let _29_778 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_binop)
in (let _29_780 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_as_type)
in (let _29_782 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp)
in (let _29_784 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp_t)
in (let _29_786 = (serialize_typ writer ast.FStar_Absyn_Syntax.assert_p)
in (let _29_788 = (serialize_typ writer ast.FStar_Absyn_Syntax.assume_p)
in (let _29_790 = (serialize_typ writer ast.FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Sig_pragma (_29_795) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Absyn_Syntax.Sig_tycon (lid, bs, k, l1, l2, qs, _29_804) -> begin
(let _29_807 = (writer.FStar_Util.write_char 'a')
in (let _29_809 = (serialize_lident writer lid)
in (let _29_811 = (serialize_binders writer bs)
in (let _29_813 = (serialize_knd writer k)
in (let _29_815 = (serialize_list writer serialize_lident l1)
in (let _29_817 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, bs, k, t, qs, _29_825) -> begin
(let _29_828 = (writer.FStar_Util.write_char 'b')
in (let _29_830 = (serialize_lident writer lid)
in (let _29_832 = (serialize_binders writer bs)
in (let _29_834 = (serialize_knd writer k)
in (let _29_836 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid1, t, tyc, qs, mutuals, _29_844) -> begin
(let t' = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(let _59_555 = (let _59_554 = (FStar_Absyn_Syntax.mk_Total (FStar_Absyn_Util.comp_result c))
in (f, _59_554))
in (FStar_Absyn_Syntax.mk_Typ_fun _59_555 None FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _29_853 = (writer.FStar_Util.write_char 'c')
in (let _29_855 = (serialize_lident writer lid1)
in (let _29_857 = (serialize_typ writer t')
in (let _29_859 = (serialize_tycon writer tyc)
in (let _29_861 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, qs, _29_867) -> begin
(let _29_870 = (writer.FStar_Util.write_char 'd')
in (let _29_872 = (serialize_lident writer lid)
in (let _29_874 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, fml, qs, _29_880) -> begin
(let _29_883 = (writer.FStar_Util.write_char 'e')
in (let _29_885 = (serialize_lident writer lid)
in (let _29_887 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _29_891, l, quals) -> begin
(let _29_896 = (writer.FStar_Util.write_char 'f')
in (let _29_898 = (serialize_letbindings writer lbs)
in (let _29_900 = (serialize_list writer serialize_lident l)
in (let _59_557 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _29_1 -> (match (_29_1) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _29_905 -> begin
false
end))))
in (writer.FStar_Util.write_bool _59_557)))))
end
| FStar_Absyn_Syntax.Sig_main (e, _29_908) -> begin
(let _29_911 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end
| FStar_Absyn_Syntax.Sig_bundle (l, qs, lids, _29_917) -> begin
(let _29_920 = (writer.FStar_Util.write_char 'h')
in (let _29_922 = (serialize_list writer serialize_sigelt l)
in (let _29_924 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _29_928) -> begin
(let _29_931 = (writer.FStar_Util.write_char 'i')
in (serialize_new_effect writer n))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, bs, c, qs, _29_938) -> begin
(let _29_941 = (writer.FStar_Util.write_char 'j')
in (let _29_943 = (serialize_lident writer lid)
in (let _29_945 = (serialize_binders writer bs)
in (let _29_947 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (se, r) -> begin
(let _29_953 = (writer.FStar_Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _29_959) -> begin
(let _29_962 = (writer.FStar_Util.write_char 'l')
in (let _29_964 = (serialize_lident writer l)
in (let _29_966 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun reader -> (let _59_578 = (deserialize_lident reader)
in (let _59_577 = (deserialize_list reader deserialize_binder)
in (let _59_576 = (deserialize_list reader deserialize_qualifier)
in (let _59_575 = (deserialize_knd reader)
in (let _59_574 = (deserialize_typ reader)
in (let _59_573 = (deserialize_typ reader)
in (let _59_572 = (deserialize_typ reader)
in (let _59_571 = (deserialize_typ reader)
in (let _59_570 = (deserialize_typ reader)
in (let _59_569 = (deserialize_typ reader)
in (let _59_568 = (deserialize_typ reader)
in (let _59_567 = (deserialize_typ reader)
in (let _59_566 = (deserialize_typ reader)
in (let _59_565 = (deserialize_typ reader)
in (let _59_564 = (deserialize_typ reader)
in (let _59_563 = (deserialize_typ reader)
in (let _59_562 = (deserialize_typ reader)
in (let _59_561 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mname = _59_578; FStar_Absyn_Syntax.binders = _59_577; FStar_Absyn_Syntax.qualifiers = _59_576; FStar_Absyn_Syntax.signature = _59_575; FStar_Absyn_Syntax.ret = _59_574; FStar_Absyn_Syntax.bind_wp = _59_573; FStar_Absyn_Syntax.bind_wlp = _59_572; FStar_Absyn_Syntax.if_then_else = _59_571; FStar_Absyn_Syntax.ite_wp = _59_570; FStar_Absyn_Syntax.ite_wlp = _59_569; FStar_Absyn_Syntax.wp_binop = _59_568; FStar_Absyn_Syntax.wp_as_type = _59_567; FStar_Absyn_Syntax.close_wp = _59_566; FStar_Absyn_Syntax.close_wp_t = _59_565; FStar_Absyn_Syntax.assert_p = _59_564; FStar_Absyn_Syntax.assume_p = _59_563; FStar_Absyn_Syntax.null_wp = _59_562; FStar_Absyn_Syntax.trivial = _59_561})))))))))))))))))))
and deserialize_sigelt = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _59_586 = (let _59_585 = (deserialize_lident reader)
in (let _59_584 = (deserialize_binders reader)
in (let _59_583 = (deserialize_knd reader)
in (let _59_582 = (deserialize_list reader deserialize_lident)
in (let _59_581 = (deserialize_list reader deserialize_lident)
in (let _59_580 = (deserialize_list reader deserialize_qualifier)
in (_59_585, _59_584, _59_583, _59_582, _59_581, _59_580, FStar_Absyn_Syntax.dummyRange)))))))
in FStar_Absyn_Syntax.Sig_tycon (_59_586))
end
| 'b' -> begin
(let _59_592 = (let _59_591 = (deserialize_lident reader)
in (let _59_590 = (deserialize_binders reader)
in (let _59_589 = (deserialize_knd reader)
in (let _59_588 = (deserialize_typ reader)
in (let _59_587 = (deserialize_list reader deserialize_qualifier)
in (_59_591, _59_590, _59_589, _59_588, _59_587, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_59_592))
end
| 'c' -> begin
(let _59_598 = (let _59_597 = (deserialize_lident reader)
in (let _59_596 = (deserialize_typ reader)
in (let _59_595 = (deserialize_tycon reader)
in (let _59_594 = (deserialize_list reader deserialize_qualifier)
in (let _59_593 = (deserialize_list reader deserialize_lident)
in (_59_597, _59_596, _59_595, _59_594, _59_593, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_datacon (_59_598))
end
| 'd' -> begin
(let _59_602 = (let _59_601 = (deserialize_lident reader)
in (let _59_600 = (deserialize_typ reader)
in (let _59_599 = (deserialize_list reader deserialize_qualifier)
in (_59_601, _59_600, _59_599, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_val_decl (_59_602))
end
| 'e' -> begin
(let _59_606 = (let _59_605 = (deserialize_lident reader)
in (let _59_604 = (deserialize_formula reader)
in (let _59_603 = (deserialize_list reader deserialize_qualifier)
in (_59_605, _59_604, _59_603, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_assume (_59_606))
end
| 'f' -> begin
(let _59_610 = (let _59_609 = (deserialize_letbindings reader)
in (let _59_608 = (deserialize_list reader deserialize_lident)
in (let _59_607 = if (reader.FStar_Util.read_bool ()) then begin
(FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end
in (_59_609, FStar_Absyn_Syntax.dummyRange, _59_608, _59_607))))
in FStar_Absyn_Syntax.Sig_let (_59_610))
end
| 'g' -> begin
(let _59_612 = (let _59_611 = (deserialize_exp reader)
in (_59_611, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_main (_59_612))
end
| 'h' -> begin
(let _59_616 = (let _59_615 = (deserialize_list reader deserialize_sigelt)
in (let _59_614 = (deserialize_list reader deserialize_qualifier)
in (let _59_613 = (deserialize_list reader deserialize_lident)
in (_59_615, _59_614, _59_613, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_bundle (_59_616))
end
| 'i' -> begin
(let _59_618 = (let _59_617 = (deserialize_new_effect reader)
in (_59_617, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_new_effect (_59_618))
end
| ('j') | ('k') | ('l') -> begin
(FStar_All.failwith "TODO")
end
| _29_983 -> begin
(parse_error ())
end))

let serialize_sigelts = (fun writer ast -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun reader -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun writer ast -> (let _29_989 = (serialize_lident writer ast.FStar_Absyn_Syntax.name)
in (let _29_991 = (serialize_sigelts writer [])
in (let _29_993 = (serialize_sigelts writer ast.FStar_Absyn_Syntax.exports)
in (writer.FStar_Util.write_bool ast.FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun reader -> (let m = (let _59_634 = (deserialize_lident reader)
in (let _59_633 = (deserialize_sigelts reader)
in (let _59_632 = (deserialize_sigelts reader)
in (let _59_631 = (reader.FStar_Util.read_bool ())
in {FStar_Absyn_Syntax.name = _59_634; FStar_Absyn_Syntax.declarations = _59_633; FStar_Absyn_Syntax.exports = _59_632; FStar_Absyn_Syntax.is_interface = _59_631; FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _29_997 = m
in {FStar_Absyn_Syntax.name = _29_997.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = m.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.exports = _29_997.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _29_997.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _29_997.FStar_Absyn_Syntax.is_deserialized})))




