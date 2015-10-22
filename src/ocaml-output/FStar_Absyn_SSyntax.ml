
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
in (serialize_list writer serialize_arg l)))
end
| FStar_Absyn_Syntax.Meta_named (t, lid) -> begin
(let _28_260 = (writer.FStar_Util.write_char 'b')
in (let _28_262 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| FStar_Absyn_Syntax.Meta_labeled (t, s, _28_267, b) -> begin
(let _28_271 = (writer.FStar_Util.write_char 'c')
in (let _28_273 = (serialize_typ writer t)
in (let _28_275 = (writer.FStar_Util.write_string s)
in (writer.FStar_Util.write_bool b))))
end
| _28_278 -> begin
(Prims.raise (Err ("unimplemented meta_t")))
end))
and serialize_arg = (fun writer ast -> (let _28_281 = (serialize_either writer serialize_typ serialize_exp (Prims.fst ast))
in (let _94_255 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _94_255))))
and serialize_args = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder = (fun writer ast -> (let _28_287 = (serialize_either writer serialize_btvar serialize_bvvar (Prims.fst ast))
in (let _94_260 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _94_260))))
and serialize_binders = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ = (fun writer ast -> (let _94_265 = (FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _94_265)))
and serialize_comp_typ = (fun writer ast -> (let _28_295 = (serialize_lident writer ast.FStar_Absyn_Syntax.effect_name)
in (let _28_297 = (serialize_typ writer ast.FStar_Absyn_Syntax.result_typ)
in (let _28_299 = (serialize_args writer ast.FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.FStar_Absyn_Syntax.flags)))))
and serialize_comp' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _28_305 = (writer.FStar_Util.write_char 'a')
in (serialize_typ writer t))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let _28_309 = (writer.FStar_Util.write_char 'b')
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
(let _28_323 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _28_329 = (writer.FStar_Util.write_char 'a')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Exp_fvar (v, b) -> begin
(let _28_335 = (writer.FStar_Util.write_char 'b')
in (let _28_337 = (serialize_fvvar writer v)
in (writer.FStar_Util.write_bool false)))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _28_341 = (writer.FStar_Util.write_char 'c')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _28_347 = (writer.FStar_Util.write_char 'd')
in (let _28_349 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_app (e, ars) -> begin
(let _28_355 = (writer.FStar_Util.write_char 'e')
in (let _28_357 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| FStar_Absyn_Syntax.Exp_match (e, l) -> begin
(let g = (fun writer eopt -> (match (eopt) with
| Some (e1) -> begin
(let _28_368 = (writer.FStar_Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.FStar_Util.write_char 'b')
end))
in (let f = (fun writer _28_376 -> (match (_28_376) with
| (p, eopt, e) -> begin
(let _28_377 = (serialize_pat writer p)
in (let _28_379 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _28_381 = (writer.FStar_Util.write_char 'f')
in (let _28_383 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let _28_390 = (writer.FStar_Util.write_char 'g')
in (let _28_392 = (serialize_exp writer e)
in (let _28_394 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _28_400 = (writer.FStar_Util.write_char 'h')
in (let _28_402 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _28_406 = (writer.FStar_Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _28_409 -> begin
(Prims.raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_desugared (e, s) -> begin
(let _28_416 = (writer.FStar_Util.write_char 'a')
in (let _28_418 = (serialize_exp writer e)
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
and serialize_exp = (fun writer ast -> (let _94_290 = (FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _94_290)))
and serialize_btvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_bvvdef = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_pat' = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _28_437 = (writer.FStar_Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _28_441 = (writer.FStar_Util.write_char 'b')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Pat_cons (v, _28_445, l) -> begin
(let _28_449 = (writer.FStar_Util.write_char 'c')
in (let _28_451 = (serialize_fvvar writer v)
in (serialize_list writer (fun w _28_456 -> (match (_28_456) with
| (p, b) -> begin
(let _28_457 = (serialize_pat w p)
in (w.FStar_Util.write_bool b))
end)) l)))
end
| FStar_Absyn_Syntax.Pat_var (v) -> begin
(let _28_461 = (writer.FStar_Util.write_char 'd')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _28_465 = (writer.FStar_Util.write_char 'e')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _28_469 = (writer.FStar_Util.write_char 'f')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _28_473 = (writer.FStar_Util.write_char 'g')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_dot_term (v, e) -> begin
(let _28_479 = (writer.FStar_Util.write_char 'h')
in (let _28_481 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (v, t) -> begin
(let _28_487 = (writer.FStar_Util.write_char 'i')
in (let _28_489 = (serialize_btvar writer v)
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
(let _28_503 = (writer.FStar_Util.write_char 'c')
in (let _28_505 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _28_511 = (writer.FStar_Util.write_char 'd')
in (let _28_513 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_lam (bs, k) -> begin
(let _28_519 = (writer.FStar_Util.write_char 'e')
in (let _28_521 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.FStar_Util.write_char 'f')
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:1")))
end
| FStar_Absyn_Syntax.Kind_delayed (_28_529, _28_531, _28_533) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd = (fun writer ast -> (let _94_307 = (FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _94_307)))
and serialize_kabbrev = (fun writer ast -> (let _28_540 = (serialize_lident writer (Prims.fst ast))
in (serialize_args writer (Prims.snd ast))))
and serialize_lbname = (fun writer ast -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings = (fun writer ast -> (let f = (fun writer lb -> (let _28_549 = (serialize_lbname writer lb.FStar_Absyn_Syntax.lbname)
in (let _28_551 = (serialize_lident writer lb.FStar_Absyn_Syntax.lbeff)
in (let _28_553 = (serialize_typ writer lb.FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.FStar_Absyn_Syntax.lbdef)))))
in (let _28_555 = (writer.FStar_Util.write_bool (Prims.fst ast))
in (serialize_list writer f (Prims.snd ast)))))
and serialize_fvar = (fun writer ast -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar = (fun writer ast -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar = (fun writer ast -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar = (fun writer ast -> (serialize_var writer serialize_knd ast))
and serialize_fvvar = (fun writer ast -> (serialize_var writer serialize_typ ast))

let rec deserialize_typ' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_358 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Typ_btvar (_94_358))
end
| 'b' -> begin
(let _94_359 = (deserialize_ftvar reader)
in FStar_Absyn_Syntax.Typ_const (_94_359))
end
| 'c' -> begin
(let _94_362 = (let _94_361 = (deserialize_binders reader)
in (let _94_360 = (deserialize_comp reader)
in (_94_361, _94_360)))
in FStar_Absyn_Syntax.Typ_fun (_94_362))
end
| 'd' -> begin
(let _94_365 = (let _94_364 = (deserialize_bvvar reader)
in (let _94_363 = (deserialize_typ reader)
in (_94_364, _94_363)))
in FStar_Absyn_Syntax.Typ_refine (_94_365))
end
| 'e' -> begin
(let _94_368 = (let _94_367 = (deserialize_typ reader)
in (let _94_366 = (deserialize_args reader)
in (_94_367, _94_366)))
in FStar_Absyn_Syntax.Typ_app (_94_368))
end
| 'f' -> begin
(let _94_371 = (let _94_370 = (deserialize_binders reader)
in (let _94_369 = (deserialize_typ reader)
in (_94_370, _94_369)))
in FStar_Absyn_Syntax.Typ_lam (_94_371))
end
| 'g' -> begin
(let _94_374 = (let _94_373 = (deserialize_typ reader)
in (let _94_372 = (deserialize_knd reader)
in (_94_373, _94_372)))
in FStar_Absyn_Syntax.Typ_ascribed (_94_374))
end
| 'h' -> begin
(let _94_375 = (deserialize_meta_t reader)
in FStar_Absyn_Syntax.Typ_meta (_94_375))
end
| 'i' -> begin
FStar_Absyn_Syntax.Typ_unknown
end
| _28_578 -> begin
(parse_error ())
end))
and deserialize_meta_t = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_379 = (let _94_378 = (deserialize_typ reader)
in (let _94_377 = (deserialize_list reader deserialize_arg)
in (_94_378, _94_377)))
in FStar_Absyn_Syntax.Meta_pattern (_94_379))
end
| 'b' -> begin
(let _94_382 = (let _94_381 = (deserialize_typ reader)
in (let _94_380 = (deserialize_lident reader)
in (_94_381, _94_380)))
in FStar_Absyn_Syntax.Meta_named (_94_382))
end
| 'c' -> begin
(let _94_386 = (let _94_385 = (deserialize_typ reader)
in (let _94_384 = (reader.FStar_Util.read_string ())
in (let _94_383 = (reader.FStar_Util.read_bool ())
in (_94_385, _94_384, FStar_Absyn_Syntax.dummyRange, _94_383))))
in FStar_Absyn_Syntax.Meta_labeled (_94_386))
end
| _28_584 -> begin
(parse_error ())
end))
and deserialize_arg = (fun reader -> (let _94_390 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _94_389 = (let _94_388 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _94_388))
in (_94_390, _94_389))))
and deserialize_args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder = (fun reader -> (let _94_395 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _94_394 = (let _94_393 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _94_393))
in (_94_395, _94_394))))
and deserialize_binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ = (fun reader -> (deserialize_syntax reader deserialize_typ' FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ = (fun reader -> (let _94_402 = (deserialize_lident reader)
in (let _94_401 = (deserialize_typ reader)
in (let _94_400 = (deserialize_args reader)
in (let _94_399 = (deserialize_list reader deserialize_cflags)
in {FStar_Absyn_Syntax.effect_name = _94_402; FStar_Absyn_Syntax.result_typ = _94_401; FStar_Absyn_Syntax.effect_args = _94_400; FStar_Absyn_Syntax.flags = _94_399})))))
and deserialize_comp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_404 = (deserialize_typ reader)
in FStar_Absyn_Syntax.Total (_94_404))
end
| 'b' -> begin
(let _94_405 = (deserialize_comp_typ reader)
in FStar_Absyn_Syntax.Comp (_94_405))
end
| _28_595 -> begin
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
(let _94_408 = (deserialize_exp reader)
in FStar_Absyn_Syntax.DECREASES (_94_408))
end
| _28_606 -> begin
(parse_error ())
end))
and deserialize_exp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_410 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Exp_bvar (_94_410))
end
| 'b' -> begin
(let _94_414 = (let _94_413 = (deserialize_fvvar reader)
in (let _94_412 = (let _28_610 = (let _94_411 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left Prims.ignore _94_411))
in None)
in (_94_413, _94_412)))
in FStar_Absyn_Syntax.Exp_fvar (_94_414))
end
| 'c' -> begin
(let _94_415 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Exp_constant (_94_415))
end
| 'd' -> begin
(let _94_418 = (let _94_417 = (deserialize_binders reader)
in (let _94_416 = (deserialize_exp reader)
in (_94_417, _94_416)))
in FStar_Absyn_Syntax.Exp_abs (_94_418))
end
| 'e' -> begin
(let _94_421 = (let _94_420 = (deserialize_exp reader)
in (let _94_419 = (deserialize_args reader)
in (_94_420, _94_419)))
in FStar_Absyn_Syntax.Exp_app (_94_421))
end
| 'f' -> begin
(let g = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_424 = (deserialize_exp reader)
in Some (_94_424))
end
| 'b' -> begin
None
end
| _28_621 -> begin
(parse_error ())
end))
in (let f = (fun reader -> (let _94_429 = (deserialize_pat reader)
in (let _94_428 = (g reader)
in (let _94_427 = (deserialize_exp reader)
in (_94_429, _94_428, _94_427)))))
in (let _94_432 = (let _94_431 = (deserialize_exp reader)
in (let _94_430 = (deserialize_list reader f)
in (_94_431, _94_430)))
in FStar_Absyn_Syntax.Exp_match (_94_432))))
end
| 'g' -> begin
(let _94_436 = (let _94_435 = (deserialize_exp reader)
in (let _94_434 = (deserialize_typ reader)
in (let _94_433 = (deserialize_option reader deserialize_lident)
in (_94_435, _94_434, _94_433))))
in FStar_Absyn_Syntax.Exp_ascribed (_94_436))
end
| 'h' -> begin
(let _94_439 = (let _94_438 = (deserialize_letbindings reader)
in (let _94_437 = (deserialize_exp reader)
in (_94_438, _94_437)))
in FStar_Absyn_Syntax.Exp_let (_94_439))
end
| 'i' -> begin
(let _94_440 = (deserialize_meta_e reader)
in FStar_Absyn_Syntax.Exp_meta (_94_440))
end
| _28_628 -> begin
(parse_error ())
end))
and deserialize_meta_e = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_444 = (let _94_443 = (deserialize_exp reader)
in (let _94_442 = (deserialize_meta_source_info reader)
in (_94_443, _94_442)))
in FStar_Absyn_Syntax.Meta_desugared (_94_444))
end
| _28_632 -> begin
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
| _28_639 -> begin
(parse_error ())
end))
and deserialize_exp = (fun reader -> (deserialize_syntax reader deserialize_exp' FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_bvvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_pat' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_450 = (deserialize_list reader deserialize_pat)
in FStar_Absyn_Syntax.Pat_disj (_94_450))
end
| 'b' -> begin
(let _94_451 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Pat_constant (_94_451))
end
| 'c' -> begin
(let _94_457 = (let _94_456 = (deserialize_fvvar reader)
in (let _94_455 = (deserialize_list reader (fun r -> (let _94_454 = (deserialize_pat r)
in (let _94_453 = (r.FStar_Util.read_bool ())
in (_94_454, _94_453)))))
in (_94_456, None, _94_455)))
in FStar_Absyn_Syntax.Pat_cons (_94_457))
end
| 'd' -> begin
(let _94_458 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_var (_94_458))
end
| 'e' -> begin
(let _94_459 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_tvar (_94_459))
end
| 'f' -> begin
(let _94_460 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_wild (_94_460))
end
| 'g' -> begin
(let _94_461 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_twild (_94_461))
end
| 'h' -> begin
(let _94_464 = (let _94_463 = (deserialize_bvvar reader)
in (let _94_462 = (deserialize_exp reader)
in (_94_463, _94_462)))
in FStar_Absyn_Syntax.Pat_dot_term (_94_464))
end
| 'i' -> begin
(let _94_467 = (let _94_466 = (deserialize_btvar reader)
in (let _94_465 = (deserialize_typ reader)
in (_94_466, _94_465)))
in FStar_Absyn_Syntax.Pat_dot_typ (_94_467))
end
| _28_655 -> begin
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
(let _94_473 = (let _94_472 = (deserialize_kabbrev reader)
in (let _94_471 = (deserialize_knd reader)
in (_94_472, _94_471)))
in FStar_Absyn_Syntax.Kind_abbrev (_94_473))
end
| 'd' -> begin
(let _94_476 = (let _94_475 = (deserialize_binders reader)
in (let _94_474 = (deserialize_knd reader)
in (_94_475, _94_474)))
in FStar_Absyn_Syntax.Kind_arrow (_94_476))
end
| 'e' -> begin
(let _94_479 = (let _94_478 = (deserialize_binders reader)
in (let _94_477 = (deserialize_knd reader)
in (_94_478, _94_477)))
in FStar_Absyn_Syntax.Kind_lam (_94_479))
end
| 'f' -> begin
FStar_Absyn_Syntax.Kind_unknown
end
| _28_666 -> begin
(parse_error ())
end))
and deserialize_knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev = (fun reader -> (let _94_483 = (deserialize_lident reader)
in (let _94_482 = (deserialize_args reader)
in (_94_483, _94_482))))
and deserialize_lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings = (fun reader -> (let f = (fun reader -> (let _94_491 = (deserialize_lbname reader)
in (let _94_490 = (deserialize_typ reader)
in (let _94_489 = (deserialize_lident reader)
in (let _94_488 = (deserialize_exp reader)
in {FStar_Absyn_Syntax.lbname = _94_491; FStar_Absyn_Syntax.lbtyp = _94_490; FStar_Absyn_Syntax.lbeff = _94_489; FStar_Absyn_Syntax.lbdef = _94_488})))))
in (let _94_493 = (reader.FStar_Util.read_bool ())
in (let _94_492 = (deserialize_list reader f)
in (_94_493, _94_492)))))
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
(let _28_686 = (writer.FStar_Util.write_char 'i')
in (serialize_lident writer lid))
end
| FStar_Absyn_Syntax.Projector (lid, v) -> begin
(let _28_692 = (writer.FStar_Util.write_char 'j')
in (let _28_694 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| FStar_Absyn_Syntax.RecordType (l) -> begin
(let _28_698 = (writer.FStar_Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _28_702 = (writer.FStar_Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.FStar_Util.write_char 'm')
end
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.FStar_Util.write_char 'o')
end
| FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _28_708 = (writer.FStar_Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| FStar_Absyn_Syntax.TotalEffect -> begin
(writer.FStar_Util.write_char 'q')
end
| _28_712 -> begin
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
(let _94_508 = (deserialize_lident reader)
in FStar_Absyn_Syntax.Discriminator (_94_508))
end
| 'j' -> begin
(let _94_511 = (let _94_510 = (deserialize_lident reader)
in (let _94_509 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_94_510, _94_509)))
in FStar_Absyn_Syntax.Projector (_94_511))
end
| 'k' -> begin
(let _94_512 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordType (_94_512))
end
| 'l' -> begin
(let _94_513 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordConstructor (_94_513))
end
| 'm' -> begin
FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _94_515 = (deserialize_option reader deserialize_lident)
in (FStar_All.pipe_right _94_515 (fun _94_514 -> FStar_Absyn_Syntax.DefaultEffect (_94_514))))
end
| 'q' -> begin
FStar_Absyn_Syntax.TotalEffect
end
| _28_727 -> begin
(parse_error ())
end))

let serialize_tycon = (fun writer _28_732 -> (match (_28_732) with
| (lid, bs, k) -> begin
(let _28_733 = (serialize_lident writer lid)
in (let _28_735 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

let deserialize_tycon = (fun reader -> (let _94_524 = (deserialize_lident reader)
in (let _94_523 = (deserialize_binders reader)
in (let _94_522 = (deserialize_knd reader)
in (_94_524, _94_523, _94_522)))))

let serialize_monad_abbrev = (fun writer ast -> (let _28_740 = (serialize_lident writer ast.FStar_Absyn_Syntax.mabbrev)
in (let _28_742 = (serialize_binders writer ast.FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.FStar_Absyn_Syntax.def))))

let deserialize_monad_abbrev = (fun reader -> (let _94_533 = (deserialize_lident reader)
in (let _94_532 = (deserialize_binders reader)
in (let _94_531 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mabbrev = _94_533; FStar_Absyn_Syntax.parms = _94_532; FStar_Absyn_Syntax.def = _94_531}))))

let serialize_sub_effect = (fun writer ast -> (let _28_747 = (serialize_lident writer ast.FStar_Absyn_Syntax.source)
in (let _28_749 = (serialize_lident writer ast.FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.FStar_Absyn_Syntax.lift))))

let deserialize_sub_effect = (fun reader -> (let _94_542 = (deserialize_lident reader)
in (let _94_541 = (deserialize_lident reader)
in (let _94_540 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.source = _94_542; FStar_Absyn_Syntax.target = _94_541; FStar_Absyn_Syntax.lift = _94_540}))))

let rec serialize_new_effect = (fun writer ast -> (let _28_754 = (serialize_lident writer ast.FStar_Absyn_Syntax.mname)
in (let _28_756 = (serialize_list writer serialize_binder ast.FStar_Absyn_Syntax.binders)
in (let _28_758 = (serialize_list writer serialize_qualifier ast.FStar_Absyn_Syntax.qualifiers)
in (let _28_760 = (serialize_knd writer ast.FStar_Absyn_Syntax.signature)
in (let _28_762 = (serialize_typ writer ast.FStar_Absyn_Syntax.ret)
in (let _28_764 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wp)
in (let _28_766 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wlp)
in (let _28_768 = (serialize_typ writer ast.FStar_Absyn_Syntax.if_then_else)
in (let _28_770 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wp)
in (let _28_772 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wlp)
in (let _28_774 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_binop)
in (let _28_776 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_as_type)
in (let _28_778 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp)
in (let _28_780 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp_t)
in (let _28_782 = (serialize_typ writer ast.FStar_Absyn_Syntax.assert_p)
in (let _28_784 = (serialize_typ writer ast.FStar_Absyn_Syntax.assume_p)
in (let _28_786 = (serialize_typ writer ast.FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Sig_pragma (_28_791) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Absyn_Syntax.Sig_tycon (lid, bs, k, l1, l2, qs, _28_800) -> begin
(let _28_803 = (writer.FStar_Util.write_char 'a')
in (let _28_805 = (serialize_lident writer lid)
in (let _28_807 = (serialize_binders writer bs)
in (let _28_809 = (serialize_knd writer k)
in (let _28_811 = (serialize_list writer serialize_lident l1)
in (let _28_813 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, bs, k, t, qs, _28_821) -> begin
(let _28_824 = (writer.FStar_Util.write_char 'b')
in (let _28_826 = (serialize_lident writer lid)
in (let _28_828 = (serialize_binders writer bs)
in (let _28_830 = (serialize_knd writer k)
in (let _28_832 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid1, t, tyc, qs, mutuals, _28_840) -> begin
(let t' = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(let _94_552 = (let _94_551 = (FStar_Absyn_Syntax.mk_Total (FStar_Absyn_Util.comp_result c))
in (f, _94_551))
in (FStar_Absyn_Syntax.mk_Typ_fun _94_552 None FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _28_849 = (writer.FStar_Util.write_char 'c')
in (let _28_851 = (serialize_lident writer lid1)
in (let _28_853 = (serialize_typ writer t')
in (let _28_855 = (serialize_tycon writer tyc)
in (let _28_857 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, qs, _28_863) -> begin
(let _28_866 = (writer.FStar_Util.write_char 'd')
in (let _28_868 = (serialize_lident writer lid)
in (let _28_870 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, fml, qs, _28_876) -> begin
(let _28_879 = (writer.FStar_Util.write_char 'e')
in (let _28_881 = (serialize_lident writer lid)
in (let _28_883 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _28_887, l, quals) -> begin
(let _28_892 = (writer.FStar_Util.write_char 'f')
in (let _28_894 = (serialize_letbindings writer lbs)
in (let _28_896 = (serialize_list writer serialize_lident l)
in (let _94_554 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _28_1 -> (match (_28_1) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _28_901 -> begin
false
end))))
in (writer.FStar_Util.write_bool _94_554)))))
end
| FStar_Absyn_Syntax.Sig_main (e, _28_904) -> begin
(let _28_907 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end
| FStar_Absyn_Syntax.Sig_bundle (l, qs, lids, _28_913) -> begin
(let _28_916 = (writer.FStar_Util.write_char 'h')
in (let _28_918 = (serialize_list writer serialize_sigelt l)
in (let _28_920 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _28_924) -> begin
(let _28_927 = (writer.FStar_Util.write_char 'i')
in (serialize_new_effect writer n))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, bs, c, qs, _28_934) -> begin
(let _28_937 = (writer.FStar_Util.write_char 'j')
in (let _28_939 = (serialize_lident writer lid)
in (let _28_941 = (serialize_binders writer bs)
in (let _28_943 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (se, r) -> begin
(let _28_949 = (writer.FStar_Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _28_955) -> begin
(let _28_958 = (writer.FStar_Util.write_char 'l')
in (let _28_960 = (serialize_lident writer l)
in (let _28_962 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

let rec deserialize_new_effect = (fun reader -> (let _94_575 = (deserialize_lident reader)
in (let _94_574 = (deserialize_list reader deserialize_binder)
in (let _94_573 = (deserialize_list reader deserialize_qualifier)
in (let _94_572 = (deserialize_knd reader)
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
in (let _94_560 = (deserialize_typ reader)
in (let _94_559 = (deserialize_typ reader)
in (let _94_558 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mname = _94_575; FStar_Absyn_Syntax.binders = _94_574; FStar_Absyn_Syntax.qualifiers = _94_573; FStar_Absyn_Syntax.signature = _94_572; FStar_Absyn_Syntax.ret = _94_571; FStar_Absyn_Syntax.bind_wp = _94_570; FStar_Absyn_Syntax.bind_wlp = _94_569; FStar_Absyn_Syntax.if_then_else = _94_568; FStar_Absyn_Syntax.ite_wp = _94_567; FStar_Absyn_Syntax.ite_wlp = _94_566; FStar_Absyn_Syntax.wp_binop = _94_565; FStar_Absyn_Syntax.wp_as_type = _94_564; FStar_Absyn_Syntax.close_wp = _94_563; FStar_Absyn_Syntax.close_wp_t = _94_562; FStar_Absyn_Syntax.assert_p = _94_561; FStar_Absyn_Syntax.assume_p = _94_560; FStar_Absyn_Syntax.null_wp = _94_559; FStar_Absyn_Syntax.trivial = _94_558})))))))))))))))))))
and deserialize_sigelt = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _94_583 = (let _94_582 = (deserialize_lident reader)
in (let _94_581 = (deserialize_binders reader)
in (let _94_580 = (deserialize_knd reader)
in (let _94_579 = (deserialize_list reader deserialize_lident)
in (let _94_578 = (deserialize_list reader deserialize_lident)
in (let _94_577 = (deserialize_list reader deserialize_qualifier)
in (_94_582, _94_581, _94_580, _94_579, _94_578, _94_577, FStar_Absyn_Syntax.dummyRange)))))))
in FStar_Absyn_Syntax.Sig_tycon (_94_583))
end
| 'b' -> begin
(let _94_589 = (let _94_588 = (deserialize_lident reader)
in (let _94_587 = (deserialize_binders reader)
in (let _94_586 = (deserialize_knd reader)
in (let _94_585 = (deserialize_typ reader)
in (let _94_584 = (deserialize_list reader deserialize_qualifier)
in (_94_588, _94_587, _94_586, _94_585, _94_584, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_94_589))
end
| 'c' -> begin
(let _94_595 = (let _94_594 = (deserialize_lident reader)
in (let _94_593 = (deserialize_typ reader)
in (let _94_592 = (deserialize_tycon reader)
in (let _94_591 = (deserialize_list reader deserialize_qualifier)
in (let _94_590 = (deserialize_list reader deserialize_lident)
in (_94_594, _94_593, _94_592, _94_591, _94_590, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_datacon (_94_595))
end
| 'd' -> begin
(let _94_599 = (let _94_598 = (deserialize_lident reader)
in (let _94_597 = (deserialize_typ reader)
in (let _94_596 = (deserialize_list reader deserialize_qualifier)
in (_94_598, _94_597, _94_596, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_val_decl (_94_599))
end
| 'e' -> begin
(let _94_603 = (let _94_602 = (deserialize_lident reader)
in (let _94_601 = (deserialize_formula reader)
in (let _94_600 = (deserialize_list reader deserialize_qualifier)
in (_94_602, _94_601, _94_600, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_assume (_94_603))
end
| 'f' -> begin
(let _94_607 = (let _94_606 = (deserialize_letbindings reader)
in (let _94_605 = (deserialize_list reader deserialize_lident)
in (let _94_604 = if (reader.FStar_Util.read_bool ()) then begin
(FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end
in (_94_606, FStar_Absyn_Syntax.dummyRange, _94_605, _94_604))))
in FStar_Absyn_Syntax.Sig_let (_94_607))
end
| 'g' -> begin
(let _94_609 = (let _94_608 = (deserialize_exp reader)
in (_94_608, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_main (_94_609))
end
| 'h' -> begin
(let _94_613 = (let _94_612 = (deserialize_list reader deserialize_sigelt)
in (let _94_611 = (deserialize_list reader deserialize_qualifier)
in (let _94_610 = (deserialize_list reader deserialize_lident)
in (_94_612, _94_611, _94_610, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_bundle (_94_613))
end
| 'i' -> begin
(let _94_615 = (let _94_614 = (deserialize_new_effect reader)
in (_94_614, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_new_effect (_94_615))
end
| ('j') | ('k') | ('l') -> begin
(FStar_All.failwith "TODO")
end
| _28_979 -> begin
(parse_error ())
end))

let serialize_sigelts = (fun writer ast -> (serialize_list writer serialize_sigelt ast))

let deserialize_sigelts = (fun reader -> (deserialize_list reader deserialize_sigelt))

let serialize_modul = (fun writer ast -> (let _28_985 = (serialize_lident writer ast.FStar_Absyn_Syntax.name)
in (let _28_987 = (serialize_sigelts writer [])
in (let _28_989 = (serialize_sigelts writer ast.FStar_Absyn_Syntax.exports)
in (writer.FStar_Util.write_bool ast.FStar_Absyn_Syntax.is_interface)))))

let deserialize_modul = (fun reader -> (let m = (let _94_631 = (deserialize_lident reader)
in (let _94_630 = (deserialize_sigelts reader)
in (let _94_629 = (deserialize_sigelts reader)
in (let _94_628 = (reader.FStar_Util.read_bool ())
in {FStar_Absyn_Syntax.name = _94_631; FStar_Absyn_Syntax.declarations = _94_630; FStar_Absyn_Syntax.exports = _94_629; FStar_Absyn_Syntax.is_interface = _94_628; FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _28_993 = m
in {FStar_Absyn_Syntax.name = _28_993.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = m.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.exports = _28_993.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _28_993.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _28_993.FStar_Absyn_Syntax.is_deserialized})))




