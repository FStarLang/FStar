
open Prims
# 11 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

exception Err of (Prims.string)

# 11 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 11 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_30_3) -> begin
_30_3
end))

# 13 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let parse_error = (fun _30_4 -> (match (()) with
| () -> begin
(FStar_All.failwith "Parse error: ill-formed cache")
end))

# 15 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

type l__Writer =
FStar_Util.oWriter

# 17 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

type l__Reader =
FStar_Util.oReader

# 19 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_option = (fun writer f l -> (match (l) with
| None -> begin
(writer.FStar_Util.write_char 'n')
end
| Some (l) -> begin
(let _30_12 = (writer.FStar_Util.write_char 's')
in (f writer l))
end))

# 24 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_option = (fun reader f -> (let n = (reader.FStar_Util.read_char ())
in if (n = 'n') then begin
None
end else begin
(let _132_21 = (f reader)
in Some (_132_21))
end))

# 29 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_list = (fun writer f l -> (let _30_22 = (writer.FStar_Util.write_int (FStar_List.length l))
in (FStar_List.iter (fun elt -> (f writer elt)) (FStar_List.rev_append l []))))

# 33 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_list = (fun reader f -> (let n = (reader.FStar_Util.read_int ())
in (let rec helper = (fun accum n -> if (n = 0) then begin
accum
end else begin
(let _132_42 = (let _132_41 = (f reader)
in (_132_41)::accum)
in (helper _132_42 (n - 1)))
end)
in (helper [] n))))

# 42 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_ident : l__Writer  ->  FStar_Ident.ident  ->  Prims.unit = (fun writer ast -> (writer.FStar_Util.write_string ast.FStar_Ident.idText))

# 43 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_ident : l__Reader  ->  FStar_Ident.ident = (fun reader -> (let _132_50 = (let _132_49 = (reader.FStar_Util.read_string ())
in (_132_49, FStar_Absyn_Syntax.dummyRange))
in (FStar_Ident.mk_ident _132_50)))

# 45 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_LongIdent : l__Writer  ->  FStar_Absyn_Syntax.l__LongIdent  ->  Prims.unit = (fun writer ast -> (let _30_37 = (serialize_list writer serialize_ident ast.FStar_Ident.ns)
in (serialize_ident writer ast.FStar_Ident.ident)))

# 49 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_LongIdent : l__Reader  ->  FStar_Ident.lident = (fun reader -> (let _132_60 = (let _132_59 = (deserialize_list reader deserialize_ident)
in (let _132_58 = (let _132_57 = (deserialize_ident reader)
in (_132_57)::[])
in (FStar_List.append _132_59 _132_58)))
in (FStar_Ident.lid_of_ids _132_60)))

# 52 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_lident : l__Writer  ->  FStar_Absyn_Syntax.l__LongIdent  ->  Prims.unit = serialize_LongIdent

# 53 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_lident : l__Reader  ->  FStar_Ident.lident = deserialize_LongIdent

# 55 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_withinfo_t = (fun writer s_v s_sort ast -> (let _30_46 = (s_v writer ast.FStar_Absyn_Syntax.v)
in (s_sort writer ast.FStar_Absyn_Syntax.sort)))

# 59 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_withinfo_t = (fun reader ds_v ds_sort -> (let _132_90 = (ds_v reader)
in (let _132_89 = (ds_sort reader)
in {FStar_Absyn_Syntax.v = _132_90; FStar_Absyn_Syntax.sort = _132_89; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange})))

# 64 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_var = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_lident s_sort ast))

# 67 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_var = (fun reader ds_sort -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

# 70 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_bvdef = (fun writer ast -> (let _30_63 = (serialize_ident writer ast.FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.FStar_Absyn_Syntax.realname)))

# 78 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_bvdef = (fun ghost reader -> (let _132_110 = (deserialize_ident reader)
in (let _132_109 = (deserialize_ident reader)
in {FStar_Absyn_Syntax.ppname = _132_110; FStar_Absyn_Syntax.realname = _132_109})))

# 82 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_bvar = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

# 85 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_bvar = (fun ghost reader ds_sort -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

# 88 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_sconst : l__Writer  ->  FStar_Const.sconst  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Const.Const_effect -> begin
(writer.FStar_Util.write_char '_')
end
| FStar_Const.Const_unit -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Const.Const_uint8 (v) -> begin
(let _30_84 = (writer.FStar_Util.write_char 'b')
in (writer.FStar_Util.write_byte v))
end
| FStar_Const.Const_bool (v) -> begin
(let _30_88 = (writer.FStar_Util.write_char 'c')
in (writer.FStar_Util.write_bool v))
end
| FStar_Const.Const_int32 (v) -> begin
(let _30_92 = (writer.FStar_Util.write_char 'd')
in (writer.FStar_Util.write_int32 v))
end
| FStar_Const.Const_int64 (v) -> begin
(let _30_96 = (writer.FStar_Util.write_char 'e')
in (writer.FStar_Util.write_int64 v))
end
| FStar_Const.Const_char (v) -> begin
(let _30_100 = (writer.FStar_Util.write_char 'f')
in (writer.FStar_Util.write_char v))
end
| FStar_Const.Const_float (v) -> begin
(let _30_104 = (writer.FStar_Util.write_char 'g')
in (writer.FStar_Util.write_double v))
end
| FStar_Const.Const_bytearray (v, _30_108) -> begin
(let _30_111 = (writer.FStar_Util.write_char 'h')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Const.Const_string (v, _30_115) -> begin
(let _30_118 = (writer.FStar_Util.write_char 'i')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Const.Const_int (v) -> begin
(let _30_122 = (writer.FStar_Util.write_char 'j')
in (writer.FStar_Util.write_string v))
end))

# 102 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_sconst : l__Reader  ->  FStar_Const.sconst = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| '_' -> begin
FStar_Const.Const_effect
end
| 'a' -> begin
FStar_Const.Const_unit
end
| 'b' -> begin
(let _132_132 = (reader.FStar_Util.read_byte ())
in FStar_Const.Const_uint8 (_132_132))
end
| 'c' -> begin
(let _132_133 = (reader.FStar_Util.read_bool ())
in FStar_Const.Const_bool (_132_133))
end
| 'd' -> begin
(let _132_134 = (reader.FStar_Util.read_int32 ())
in FStar_Const.Const_int32 (_132_134))
end
| 'e' -> begin
(let _132_135 = (reader.FStar_Util.read_int64 ())
in FStar_Const.Const_int64 (_132_135))
end
| 'f' -> begin
(let _132_136 = (reader.FStar_Util.read_char ())
in FStar_Const.Const_char (_132_136))
end
| 'g' -> begin
(let _132_137 = (reader.FStar_Util.read_double ())
in FStar_Const.Const_float (_132_137))
end
| 'h' -> begin
(let _132_139 = (let _132_138 = (reader.FStar_Util.read_bytearray ())
in (_132_138, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_bytearray (_132_139))
end
| 'i' -> begin
(let _132_141 = (let _132_140 = (reader.FStar_Util.read_bytearray ())
in (_132_140, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_132_141))
end
| 'j' -> begin
(let _132_142 = (reader.FStar_Util.read_string ())
in FStar_Const.Const_int (_132_142))
end
| _30_137 -> begin
(parse_error ())
end))

# 117 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_either = (fun writer s_l s_r ast -> (match (ast) with
| FStar_Util.Inl (v) -> begin
(let _30_146 = (writer.FStar_Util.write_char 'a')
in (s_l writer v))
end
| FStar_Util.Inr (v) -> begin
(let _30_150 = (writer.FStar_Util.write_char 'b')
in (s_r writer v))
end))

# 122 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_either = (fun reader ds_l ds_r -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_168 = (ds_l reader)
in FStar_Util.Inl (_132_168))
end
| 'b' -> begin
(let _132_169 = (ds_r reader)
in FStar_Util.Inr (_132_169))
end
| _30_160 -> begin
(parse_error ())
end))

# 128 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_syntax = (fun writer s_a ast -> (s_a writer ast.FStar_Absyn_Syntax.n))

# 130 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_syntax = (fun reader ds_a ds_b -> (let _132_188 = (ds_a reader)
in (let _132_187 = (FStar_Util.mk_ref None)
in (let _132_186 = (FStar_Util.mk_ref None)
in (let _132_185 = (FStar_Util.mk_ref None)
in {FStar_Absyn_Syntax.n = _132_188; FStar_Absyn_Syntax.tk = _132_187; FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange; FStar_Absyn_Syntax.fvs = _132_186; FStar_Absyn_Syntax.uvs = _132_185})))))

# 137 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let rec serialize_typ' : l__Writer  ->  FStar_Absyn_Syntax.typ'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(let _30_175 = (writer.FStar_Util.write_char 'a')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(let _30_179 = (writer.FStar_Util.write_char 'b')
in (serialize_ftvar writer v))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _30_185 = (writer.FStar_Util.write_char 'c')
in (let _30_187 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| FStar_Absyn_Syntax.Typ_refine (v, t) -> begin
(let _30_193 = (writer.FStar_Util.write_char 'd')
in (let _30_195 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_app (t, ars) -> begin
(let _30_201 = (writer.FStar_Util.write_char 'e')
in (let _30_203 = (serialize_typ writer t)
in (let _30_205 = (serialize_args writer ars)
in if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (_30_208, _30_210) -> begin
(FStar_Util.print_string "type application node with lam\n")
end
| _30_214 -> begin
()
end)
end else begin
()
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _30_219 = (writer.FStar_Util.write_char 'f')
in (let _30_221 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _30_227 = (writer.FStar_Util.write_char 'g')
in (let _30_229 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Typ_meta (m) -> begin
(let _30_233 = (writer.FStar_Util.write_char 'h')
in (serialize_meta_t writer m))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(writer.FStar_Util.write_char 'i')
end
| FStar_Absyn_Syntax.Typ_uvar (_30_237, _30_239) -> begin
(Prims.raise (Err ("typ not impl:1")))
end
| FStar_Absyn_Syntax.Typ_delayed (_30_243, _30_245) -> begin
(Prims.raise (Err ("typ not impl:2")))
end))
and serialize_meta_t : l__Writer  ->  FStar_Absyn_Syntax.meta_t  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_pattern (t, l) -> begin
(let _30_254 = (writer.FStar_Util.write_char 'a')
in (let _30_256 = (serialize_typ writer t)
in (serialize_list writer (fun w -> (serialize_list w serialize_arg)) l)))
end
| FStar_Absyn_Syntax.Meta_named (t, lid) -> begin
(let _30_263 = (writer.FStar_Util.write_char 'b')
in (let _30_265 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| FStar_Absyn_Syntax.Meta_labeled (t, s, _30_270, b) -> begin
(let _30_274 = (writer.FStar_Util.write_char 'c')
in (let _30_276 = (serialize_typ writer t)
in (let _30_278 = (writer.FStar_Util.write_string s)
in (writer.FStar_Util.write_bool b))))
end
| _30_281 -> begin
(Prims.raise (Err ("unimplemented meta_t")))
end))
and serialize_arg : l__Writer  ->  FStar_Absyn_Syntax.arg  ->  Prims.unit = (fun writer ast -> (let _30_284 = (serialize_either writer serialize_typ serialize_exp (Prims.fst ast))
in (let _132_257 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _132_257))))
and serialize_args : l__Writer  ->  FStar_Absyn_Syntax.args  ->  Prims.unit = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder : l__Writer  ->  FStar_Absyn_Syntax.binder  ->  Prims.unit = (fun writer ast -> (let _30_290 = (serialize_either writer serialize_btvar serialize_bvvar (Prims.fst ast))
in (let _132_262 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _132_262))))
and serialize_binders : l__Writer  ->  FStar_Absyn_Syntax.binders  ->  Prims.unit = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ : l__Writer  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun writer ast -> (let _132_267 = (FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _132_267)))
and serialize_comp_typ : l__Writer  ->  FStar_Absyn_Syntax.comp_typ  ->  Prims.unit = (fun writer ast -> (let _30_298 = (serialize_lident writer ast.FStar_Absyn_Syntax.effect_name)
in (let _30_300 = (serialize_typ writer ast.FStar_Absyn_Syntax.result_typ)
in (let _30_302 = (serialize_args writer ast.FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.FStar_Absyn_Syntax.flags)))))
and serialize_comp' : l__Writer  ->  FStar_Absyn_Syntax.comp'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _30_308 = (writer.FStar_Util.write_char 'a')
in (serialize_typ writer t))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let _30_312 = (writer.FStar_Util.write_char 'b')
in (serialize_comp_typ writer c))
end))
and serialize_comp : l__Writer  ->  FStar_Absyn_Syntax.comp  ->  Prims.unit = (fun writer ast -> (serialize_syntax writer serialize_comp' ast))
and serialize_cflags : l__Writer  ->  FStar_Absyn_Syntax.cflags  ->  Prims.unit = (fun writer ast -> (match (ast) with
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
(let _30_326 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' : l__Writer  ->  FStar_Absyn_Syntax.exp'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(let _30_332 = (writer.FStar_Util.write_char 'a')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Exp_fvar (v, b) -> begin
(let _30_338 = (writer.FStar_Util.write_char 'b')
in (let _30_340 = (serialize_fvvar writer v)
in (writer.FStar_Util.write_bool false)))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _30_344 = (writer.FStar_Util.write_char 'c')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _30_350 = (writer.FStar_Util.write_char 'd')
in (let _30_352 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_app (e, ars) -> begin
(let _30_358 = (writer.FStar_Util.write_char 'e')
in (let _30_360 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| FStar_Absyn_Syntax.Exp_match (e, l) -> begin
(let g = (fun writer eopt -> (match (eopt) with
| Some (e1) -> begin
(let _30_371 = (writer.FStar_Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.FStar_Util.write_char 'b')
end))
in (let f = (fun writer _30_379 -> (match (_30_379) with
| (p, eopt, e) -> begin
(let _30_380 = (serialize_pat writer p)
in (let _30_382 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (let _30_384 = (writer.FStar_Util.write_char 'f')
in (let _30_386 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let _30_393 = (writer.FStar_Util.write_char 'g')
in (let _30_395 = (serialize_exp writer e)
in (let _30_397 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(let _30_403 = (writer.FStar_Util.write_char 'h')
in (let _30_405 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_meta (m) -> begin
(let _30_409 = (writer.FStar_Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _30_412 -> begin
(Prims.raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e : l__Writer  ->  FStar_Absyn_Syntax.meta_e  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_desugared (e, s) -> begin
(let _30_419 = (writer.FStar_Util.write_char 'a')
in (let _30_421 = (serialize_exp writer e)
in (serialize_meta_source_info writer s)))
end))
and serialize_meta_source_info : l__Writer  ->  FStar_Absyn_Syntax.meta_source_info  ->  Prims.unit = (fun writer ast -> (match (ast) with
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
and serialize_exp : l__Writer  ->  FStar_Absyn_Syntax.exp  ->  Prims.unit = (fun writer ast -> (let _132_292 = (FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _132_292)))
and serialize_btvdef : l__Writer  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.unit = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_bvvdef : l__Writer  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.unit = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_pat' : l__Writer  ->  FStar_Absyn_Syntax.pat'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Pat_disj (l) -> begin
(let _30_440 = (writer.FStar_Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _30_444 = (writer.FStar_Util.write_char 'b')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Pat_cons (v, _30_448, l) -> begin
(let _30_452 = (writer.FStar_Util.write_char 'c')
in (let _30_454 = (serialize_fvvar writer v)
in (serialize_list writer (fun w _30_459 -> (match (_30_459) with
| (p, b) -> begin
(let _30_460 = (serialize_pat w p)
in (w.FStar_Util.write_bool b))
end)) l)))
end
| FStar_Absyn_Syntax.Pat_var (v) -> begin
(let _30_464 = (writer.FStar_Util.write_char 'd')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(let _30_468 = (writer.FStar_Util.write_char 'e')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_wild (v) -> begin
(let _30_472 = (writer.FStar_Util.write_char 'f')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_twild (v) -> begin
(let _30_476 = (writer.FStar_Util.write_char 'g')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_dot_term (v, e) -> begin
(let _30_482 = (writer.FStar_Util.write_char 'h')
in (let _30_484 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (v, t) -> begin
(let _30_490 = (writer.FStar_Util.write_char 'i')
in (let _30_492 = (serialize_btvar writer v)
in (serialize_typ writer t)))
end))
and serialize_pat : l__Writer  ->  FStar_Absyn_Syntax.pat  ->  Prims.unit = (fun writer ast -> (serialize_withinfo_t writer serialize_pat' (fun w kt -> ()) ast))
and serialize_knd' : l__Writer  ->  FStar_Absyn_Syntax.knd'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Kind_type -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Absyn_Syntax.Kind_effect -> begin
(writer.FStar_Util.write_char 'b')
end
| FStar_Absyn_Syntax.Kind_abbrev (ka, k) -> begin
(let _30_506 = (writer.FStar_Util.write_char 'c')
in (let _30_508 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _30_514 = (writer.FStar_Util.write_char 'd')
in (let _30_516 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_lam (bs, k) -> begin
(let _30_522 = (writer.FStar_Util.write_char 'e')
in (let _30_524 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(writer.FStar_Util.write_char 'f')
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:1")))
end
| FStar_Absyn_Syntax.Kind_delayed (_30_532, _30_534, _30_536) -> begin
(Prims.raise (Err ("knd\' serialization unimplemented:2")))
end))
and serialize_knd : l__Writer  ->  FStar_Absyn_Syntax.knd  ->  Prims.unit = (fun writer ast -> (let _132_309 = (FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _132_309)))
and serialize_kabbrev : l__Writer  ->  FStar_Absyn_Syntax.kabbrev  ->  Prims.unit = (fun writer ast -> (let _30_543 = (serialize_lident writer (Prims.fst ast))
in (serialize_args writer (Prims.snd ast))))
and serialize_lbname : l__Writer  ->  FStar_Absyn_Syntax.lbname  ->  Prims.unit = (fun writer ast -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings : l__Writer  ->  FStar_Absyn_Syntax.letbindings  ->  Prims.unit = (fun writer ast -> (let f = (fun writer lb -> (let _30_552 = (serialize_lbname writer lb.FStar_Absyn_Syntax.lbname)
in (let _30_554 = (serialize_lident writer lb.FStar_Absyn_Syntax.lbeff)
in (let _30_556 = (serialize_typ writer lb.FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.FStar_Absyn_Syntax.lbdef)))))
in (let _30_558 = (writer.FStar_Util.write_bool (Prims.fst ast))
in (serialize_list writer f (Prims.snd ast)))))
and serialize_fvar : l__Writer  ->  FStar_Absyn_Syntax.fvar  ->  Prims.unit = (fun writer ast -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar : l__Writer  ->  FStar_Absyn_Syntax.btvar  ->  Prims.unit = (fun writer ast -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar : l__Writer  ->  FStar_Absyn_Syntax.bvvar  ->  Prims.unit = (fun writer ast -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar : l__Writer  ->  FStar_Absyn_Syntax.ftvar  ->  Prims.unit = (fun writer ast -> (serialize_var writer serialize_knd ast))
and serialize_fvvar : l__Writer  ->  FStar_Absyn_Syntax.fvvar  ->  Prims.unit = (fun writer ast -> (serialize_var writer serialize_typ ast))

# 282 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let rec deserialize_typ' : l__Reader  ->  FStar_Absyn_Syntax.typ' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_360 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Typ_btvar (_132_360))
end
| 'b' -> begin
(let _132_361 = (deserialize_ftvar reader)
in FStar_Absyn_Syntax.Typ_const (_132_361))
end
| 'c' -> begin
(let _132_364 = (let _132_363 = (deserialize_binders reader)
in (let _132_362 = (deserialize_comp reader)
in (_132_363, _132_362)))
in FStar_Absyn_Syntax.Typ_fun (_132_364))
end
| 'd' -> begin
(let _132_367 = (let _132_366 = (deserialize_bvvar reader)
in (let _132_365 = (deserialize_typ reader)
in (_132_366, _132_365)))
in FStar_Absyn_Syntax.Typ_refine (_132_367))
end
| 'e' -> begin
(let _132_370 = (let _132_369 = (deserialize_typ reader)
in (let _132_368 = (deserialize_args reader)
in (_132_369, _132_368)))
in FStar_Absyn_Syntax.Typ_app (_132_370))
end
| 'f' -> begin
(let _132_373 = (let _132_372 = (deserialize_binders reader)
in (let _132_371 = (deserialize_typ reader)
in (_132_372, _132_371)))
in FStar_Absyn_Syntax.Typ_lam (_132_373))
end
| 'g' -> begin
(let _132_376 = (let _132_375 = (deserialize_typ reader)
in (let _132_374 = (deserialize_knd reader)
in (_132_375, _132_374)))
in FStar_Absyn_Syntax.Typ_ascribed (_132_376))
end
| 'h' -> begin
(let _132_377 = (deserialize_meta_t reader)
in FStar_Absyn_Syntax.Typ_meta (_132_377))
end
| 'i' -> begin
FStar_Absyn_Syntax.Typ_unknown
end
| _30_581 -> begin
(parse_error ())
end))
and deserialize_meta_t : l__Reader  ->  FStar_Absyn_Syntax.meta_t = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_382 = (let _132_381 = (deserialize_typ reader)
in (let _132_380 = (deserialize_list reader (fun r -> (deserialize_list r deserialize_arg)))
in (_132_381, _132_380)))
in FStar_Absyn_Syntax.Meta_pattern (_132_382))
end
| 'b' -> begin
(let _132_385 = (let _132_384 = (deserialize_typ reader)
in (let _132_383 = (deserialize_lident reader)
in (_132_384, _132_383)))
in FStar_Absyn_Syntax.Meta_named (_132_385))
end
| 'c' -> begin
(let _132_389 = (let _132_388 = (deserialize_typ reader)
in (let _132_387 = (reader.FStar_Util.read_string ())
in (let _132_386 = (reader.FStar_Util.read_bool ())
in (_132_388, _132_387, FStar_Absyn_Syntax.dummyRange, _132_386))))
in FStar_Absyn_Syntax.Meta_labeled (_132_389))
end
| _30_588 -> begin
(parse_error ())
end))
and deserialize_arg : l__Reader  ->  FStar_Absyn_Syntax.arg = (fun reader -> (let _132_393 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _132_392 = (let _132_391 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _132_391))
in (_132_393, _132_392))))
and deserialize_args : l__Reader  ->  FStar_Absyn_Syntax.args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder : l__Reader  ->  FStar_Absyn_Syntax.binder = (fun reader -> (let _132_398 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _132_397 = (let _132_396 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _132_396))
in (_132_398, _132_397))))
and deserialize_binders : l__Reader  ->  FStar_Absyn_Syntax.binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ : l__Reader  ->  FStar_Absyn_Syntax.typ = (fun reader -> (deserialize_syntax reader deserialize_typ' FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ : l__Reader  ->  FStar_Absyn_Syntax.comp_typ = (fun reader -> (let _132_405 = (deserialize_lident reader)
in (let _132_404 = (deserialize_typ reader)
in (let _132_403 = (deserialize_args reader)
in (let _132_402 = (deserialize_list reader deserialize_cflags)
in {FStar_Absyn_Syntax.effect_name = _132_405; FStar_Absyn_Syntax.result_typ = _132_404; FStar_Absyn_Syntax.effect_args = _132_403; FStar_Absyn_Syntax.flags = _132_402})))))
and deserialize_comp' : l__Reader  ->  FStar_Absyn_Syntax.comp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_407 = (deserialize_typ reader)
in FStar_Absyn_Syntax.Total (_132_407))
end
| 'b' -> begin
(let _132_408 = (deserialize_comp_typ reader)
in FStar_Absyn_Syntax.Comp (_132_408))
end
| _30_599 -> begin
(parse_error ())
end))
and deserialize_comp : l__Reader  ->  FStar_Absyn_Syntax.comp = (fun reader -> (deserialize_syntax reader deserialize_comp' ()))
and deserialize_cflags : l__Reader  ->  FStar_Absyn_Syntax.cflags = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
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
(let _132_411 = (deserialize_exp reader)
in FStar_Absyn_Syntax.DECREASES (_132_411))
end
| _30_610 -> begin
(parse_error ())
end))
and deserialize_exp' : l__Reader  ->  FStar_Absyn_Syntax.exp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_413 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Exp_bvar (_132_413))
end
| 'b' -> begin
(let _132_417 = (let _132_416 = (deserialize_fvvar reader)
in (let _132_415 = (let _30_614 = (let _132_414 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left Prims.ignore _132_414))
in None)
in (_132_416, _132_415)))
in FStar_Absyn_Syntax.Exp_fvar (_132_417))
end
| 'c' -> begin
(let _132_418 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Exp_constant (_132_418))
end
| 'd' -> begin
(let _132_421 = (let _132_420 = (deserialize_binders reader)
in (let _132_419 = (deserialize_exp reader)
in (_132_420, _132_419)))
in FStar_Absyn_Syntax.Exp_abs (_132_421))
end
| 'e' -> begin
(let _132_424 = (let _132_423 = (deserialize_exp reader)
in (let _132_422 = (deserialize_args reader)
in (_132_423, _132_422)))
in FStar_Absyn_Syntax.Exp_app (_132_424))
end
| 'f' -> begin
(let g = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_427 = (deserialize_exp reader)
in Some (_132_427))
end
| 'b' -> begin
None
end
| _30_625 -> begin
(parse_error ())
end))
in (let f = (fun reader -> (let _132_432 = (deserialize_pat reader)
in (let _132_431 = (g reader)
in (let _132_430 = (deserialize_exp reader)
in (_132_432, _132_431, _132_430)))))
in (let _132_435 = (let _132_434 = (deserialize_exp reader)
in (let _132_433 = (deserialize_list reader f)
in (_132_434, _132_433)))
in FStar_Absyn_Syntax.Exp_match (_132_435))))
end
| 'g' -> begin
(let _132_439 = (let _132_438 = (deserialize_exp reader)
in (let _132_437 = (deserialize_typ reader)
in (let _132_436 = (deserialize_option reader deserialize_lident)
in (_132_438, _132_437, _132_436))))
in FStar_Absyn_Syntax.Exp_ascribed (_132_439))
end
| 'h' -> begin
(let _132_442 = (let _132_441 = (deserialize_letbindings reader)
in (let _132_440 = (deserialize_exp reader)
in (_132_441, _132_440)))
in FStar_Absyn_Syntax.Exp_let (_132_442))
end
| 'i' -> begin
(let _132_443 = (deserialize_meta_e reader)
in FStar_Absyn_Syntax.Exp_meta (_132_443))
end
| _30_632 -> begin
(parse_error ())
end))
and deserialize_meta_e : l__Reader  ->  FStar_Absyn_Syntax.meta_e = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_447 = (let _132_446 = (deserialize_exp reader)
in (let _132_445 = (deserialize_meta_source_info reader)
in (_132_446, _132_445)))
in FStar_Absyn_Syntax.Meta_desugared (_132_447))
end
| _30_636 -> begin
(parse_error ())
end))
and deserialize_meta_source_info : l__Reader  ->  FStar_Absyn_Syntax.meta_source_info = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
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
| _30_643 -> begin
(parse_error ())
end))
and deserialize_exp : l__Reader  ->  FStar_Absyn_Syntax.exp = (fun reader -> (deserialize_syntax reader deserialize_exp' FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef : l__Reader  ->  FStar_Absyn_Syntax.btvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_bvvdef : l__Reader  ->  FStar_Absyn_Syntax.bvvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_pat' : l__Reader  ->  FStar_Absyn_Syntax.pat' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_453 = (deserialize_list reader deserialize_pat)
in FStar_Absyn_Syntax.Pat_disj (_132_453))
end
| 'b' -> begin
(let _132_454 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Pat_constant (_132_454))
end
| 'c' -> begin
(let _132_460 = (let _132_459 = (deserialize_fvvar reader)
in (let _132_458 = (deserialize_list reader (fun r -> (let _132_457 = (deserialize_pat r)
in (let _132_456 = (r.FStar_Util.read_bool ())
in (_132_457, _132_456)))))
in (_132_459, None, _132_458)))
in FStar_Absyn_Syntax.Pat_cons (_132_460))
end
| 'd' -> begin
(let _132_461 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_var (_132_461))
end
| 'e' -> begin
(let _132_462 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_tvar (_132_462))
end
| 'f' -> begin
(let _132_463 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_wild (_132_463))
end
| 'g' -> begin
(let _132_464 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_twild (_132_464))
end
| 'h' -> begin
(let _132_467 = (let _132_466 = (deserialize_bvvar reader)
in (let _132_465 = (deserialize_exp reader)
in (_132_466, _132_465)))
in FStar_Absyn_Syntax.Pat_dot_term (_132_467))
end
| 'i' -> begin
(let _132_470 = (let _132_469 = (deserialize_btvar reader)
in (let _132_468 = (deserialize_typ reader)
in (_132_469, _132_468)))
in FStar_Absyn_Syntax.Pat_dot_typ (_132_470))
end
| _30_659 -> begin
(parse_error ())
end))
and deserialize_pat : l__Reader  ->  FStar_Absyn_Syntax.pat = (fun reader -> (deserialize_withinfo_t reader deserialize_pat' (fun r -> None)))
and deserialize_knd' : l__Reader  ->  FStar_Absyn_Syntax.knd' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
FStar_Absyn_Syntax.Kind_type
end
| 'b' -> begin
FStar_Absyn_Syntax.Kind_effect
end
| 'c' -> begin
(let _132_476 = (let _132_475 = (deserialize_kabbrev reader)
in (let _132_474 = (deserialize_knd reader)
in (_132_475, _132_474)))
in FStar_Absyn_Syntax.Kind_abbrev (_132_476))
end
| 'd' -> begin
(let _132_479 = (let _132_478 = (deserialize_binders reader)
in (let _132_477 = (deserialize_knd reader)
in (_132_478, _132_477)))
in FStar_Absyn_Syntax.Kind_arrow (_132_479))
end
| 'e' -> begin
(let _132_482 = (let _132_481 = (deserialize_binders reader)
in (let _132_480 = (deserialize_knd reader)
in (_132_481, _132_480)))
in FStar_Absyn_Syntax.Kind_lam (_132_482))
end
| 'f' -> begin
FStar_Absyn_Syntax.Kind_unknown
end
| _30_670 -> begin
(parse_error ())
end))
and deserialize_knd : l__Reader  ->  FStar_Absyn_Syntax.knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev : l__Reader  ->  FStar_Absyn_Syntax.kabbrev = (fun reader -> (let _132_486 = (deserialize_lident reader)
in (let _132_485 = (deserialize_args reader)
in (_132_486, _132_485))))
and deserialize_lbname : l__Reader  ->  FStar_Absyn_Syntax.lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings : l__Reader  ->  FStar_Absyn_Syntax.letbindings = (fun reader -> (let f = (fun reader -> (let _132_494 = (deserialize_lbname reader)
in (let _132_493 = (deserialize_typ reader)
in (let _132_492 = (deserialize_lident reader)
in (let _132_491 = (deserialize_exp reader)
in {FStar_Absyn_Syntax.lbname = _132_494; FStar_Absyn_Syntax.lbtyp = _132_493; FStar_Absyn_Syntax.lbeff = _132_492; FStar_Absyn_Syntax.lbdef = _132_491})))))
in (let _132_496 = (reader.FStar_Util.read_bool ())
in (let _132_495 = (deserialize_list reader f)
in (_132_496, _132_495)))))
and deserialize_fvar : l__Reader  ->  FStar_Absyn_Syntax.fvar = (fun reader -> (deserialize_either reader deserialize_btvdef deserialize_bvvdef))
and deserialize_btvar : l__Reader  ->  FStar_Absyn_Syntax.btvar = (fun reader -> (deserialize_bvar None reader deserialize_knd))
and deserialize_bvvar : l__Reader  ->  FStar_Absyn_Syntax.bvvar = (fun reader -> (deserialize_bvar None reader deserialize_typ))
and deserialize_ftvar : l__Reader  ->  FStar_Absyn_Syntax.ftvar = (fun reader -> (deserialize_var reader deserialize_knd))
and deserialize_fvvar : l__Reader  ->  FStar_Absyn_Syntax.fvvar = (fun reader -> (deserialize_var reader deserialize_typ))

# 427 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_formula : l__Writer  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = serialize_typ

# 428 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_formula : l__Reader  ->  FStar_Absyn_Syntax.typ = deserialize_typ

# 430 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_qualifier : l__Writer  ->  FStar_Absyn_Syntax.qualifier  ->  Prims.unit = (fun writer ast -> (match (ast) with
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
(let _30_690 = (writer.FStar_Util.write_char 'i')
in (serialize_lident writer lid))
end
| FStar_Absyn_Syntax.Projector (lid, v) -> begin
(let _30_696 = (writer.FStar_Util.write_char 'j')
in (let _30_698 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| FStar_Absyn_Syntax.RecordType (l) -> begin
(let _30_702 = (writer.FStar_Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(let _30_706 = (writer.FStar_Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.FStar_Util.write_char 'm')
end
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.FStar_Util.write_char 'o')
end
| FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(let _30_712 = (writer.FStar_Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| FStar_Absyn_Syntax.TotalEffect -> begin
(writer.FStar_Util.write_char 'q')
end
| _30_716 -> begin
(FStar_All.failwith "Unexpected qualifier")
end))

# 446 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_qualifier : l__Reader  ->  FStar_Absyn_Syntax.qualifier = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
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
(let _132_511 = (deserialize_lident reader)
in FStar_Absyn_Syntax.Discriminator (_132_511))
end
| 'j' -> begin
(let _132_514 = (let _132_513 = (deserialize_lident reader)
in (let _132_512 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_132_513, _132_512)))
in FStar_Absyn_Syntax.Projector (_132_514))
end
| 'k' -> begin
(let _132_515 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordType (_132_515))
end
| 'l' -> begin
(let _132_516 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordConstructor (_132_516))
end
| 'm' -> begin
FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _132_518 = (deserialize_option reader deserialize_lident)
in (FStar_All.pipe_right _132_518 (fun _132_517 -> FStar_Absyn_Syntax.DefaultEffect (_132_517))))
end
| 'q' -> begin
FStar_Absyn_Syntax.TotalEffect
end
| _30_731 -> begin
(parse_error ())
end))

# 462 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_tycon : l__Writer  ->  FStar_Absyn_Syntax.tycon  ->  Prims.unit = (fun writer _30_736 -> (match (_30_736) with
| (lid, bs, k) -> begin
(let _30_737 = (serialize_lident writer lid)
in (let _30_739 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

# 463 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_tycon : l__Reader  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun reader -> (let _132_527 = (deserialize_lident reader)
in (let _132_526 = (deserialize_binders reader)
in (let _132_525 = (deserialize_knd reader)
in (_132_527, _132_526, _132_525)))))

# 465 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_monad_abbrev : l__Writer  ->  FStar_Absyn_Syntax.monad_abbrev  ->  Prims.unit = (fun writer ast -> (let _30_744 = (serialize_lident writer ast.FStar_Absyn_Syntax.mabbrev)
in (let _30_746 = (serialize_binders writer ast.FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.FStar_Absyn_Syntax.def))))

# 470 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_monad_abbrev : l__Reader  ->  FStar_Absyn_Syntax.monad_abbrev = (fun reader -> (let _132_536 = (deserialize_lident reader)
in (let _132_535 = (deserialize_binders reader)
in (let _132_534 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mabbrev = _132_536; FStar_Absyn_Syntax.parms = _132_535; FStar_Absyn_Syntax.def = _132_534}))))

# 475 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_sub_effect : l__Writer  ->  FStar_Absyn_Syntax.sub_eff  ->  Prims.unit = (fun writer ast -> (let _30_751 = (serialize_lident writer ast.FStar_Absyn_Syntax.source)
in (let _30_753 = (serialize_lident writer ast.FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.FStar_Absyn_Syntax.lift))))

# 480 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_sub_effect : l__Reader  ->  FStar_Absyn_Syntax.sub_eff = (fun reader -> (let _132_545 = (deserialize_lident reader)
in (let _132_544 = (deserialize_lident reader)
in (let _132_543 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.source = _132_545; FStar_Absyn_Syntax.target = _132_544; FStar_Absyn_Syntax.lift = _132_543}))))

# 485 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let rec serialize_new_effect : l__Writer  ->  FStar_Absyn_Syntax.eff_decl  ->  Prims.unit = (fun writer ast -> (let _30_758 = (serialize_lident writer ast.FStar_Absyn_Syntax.mname)
in (let _30_760 = (serialize_list writer serialize_binder ast.FStar_Absyn_Syntax.binders)
in (let _30_762 = (serialize_list writer serialize_qualifier ast.FStar_Absyn_Syntax.qualifiers)
in (let _30_764 = (serialize_knd writer ast.FStar_Absyn_Syntax.signature)
in (let _30_766 = (serialize_typ writer ast.FStar_Absyn_Syntax.ret)
in (let _30_768 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wp)
in (let _30_770 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wlp)
in (let _30_772 = (serialize_typ writer ast.FStar_Absyn_Syntax.if_then_else)
in (let _30_774 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wp)
in (let _30_776 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wlp)
in (let _30_778 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_binop)
in (let _30_780 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_as_type)
in (let _30_782 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp)
in (let _30_784 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp_t)
in (let _30_786 = (serialize_typ writer ast.FStar_Absyn_Syntax.assert_p)
in (let _30_788 = (serialize_typ writer ast.FStar_Absyn_Syntax.assume_p)
in (let _30_790 = (serialize_typ writer ast.FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt : l__Writer  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Sig_pragma (_30_795) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Absyn_Syntax.Sig_tycon (lid, bs, k, l1, l2, qs, _30_804) -> begin
(let _30_807 = (writer.FStar_Util.write_char 'a')
in (let _30_809 = (serialize_lident writer lid)
in (let _30_811 = (serialize_binders writer bs)
in (let _30_813 = (serialize_knd writer k)
in (let _30_815 = (serialize_list writer serialize_lident l1)
in (let _30_817 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, bs, k, t, qs, _30_825) -> begin
(let _30_828 = (writer.FStar_Util.write_char 'b')
in (let _30_830 = (serialize_lident writer lid)
in (let _30_832 = (serialize_binders writer bs)
in (let _30_834 = (serialize_knd writer k)
in (let _30_836 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid1, t, tyc, qs, mutuals, _30_844) -> begin
(let t' = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(let _132_555 = (let _132_554 = (FStar_Absyn_Syntax.mk_Total (FStar_Absyn_Util.comp_result c))
in (f, _132_554))
in (FStar_Absyn_Syntax.mk_Typ_fun _132_555 None FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (let _30_853 = (writer.FStar_Util.write_char 'c')
in (let _30_855 = (serialize_lident writer lid1)
in (let _30_857 = (serialize_typ writer t')
in (let _30_859 = (serialize_tycon writer tyc)
in (let _30_861 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, qs, _30_867) -> begin
(let _30_870 = (writer.FStar_Util.write_char 'd')
in (let _30_872 = (serialize_lident writer lid)
in (let _30_874 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, fml, qs, _30_880) -> begin
(let _30_883 = (writer.FStar_Util.write_char 'e')
in (let _30_885 = (serialize_lident writer lid)
in (let _30_887 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _30_891, l, quals) -> begin
(let _30_896 = (writer.FStar_Util.write_char 'f')
in (let _30_898 = (serialize_letbindings writer lbs)
in (let _30_900 = (serialize_list writer serialize_lident l)
in (let _132_557 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _30_1 -> (match (_30_1) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _30_905 -> begin
false
end))))
in (writer.FStar_Util.write_bool _132_557)))))
end
| FStar_Absyn_Syntax.Sig_main (e, _30_908) -> begin
(let _30_911 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end
| FStar_Absyn_Syntax.Sig_bundle (l, qs, lids, _30_917) -> begin
(let _30_920 = (writer.FStar_Util.write_char 'h')
in (let _30_922 = (serialize_list writer serialize_sigelt l)
in (let _30_924 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _30_928) -> begin
(let _30_931 = (writer.FStar_Util.write_char 'i')
in (serialize_new_effect writer n))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, bs, c, qs, _30_938) -> begin
(let _30_941 = (writer.FStar_Util.write_char 'j')
in (let _30_943 = (serialize_lident writer lid)
in (let _30_945 = (serialize_binders writer bs)
in (let _30_947 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (se, r) -> begin
(let _30_953 = (writer.FStar_Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _30_959) -> begin
(let _30_962 = (writer.FStar_Util.write_char 'l')
in (let _30_964 = (serialize_lident writer l)
in (let _30_966 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

# 558 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let rec deserialize_new_effect : l__Reader  ->  FStar_Absyn_Syntax.eff_decl = (fun reader -> (let _132_578 = (deserialize_lident reader)
in (let _132_577 = (deserialize_list reader deserialize_binder)
in (let _132_576 = (deserialize_list reader deserialize_qualifier)
in (let _132_575 = (deserialize_knd reader)
in (let _132_574 = (deserialize_typ reader)
in (let _132_573 = (deserialize_typ reader)
in (let _132_572 = (deserialize_typ reader)
in (let _132_571 = (deserialize_typ reader)
in (let _132_570 = (deserialize_typ reader)
in (let _132_569 = (deserialize_typ reader)
in (let _132_568 = (deserialize_typ reader)
in (let _132_567 = (deserialize_typ reader)
in (let _132_566 = (deserialize_typ reader)
in (let _132_565 = (deserialize_typ reader)
in (let _132_564 = (deserialize_typ reader)
in (let _132_563 = (deserialize_typ reader)
in (let _132_562 = (deserialize_typ reader)
in (let _132_561 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mname = _132_578; FStar_Absyn_Syntax.binders = _132_577; FStar_Absyn_Syntax.qualifiers = _132_576; FStar_Absyn_Syntax.signature = _132_575; FStar_Absyn_Syntax.ret = _132_574; FStar_Absyn_Syntax.bind_wp = _132_573; FStar_Absyn_Syntax.bind_wlp = _132_572; FStar_Absyn_Syntax.if_then_else = _132_571; FStar_Absyn_Syntax.ite_wp = _132_570; FStar_Absyn_Syntax.ite_wlp = _132_569; FStar_Absyn_Syntax.wp_binop = _132_568; FStar_Absyn_Syntax.wp_as_type = _132_567; FStar_Absyn_Syntax.close_wp = _132_566; FStar_Absyn_Syntax.close_wp_t = _132_565; FStar_Absyn_Syntax.assert_p = _132_564; FStar_Absyn_Syntax.assume_p = _132_563; FStar_Absyn_Syntax.null_wp = _132_562; FStar_Absyn_Syntax.trivial = _132_561})))))))))))))))))))
and deserialize_sigelt : l__Reader  ->  FStar_Absyn_Syntax.sigelt = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _132_586 = (let _132_585 = (deserialize_lident reader)
in (let _132_584 = (deserialize_binders reader)
in (let _132_583 = (deserialize_knd reader)
in (let _132_582 = (deserialize_list reader deserialize_lident)
in (let _132_581 = (deserialize_list reader deserialize_lident)
in (let _132_580 = (deserialize_list reader deserialize_qualifier)
in (_132_585, _132_584, _132_583, _132_582, _132_581, _132_580, FStar_Absyn_Syntax.dummyRange)))))))
in FStar_Absyn_Syntax.Sig_tycon (_132_586))
end
| 'b' -> begin
(let _132_592 = (let _132_591 = (deserialize_lident reader)
in (let _132_590 = (deserialize_binders reader)
in (let _132_589 = (deserialize_knd reader)
in (let _132_588 = (deserialize_typ reader)
in (let _132_587 = (deserialize_list reader deserialize_qualifier)
in (_132_591, _132_590, _132_589, _132_588, _132_587, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_132_592))
end
| 'c' -> begin
(let _132_598 = (let _132_597 = (deserialize_lident reader)
in (let _132_596 = (deserialize_typ reader)
in (let _132_595 = (deserialize_tycon reader)
in (let _132_594 = (deserialize_list reader deserialize_qualifier)
in (let _132_593 = (deserialize_list reader deserialize_lident)
in (_132_597, _132_596, _132_595, _132_594, _132_593, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_datacon (_132_598))
end
| 'd' -> begin
(let _132_602 = (let _132_601 = (deserialize_lident reader)
in (let _132_600 = (deserialize_typ reader)
in (let _132_599 = (deserialize_list reader deserialize_qualifier)
in (_132_601, _132_600, _132_599, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_val_decl (_132_602))
end
| 'e' -> begin
(let _132_606 = (let _132_605 = (deserialize_lident reader)
in (let _132_604 = (deserialize_formula reader)
in (let _132_603 = (deserialize_list reader deserialize_qualifier)
in (_132_605, _132_604, _132_603, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_assume (_132_606))
end
| 'f' -> begin
(let _132_610 = (let _132_609 = (deserialize_letbindings reader)
in (let _132_608 = (deserialize_list reader deserialize_lident)
in (let _132_607 = if (reader.FStar_Util.read_bool ()) then begin
(FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end
in (_132_609, FStar_Absyn_Syntax.dummyRange, _132_608, _132_607))))
in FStar_Absyn_Syntax.Sig_let (_132_610))
end
| 'g' -> begin
(let _132_612 = (let _132_611 = (deserialize_exp reader)
in (_132_611, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_main (_132_612))
end
| 'h' -> begin
(let _132_616 = (let _132_615 = (deserialize_list reader deserialize_sigelt)
in (let _132_614 = (deserialize_list reader deserialize_qualifier)
in (let _132_613 = (deserialize_list reader deserialize_lident)
in (_132_615, _132_614, _132_613, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_bundle (_132_616))
end
| 'i' -> begin
(let _132_618 = (let _132_617 = (deserialize_new_effect reader)
in (_132_617, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_new_effect (_132_618))
end
| ('j') | ('k') | ('l') -> begin
(FStar_All.failwith "TODO")
end
| _30_983 -> begin
(parse_error ())
end))

# 607 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_sigelts : l__Writer  ->  FStar_Absyn_Syntax.sigelts  ->  Prims.unit = (fun writer ast -> (serialize_list writer serialize_sigelt ast))

# 608 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_sigelts : l__Reader  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun reader -> (deserialize_list reader deserialize_sigelt))

# 610 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let serialize_modul : l__Writer  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun writer ast -> (let _30_989 = (serialize_lident writer ast.FStar_Absyn_Syntax.name)
in (let _30_991 = (serialize_sigelts writer [])
in (let _30_993 = (serialize_sigelts writer ast.FStar_Absyn_Syntax.exports)
in (writer.FStar_Util.write_bool ast.FStar_Absyn_Syntax.is_interface)))))

# 616 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\ssyntax.fs"

let deserialize_modul : l__Reader  ->  FStar_Absyn_Syntax.modul = (fun reader -> (let m = (let _132_634 = (deserialize_lident reader)
in (let _132_633 = (deserialize_sigelts reader)
in (let _132_632 = (deserialize_sigelts reader)
in (let _132_631 = (reader.FStar_Util.read_bool ())
in {FStar_Absyn_Syntax.name = _132_634; FStar_Absyn_Syntax.declarations = _132_633; FStar_Absyn_Syntax.exports = _132_632; FStar_Absyn_Syntax.is_interface = _132_631; FStar_Absyn_Syntax.is_deserialized = true}))))
in (let _30_997 = m
in {FStar_Absyn_Syntax.name = _30_997.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = m.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.exports = _30_997.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _30_997.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _30_997.FStar_Absyn_Syntax.is_deserialized})))




