
open Prims
# 11 "FStar.Absyn.SSyntax.fst"
exception Err of (Prims.string)

# 11 "FStar.Absyn.SSyntax.fst"
let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 11 "FStar.Absyn.SSyntax.fst"
let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_29_3) -> begin
_29_3
end))

# 13 "FStar.Absyn.SSyntax.fst"
let parse_error = (fun _29_4 -> (match (()) with
| () -> begin
(FStar_All.failwith "Parse error: ill-formed cache")
end))

# 15 "FStar.Absyn.SSyntax.fst"
type l__Writer =
FStar_Util.oWriter

# 17 "FStar.Absyn.SSyntax.fst"
type l__Reader =
FStar_Util.oReader

# 19 "FStar.Absyn.SSyntax.fst"
let serialize_option = (fun writer f l -> (match (l) with
| None -> begin
(writer.FStar_Util.write_char 'n')
end
| Some (l) -> begin
(
# 22 "FStar.Absyn.SSyntax.fst"
let _29_12 = (writer.FStar_Util.write_char 's')
in (f writer l))
end))

# 24 "FStar.Absyn.SSyntax.fst"
let deserialize_option = (fun reader f -> (
# 25 "FStar.Absyn.SSyntax.fst"
let n = (reader.FStar_Util.read_char ())
in if (n = 'n') then begin
None
end else begin
(let _108_21 = (f reader)
in Some (_108_21))
end))

# 29 "FStar.Absyn.SSyntax.fst"
let serialize_list = (fun writer f l -> (
# 30 "FStar.Absyn.SSyntax.fst"
let _29_22 = (writer.FStar_Util.write_int (FStar_List.length l))
in (FStar_List.iter (fun elt -> (f writer elt)) (FStar_List.rev_append l []))))

# 33 "FStar.Absyn.SSyntax.fst"
let deserialize_list = (fun reader f -> (
# 34 "FStar.Absyn.SSyntax.fst"
let n = (reader.FStar_Util.read_int ())
in (
# 35 "FStar.Absyn.SSyntax.fst"
let rec helper = (fun accum n -> if (n = 0) then begin
accum
end else begin
(let _108_42 = (let _108_41 = (f reader)
in (_108_41)::accum)
in (helper _108_42 (n - 1)))
end)
in (helper [] n))))

# 42 "FStar.Absyn.SSyntax.fst"
let serialize_ident : l__Writer  ->  FStar_Ident.ident  ->  Prims.unit = (fun writer ast -> (writer.FStar_Util.write_string ast.FStar_Ident.idText))

# 43 "FStar.Absyn.SSyntax.fst"
let deserialize_ident : l__Reader  ->  FStar_Ident.ident = (fun reader -> (let _108_50 = (let _108_49 = (reader.FStar_Util.read_string ())
in (_108_49, FStar_Absyn_Syntax.dummyRange))
in (FStar_Ident.mk_ident _108_50)))

# 45 "FStar.Absyn.SSyntax.fst"
let serialize_LongIdent : l__Writer  ->  FStar_Absyn_Syntax.l__LongIdent  ->  Prims.unit = (fun writer ast -> (
# 46 "FStar.Absyn.SSyntax.fst"
let _29_37 = (serialize_list writer serialize_ident ast.FStar_Ident.ns)
in (serialize_ident writer ast.FStar_Ident.ident)))

# 49 "FStar.Absyn.SSyntax.fst"
let deserialize_LongIdent : l__Reader  ->  FStar_Ident.lident = (fun reader -> (let _108_60 = (let _108_59 = (deserialize_list reader deserialize_ident)
in (let _108_58 = (let _108_57 = (deserialize_ident reader)
in (_108_57)::[])
in (FStar_List.append _108_59 _108_58)))
in (FStar_Ident.lid_of_ids _108_60)))

# 52 "FStar.Absyn.SSyntax.fst"
let serialize_lident : l__Writer  ->  FStar_Absyn_Syntax.l__LongIdent  ->  Prims.unit = serialize_LongIdent

# 53 "FStar.Absyn.SSyntax.fst"
let deserialize_lident : l__Reader  ->  FStar_Ident.lident = deserialize_LongIdent

# 55 "FStar.Absyn.SSyntax.fst"
let serialize_withinfo_t = (fun writer s_v s_sort ast -> (
# 56 "FStar.Absyn.SSyntax.fst"
let _29_46 = (s_v writer ast.FStar_Absyn_Syntax.v)
in (s_sort writer ast.FStar_Absyn_Syntax.sort)))

# 59 "FStar.Absyn.SSyntax.fst"
let deserialize_withinfo_t = (fun reader ds_v ds_sort -> (let _108_90 = (ds_v reader)
in (let _108_89 = (ds_sort reader)
in {FStar_Absyn_Syntax.v = _108_90; FStar_Absyn_Syntax.sort = _108_89; FStar_Absyn_Syntax.p = FStar_Absyn_Syntax.dummyRange})))

# 64 "FStar.Absyn.SSyntax.fst"
let serialize_var = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_lident s_sort ast))

# 67 "FStar.Absyn.SSyntax.fst"
let deserialize_var = (fun reader ds_sort -> (deserialize_withinfo_t reader deserialize_lident ds_sort))

# 70 "FStar.Absyn.SSyntax.fst"
let serialize_bvdef = (fun writer ast -> (
# 71 "FStar.Absyn.SSyntax.fst"
let _29_63 = (serialize_ident writer ast.FStar_Absyn_Syntax.ppname)
in (serialize_ident writer ast.FStar_Absyn_Syntax.realname)))

# 78 "FStar.Absyn.SSyntax.fst"
let deserialize_bvdef = (fun ghost reader -> (let _108_110 = (deserialize_ident reader)
in (let _108_109 = (deserialize_ident reader)
in {FStar_Absyn_Syntax.ppname = _108_110; FStar_Absyn_Syntax.realname = _108_109})))

# 82 "FStar.Absyn.SSyntax.fst"
let serialize_bvar = (fun writer s_sort ast -> (serialize_withinfo_t writer serialize_bvdef s_sort ast))

# 85 "FStar.Absyn.SSyntax.fst"
let deserialize_bvar = (fun ghost reader ds_sort -> (deserialize_withinfo_t reader (deserialize_bvdef ghost) ds_sort))

# 88 "FStar.Absyn.SSyntax.fst"
let serialize_sconst : l__Writer  ->  FStar_Const.sconst  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Const.Const_effect -> begin
(writer.FStar_Util.write_char '_')
end
| FStar_Const.Const_unit -> begin
(writer.FStar_Util.write_char 'a')
end
| FStar_Const.Const_uint8 (v) -> begin
(
# 92 "FStar.Absyn.SSyntax.fst"
let _29_84 = (writer.FStar_Util.write_char 'b')
in (writer.FStar_Util.write_byte v))
end
| FStar_Const.Const_bool (v) -> begin
(
# 93 "FStar.Absyn.SSyntax.fst"
let _29_88 = (writer.FStar_Util.write_char 'c')
in (writer.FStar_Util.write_bool v))
end
| FStar_Const.Const_int32 (v) -> begin
(
# 94 "FStar.Absyn.SSyntax.fst"
let _29_92 = (writer.FStar_Util.write_char 'd')
in (writer.FStar_Util.write_int32 v))
end
| FStar_Const.Const_int64 (v) -> begin
(
# 95 "FStar.Absyn.SSyntax.fst"
let _29_96 = (writer.FStar_Util.write_char 'e')
in (writer.FStar_Util.write_int64 v))
end
| FStar_Const.Const_char (v) -> begin
(
# 96 "FStar.Absyn.SSyntax.fst"
let _29_100 = (writer.FStar_Util.write_char 'f')
in (writer.FStar_Util.write_char v))
end
| FStar_Const.Const_float (v) -> begin
(
# 97 "FStar.Absyn.SSyntax.fst"
let _29_104 = (writer.FStar_Util.write_char 'g')
in (writer.FStar_Util.write_double v))
end
| FStar_Const.Const_bytearray (v, _29_108) -> begin
(
# 98 "FStar.Absyn.SSyntax.fst"
let _29_111 = (writer.FStar_Util.write_char 'h')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Const.Const_string (v, _29_115) -> begin
(
# 99 "FStar.Absyn.SSyntax.fst"
let _29_118 = (writer.FStar_Util.write_char 'i')
in (writer.FStar_Util.write_bytearray v))
end
| FStar_Const.Const_int (v) -> begin
(
# 100 "FStar.Absyn.SSyntax.fst"
let _29_122 = (writer.FStar_Util.write_char 'j')
in (writer.FStar_Util.write_string v))
end))

# 102 "FStar.Absyn.SSyntax.fst"
let deserialize_sconst : l__Reader  ->  FStar_Const.sconst = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| '_' -> begin
FStar_Const.Const_effect
end
| 'a' -> begin
FStar_Const.Const_unit
end
| 'b' -> begin
(let _108_132 = (reader.FStar_Util.read_byte ())
in FStar_Const.Const_uint8 (_108_132))
end
| 'c' -> begin
(let _108_133 = (reader.FStar_Util.read_bool ())
in FStar_Const.Const_bool (_108_133))
end
| 'd' -> begin
(let _108_134 = (reader.FStar_Util.read_int32 ())
in FStar_Const.Const_int32 (_108_134))
end
| 'e' -> begin
(let _108_135 = (reader.FStar_Util.read_int64 ())
in FStar_Const.Const_int64 (_108_135))
end
| 'f' -> begin
(let _108_136 = (reader.FStar_Util.read_char ())
in FStar_Const.Const_char (_108_136))
end
| 'g' -> begin
(let _108_137 = (reader.FStar_Util.read_double ())
in FStar_Const.Const_float (_108_137))
end
| 'h' -> begin
(let _108_139 = (let _108_138 = (reader.FStar_Util.read_bytearray ())
in (_108_138, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_bytearray (_108_139))
end
| 'i' -> begin
(let _108_141 = (let _108_140 = (reader.FStar_Util.read_bytearray ())
in (_108_140, FStar_Absyn_Syntax.dummyRange))
in FStar_Const.Const_string (_108_141))
end
| 'j' -> begin
(let _108_142 = (reader.FStar_Util.read_string ())
in FStar_Const.Const_int (_108_142))
end
| _29_137 -> begin
(parse_error ())
end))

# 117 "FStar.Absyn.SSyntax.fst"
let serialize_either = (fun writer s_l s_r ast -> (match (ast) with
| FStar_Util.Inl (v) -> begin
(
# 119 "FStar.Absyn.SSyntax.fst"
let _29_146 = (writer.FStar_Util.write_char 'a')
in (s_l writer v))
end
| FStar_Util.Inr (v) -> begin
(
# 120 "FStar.Absyn.SSyntax.fst"
let _29_150 = (writer.FStar_Util.write_char 'b')
in (s_r writer v))
end))

# 122 "FStar.Absyn.SSyntax.fst"
let deserialize_either = (fun reader ds_l ds_r -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_168 = (ds_l reader)
in FStar_Util.Inl (_108_168))
end
| 'b' -> begin
(let _108_169 = (ds_r reader)
in FStar_Util.Inr (_108_169))
end
| _29_160 -> begin
(parse_error ())
end))

# 128 "FStar.Absyn.SSyntax.fst"
let serialize_syntax = (fun writer s_a ast -> (s_a writer ast.FStar_Absyn_Syntax.n))

# 130 "FStar.Absyn.SSyntax.fst"
let deserialize_syntax = (fun reader ds_a ds_b -> (let _108_188 = (ds_a reader)
in (let _108_187 = (FStar_Util.mk_ref None)
in (let _108_186 = (FStar_Util.mk_ref None)
in (let _108_185 = (FStar_Util.mk_ref None)
in {FStar_Absyn_Syntax.n = _108_188; FStar_Absyn_Syntax.tk = _108_187; FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange; FStar_Absyn_Syntax.fvs = _108_186; FStar_Absyn_Syntax.uvs = _108_185})))))

# 137 "FStar.Absyn.SSyntax.fst"
let rec serialize_typ' : l__Writer  ->  FStar_Absyn_Syntax.typ'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Typ_btvar (v) -> begin
(
# 139 "FStar.Absyn.SSyntax.fst"
let _29_175 = (writer.FStar_Util.write_char 'a')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Typ_const (v) -> begin
(
# 140 "FStar.Absyn.SSyntax.fst"
let _29_179 = (writer.FStar_Util.write_char 'b')
in (serialize_ftvar writer v))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 141 "FStar.Absyn.SSyntax.fst"
let _29_185 = (writer.FStar_Util.write_char 'c')
in (
# 141 "FStar.Absyn.SSyntax.fst"
let _29_187 = (serialize_binders writer bs)
in (serialize_comp writer c)))
end
| FStar_Absyn_Syntax.Typ_refine (v, t) -> begin
(
# 142 "FStar.Absyn.SSyntax.fst"
let _29_193 = (writer.FStar_Util.write_char 'd')
in (
# 142 "FStar.Absyn.SSyntax.fst"
let _29_195 = (serialize_bvvar writer v)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_app (t, ars) -> begin
(
# 144 "FStar.Absyn.SSyntax.fst"
let _29_201 = (writer.FStar_Util.write_char 'e')
in (
# 144 "FStar.Absyn.SSyntax.fst"
let _29_203 = (serialize_typ writer t)
in (
# 144 "FStar.Absyn.SSyntax.fst"
let _29_205 = (serialize_args writer ars)
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
(
# 150 "FStar.Absyn.SSyntax.fst"
let _29_219 = (writer.FStar_Util.write_char 'f')
in (
# 150 "FStar.Absyn.SSyntax.fst"
let _29_221 = (serialize_binders writer bs)
in (serialize_typ writer t)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(
# 151 "FStar.Absyn.SSyntax.fst"
let _29_227 = (writer.FStar_Util.write_char 'g')
in (
# 151 "FStar.Absyn.SSyntax.fst"
let _29_229 = (serialize_typ writer t)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Typ_meta (m) -> begin
(
# 152 "FStar.Absyn.SSyntax.fst"
let _29_233 = (writer.FStar_Util.write_char 'h')
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
and serialize_meta_t : l__Writer  ->  FStar_Absyn_Syntax.meta_t  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_pattern (t, l) -> begin
(
# 159 "FStar.Absyn.SSyntax.fst"
let _29_254 = (writer.FStar_Util.write_char 'a')
in (
# 159 "FStar.Absyn.SSyntax.fst"
let _29_256 = (serialize_typ writer t)
in (serialize_list writer (fun w -> (serialize_list w serialize_arg)) l)))
end
| FStar_Absyn_Syntax.Meta_named (t, lid) -> begin
(
# 160 "FStar.Absyn.SSyntax.fst"
let _29_263 = (writer.FStar_Util.write_char 'b')
in (
# 160 "FStar.Absyn.SSyntax.fst"
let _29_265 = (serialize_typ writer t)
in (serialize_lident writer lid)))
end
| FStar_Absyn_Syntax.Meta_labeled (t, s, _29_270, b) -> begin
(
# 161 "FStar.Absyn.SSyntax.fst"
let _29_274 = (writer.FStar_Util.write_char 'c')
in (
# 161 "FStar.Absyn.SSyntax.fst"
let _29_276 = (serialize_typ writer t)
in (
# 161 "FStar.Absyn.SSyntax.fst"
let _29_278 = (writer.FStar_Util.write_string s)
in (writer.FStar_Util.write_bool b))))
end
| _29_281 -> begin
(Prims.raise (Err ("unimplemented meta_t")))
end))
and serialize_arg : l__Writer  ->  FStar_Absyn_Syntax.arg  ->  Prims.unit = (fun writer ast -> (
# 164 "FStar.Absyn.SSyntax.fst"
let _29_284 = (serialize_either writer serialize_typ serialize_exp (Prims.fst ast))
in (let _108_257 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _108_257))))
and serialize_args : l__Writer  ->  FStar_Absyn_Syntax.args  ->  Prims.unit = (fun writer ast -> (serialize_list writer serialize_arg ast))
and serialize_binder : l__Writer  ->  FStar_Absyn_Syntax.binder  ->  Prims.unit = (fun writer ast -> (
# 168 "FStar.Absyn.SSyntax.fst"
let _29_290 = (serialize_either writer serialize_btvar serialize_bvvar (Prims.fst ast))
in (let _108_262 = (FStar_All.pipe_left FStar_Absyn_Syntax.is_implicit (Prims.snd ast))
in (writer.FStar_Util.write_bool _108_262))))
and serialize_binders : l__Writer  ->  FStar_Absyn_Syntax.binders  ->  Prims.unit = (fun writer ast -> (serialize_list writer serialize_binder ast))
and serialize_typ : l__Writer  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun writer ast -> (let _108_267 = (FStar_Absyn_Util.compress_typ ast)
in (serialize_syntax writer serialize_typ' _108_267)))
and serialize_comp_typ : l__Writer  ->  FStar_Absyn_Syntax.comp_typ  ->  Prims.unit = (fun writer ast -> (
# 175 "FStar.Absyn.SSyntax.fst"
let _29_298 = (serialize_lident writer ast.FStar_Absyn_Syntax.effect_name)
in (
# 176 "FStar.Absyn.SSyntax.fst"
let _29_300 = (serialize_typ writer ast.FStar_Absyn_Syntax.result_typ)
in (
# 177 "FStar.Absyn.SSyntax.fst"
let _29_302 = (serialize_args writer ast.FStar_Absyn_Syntax.effect_args)
in (serialize_list writer serialize_cflags ast.FStar_Absyn_Syntax.flags)))))
and serialize_comp' : l__Writer  ->  FStar_Absyn_Syntax.comp'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 182 "FStar.Absyn.SSyntax.fst"
let _29_308 = (writer.FStar_Util.write_char 'a')
in (serialize_typ writer t))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(
# 183 "FStar.Absyn.SSyntax.fst"
let _29_312 = (writer.FStar_Util.write_char 'b')
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
(
# 195 "FStar.Absyn.SSyntax.fst"
let _29_326 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end))
and serialize_exp' : l__Writer  ->  FStar_Absyn_Syntax.exp'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Exp_bvar (v) -> begin
(
# 199 "FStar.Absyn.SSyntax.fst"
let _29_332 = (writer.FStar_Util.write_char 'a')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Exp_fvar (v, b) -> begin
(
# 200 "FStar.Absyn.SSyntax.fst"
let _29_338 = (writer.FStar_Util.write_char 'b')
in (
# 200 "FStar.Absyn.SSyntax.fst"
let _29_340 = (serialize_fvvar writer v)
in (writer.FStar_Util.write_bool false)))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(
# 201 "FStar.Absyn.SSyntax.fst"
let _29_344 = (writer.FStar_Util.write_char 'c')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(
# 202 "FStar.Absyn.SSyntax.fst"
let _29_350 = (writer.FStar_Util.write_char 'd')
in (
# 202 "FStar.Absyn.SSyntax.fst"
let _29_352 = (serialize_binders writer bs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_app (e, ars) -> begin
(
# 203 "FStar.Absyn.SSyntax.fst"
let _29_358 = (writer.FStar_Util.write_char 'e')
in (
# 203 "FStar.Absyn.SSyntax.fst"
let _29_360 = (serialize_exp writer e)
in (serialize_args writer ars)))
end
| FStar_Absyn_Syntax.Exp_match (e, l) -> begin
(
# 205 "FStar.Absyn.SSyntax.fst"
let g = (fun writer eopt -> (match (eopt) with
| Some (e1) -> begin
(
# 207 "FStar.Absyn.SSyntax.fst"
let _29_371 = (writer.FStar_Util.write_char 'a')
in (serialize_exp writer e1))
end
| None -> begin
(writer.FStar_Util.write_char 'b')
end))
in (
# 210 "FStar.Absyn.SSyntax.fst"
let f = (fun writer _29_379 -> (match (_29_379) with
| (p, eopt, e) -> begin
(
# 210 "FStar.Absyn.SSyntax.fst"
let _29_380 = (serialize_pat writer p)
in (
# 210 "FStar.Absyn.SSyntax.fst"
let _29_382 = (g writer eopt)
in (serialize_exp writer e)))
end))
in (
# 211 "FStar.Absyn.SSyntax.fst"
let _29_384 = (writer.FStar_Util.write_char 'f')
in (
# 211 "FStar.Absyn.SSyntax.fst"
let _29_386 = (serialize_exp writer e)
in (serialize_list writer f l)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(
# 212 "FStar.Absyn.SSyntax.fst"
let _29_393 = (writer.FStar_Util.write_char 'g')
in (
# 212 "FStar.Absyn.SSyntax.fst"
let _29_395 = (serialize_exp writer e)
in (
# 212 "FStar.Absyn.SSyntax.fst"
let _29_397 = (serialize_typ writer t)
in (serialize_option writer serialize_lident l))))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e) -> begin
(
# 213 "FStar.Absyn.SSyntax.fst"
let _29_403 = (writer.FStar_Util.write_char 'h')
in (
# 213 "FStar.Absyn.SSyntax.fst"
let _29_405 = (serialize_letbindings writer lbs)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Exp_meta (m) -> begin
(
# 214 "FStar.Absyn.SSyntax.fst"
let _29_409 = (writer.FStar_Util.write_char 'i')
in (serialize_meta_e writer m))
end
| _29_412 -> begin
(Prims.raise (Err ("unimplemented exp\'")))
end))
and serialize_meta_e : l__Writer  ->  FStar_Absyn_Syntax.meta_e  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Meta_desugared (e, s) -> begin
(
# 219 "FStar.Absyn.SSyntax.fst"
let _29_419 = (writer.FStar_Util.write_char 'a')
in (
# 219 "FStar.Absyn.SSyntax.fst"
let _29_421 = (serialize_exp writer e)
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
and serialize_exp : l__Writer  ->  FStar_Absyn_Syntax.exp  ->  Prims.unit = (fun writer ast -> (let _108_292 = (FStar_Absyn_Util.compress_exp ast)
in (serialize_syntax writer serialize_exp' _108_292)))
and serialize_btvdef : l__Writer  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.unit = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_bvvdef : l__Writer  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.unit = (fun writer ast -> (serialize_bvdef writer ast))
and serialize_pat' : l__Writer  ->  FStar_Absyn_Syntax.pat'  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Pat_disj (l) -> begin
(
# 238 "FStar.Absyn.SSyntax.fst"
let _29_440 = (writer.FStar_Util.write_char 'a')
in (serialize_list writer serialize_pat l))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(
# 239 "FStar.Absyn.SSyntax.fst"
let _29_444 = (writer.FStar_Util.write_char 'b')
in (serialize_sconst writer c))
end
| FStar_Absyn_Syntax.Pat_cons (v, _29_448, l) -> begin
(
# 240 "FStar.Absyn.SSyntax.fst"
let _29_452 = (writer.FStar_Util.write_char 'c')
in (
# 240 "FStar.Absyn.SSyntax.fst"
let _29_454 = (serialize_fvvar writer v)
in (serialize_list writer (fun w _29_459 -> (match (_29_459) with
| (p, b) -> begin
(
# 240 "FStar.Absyn.SSyntax.fst"
let _29_460 = (serialize_pat w p)
in (w.FStar_Util.write_bool b))
end)) l)))
end
| FStar_Absyn_Syntax.Pat_var (v) -> begin
(
# 241 "FStar.Absyn.SSyntax.fst"
let _29_464 = (writer.FStar_Util.write_char 'd')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_tvar (v) -> begin
(
# 242 "FStar.Absyn.SSyntax.fst"
let _29_468 = (writer.FStar_Util.write_char 'e')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_wild (v) -> begin
(
# 243 "FStar.Absyn.SSyntax.fst"
let _29_472 = (writer.FStar_Util.write_char 'f')
in (serialize_bvvar writer v))
end
| FStar_Absyn_Syntax.Pat_twild (v) -> begin
(
# 244 "FStar.Absyn.SSyntax.fst"
let _29_476 = (writer.FStar_Util.write_char 'g')
in (serialize_btvar writer v))
end
| FStar_Absyn_Syntax.Pat_dot_term (v, e) -> begin
(
# 245 "FStar.Absyn.SSyntax.fst"
let _29_482 = (writer.FStar_Util.write_char 'h')
in (
# 245 "FStar.Absyn.SSyntax.fst"
let _29_484 = (serialize_bvvar writer v)
in (serialize_exp writer e)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (v, t) -> begin
(
# 246 "FStar.Absyn.SSyntax.fst"
let _29_490 = (writer.FStar_Util.write_char 'i')
in (
# 246 "FStar.Absyn.SSyntax.fst"
let _29_492 = (serialize_btvar writer v)
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
(
# 255 "FStar.Absyn.SSyntax.fst"
let _29_506 = (writer.FStar_Util.write_char 'c')
in (
# 255 "FStar.Absyn.SSyntax.fst"
let _29_508 = (serialize_kabbrev writer ka)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 256 "FStar.Absyn.SSyntax.fst"
let _29_514 = (writer.FStar_Util.write_char 'd')
in (
# 256 "FStar.Absyn.SSyntax.fst"
let _29_516 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end
| FStar_Absyn_Syntax.Kind_lam (bs, k) -> begin
(
# 257 "FStar.Absyn.SSyntax.fst"
let _29_522 = (writer.FStar_Util.write_char 'e')
in (
# 257 "FStar.Absyn.SSyntax.fst"
let _29_524 = (serialize_binders writer bs)
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
and serialize_knd : l__Writer  ->  FStar_Absyn_Syntax.knd  ->  Prims.unit = (fun writer ast -> (let _108_309 = (FStar_Absyn_Util.compress_kind ast)
in (serialize_syntax writer serialize_knd' _108_309)))
and serialize_kabbrev : l__Writer  ->  FStar_Absyn_Syntax.kabbrev  ->  Prims.unit = (fun writer ast -> (
# 264 "FStar.Absyn.SSyntax.fst"
let _29_543 = (serialize_lident writer (Prims.fst ast))
in (serialize_args writer (Prims.snd ast))))
and serialize_lbname : l__Writer  ->  FStar_Absyn_Syntax.lbname  ->  Prims.unit = (fun writer ast -> (serialize_either writer serialize_bvvdef serialize_lident ast))
and serialize_letbindings : l__Writer  ->  FStar_Absyn_Syntax.letbindings  ->  Prims.unit = (fun writer ast -> (
# 269 "FStar.Absyn.SSyntax.fst"
let f = (fun writer lb -> (
# 269 "FStar.Absyn.SSyntax.fst"
let _29_552 = (serialize_lbname writer lb.FStar_Absyn_Syntax.lbname)
in (
# 269 "FStar.Absyn.SSyntax.fst"
let _29_554 = (serialize_lident writer lb.FStar_Absyn_Syntax.lbeff)
in (
# 269 "FStar.Absyn.SSyntax.fst"
let _29_556 = (serialize_typ writer lb.FStar_Absyn_Syntax.lbtyp)
in (serialize_exp writer lb.FStar_Absyn_Syntax.lbdef)))))
in (
# 270 "FStar.Absyn.SSyntax.fst"
let _29_558 = (writer.FStar_Util.write_bool (Prims.fst ast))
in (serialize_list writer f (Prims.snd ast)))))
and serialize_fvar : l__Writer  ->  FStar_Absyn_Syntax.fvar  ->  Prims.unit = (fun writer ast -> (serialize_either writer serialize_btvdef serialize_bvvdef ast))
and serialize_btvar : l__Writer  ->  FStar_Absyn_Syntax.btvar  ->  Prims.unit = (fun writer ast -> (serialize_bvar writer serialize_knd ast))
and serialize_bvvar : l__Writer  ->  FStar_Absyn_Syntax.bvvar  ->  Prims.unit = (fun writer ast -> (serialize_bvar writer serialize_typ ast))
and serialize_ftvar : l__Writer  ->  FStar_Absyn_Syntax.ftvar  ->  Prims.unit = (fun writer ast -> (serialize_var writer serialize_knd ast))
and serialize_fvvar : l__Writer  ->  FStar_Absyn_Syntax.fvvar  ->  Prims.unit = (fun writer ast -> (serialize_var writer serialize_typ ast))

# 282 "FStar.Absyn.SSyntax.fst"
let rec deserialize_typ' : l__Reader  ->  FStar_Absyn_Syntax.typ' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_360 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Typ_btvar (_108_360))
end
| 'b' -> begin
(let _108_361 = (deserialize_ftvar reader)
in FStar_Absyn_Syntax.Typ_const (_108_361))
end
| 'c' -> begin
(let _108_364 = (let _108_363 = (deserialize_binders reader)
in (let _108_362 = (deserialize_comp reader)
in (_108_363, _108_362)))
in FStar_Absyn_Syntax.Typ_fun (_108_364))
end
| 'd' -> begin
(let _108_367 = (let _108_366 = (deserialize_bvvar reader)
in (let _108_365 = (deserialize_typ reader)
in (_108_366, _108_365)))
in FStar_Absyn_Syntax.Typ_refine (_108_367))
end
| 'e' -> begin
(let _108_370 = (let _108_369 = (deserialize_typ reader)
in (let _108_368 = (deserialize_args reader)
in (_108_369, _108_368)))
in FStar_Absyn_Syntax.Typ_app (_108_370))
end
| 'f' -> begin
(let _108_373 = (let _108_372 = (deserialize_binders reader)
in (let _108_371 = (deserialize_typ reader)
in (_108_372, _108_371)))
in FStar_Absyn_Syntax.Typ_lam (_108_373))
end
| 'g' -> begin
(let _108_376 = (let _108_375 = (deserialize_typ reader)
in (let _108_374 = (deserialize_knd reader)
in (_108_375, _108_374)))
in FStar_Absyn_Syntax.Typ_ascribed (_108_376))
end
| 'h' -> begin
(let _108_377 = (deserialize_meta_t reader)
in FStar_Absyn_Syntax.Typ_meta (_108_377))
end
| 'i' -> begin
FStar_Absyn_Syntax.Typ_unknown
end
| _29_581 -> begin
(parse_error ())
end))
and deserialize_meta_t : l__Reader  ->  FStar_Absyn_Syntax.meta_t = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_382 = (let _108_381 = (deserialize_typ reader)
in (let _108_380 = (deserialize_list reader (fun r -> (deserialize_list r deserialize_arg)))
in (_108_381, _108_380)))
in FStar_Absyn_Syntax.Meta_pattern (_108_382))
end
| 'b' -> begin
(let _108_385 = (let _108_384 = (deserialize_typ reader)
in (let _108_383 = (deserialize_lident reader)
in (_108_384, _108_383)))
in FStar_Absyn_Syntax.Meta_named (_108_385))
end
| 'c' -> begin
(let _108_389 = (let _108_388 = (deserialize_typ reader)
in (let _108_387 = (reader.FStar_Util.read_string ())
in (let _108_386 = (reader.FStar_Util.read_bool ())
in (_108_388, _108_387, FStar_Absyn_Syntax.dummyRange, _108_386))))
in FStar_Absyn_Syntax.Meta_labeled (_108_389))
end
| _29_588 -> begin
(parse_error ())
end))
and deserialize_arg : l__Reader  ->  FStar_Absyn_Syntax.arg = (fun reader -> (let _108_393 = (deserialize_either reader deserialize_typ deserialize_exp)
in (let _108_392 = (let _108_391 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _108_391))
in (_108_393, _108_392))))
and deserialize_args : l__Reader  ->  FStar_Absyn_Syntax.args = (fun reader -> (deserialize_list reader deserialize_arg))
and deserialize_binder : l__Reader  ->  FStar_Absyn_Syntax.binder = (fun reader -> (let _108_398 = (deserialize_either reader deserialize_btvar deserialize_bvvar)
in (let _108_397 = (let _108_396 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left FStar_Absyn_Syntax.as_implicit _108_396))
in (_108_398, _108_397))))
and deserialize_binders : l__Reader  ->  FStar_Absyn_Syntax.binders = (fun reader -> (deserialize_list reader deserialize_binder))
and deserialize_typ : l__Reader  ->  FStar_Absyn_Syntax.typ = (fun reader -> (deserialize_syntax reader deserialize_typ' FStar_Absyn_Syntax.mk_Kind_unknown))
and deserialize_comp_typ : l__Reader  ->  FStar_Absyn_Syntax.comp_typ = (fun reader -> (let _108_405 = (deserialize_lident reader)
in (let _108_404 = (deserialize_typ reader)
in (let _108_403 = (deserialize_args reader)
in (let _108_402 = (deserialize_list reader deserialize_cflags)
in {FStar_Absyn_Syntax.effect_name = _108_405; FStar_Absyn_Syntax.result_typ = _108_404; FStar_Absyn_Syntax.effect_args = _108_403; FStar_Absyn_Syntax.flags = _108_402})))))
and deserialize_comp' : l__Reader  ->  FStar_Absyn_Syntax.comp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_407 = (deserialize_typ reader)
in FStar_Absyn_Syntax.Total (_108_407))
end
| 'b' -> begin
(let _108_408 = (deserialize_comp_typ reader)
in FStar_Absyn_Syntax.Comp (_108_408))
end
| _29_599 -> begin
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
(let _108_411 = (deserialize_exp reader)
in FStar_Absyn_Syntax.DECREASES (_108_411))
end
| _29_610 -> begin
(parse_error ())
end))
and deserialize_exp' : l__Reader  ->  FStar_Absyn_Syntax.exp' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_413 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Exp_bvar (_108_413))
end
| 'b' -> begin
(let _108_417 = (let _108_416 = (deserialize_fvvar reader)
in (let _108_415 = (
# 341 "FStar.Absyn.SSyntax.fst"
let _29_614 = (let _108_414 = (reader.FStar_Util.read_bool ())
in (FStar_All.pipe_left Prims.ignore _108_414))
in None)
in (_108_416, _108_415)))
in FStar_Absyn_Syntax.Exp_fvar (_108_417))
end
| 'c' -> begin
(let _108_418 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Exp_constant (_108_418))
end
| 'd' -> begin
(let _108_421 = (let _108_420 = (deserialize_binders reader)
in (let _108_419 = (deserialize_exp reader)
in (_108_420, _108_419)))
in FStar_Absyn_Syntax.Exp_abs (_108_421))
end
| 'e' -> begin
(let _108_424 = (let _108_423 = (deserialize_exp reader)
in (let _108_422 = (deserialize_args reader)
in (_108_423, _108_422)))
in FStar_Absyn_Syntax.Exp_app (_108_424))
end
| 'f' -> begin
(
# 346 "FStar.Absyn.SSyntax.fst"
let g = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_427 = (deserialize_exp reader)
in Some (_108_427))
end
| 'b' -> begin
None
end
| _29_625 -> begin
(parse_error ())
end))
in (
# 352 "FStar.Absyn.SSyntax.fst"
let f = (fun reader -> (let _108_432 = (deserialize_pat reader)
in (let _108_431 = (g reader)
in (let _108_430 = (deserialize_exp reader)
in (_108_432, _108_431, _108_430)))))
in (let _108_435 = (let _108_434 = (deserialize_exp reader)
in (let _108_433 = (deserialize_list reader f)
in (_108_434, _108_433)))
in FStar_Absyn_Syntax.Exp_match (_108_435))))
end
| 'g' -> begin
(let _108_439 = (let _108_438 = (deserialize_exp reader)
in (let _108_437 = (deserialize_typ reader)
in (let _108_436 = (deserialize_option reader deserialize_lident)
in (_108_438, _108_437, _108_436))))
in FStar_Absyn_Syntax.Exp_ascribed (_108_439))
end
| 'h' -> begin
(let _108_442 = (let _108_441 = (deserialize_letbindings reader)
in (let _108_440 = (deserialize_exp reader)
in (_108_441, _108_440)))
in FStar_Absyn_Syntax.Exp_let (_108_442))
end
| 'i' -> begin
(let _108_443 = (deserialize_meta_e reader)
in FStar_Absyn_Syntax.Exp_meta (_108_443))
end
| _29_632 -> begin
(parse_error ())
end))
and deserialize_meta_e : l__Reader  ->  FStar_Absyn_Syntax.meta_e = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_447 = (let _108_446 = (deserialize_exp reader)
in (let _108_445 = (deserialize_meta_source_info reader)
in (_108_446, _108_445)))
in FStar_Absyn_Syntax.Meta_desugared (_108_447))
end
| _29_636 -> begin
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
| _29_643 -> begin
(parse_error ())
end))
and deserialize_exp : l__Reader  ->  FStar_Absyn_Syntax.exp = (fun reader -> (deserialize_syntax reader deserialize_exp' FStar_Absyn_Syntax.mk_Typ_unknown))
and deserialize_btvdef : l__Reader  ->  FStar_Absyn_Syntax.btvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_bvvdef : l__Reader  ->  FStar_Absyn_Syntax.bvvdef = (fun reader -> (deserialize_bvdef None reader))
and deserialize_pat' : l__Reader  ->  FStar_Absyn_Syntax.pat' = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_453 = (deserialize_list reader deserialize_pat)
in FStar_Absyn_Syntax.Pat_disj (_108_453))
end
| 'b' -> begin
(let _108_454 = (deserialize_sconst reader)
in FStar_Absyn_Syntax.Pat_constant (_108_454))
end
| 'c' -> begin
(let _108_460 = (let _108_459 = (deserialize_fvvar reader)
in (let _108_458 = (deserialize_list reader (fun r -> (let _108_457 = (deserialize_pat r)
in (let _108_456 = (r.FStar_Util.read_bool ())
in (_108_457, _108_456)))))
in (_108_459, None, _108_458)))
in FStar_Absyn_Syntax.Pat_cons (_108_460))
end
| 'd' -> begin
(let _108_461 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_var (_108_461))
end
| 'e' -> begin
(let _108_462 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_tvar (_108_462))
end
| 'f' -> begin
(let _108_463 = (deserialize_bvvar reader)
in FStar_Absyn_Syntax.Pat_wild (_108_463))
end
| 'g' -> begin
(let _108_464 = (deserialize_btvar reader)
in FStar_Absyn_Syntax.Pat_twild (_108_464))
end
| 'h' -> begin
(let _108_467 = (let _108_466 = (deserialize_bvvar reader)
in (let _108_465 = (deserialize_exp reader)
in (_108_466, _108_465)))
in FStar_Absyn_Syntax.Pat_dot_term (_108_467))
end
| 'i' -> begin
(let _108_470 = (let _108_469 = (deserialize_btvar reader)
in (let _108_468 = (deserialize_typ reader)
in (_108_469, _108_468)))
in FStar_Absyn_Syntax.Pat_dot_typ (_108_470))
end
| _29_659 -> begin
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
(let _108_476 = (let _108_475 = (deserialize_kabbrev reader)
in (let _108_474 = (deserialize_knd reader)
in (_108_475, _108_474)))
in FStar_Absyn_Syntax.Kind_abbrev (_108_476))
end
| 'd' -> begin
(let _108_479 = (let _108_478 = (deserialize_binders reader)
in (let _108_477 = (deserialize_knd reader)
in (_108_478, _108_477)))
in FStar_Absyn_Syntax.Kind_arrow (_108_479))
end
| 'e' -> begin
(let _108_482 = (let _108_481 = (deserialize_binders reader)
in (let _108_480 = (deserialize_knd reader)
in (_108_481, _108_480)))
in FStar_Absyn_Syntax.Kind_lam (_108_482))
end
| 'f' -> begin
FStar_Absyn_Syntax.Kind_unknown
end
| _29_670 -> begin
(parse_error ())
end))
and deserialize_knd : l__Reader  ->  FStar_Absyn_Syntax.knd = (fun reader -> (deserialize_syntax reader deserialize_knd' ()))
and deserialize_kabbrev : l__Reader  ->  FStar_Absyn_Syntax.kabbrev = (fun reader -> (let _108_486 = (deserialize_lident reader)
in (let _108_485 = (deserialize_args reader)
in (_108_486, _108_485))))
and deserialize_lbname : l__Reader  ->  FStar_Absyn_Syntax.lbname = (fun reader -> (deserialize_either reader deserialize_bvvdef deserialize_lident))
and deserialize_letbindings : l__Reader  ->  FStar_Absyn_Syntax.letbindings = (fun reader -> (
# 411 "FStar.Absyn.SSyntax.fst"
let f = (fun reader -> (let _108_494 = (deserialize_lbname reader)
in (let _108_493 = (deserialize_typ reader)
in (let _108_492 = (deserialize_lident reader)
in (let _108_491 = (deserialize_exp reader)
in {FStar_Absyn_Syntax.lbname = _108_494; FStar_Absyn_Syntax.lbtyp = _108_493; FStar_Absyn_Syntax.lbeff = _108_492; FStar_Absyn_Syntax.lbdef = _108_491})))))
in (let _108_496 = (reader.FStar_Util.read_bool ())
in (let _108_495 = (deserialize_list reader f)
in (_108_496, _108_495)))))
and deserialize_fvar : l__Reader  ->  FStar_Absyn_Syntax.fvar = (fun reader -> (deserialize_either reader deserialize_btvdef deserialize_bvvdef))
and deserialize_btvar : l__Reader  ->  FStar_Absyn_Syntax.btvar = (fun reader -> (deserialize_bvar None reader deserialize_knd))
and deserialize_bvvar : l__Reader  ->  FStar_Absyn_Syntax.bvvar = (fun reader -> (deserialize_bvar None reader deserialize_typ))
and deserialize_ftvar : l__Reader  ->  FStar_Absyn_Syntax.ftvar = (fun reader -> (deserialize_var reader deserialize_knd))
and deserialize_fvvar : l__Reader  ->  FStar_Absyn_Syntax.fvvar = (fun reader -> (deserialize_var reader deserialize_typ))

# 427 "FStar.Absyn.SSyntax.fst"
let serialize_formula : l__Writer  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = serialize_typ

# 428 "FStar.Absyn.SSyntax.fst"
let deserialize_formula : l__Reader  ->  FStar_Absyn_Syntax.typ = deserialize_typ

# 430 "FStar.Absyn.SSyntax.fst"
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
(
# 436 "FStar.Absyn.SSyntax.fst"
let _29_690 = (writer.FStar_Util.write_char 'i')
in (serialize_lident writer lid))
end
| FStar_Absyn_Syntax.Projector (lid, v) -> begin
(
# 437 "FStar.Absyn.SSyntax.fst"
let _29_696 = (writer.FStar_Util.write_char 'j')
in (
# 437 "FStar.Absyn.SSyntax.fst"
let _29_698 = (serialize_lident writer lid)
in (serialize_either writer serialize_btvdef serialize_bvvdef v)))
end
| FStar_Absyn_Syntax.RecordType (l) -> begin
(
# 438 "FStar.Absyn.SSyntax.fst"
let _29_702 = (writer.FStar_Util.write_char 'k')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.RecordConstructor (l) -> begin
(
# 439 "FStar.Absyn.SSyntax.fst"
let _29_706 = (writer.FStar_Util.write_char 'l')
in (serialize_list writer serialize_lident l))
end
| FStar_Absyn_Syntax.ExceptionConstructor -> begin
(writer.FStar_Util.write_char 'm')
end
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
(writer.FStar_Util.write_char 'o')
end
| FStar_Absyn_Syntax.DefaultEffect (l) -> begin
(
# 442 "FStar.Absyn.SSyntax.fst"
let _29_712 = (writer.FStar_Util.write_char 'p')
in (serialize_option writer serialize_lident l))
end
| FStar_Absyn_Syntax.TotalEffect -> begin
(writer.FStar_Util.write_char 'q')
end
| _29_716 -> begin
(FStar_All.failwith "Unexpected qualifier")
end))

# 446 "FStar.Absyn.SSyntax.fst"
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
(let _108_511 = (deserialize_lident reader)
in FStar_Absyn_Syntax.Discriminator (_108_511))
end
| 'j' -> begin
(let _108_514 = (let _108_513 = (deserialize_lident reader)
in (let _108_512 = (deserialize_either reader deserialize_btvdef deserialize_bvvdef)
in (_108_513, _108_512)))
in FStar_Absyn_Syntax.Projector (_108_514))
end
| 'k' -> begin
(let _108_515 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordType (_108_515))
end
| 'l' -> begin
(let _108_516 = (deserialize_list reader deserialize_lident)
in FStar_Absyn_Syntax.RecordConstructor (_108_516))
end
| 'm' -> begin
FStar_Absyn_Syntax.ExceptionConstructor
end
| 'o' -> begin
FStar_Absyn_Syntax.HasMaskedEffect
end
| 'p' -> begin
(let _108_518 = (deserialize_option reader deserialize_lident)
in (FStar_All.pipe_right _108_518 (fun _108_517 -> FStar_Absyn_Syntax.DefaultEffect (_108_517))))
end
| 'q' -> begin
FStar_Absyn_Syntax.TotalEffect
end
| _29_731 -> begin
(parse_error ())
end))

# 462 "FStar.Absyn.SSyntax.fst"
let serialize_tycon : l__Writer  ->  FStar_Absyn_Syntax.tycon  ->  Prims.unit = (fun writer _29_736 -> (match (_29_736) with
| (lid, bs, k) -> begin
(
# 462 "FStar.Absyn.SSyntax.fst"
let _29_737 = (serialize_lident writer lid)
in (
# 462 "FStar.Absyn.SSyntax.fst"
let _29_739 = (serialize_binders writer bs)
in (serialize_knd writer k)))
end))

# 463 "FStar.Absyn.SSyntax.fst"
let deserialize_tycon : l__Reader  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun reader -> (let _108_527 = (deserialize_lident reader)
in (let _108_526 = (deserialize_binders reader)
in (let _108_525 = (deserialize_knd reader)
in (_108_527, _108_526, _108_525)))))

# 465 "FStar.Absyn.SSyntax.fst"
let serialize_monad_abbrev : l__Writer  ->  FStar_Absyn_Syntax.monad_abbrev  ->  Prims.unit = (fun writer ast -> (
# 466 "FStar.Absyn.SSyntax.fst"
let _29_744 = (serialize_lident writer ast.FStar_Absyn_Syntax.mabbrev)
in (
# 467 "FStar.Absyn.SSyntax.fst"
let _29_746 = (serialize_binders writer ast.FStar_Absyn_Syntax.parms)
in (serialize_typ writer ast.FStar_Absyn_Syntax.def))))

# 470 "FStar.Absyn.SSyntax.fst"
let deserialize_monad_abbrev : l__Reader  ->  FStar_Absyn_Syntax.monad_abbrev = (fun reader -> (let _108_536 = (deserialize_lident reader)
in (let _108_535 = (deserialize_binders reader)
in (let _108_534 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mabbrev = _108_536; FStar_Absyn_Syntax.parms = _108_535; FStar_Absyn_Syntax.def = _108_534}))))

# 475 "FStar.Absyn.SSyntax.fst"
let serialize_sub_effect : l__Writer  ->  FStar_Absyn_Syntax.sub_eff  ->  Prims.unit = (fun writer ast -> (
# 476 "FStar.Absyn.SSyntax.fst"
let _29_751 = (serialize_lident writer ast.FStar_Absyn_Syntax.source)
in (
# 477 "FStar.Absyn.SSyntax.fst"
let _29_753 = (serialize_lident writer ast.FStar_Absyn_Syntax.target)
in (serialize_typ writer ast.FStar_Absyn_Syntax.lift))))

# 480 "FStar.Absyn.SSyntax.fst"
let deserialize_sub_effect : l__Reader  ->  FStar_Absyn_Syntax.sub_eff = (fun reader -> (let _108_545 = (deserialize_lident reader)
in (let _108_544 = (deserialize_lident reader)
in (let _108_543 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.source = _108_545; FStar_Absyn_Syntax.target = _108_544; FStar_Absyn_Syntax.lift = _108_543}))))

# 485 "FStar.Absyn.SSyntax.fst"
let rec serialize_new_effect : l__Writer  ->  FStar_Absyn_Syntax.eff_decl  ->  Prims.unit = (fun writer ast -> (
# 486 "FStar.Absyn.SSyntax.fst"
let _29_758 = (serialize_lident writer ast.FStar_Absyn_Syntax.mname)
in (
# 487 "FStar.Absyn.SSyntax.fst"
let _29_760 = (serialize_list writer serialize_binder ast.FStar_Absyn_Syntax.binders)
in (
# 488 "FStar.Absyn.SSyntax.fst"
let _29_762 = (serialize_list writer serialize_qualifier ast.FStar_Absyn_Syntax.qualifiers)
in (
# 489 "FStar.Absyn.SSyntax.fst"
let _29_764 = (serialize_knd writer ast.FStar_Absyn_Syntax.signature)
in (
# 490 "FStar.Absyn.SSyntax.fst"
let _29_766 = (serialize_typ writer ast.FStar_Absyn_Syntax.ret)
in (
# 491 "FStar.Absyn.SSyntax.fst"
let _29_768 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wp)
in (
# 492 "FStar.Absyn.SSyntax.fst"
let _29_770 = (serialize_typ writer ast.FStar_Absyn_Syntax.bind_wlp)
in (
# 493 "FStar.Absyn.SSyntax.fst"
let _29_772 = (serialize_typ writer ast.FStar_Absyn_Syntax.if_then_else)
in (
# 494 "FStar.Absyn.SSyntax.fst"
let _29_774 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wp)
in (
# 495 "FStar.Absyn.SSyntax.fst"
let _29_776 = (serialize_typ writer ast.FStar_Absyn_Syntax.ite_wlp)
in (
# 496 "FStar.Absyn.SSyntax.fst"
let _29_778 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_binop)
in (
# 497 "FStar.Absyn.SSyntax.fst"
let _29_780 = (serialize_typ writer ast.FStar_Absyn_Syntax.wp_as_type)
in (
# 498 "FStar.Absyn.SSyntax.fst"
let _29_782 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp)
in (
# 499 "FStar.Absyn.SSyntax.fst"
let _29_784 = (serialize_typ writer ast.FStar_Absyn_Syntax.close_wp_t)
in (
# 500 "FStar.Absyn.SSyntax.fst"
let _29_786 = (serialize_typ writer ast.FStar_Absyn_Syntax.assert_p)
in (
# 501 "FStar.Absyn.SSyntax.fst"
let _29_788 = (serialize_typ writer ast.FStar_Absyn_Syntax.assume_p)
in (
# 502 "FStar.Absyn.SSyntax.fst"
let _29_790 = (serialize_typ writer ast.FStar_Absyn_Syntax.null_wp)
in (serialize_typ writer ast.FStar_Absyn_Syntax.trivial)))))))))))))))))))
and serialize_sigelt : l__Writer  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun writer ast -> (match (ast) with
| FStar_Absyn_Syntax.Sig_pragma (_29_795) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Absyn_Syntax.Sig_tycon (lid, bs, k, l1, l2, qs, _29_804) -> begin
(
# 509 "FStar.Absyn.SSyntax.fst"
let _29_807 = (writer.FStar_Util.write_char 'a')
in (
# 510 "FStar.Absyn.SSyntax.fst"
let _29_809 = (serialize_lident writer lid)
in (
# 510 "FStar.Absyn.SSyntax.fst"
let _29_811 = (serialize_binders writer bs)
in (
# 510 "FStar.Absyn.SSyntax.fst"
let _29_813 = (serialize_knd writer k)
in (
# 511 "FStar.Absyn.SSyntax.fst"
let _29_815 = (serialize_list writer serialize_lident l1)
in (
# 511 "FStar.Absyn.SSyntax.fst"
let _29_817 = (serialize_list writer serialize_lident l2)
in (serialize_list writer serialize_qualifier qs)))))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, bs, k, t, qs, _29_825) -> begin
(
# 514 "FStar.Absyn.SSyntax.fst"
let _29_828 = (writer.FStar_Util.write_char 'b')
in (
# 515 "FStar.Absyn.SSyntax.fst"
let _29_830 = (serialize_lident writer lid)
in (
# 515 "FStar.Absyn.SSyntax.fst"
let _29_832 = (serialize_binders writer bs)
in (
# 515 "FStar.Absyn.SSyntax.fst"
let _29_834 = (serialize_knd writer k)
in (
# 516 "FStar.Absyn.SSyntax.fst"
let _29_836 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))))
end
| FStar_Absyn_Syntax.Sig_datacon (lid1, t, tyc, qs, mutuals, _29_844) -> begin
(
# 518 "FStar.Absyn.SSyntax.fst"
let t' = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(let _108_555 = (let _108_554 = (FStar_Absyn_Syntax.mk_Total (FStar_Absyn_Util.comp_result c))
in (f, _108_554))
in (FStar_Absyn_Syntax.mk_Typ_fun _108_555 None FStar_Absyn_Syntax.dummyRange))
end
| None -> begin
t
end)
in (
# 523 "FStar.Absyn.SSyntax.fst"
let _29_853 = (writer.FStar_Util.write_char 'c')
in (
# 524 "FStar.Absyn.SSyntax.fst"
let _29_855 = (serialize_lident writer lid1)
in (
# 524 "FStar.Absyn.SSyntax.fst"
let _29_857 = (serialize_typ writer t')
in (
# 524 "FStar.Absyn.SSyntax.fst"
let _29_859 = (serialize_tycon writer tyc)
in (
# 525 "FStar.Absyn.SSyntax.fst"
let _29_861 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident mutuals)))))))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, qs, _29_867) -> begin
(
# 528 "FStar.Absyn.SSyntax.fst"
let _29_870 = (writer.FStar_Util.write_char 'd')
in (
# 529 "FStar.Absyn.SSyntax.fst"
let _29_872 = (serialize_lident writer lid)
in (
# 529 "FStar.Absyn.SSyntax.fst"
let _29_874 = (serialize_typ writer t)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, fml, qs, _29_880) -> begin
(
# 531 "FStar.Absyn.SSyntax.fst"
let _29_883 = (writer.FStar_Util.write_char 'e')
in (
# 532 "FStar.Absyn.SSyntax.fst"
let _29_885 = (serialize_lident writer lid)
in (
# 532 "FStar.Absyn.SSyntax.fst"
let _29_887 = (serialize_formula writer fml)
in (serialize_list writer serialize_qualifier qs))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, _29_891, l, quals) -> begin
(
# 534 "FStar.Absyn.SSyntax.fst"
let _29_896 = (writer.FStar_Util.write_char 'f')
in (
# 535 "FStar.Absyn.SSyntax.fst"
let _29_898 = (serialize_letbindings writer lbs)
in (
# 535 "FStar.Absyn.SSyntax.fst"
let _29_900 = (serialize_list writer serialize_lident l)
in (let _108_557 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _29_1 -> (match (_29_1) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _29_905 -> begin
false
end))))
in (writer.FStar_Util.write_bool _108_557)))))
end
| FStar_Absyn_Syntax.Sig_main (e, _29_908) -> begin
(
# 536 "FStar.Absyn.SSyntax.fst"
let _29_911 = (writer.FStar_Util.write_char 'g')
in (serialize_exp writer e))
end
| FStar_Absyn_Syntax.Sig_bundle (l, qs, lids, _29_917) -> begin
(
# 538 "FStar.Absyn.SSyntax.fst"
let _29_920 = (writer.FStar_Util.write_char 'h')
in (
# 539 "FStar.Absyn.SSyntax.fst"
let _29_922 = (serialize_list writer serialize_sigelt l)
in (
# 540 "FStar.Absyn.SSyntax.fst"
let _29_924 = (serialize_list writer serialize_qualifier qs)
in (serialize_list writer serialize_lident lids))))
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _29_928) -> begin
(
# 543 "FStar.Absyn.SSyntax.fst"
let _29_931 = (writer.FStar_Util.write_char 'i')
in (serialize_new_effect writer n))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, bs, c, qs, _29_938) -> begin
(
# 546 "FStar.Absyn.SSyntax.fst"
let _29_941 = (writer.FStar_Util.write_char 'j')
in (
# 547 "FStar.Absyn.SSyntax.fst"
let _29_943 = (serialize_lident writer lid)
in (
# 547 "FStar.Absyn.SSyntax.fst"
let _29_945 = (serialize_binders writer bs)
in (
# 548 "FStar.Absyn.SSyntax.fst"
let _29_947 = (serialize_comp writer c)
in (serialize_list writer serialize_qualifier qs)))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (se, r) -> begin
(
# 550 "FStar.Absyn.SSyntax.fst"
let _29_953 = (writer.FStar_Util.write_char 'k')
in (serialize_sub_effect writer se))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _29_959) -> begin
(
# 553 "FStar.Absyn.SSyntax.fst"
let _29_962 = (writer.FStar_Util.write_char 'l')
in (
# 554 "FStar.Absyn.SSyntax.fst"
let _29_964 = (serialize_lident writer l)
in (
# 555 "FStar.Absyn.SSyntax.fst"
let _29_966 = (serialize_list writer serialize_binder binders)
in (serialize_knd writer k))))
end))

# 558 "FStar.Absyn.SSyntax.fst"
let rec deserialize_new_effect : l__Reader  ->  FStar_Absyn_Syntax.eff_decl = (fun reader -> (let _108_578 = (deserialize_lident reader)
in (let _108_577 = (deserialize_list reader deserialize_binder)
in (let _108_576 = (deserialize_list reader deserialize_qualifier)
in (let _108_575 = (deserialize_knd reader)
in (let _108_574 = (deserialize_typ reader)
in (let _108_573 = (deserialize_typ reader)
in (let _108_572 = (deserialize_typ reader)
in (let _108_571 = (deserialize_typ reader)
in (let _108_570 = (deserialize_typ reader)
in (let _108_569 = (deserialize_typ reader)
in (let _108_568 = (deserialize_typ reader)
in (let _108_567 = (deserialize_typ reader)
in (let _108_566 = (deserialize_typ reader)
in (let _108_565 = (deserialize_typ reader)
in (let _108_564 = (deserialize_typ reader)
in (let _108_563 = (deserialize_typ reader)
in (let _108_562 = (deserialize_typ reader)
in (let _108_561 = (deserialize_typ reader)
in {FStar_Absyn_Syntax.mname = _108_578; FStar_Absyn_Syntax.binders = _108_577; FStar_Absyn_Syntax.qualifiers = _108_576; FStar_Absyn_Syntax.signature = _108_575; FStar_Absyn_Syntax.ret = _108_574; FStar_Absyn_Syntax.bind_wp = _108_573; FStar_Absyn_Syntax.bind_wlp = _108_572; FStar_Absyn_Syntax.if_then_else = _108_571; FStar_Absyn_Syntax.ite_wp = _108_570; FStar_Absyn_Syntax.ite_wlp = _108_569; FStar_Absyn_Syntax.wp_binop = _108_568; FStar_Absyn_Syntax.wp_as_type = _108_567; FStar_Absyn_Syntax.close_wp = _108_566; FStar_Absyn_Syntax.close_wp_t = _108_565; FStar_Absyn_Syntax.assert_p = _108_564; FStar_Absyn_Syntax.assume_p = _108_563; FStar_Absyn_Syntax.null_wp = _108_562; FStar_Absyn_Syntax.trivial = _108_561})))))))))))))))))))
and deserialize_sigelt : l__Reader  ->  FStar_Absyn_Syntax.sigelt = (fun reader -> (match ((reader.FStar_Util.read_char ())) with
| 'a' -> begin
(let _108_586 = (let _108_585 = (deserialize_lident reader)
in (let _108_584 = (deserialize_binders reader)
in (let _108_583 = (deserialize_knd reader)
in (let _108_582 = (deserialize_list reader deserialize_lident)
in (let _108_581 = (deserialize_list reader deserialize_lident)
in (let _108_580 = (deserialize_list reader deserialize_qualifier)
in (_108_585, _108_584, _108_583, _108_582, _108_581, _108_580, FStar_Absyn_Syntax.dummyRange)))))))
in FStar_Absyn_Syntax.Sig_tycon (_108_586))
end
| 'b' -> begin
(let _108_592 = (let _108_591 = (deserialize_lident reader)
in (let _108_590 = (deserialize_binders reader)
in (let _108_589 = (deserialize_knd reader)
in (let _108_588 = (deserialize_typ reader)
in (let _108_587 = (deserialize_list reader deserialize_qualifier)
in (_108_591, _108_590, _108_589, _108_588, _108_587, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_108_592))
end
| 'c' -> begin
(let _108_598 = (let _108_597 = (deserialize_lident reader)
in (let _108_596 = (deserialize_typ reader)
in (let _108_595 = (deserialize_tycon reader)
in (let _108_594 = (deserialize_list reader deserialize_qualifier)
in (let _108_593 = (deserialize_list reader deserialize_lident)
in (_108_597, _108_596, _108_595, _108_594, _108_593, FStar_Absyn_Syntax.dummyRange))))))
in FStar_Absyn_Syntax.Sig_datacon (_108_598))
end
| 'd' -> begin
(let _108_602 = (let _108_601 = (deserialize_lident reader)
in (let _108_600 = (deserialize_typ reader)
in (let _108_599 = (deserialize_list reader deserialize_qualifier)
in (_108_601, _108_600, _108_599, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_val_decl (_108_602))
end
| 'e' -> begin
(let _108_606 = (let _108_605 = (deserialize_lident reader)
in (let _108_604 = (deserialize_formula reader)
in (let _108_603 = (deserialize_list reader deserialize_qualifier)
in (_108_605, _108_604, _108_603, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_assume (_108_606))
end
| 'f' -> begin
(let _108_610 = (let _108_609 = (deserialize_letbindings reader)
in (let _108_608 = (deserialize_list reader deserialize_lident)
in (let _108_607 = if (reader.FStar_Util.read_bool ()) then begin
(FStar_Absyn_Syntax.HasMaskedEffect)::[]
end else begin
[]
end
in (_108_609, FStar_Absyn_Syntax.dummyRange, _108_608, _108_607))))
in FStar_Absyn_Syntax.Sig_let (_108_610))
end
| 'g' -> begin
(let _108_612 = (let _108_611 = (deserialize_exp reader)
in (_108_611, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_main (_108_612))
end
| 'h' -> begin
(let _108_616 = (let _108_615 = (deserialize_list reader deserialize_sigelt)
in (let _108_614 = (deserialize_list reader deserialize_qualifier)
in (let _108_613 = (deserialize_list reader deserialize_lident)
in (_108_615, _108_614, _108_613, FStar_Absyn_Syntax.dummyRange))))
in FStar_Absyn_Syntax.Sig_bundle (_108_616))
end
| 'i' -> begin
(let _108_618 = (let _108_617 = (deserialize_new_effect reader)
in (_108_617, FStar_Absyn_Syntax.dummyRange))
in FStar_Absyn_Syntax.Sig_new_effect (_108_618))
end
| ('j') | ('k') | ('l') -> begin
(FStar_All.failwith "TODO")
end
| _29_983 -> begin
(parse_error ())
end))

# 607 "FStar.Absyn.SSyntax.fst"
let serialize_sigelts : l__Writer  ->  FStar_Absyn_Syntax.sigelts  ->  Prims.unit = (fun writer ast -> (serialize_list writer serialize_sigelt ast))

# 608 "FStar.Absyn.SSyntax.fst"
let deserialize_sigelts : l__Reader  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun reader -> (deserialize_list reader deserialize_sigelt))

# 610 "FStar.Absyn.SSyntax.fst"
let serialize_modul : l__Writer  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun writer ast -> (
# 611 "FStar.Absyn.SSyntax.fst"
let _29_989 = (serialize_lident writer ast.FStar_Absyn_Syntax.name)
in (
# 612 "FStar.Absyn.SSyntax.fst"
let _29_991 = (serialize_sigelts writer [])
in (
# 613 "FStar.Absyn.SSyntax.fst"
let _29_993 = (serialize_sigelts writer ast.FStar_Absyn_Syntax.exports)
in (writer.FStar_Util.write_bool ast.FStar_Absyn_Syntax.is_interface)))))

# 616 "FStar.Absyn.SSyntax.fst"
let deserialize_modul : l__Reader  ->  FStar_Absyn_Syntax.modul = (fun reader -> (
# 617 "FStar.Absyn.SSyntax.fst"
let m = (let _108_634 = (deserialize_lident reader)
in (let _108_633 = (deserialize_sigelts reader)
in (let _108_632 = (deserialize_sigelts reader)
in (let _108_631 = (reader.FStar_Util.read_bool ())
in {FStar_Absyn_Syntax.name = _108_634; FStar_Absyn_Syntax.declarations = _108_633; FStar_Absyn_Syntax.exports = _108_632; FStar_Absyn_Syntax.is_interface = _108_631; FStar_Absyn_Syntax.is_deserialized = true}))))
in (
# 622 "FStar.Absyn.SSyntax.fst"
let _29_997 = m
in {FStar_Absyn_Syntax.name = _29_997.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = m.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.exports = _29_997.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _29_997.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _29_997.FStar_Absyn_Syntax.is_deserialized})))




