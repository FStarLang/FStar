
open Prims
# 24 "FStar.Extraction.ML.Util.fst"
let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))

# 29 "FStar.Extraction.ML.Util.fst"
let mlconst_of_const : FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun sctt -> (match (sctt) with
| (FStar_Const.Const_range (_)) | (FStar_Const.Const_effect) -> begin
(FStar_All.failwith "Unsupported constant")
end
| FStar_Const.Const_unit -> begin
FStar_Extraction_ML_Syntax.MLC_Unit
end
| FStar_Const.Const_char (c) -> begin
FStar_Extraction_ML_Syntax.MLC_Char (c)
end
| FStar_Const.Const_uint8 (c) -> begin
FStar_Extraction_ML_Syntax.MLC_Byte (c)
end
| FStar_Const.Const_int (c) -> begin
FStar_Extraction_ML_Syntax.MLC_Int (c)
end
| FStar_Const.Const_int32 (i) -> begin
FStar_Extraction_ML_Syntax.MLC_Int32 (i)
end
| FStar_Const.Const_int64 (i) -> begin
FStar_Extraction_ML_Syntax.MLC_Int64 (i)
end
| FStar_Const.Const_bool (b) -> begin
FStar_Extraction_ML_Syntax.MLC_Bool (b)
end
| FStar_Const.Const_float (d) -> begin
FStar_Extraction_ML_Syntax.MLC_Float (d)
end
| FStar_Const.Const_bytearray (bytes, _59_35) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, _59_40) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end))

# 49 "FStar.Extraction.ML.Util.fst"
let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> (FStar_All.try_with (fun _59_46 -> (match (()) with
| () -> begin
(mlconst_of_const c)
end)) (fun _59_45 -> (match (_59_45) with
| _59_49 -> begin
(let _140_14 = (let _140_13 = (FStar_Range.string_of_range p)
in (let _140_12 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _140_13 _140_12)))
in (FStar_All.failwith _140_14))
end))))

# 53 "FStar.Extraction.ML.Util.fst"
let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _59_59 -> (match (_59_59) with
| (y, _59_58) -> begin
(y = x)
end)) subst)) with
| Some (ts) -> begin
(Prims.snd ts)
end
| None -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _140_22 = (let _140_21 = (subst_aux subst t1)
in (let _140_20 = (subst_aux subst t2)
in (_140_21, f, _140_20)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_140_22))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _140_24 = (let _140_23 = (FStar_List.map (subst_aux subst) args)
in (_140_23, path))
in FStar_Extraction_ML_Syntax.MLTY_Named (_140_24))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _140_25 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_140_25))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

# 63 "FStar.Extraction.ML.Util.fst"
let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun _59_77 args -> (match (_59_77) with
| (formals, t) -> begin
if ((FStar_List.length formals) <> (FStar_List.length args)) then begin
(FStar_All.failwith "Substitution must be fully applied: instantiation of %A failed; got %A\n")
end else begin
(let _140_30 = (FStar_List.zip formals args)
in (subst_aux _140_30 t))
end
end))

# 68 "FStar.Extraction.ML.Util.fst"
let delta_unfold : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g _59_1 -> (match (_59_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _140_35 = (subst ts args)
in Some (_140_35))
end
| _59_88 -> begin
None
end)
end
| _59_90 -> begin
None
end))

# 76 "FStar.Extraction.ML.Util.fst"
let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match ((f, f')) with
| (FStar_Extraction_ML_Syntax.E_PURE, _59_95) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| _59_104 -> begin
false
end))

# 82 "FStar.Extraction.ML.Util.fst"
let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun _59_2 -> (match (_59_2) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

# 87 "FStar.Extraction.ML.Util.fst"
let join : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag = (fun f f' -> (match ((f, f')) with
| ((FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_PURE)) | ((FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_IMPURE)) | ((FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE)) -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_PURE) -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_PURE) -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| _59_133 -> begin
(let _140_46 = (FStar_Util.format2 "Impossible: Inconsistent effects %s and %s" (eff_to_string f) (eff_to_string f'))
in (FStar_All.failwith _140_46))
end))

# 97 "FStar.Extraction.ML.Util.fst"
let join_l : FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun fs -> (FStar_List.fold_left join FStar_Extraction_ML_Syntax.E_PURE fs))

# 99 "FStar.Extraction.ML.Util.fst"
let mk_ty_fun = (fun _0_5 -> (FStar_List.fold_right (fun _59_138 t -> (match (_59_138) with
| (_59_136, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((t0, FStar_Extraction_ML_Syntax.E_PURE, t))
end))))

# 101 "FStar.Extraction.ML.Util.fst"
let rec type_leq_c : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g e t t' -> (match ((t, t')) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
if ((Prims.fst x) = (Prims.fst y)) then begin
(true, e)
end else begin
(false, None)
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(
# 117 "FStar.Extraction.ML.Util.fst"
let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| _59_165 -> begin
(
# 120 "FStar.Extraction.ML.Util.fst"
let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((FStar_List.append xs ys), body))
end
| _59_171 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((xs, body))
end)
in (let _140_68 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.ty)
in (FStar_Extraction_ML_Syntax.with_ty _140_68 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (x::xs, body); FStar_Extraction_ML_Syntax.ty = _59_176; FStar_Extraction_ML_Syntax.loc = _59_174}) -> begin
if ((type_leq g t1' t1) && (eff_leq f f')) then begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
if (type_leq g t2 t2') then begin
(
# 131 "FStar.Extraction.ML.Util.fst"
let body = if (type_leq g t2 FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t2'))))
end
in (let _140_72 = (let _140_71 = (let _140_70 = (let _140_69 = ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.ty)
in (FStar_Extraction_ML_Syntax.with_ty _140_69))
in (FStar_All.pipe_left _140_70 (FStar_Extraction_ML_Syntax.MLE_Fun (((x)::[], body)))))
in Some (_140_71))
in (true, _140_72)))
end else begin
(false, None)
end
end else begin
(
# 136 "FStar.Extraction.ML.Util.fst"
let _59_188 = (let _140_75 = (let _140_74 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _140_73 -> Some (_140_73)) _140_74))
in (type_leq_c g _140_75 t2 t2'))
in (match (_59_188) with
| (ok, body) -> begin
(
# 137 "FStar.Extraction.ML.Util.fst"
let res = (match (body) with
| Some (body) -> begin
(let _140_76 = (mk_fun ((x)::[]) body)
in Some (_140_76))
end
| _59_192 -> begin
None
end)
in (ok, res))
end))
end
end else begin
(false, None)
end
end
| _59_195 -> begin
if (((type_leq g t1' t1) && (eff_leq f f')) && (type_leq g t2 t2')) then begin
(true, e)
end else begin
(false, None)
end
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
if (path = path') then begin
if (FStar_List.forall2 (type_leq g) args args') then begin
(true, e)
end else begin
(false, None)
end
end else begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(type_leq_c g e t t')
end
| None -> begin
(match ((delta_unfold g t')) with
| None -> begin
(false, None)
end
| Some (t') -> begin
(type_leq_c g e t t')
end)
end)
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
if (FStar_List.forall2 (type_leq g) ts ts') then begin
(true, e)
end else begin
(false, None)
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
(true, e)
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (_59_220), _59_223) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(type_leq_c g e t t')
end
| _59_228 -> begin
(false, None)
end)
end
| (_59_230, FStar_Extraction_ML_Syntax.MLTY_Named (_59_232)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(type_leq_c g e t t')
end
| _59_238 -> begin
(false, None)
end)
end
| _59_240 -> begin
(false, None)
end))
and type_leq : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (let _140_80 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right _140_80 Prims.fst)))

# 184 "FStar.Extraction.ML.Util.fst"
let unit_binder : FStar_Absyn_Syntax.binder = (
# 187 "FStar.Extraction.ML.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))

# 188 "FStar.Extraction.ML.Util.fst"
let is_type_abstraction = (fun _59_3 -> (match (_59_3) with
| (FStar_Util.Inl (_59_249), _59_252)::_59_247 -> begin
true
end
| _59_256 -> begin
false
end))

# 192 "FStar.Extraction.ML.Util.fst"
let mkTypFun : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.FStar_Absyn_Syntax.pos))

# 195 "FStar.Extraction.ML.Util.fst"
let mkTypApp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.FStar_Absyn_Syntax.pos))

# 198 "FStar.Extraction.ML.Util.fst"
let tbinder_prefix : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun t -> (match ((let _140_96 = (FStar_Absyn_Util.compress_typ t)
in _140_96.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _59_4 -> (match (_59_4) with
| (FStar_Util.Inr (_59_270), _59_273) -> begin
true
end
| _59_276 -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some (bs, b, rest) -> begin
(let _140_98 = (mkTypFun ((b)::rest) c t)
in (bs, _140_98))
end)
end
| _59_284 -> begin
([], t)
end))

# 209 "FStar.Extraction.ML.Util.fst"
let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _59_287 -> (match (_59_287) with
| (ns, n) -> begin
if (ns = ("Prims")::[]) then begin
(match (n) with
| "MkTuple2" -> begin
Some (2)
end
| "MkTuple3" -> begin
Some (3)
end
| "MkTuple4" -> begin
Some (4)
end
| "MkTuple5" -> begin
Some (5)
end
| "MkTuple6" -> begin
Some (6)
end
| "MkTuple7" -> begin
Some (7)
end
| "MkTuple8" -> begin
Some (8)
end
| _59_296 -> begin
None
end)
end else begin
None
end
end))

# 223 "FStar.Extraction.ML.Util.fst"
let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| _59_305 -> begin
e
end)
end
| _59_307 -> begin
e
end))

# 230 "FStar.Extraction.ML.Util.fst"
let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun _59_5 -> (match (_59_5) with
| f::_59_310 -> begin
(
# 234 "FStar.Extraction.ML.Util.fst"
let _59_316 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (_59_316) with
| (ns, _59_315) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| _59_319 -> begin
(FStar_All.failwith "impos")
end))

# 236 "FStar.Extraction.ML.Util.fst"
let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> (f.FStar_Ident.ident.FStar_Ident.idText, e)) fs vs))

# 238 "FStar.Extraction.ML.Util.fst"
let resugar_pat : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _59_333 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_59_335, fns)) -> begin
(
# 247 "FStar.Extraction.ML.Util.fst"
let p = (record_field_path fns)
in (
# 248 "FStar.Extraction.ML.Util.fst"
let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _59_343 -> begin
p
end)
end)
end
| _59_345 -> begin
p
end))

# 252 "FStar.Extraction.ML.Util.fst"
let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _59_348 -> (match (_59_348) with
| (ns, n) -> begin
if (ns = ("Prims")::[]) then begin
(match (n) with
| "Tuple2" -> begin
Some (2)
end
| "Tuple3" -> begin
Some (3)
end
| "Tuple4" -> begin
Some (4)
end
| "Tuple5" -> begin
Some (5)
end
| "Tuple6" -> begin
Some (6)
end
| "Tuple7" -> begin
Some (7)
end
| "Tuple8" -> begin
Some (8)
end
| _59_357 -> begin
None
end)
end else begin
None
end
end))

# 266 "FStar.Extraction.ML.Util.fst"
let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _59_366 -> begin
t
end)
end
| _59_368 -> begin
t
end))

# 274 "FStar.Extraction.ML.Util.fst"
let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun _59_369 -> (match (()) with
| () -> begin
((let _140_120 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.get _140_120)) = "FSharp")
end))

# 276 "FStar.Extraction.ML.Util.fst"
let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> if (codegen_fsharp ()) then begin
(FStar_String.concat "." ns)
end else begin
(FStar_String.concat "_" ns)
end)

# 280 "FStar.Extraction.ML.Util.fst"
let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun _59_373 -> (match (_59_373) with
| (ns, n) -> begin
if (codegen_fsharp ()) then begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end else begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end
end))

# 284 "FStar.Extraction.ML.Util.fst"
let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (let _140_128 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in (_140_128, l.FStar_Ident.ident.FStar_Ident.idText)))

# 285 "FStar.Extraction.ML.Util.fst"
let rec erasableType : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> if (FStar_Extraction_ML_Env.erasableTypeNoDelta t) then begin
true
end else begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(erasableType g t)
end
| None -> begin
false
end)
end)

# 293 "FStar.Extraction.ML.Util.fst"
let rec eraseTypeDeep : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
if (etag = FStar_Extraction_ML_Syntax.E_PURE) then begin
(let _140_139 = (let _140_138 = (eraseTypeDeep g tyd)
in (let _140_137 = (eraseTypeDeep g tycd)
in (_140_138, etag, _140_137)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_140_139))
end else begin
t
end
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
if (erasableType g t) then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
(let _140_141 = (let _140_140 = (FStar_List.map (eraseTypeDeep g) lty)
in (_140_140, mlp))
in FStar_Extraction_ML_Syntax.MLTY_Named (_140_141))
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _140_142 = (FStar_List.map (eraseTypeDeep g) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_140_142))
end
| _59_395 -> begin
t
end))

# 300 "FStar.Extraction.ML.Util.fst"
let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name ((("Prims")::[], "op_Equality"))))

# 302 "FStar.Extraction.ML.Util.fst"
let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (let _140_144 = (let _140_143 = ((mk_ty_fun ()) (((("x", 0), FStar_Extraction_ML_Syntax.ml_bool_ty))::((("y", 0), FStar_Extraction_ML_Syntax.ml_bool_ty))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty _140_143))
in (FStar_All.pipe_left _140_144 (FStar_Extraction_ML_Syntax.MLE_Name ((("Prims")::[], "op_AmpAmp")))))

# 303 "FStar.Extraction.ML.Util.fst"
let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App ((prims_op_amp_amp, (e1)::(e2)::[])))))

# 304 "FStar.Extraction.ML.Util.fst"
let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option = (fun e1 e2 -> (match ((e1, e2)) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
(let _140_153 = (conjoin x y)
in Some (_140_153))
end))




