
open Prims
# 26 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))

# 32 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let mlconst_of_const : FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun sctt -> (match (sctt) with
| FStar_Const.Const_effect -> begin
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
| FStar_Const.Const_bytearray (bytes, _75_32) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, _75_37) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end))

# 50 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> (FStar_All.try_with (fun _75_43 -> (match (()) with
| () -> begin
(mlconst_of_const c)
end)) (fun _75_42 -> (match (_75_42) with
| _75_46 -> begin
(let _177_14 = (let _177_13 = (FStar_Range.string_of_range p)
in (let _177_12 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _177_13 _177_12)))
in (FStar_All.failwith _177_14))
end))))

# 54 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _75_56 -> (match (_75_56) with
| (y, _75_55) -> begin
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
(let _177_22 = (let _177_21 = (subst_aux subst t1)
in (let _177_20 = (subst_aux subst t2)
in (_177_21, f, _177_20)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_177_22))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _177_24 = (let _177_23 = (FStar_List.map (subst_aux subst) args)
in (_177_23, path))
in FStar_Extraction_ML_Syntax.MLTY_Named (_177_24))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _177_25 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_177_25))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

# 64 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun _75_74 args -> (match (_75_74) with
| (formals, t) -> begin
if ((FStar_List.length formals) <> (FStar_List.length args)) then begin
(FStar_All.failwith "Substitution must be fully applied: instantiation of %A failed; got %A\n")
end else begin
(let _177_30 = (FStar_List.zip formals args)
in (subst_aux _177_30 t))
end
end))

# 69 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let delta_unfold : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g _75_1 -> (match (_75_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _177_35 = (subst ts args)
in Some (_177_35))
end
| _75_85 -> begin
None
end)
end
| _75_87 -> begin
None
end))

# 77 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match ((f, f')) with
| (FStar_Extraction_ML_Syntax.E_PURE, _75_92) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| _75_101 -> begin
false
end))

# 83 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun _75_2 -> (match (_75_2) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

# 88 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

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
| _75_130 -> begin
(let _177_46 = (FStar_Util.format2 "Impossible: Inconsistent effects %s and %s" (eff_to_string f) (eff_to_string f'))
in (FStar_All.failwith _177_46))
end))

# 98 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let join_l : FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun fs -> (FStar_List.fold_left join FStar_Extraction_ML_Syntax.E_PURE fs))

# 100 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let mk_ty_fun = (fun _102_95 -> (FStar_List.fold_right (fun _75_135 t -> (match (_75_135) with
| (_75_133, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((t0, FStar_Extraction_ML_Syntax.E_PURE, t))
end))))

# 108 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let rec type_leq_c : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g e t t' -> (match ((t, t')) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
if ((Prims.fst x) = (Prims.fst y)) then begin
(true, e)
end else begin
(false, None)
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| _75_162 -> begin
(let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((FStar_List.append xs ys), body))
end
| _75_168 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((xs, body))
end)
in (let _177_68 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.ty)
in (FStar_Extraction_ML_Syntax.with_ty _177_68 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (x::xs, body); FStar_Extraction_ML_Syntax.ty = _75_171}) -> begin
if ((type_leq g t1' t1) && (eff_leq f f')) then begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
if (type_leq g t2 t2') then begin
(let body = if (type_leq g t2 FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t2'))))
end
in (let _177_72 = (let _177_71 = (let _177_70 = (let _177_69 = ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.ty)
in (FStar_Extraction_ML_Syntax.with_ty _177_69))
in (FStar_All.pipe_left _177_70 (FStar_Extraction_ML_Syntax.MLE_Fun (((x)::[], body)))))
in Some (_177_71))
in (true, _177_72)))
end else begin
(false, None)
end
end else begin
(let _75_183 = (let _177_75 = (let _177_74 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _177_73 -> Some (_177_73)) _177_74))
in (type_leq_c g _177_75 t2 t2'))
in (match (_75_183) with
| (ok, body) -> begin
(let res = (match (body) with
| Some (body) -> begin
(let _177_76 = (mk_fun ((x)::[]) body)
in Some (_177_76))
end
| _75_187 -> begin
None
end)
in (ok, res))
end))
end
end else begin
(false, None)
end
end
| _75_190 -> begin
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
| (FStar_Extraction_ML_Syntax.MLTY_Named (_75_215), _75_218) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(type_leq_c g e t t')
end
| _75_223 -> begin
(false, None)
end)
end
| (_75_225, FStar_Extraction_ML_Syntax.MLTY_Named (_75_227)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(type_leq_c g e t t')
end
| _75_233 -> begin
(false, None)
end)
end
| _75_235 -> begin
(false, None)
end))
and type_leq : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (let _177_80 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right _177_80 Prims.fst)))

# 185 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let unit_binder : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, FStar_Absyn_Syntax.bvvar) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) = (let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))

# 189 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let is_type_abstraction = (fun _75_3 -> (match (_75_3) with
| (FStar_Util.Inl (_75_244), _75_247)::_75_242 -> begin
true
end
| _75_251 -> begin
false
end))

# 193 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let mkTypFun : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.FStar_Absyn_Syntax.pos))

# 196 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let mkTypApp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.FStar_Absyn_Syntax.pos))

# 201 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let tbinder_prefix : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun t -> (match ((let _177_96 = (FStar_Absyn_Util.compress_typ t)
in _177_96.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _75_4 -> (match (_75_4) with
| (FStar_Util.Inr (_75_265), _75_268) -> begin
true
end
| _75_271 -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some (bs, b, rest) -> begin
(let _177_98 = (mkTypFun ((b)::rest) c t)
in (bs, _177_98))
end)
end
| _75_279 -> begin
([], t)
end))

# 211 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _75_282 -> (match (_75_282) with
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
| _75_291 -> begin
None
end)
end else begin
None
end
end))

# 224 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| _75_300 -> begin
e
end)
end
| _75_302 -> begin
e
end))

# 231 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun _75_5 -> (match (_75_5) with
| f::_75_305 -> begin
(let _75_311 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (_75_311) with
| (ns, _75_310) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| _75_314 -> begin
(FStar_All.failwith "impos")
end))

# 237 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> (f.FStar_Ident.ident.FStar_Ident.idText, e)) fs vs))

# 239 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let resugar_pat : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _75_328 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_75_330, fns)) -> begin
(let p = (record_field_path fns)
in (let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _75_338 -> begin
p
end)
end)
end
| _75_340 -> begin
p
end))

# 254 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _75_343 -> (match (_75_343) with
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
| _75_352 -> begin
None
end)
end else begin
None
end
end))

# 267 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _75_361 -> begin
t
end)
end
| _75_363 -> begin
t
end))

# 275 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun _75_364 -> (match (()) with
| () -> begin
((let _177_120 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.get _177_120)) = "FSharp")
end))

# 276 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> if (codegen_fsharp ()) then begin
(FStar_String.concat "." ns)
end else begin
(FStar_String.concat "_" ns)
end)

# 280 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun _75_368 -> (match (_75_368) with
| (ns, n) -> begin
if (codegen_fsharp ()) then begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end else begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end
end))

# 284 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (let _177_128 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in (_177_128, l.FStar_Ident.ident.FStar_Ident.idText)))

# 286 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

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

# 294 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let rec eraseTypeDeep : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
if (etag = FStar_Extraction_ML_Syntax.E_PURE) then begin
(let _177_139 = (let _177_138 = (eraseTypeDeep g tyd)
in (let _177_137 = (eraseTypeDeep g tycd)
in (_177_138, etag, _177_137)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_177_139))
end else begin
t
end
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
if (erasableType g t) then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
(let _177_141 = (let _177_140 = (FStar_List.map (eraseTypeDeep g) lty)
in (_177_140, mlp))
in FStar_Extraction_ML_Syntax.MLTY_Named (_177_141))
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _177_142 = (FStar_List.map (eraseTypeDeep g) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_177_142))
end
| _75_390 -> begin
t
end))

# 301 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name ((("Prims")::[], "op_Equality"))))

# 302 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (let _177_144 = (let _177_143 = ((mk_ty_fun ()) (((("x", 0), FStar_Extraction_ML_Syntax.ml_bool_ty))::((("y", 0), FStar_Extraction_ML_Syntax.ml_bool_ty))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty _177_143))
in (FStar_All.pipe_left _177_144 (FStar_Extraction_ML_Syntax.MLE_Name ((("Prims")::[], "op_AmpAmp")))))

# 303 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App ((prims_op_amp_amp, (e1)::(e2)::[])))))

# 304 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\util.fs"

let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option = (fun e1 e2 -> (match ((e1, e2)) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
(let _177_153 = (conjoin x y)
in Some (_177_153))
end))




