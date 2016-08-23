
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
| FStar_Const.Const_int (s, i) -> begin
FStar_Extraction_ML_Syntax.MLC_Int (((s), (i)))
end
| FStar_Const.Const_bool (b) -> begin
FStar_Extraction_ML_Syntax.MLC_Bool (b)
end
| FStar_Const.Const_float (d) -> begin
FStar_Extraction_ML_Syntax.MLC_Float (d)
end
| FStar_Const.Const_bytearray (bytes, _73_32) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, _73_37) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
(FStar_All.failwith "Unhandled constant: reify/reflect")
end))

# 50 "FStar.Extraction.ML.Util.fst"
let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> try
(match (()) with
| () -> begin
(mlconst_of_const c)
end)
with
| _73_50 -> begin
(let _166_14 = (let _166_13 = (FStar_Range.string_of_range p)
in (let _166_12 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _166_13 _166_12)))
in (FStar_All.failwith _166_14))
end)

# 54 "FStar.Extraction.ML.Util.fst"
let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _73_60 -> (match (_73_60) with
| (y, _73_59) -> begin
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
(let _166_22 = (let _166_21 = (subst_aux subst t1)
in (let _166_20 = (subst_aux subst t2)
in ((_166_21), (f), (_166_20))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_166_22))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _166_24 = (let _166_23 = (FStar_List.map (subst_aux subst) args)
in ((_166_23), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_166_24))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _166_25 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_166_25))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

# 64 "FStar.Extraction.ML.Util.fst"
let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun _73_78 args -> (match (_73_78) with
| (formals, t) -> begin
if ((FStar_List.length formals) <> (FStar_List.length args)) then begin
(FStar_All.failwith "Substitution must be fully applied")
end else begin
(let _166_30 = (FStar_List.zip formals args)
in (subst_aux _166_30 t))
end
end))

# 69 "FStar.Extraction.ML.Util.fst"
let delta_unfold : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g _73_1 -> (match (_73_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _166_35 = (subst ts args)
in Some (_166_35))
end
| _73_89 -> begin
None
end)
end
| _73_91 -> begin
None
end))

# 77 "FStar.Extraction.ML.Util.fst"
let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g _73_2 -> (match (_73_2) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_UEnv.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _166_40 = (subst ts args)
in Some (_166_40))
end
| _73_101 -> begin
None
end)
end
| _73_103 -> begin
None
end))

# 88 "FStar.Extraction.ML.Util.fst"
let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, _73_108) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| _73_117 -> begin
false
end))

# 95 "FStar.Extraction.ML.Util.fst"
let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun _73_3 -> (match (_73_3) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

# 100 "FStar.Extraction.ML.Util.fst"
let join : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag = (fun f f' -> (match (((f), (f'))) with
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
| _73_146 -> begin
(let _166_51 = (FStar_Util.format2 "Impossible: Inconsistent effects %s and %s" (eff_to_string f) (eff_to_string f'))
in (FStar_All.failwith _166_51))
end))

# 110 "FStar.Extraction.ML.Util.fst"
let join_l : FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun fs -> (FStar_List.fold_left join FStar_Extraction_ML_Syntax.E_PURE fs))

# 112 "FStar.Extraction.ML.Util.fst"
let mk_ty_fun = (fun _0_5 -> (FStar_List.fold_right (fun _73_151 t -> (match (_73_151) with
| (_73_149, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((t0), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end))))

# 114 "FStar.Extraction.ML.Util.fst"
type unfold_t =
FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option

# 116 "FStar.Extraction.ML.Util.fst"
let rec type_leq_c : unfold_t  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun unfold e t t' -> (match (((t), (t'))) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
if ((Prims.fst x) = (Prims.fst y)) then begin
((true), (e))
end else begin
((false), (None))
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(
# 132 "FStar.Extraction.ML.Util.fst"
let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| _73_178 -> begin
(
# 135 "FStar.Extraction.ML.Util.fst"
let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body)))
end
| _73_184 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (let _166_75 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty _166_75 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = _73_189; FStar_Extraction_ML_Syntax.loc = _73_187}) -> begin
if ((type_leq unfold t1' t1) && (eff_leq f f')) then begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
if (type_leq unfold t2 t2') then begin
(
# 146 "FStar.Extraction.ML.Util.fst"
let body = if (type_leq unfold t2 FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end
in (let _166_79 = (let _166_78 = (let _166_77 = (let _166_76 = ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty _166_76))
in (FStar_All.pipe_left _166_77 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body))))))
in Some (_166_78))
in ((true), (_166_79))))
end else begin
((false), (None))
end
end else begin
(
# 151 "FStar.Extraction.ML.Util.fst"
let _73_201 = (let _166_82 = (let _166_81 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _166_80 -> Some (_166_80)) _166_81))
in (type_leq_c unfold _166_82 t2 t2'))
in (match (_73_201) with
| (ok, body) -> begin
(
# 152 "FStar.Extraction.ML.Util.fst"
let res = (match (body) with
| Some (body) -> begin
(let _166_83 = (mk_fun ((x)::[]) body)
in Some (_166_83))
end
| _73_205 -> begin
None
end)
in ((ok), (res)))
end))
end
end else begin
((false), (None))
end
end
| _73_208 -> begin
if (((type_leq unfold t1' t1) && (eff_leq f f')) && (type_leq unfold t2 t2')) then begin
((true), (e))
end else begin
((false), (None))
end
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
if (path = path') then begin
if (FStar_List.forall2 (type_leq unfold) args args') then begin
((true), (e))
end else begin
((false), (None))
end
end else begin
(match ((unfold t)) with
| Some (t) -> begin
(type_leq_c unfold e t t')
end
| None -> begin
(match ((unfold t')) with
| None -> begin
((false), (None))
end
| Some (t') -> begin
(type_leq_c unfold e t t')
end)
end)
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
if (FStar_List.forall2 (type_leq unfold) ts ts') then begin
((true), (e))
end else begin
((false), (None))
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (_73_233), _73_236) -> begin
(match ((unfold t)) with
| Some (t) -> begin
(type_leq_c unfold e t t')
end
| _73_241 -> begin
((false), (None))
end)
end
| (_73_243, FStar_Extraction_ML_Syntax.MLTY_Named (_73_245)) -> begin
(match ((unfold t')) with
| Some (t') -> begin
(type_leq_c unfold e t t')
end
| _73_251 -> begin
((false), (None))
end)
end
| _73_253 -> begin
((false), (None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (let _166_87 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right _166_87 Prims.fst)))

# 199 "FStar.Extraction.ML.Util.fst"
let unit_binder : FStar_Absyn_Syntax.binder = (
# 202 "FStar.Extraction.ML.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))

# 203 "FStar.Extraction.ML.Util.fst"
let is_type_abstraction = (fun _73_4 -> (match (_73_4) with
| ((FStar_Util.Inl (_73_262), _73_265))::_73_260 -> begin
true
end
| _73_269 -> begin
false
end))

# 207 "FStar.Extraction.ML.Util.fst"
let mkTypFun : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None original.FStar_Absyn_Syntax.pos))

# 210 "FStar.Extraction.ML.Util.fst"
let mkTypApp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app ((typ), (arrgs)) None original.FStar_Absyn_Syntax.pos))

# 213 "FStar.Extraction.ML.Util.fst"
let tbinder_prefix : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun t -> (match ((let _166_103 = (FStar_Absyn_Util.compress_typ t)
in _166_103.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _73_5 -> (match (_73_5) with
| (FStar_Util.Inr (_73_283), _73_286) -> begin
true
end
| _73_289 -> begin
false
end)) bs)) with
| None -> begin
((bs), (t))
end
| Some (bs, b, rest) -> begin
(let _166_105 = (mkTypFun ((b)::rest) c t)
in ((bs), (_166_105)))
end)
end
| _73_297 -> begin
(([]), (t))
end))

# 224 "FStar.Extraction.ML.Util.fst"
let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _73_300 -> (match (_73_300) with
| (ns, n) -> begin
if (ns = ("Prims")::[]) then begin
if (FStar_Options.universes ()) then begin
(match (n) with
| "Mktuple2" -> begin
Some (2)
end
| "Mktuple3" -> begin
Some (3)
end
| "Mktuple4" -> begin
Some (4)
end
| "Mktuple5" -> begin
Some (5)
end
| "Mktuple6" -> begin
Some (6)
end
| "Mktuple7" -> begin
Some (7)
end
| "Mktuple8" -> begin
Some (8)
end
| _73_309 -> begin
None
end)
end else begin
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
| _73_318 -> begin
None
end)
end
end else begin
None
end
end))

# 248 "FStar.Extraction.ML.Util.fst"
let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| _73_327 -> begin
e
end)
end
| _73_329 -> begin
e
end))

# 255 "FStar.Extraction.ML.Util.fst"
let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun _73_6 -> (match (_73_6) with
| (f)::_73_332 -> begin
(
# 259 "FStar.Extraction.ML.Util.fst"
let _73_338 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (_73_338) with
| (ns, _73_337) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| _73_341 -> begin
(FStar_All.failwith "impos")
end))

# 261 "FStar.Extraction.ML.Util.fst"
let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))

# 263 "FStar.Extraction.ML.Util.fst"
let resugar_pat : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _73_355 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_73_357, fns)) -> begin
(
# 272 "FStar.Extraction.ML.Util.fst"
let p = (record_field_path fns)
in (
# 273 "FStar.Extraction.ML.Util.fst"
let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((p), (fs)))))
end
| _73_365 -> begin
p
end)
end)
end
| _73_367 -> begin
p
end))

# 277 "FStar.Extraction.ML.Util.fst"
let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _73_370 -> (match (_73_370) with
| (ns, n) -> begin
if (ns = ("Prims")::[]) then begin
if (FStar_Options.universes ()) then begin
(match (n) with
| "tuple2" -> begin
Some (2)
end
| "tuple3" -> begin
Some (3)
end
| "tuple4" -> begin
Some (4)
end
| "tuple5" -> begin
Some (5)
end
| "tuple6" -> begin
Some (6)
end
| "tuple7" -> begin
Some (7)
end
| "tuple8" -> begin
Some (8)
end
| _73_379 -> begin
None
end)
end else begin
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
| _73_388 -> begin
None
end)
end
end else begin
None
end
end))

# 301 "FStar.Extraction.ML.Util.fst"
let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _73_397 -> begin
t
end)
end
| _73_399 -> begin
t
end))

# 309 "FStar.Extraction.ML.Util.fst"
let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun _73_400 -> (match (()) with
| () -> begin
((let _166_127 = (FStar_Options.codegen ())
in (FStar_Option.get _166_127)) = "FSharp")
end))

# 311 "FStar.Extraction.ML.Util.fst"
let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> if (codegen_fsharp ()) then begin
(FStar_String.concat "." ns)
end else begin
(FStar_String.concat "_" ns)
end)

# 315 "FStar.Extraction.ML.Util.fst"
let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun _73_404 -> (match (_73_404) with
| (ns, n) -> begin
if (codegen_fsharp ()) then begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end else begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end
end))

# 319 "FStar.Extraction.ML.Util.fst"
let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (let _166_135 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((_166_135), (l.FStar_Ident.ident.FStar_Ident.idText))))

# 320 "FStar.Extraction.ML.Util.fst"
let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold t -> if (FStar_Extraction_ML_Env.erasableTypeNoDelta t) then begin
true
end else begin
(match ((unfold t)) with
| Some (t) -> begin
(erasableType unfold t)
end
| None -> begin
false
end)
end)

# 328 "FStar.Extraction.ML.Util.fst"
let rec eraseTypeDeep : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun unfold t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
if (etag = FStar_Extraction_ML_Syntax.E_PURE) then begin
(let _166_146 = (let _166_145 = (eraseTypeDeep unfold tyd)
in (let _166_144 = (eraseTypeDeep unfold tycd)
in ((_166_145), (etag), (_166_144))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_166_146))
end else begin
t
end
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
if (erasableType unfold t) then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
(let _166_148 = (let _166_147 = (FStar_List.map (eraseTypeDeep unfold) lty)
in ((_166_147), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_166_148))
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _166_149 = (FStar_List.map (eraseTypeDeep unfold) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_166_149))
end
| _73_426 -> begin
t
end))

# 335 "FStar.Extraction.ML.Util.fst"
let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))

# 337 "FStar.Extraction.ML.Util.fst"
let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (let _166_151 = (let _166_150 = ((mk_ty_fun ()) (((((("x"), (0))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((((("y"), (0))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty _166_150))
in (FStar_All.pipe_left _166_151 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))

# 338 "FStar.Extraction.ML.Util.fst"
let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App (((prims_op_amp_amp), ((e1)::(e2)::[]))))))

# 339 "FStar.Extraction.ML.Util.fst"
let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option = (fun e1 e2 -> (match (((e1), (e2))) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
(let _166_160 = (conjoin x y)
in Some (_166_160))
end))

# 344 "FStar.Extraction.ML.Util.fst"
let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (
# 347 "FStar.Extraction.ML.Util.fst"
let pos = (FStar_Range.start_of_range r)
in (
# 348 "FStar.Extraction.ML.Util.fst"
let line = (FStar_Range.line_of_pos pos)
in (let _166_163 = (FStar_Range.file_of_range r)
in ((line), (_166_163))))))

# 349 "FStar.Extraction.ML.Util.fst"
let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _73_452, b) -> begin
(let _166_166 = (argTypes b)
in (a)::_166_166)
end
| _73_457 -> begin
[]
end))




