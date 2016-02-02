
open Prims
let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))

let mlconst_of_const = (fun sctt -> (match (sctt) with
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
| FStar_Const.Const_bytearray (bytes, _71_32) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, _71_37) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end))

let mlconst_of_const' = (fun p c -> (FStar_All.try_with (fun _71_43 -> (match (()) with
| () -> begin
(mlconst_of_const c)
end)) (fun _71_42 -> (match (_71_42) with
| _71_46 -> begin
(let _148_14 = (let _148_13 = (FStar_Range.string_of_range p)
in (let _148_12 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _148_13 _148_12)))
in (FStar_All.failwith _148_14))
end))))

let rec subst_aux = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _71_56 -> (match (_71_56) with
| (y, _71_55) -> begin
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
(let _148_22 = (let _148_21 = (subst_aux subst t1)
in (let _148_20 = (subst_aux subst t2)
in (_148_21, f, _148_20)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_148_22))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _148_24 = (let _148_23 = (FStar_List.map (subst_aux subst) args)
in (_148_23, path))
in FStar_Extraction_ML_Syntax.MLTY_Named (_148_24))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _148_25 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_148_25))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

let subst = (fun _71_74 args -> (match (_71_74) with
| (formals, t) -> begin
if ((FStar_List.length formals) <> (FStar_List.length args)) then begin
(FStar_All.failwith "Substitution must be fully applied: instantiation of %A failed; got %A\n")
end else begin
(let _148_30 = (FStar_List.zip formals args)
in (subst_aux _148_30 t))
end
end))

let delta_unfold = (fun g _71_1 -> (match (_71_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _148_35 = (subst ts args)
in Some (_148_35))
end
| _71_85 -> begin
None
end)
end
| _71_87 -> begin
None
end))

let eff_leq = (fun f f' -> (match ((f, f')) with
| (FStar_Extraction_ML_Syntax.E_PURE, _71_92) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| _71_101 -> begin
false
end))

let eff_to_string = (fun _71_2 -> (match (_71_2) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

let join = (fun f f' -> (match ((f, f')) with
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
| _71_130 -> begin
(let _148_46 = (FStar_Util.format2 "Impossible: Inconsistent effects %s and %s" (eff_to_string f) (eff_to_string f'))
in (FStar_All.failwith _148_46))
end))

let join_l = (fun fs -> (FStar_List.fold_left join FStar_Extraction_ML_Syntax.E_PURE fs))

let mk_ty_fun = (fun _77_95 -> (FStar_List.fold_right (fun _71_135 t -> (match (_71_135) with
| (_71_133, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((t0, FStar_Extraction_ML_Syntax.E_PURE, t))
end))))

let rec type_leq_c = (fun g e t t' -> (match ((t, t')) with
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
| _71_162 -> begin
(let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((FStar_List.append xs ys), body))
end
| _71_168 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((xs, body))
end)
in (let _148_68 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.ty)
in (FStar_Extraction_ML_Syntax.with_ty _148_68 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (x::xs, body); FStar_Extraction_ML_Syntax.ty = _71_171}) -> begin
if ((type_leq g t1' t1) && (eff_leq f f')) then begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
if (type_leq g t2 t2') then begin
(let body = if (type_leq g t2 FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t2'))))
end
in (let _148_72 = (let _148_71 = (let _148_70 = (let _148_69 = ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.ty)
in (FStar_Extraction_ML_Syntax.with_ty _148_69))
in (FStar_All.pipe_left _148_70 (FStar_Extraction_ML_Syntax.MLE_Fun (((x)::[], body)))))
in Some (_148_71))
in (true, _148_72)))
end else begin
(false, None)
end
end else begin
(let _71_183 = (let _148_75 = (let _148_74 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _148_73 -> Some (_148_73)) _148_74))
in (type_leq_c g _148_75 t2 t2'))
in (match (_71_183) with
| (ok, body) -> begin
(let res = (match (body) with
| Some (body) -> begin
(let _148_76 = (mk_fun ((x)::[]) body)
in Some (_148_76))
end
| _71_187 -> begin
None
end)
in (ok, res))
end))
end
end else begin
(false, None)
end
end
| _71_190 -> begin
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
| (FStar_Extraction_ML_Syntax.MLTY_Named (_71_215), _71_218) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(type_leq_c g e t t')
end
| _71_223 -> begin
(false, None)
end)
end
| (_71_225, FStar_Extraction_ML_Syntax.MLTY_Named (_71_227)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(type_leq_c g e t t')
end
| _71_233 -> begin
(false, None)
end)
end
| _71_235 -> begin
(false, None)
end))
and type_leq = (fun g t1 t2 -> (let _148_80 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right _148_80 Prims.fst)))

let unit_binder = (let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))

let is_type_abstraction = (fun _71_3 -> (match (_71_3) with
| (FStar_Util.Inl (_71_244), _71_247)::_71_242 -> begin
true
end
| _71_251 -> begin
false
end))

let mkTypFun = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.FStar_Absyn_Syntax.pos))

let mkTypApp = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.FStar_Absyn_Syntax.pos))

let tbinder_prefix = (fun t -> (match ((let _148_96 = (FStar_Absyn_Util.compress_typ t)
in _148_96.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _71_4 -> (match (_71_4) with
| (FStar_Util.Inr (_71_265), _71_268) -> begin
true
end
| _71_271 -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some (bs, b, rest) -> begin
(let _148_98 = (mkTypFun ((b)::rest) c t)
in (bs, _148_98))
end)
end
| _71_279 -> begin
([], t)
end))

let is_xtuple = (fun _71_282 -> (match (_71_282) with
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
| _71_290 -> begin
None
end)
end else begin
None
end
end))

let resugar_exp = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| _71_299 -> begin
e
end)
end
| _71_301 -> begin
e
end))

let record_field_path = (fun _71_5 -> (match (_71_5) with
| f::_71_304 -> begin
(let _71_310 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (_71_310) with
| (ns, _71_309) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| _71_313 -> begin
(FStar_All.failwith "impos")
end))

let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> (f.FStar_Ident.ident.FStar_Ident.idText, e)) fs vs))

let resugar_pat = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _71_327 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_71_329, fns)) -> begin
(let p = (record_field_path fns)
in (let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _71_337 -> begin
p
end)
end)
end
| _71_339 -> begin
p
end))

let is_xtuple_ty = (fun _71_342 -> (match (_71_342) with
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
| _71_350 -> begin
None
end)
end else begin
None
end
end))

let resugar_mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _71_359 -> begin
t
end)
end
| _71_361 -> begin
t
end))

let codegen_fsharp = (fun _71_362 -> (match (()) with
| () -> begin
((let _148_120 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.get _148_120)) = "FSharp")
end))

let flatten_ns = (fun ns -> if (codegen_fsharp ()) then begin
(FStar_String.concat "." ns)
end else begin
(FStar_String.concat "_" ns)
end)

let flatten_mlpath = (fun _71_366 -> (match (_71_366) with
| (ns, n) -> begin
if (codegen_fsharp ()) then begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end else begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end
end))

let mlpath_of_lid = (fun l -> (let _148_128 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in (_148_128, l.FStar_Ident.ident.FStar_Ident.idText)))

let rec erasableType = (fun g t -> if (FStar_Extraction_ML_Env.erasableTypeNoDelta t) then begin
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

let rec eraseTypeDeep = (fun g t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
if (etag = FStar_Extraction_ML_Syntax.E_PURE) then begin
(let _148_139 = (let _148_138 = (eraseTypeDeep g tyd)
in (let _148_137 = (eraseTypeDeep g tycd)
in (_148_138, etag, _148_137)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_148_139))
end else begin
t
end
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
if (erasableType g t) then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
(let _148_141 = (let _148_140 = (FStar_List.map (eraseTypeDeep g) lty)
in (_148_140, mlp))
in FStar_Extraction_ML_Syntax.MLTY_Named (_148_141))
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _148_142 = (FStar_List.map (eraseTypeDeep g) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_148_142))
end
| _71_388 -> begin
t
end))

let prims_op_equality = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name ((("Prims")::[], "op_Equality"))))

let prims_op_amp_amp = (let _148_144 = (let _148_143 = ((mk_ty_fun ()) (((("x", 0), FStar_Extraction_ML_Syntax.ml_bool_ty))::((("y", 0), FStar_Extraction_ML_Syntax.ml_bool_ty))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty _148_143))
in (FStar_All.pipe_left _148_144 (FStar_Extraction_ML_Syntax.MLE_Name ((("Prims")::[], "op_AmpAmp")))))

let conjoin = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App ((prims_op_amp_amp, (e1)::(e2)::[])))))

let conjoin_opt = (fun e1 e2 -> (match ((e1, e2)) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
(let _148_153 = (conjoin x y)
in Some (_148_153))
end))




