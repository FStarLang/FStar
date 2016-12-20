
open Prims

let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))


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
| FStar_Const.Const_bytearray (bytes, _76_32) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, _76_37) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
(FStar_All.failwith "Unhandled constant: reify/reflect")
end))


let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> try
(match (()) with
| () -> begin
(mlconst_of_const c)
end)
with
| _76_50 -> begin
(let _173_14 = (let _173_13 = (FStar_Range.string_of_range p)
in (let _173_12 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _173_13 _173_12)))
in (FStar_All.failwith _173_14))
end)


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _76_60 -> (match (_76_60) with
| (y, _76_59) -> begin
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
(let _173_22 = (let _173_21 = (subst_aux subst t1)
in (let _173_20 = (subst_aux subst t2)
in ((_173_21), (f), (_173_20))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_173_22))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _173_24 = (let _173_23 = (FStar_List.map (subst_aux subst) args)
in ((_173_23), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_173_24))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _173_25 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_173_25))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun _76_78 args -> (match (_76_78) with
| (formals, t) -> begin
if ((FStar_List.length formals) <> (FStar_List.length args)) then begin
(FStar_All.failwith "Substitution must be fully applied (see GitHub issue #490)")
end else begin
(let _173_30 = (FStar_List.zip formals args)
in (subst_aux _173_30 t))
end
end))


let delta_unfold : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g _76_1 -> (match (_76_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _173_35 = (subst ts args)
in Some (_173_35))
end
| _76_89 -> begin
None
end)
end
| _76_91 -> begin
None
end))


let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g _76_2 -> (match (_76_2) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_UEnv.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _173_40 = (subst ts args)
in Some (_173_40))
end
| _76_101 -> begin
None
end)
end
| _76_103 -> begin
None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, _76_108) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| _76_117 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun _76_3 -> (match (_76_3) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))


let join : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r f f' -> (match (((f), (f'))) with
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
| _76_147 -> begin
(let _173_54 = (let _173_53 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" _173_53 (eff_to_string f) (eff_to_string f')))
in (FStar_All.failwith _173_54))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun = (fun _97_95 -> (FStar_List.fold_right (fun _76_153 t -> (match (_76_153) with
| (_76_151, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((t0), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end))))


type unfold_t =
FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option


let rec type_leq_c : unfold_t  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun unfold_ty e t t' -> (match (((t), (t'))) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
if ((Prims.fst x) = (Prims.fst y)) then begin
((true), (e))
end else begin
((false), (None))
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| _76_180 -> begin
(

let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body)))
end
| _76_186 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (let _173_80 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty _173_80 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = _76_191; FStar_Extraction_ML_Syntax.loc = _76_189}) -> begin
if ((type_leq unfold_ty t1' t1) && (eff_leq f f')) then begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
if (type_leq unfold_ty t2 t2') then begin
(

let body = if (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end
in (let _173_84 = (let _173_83 = (let _173_82 = (let _173_81 = ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty _173_81))
in (FStar_All.pipe_left _173_82 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body))))))
in Some (_173_83))
in ((true), (_173_84))))
end else begin
((false), (None))
end
end else begin
(

let _76_203 = (let _173_87 = (let _173_86 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _173_85 -> Some (_173_85)) _173_86))
in (type_leq_c unfold_ty _173_87 t2 t2'))
in (match (_76_203) with
| (ok, body) -> begin
(

let res = (match (body) with
| Some (body) -> begin
(let _173_88 = (mk_fun ((x)::[]) body)
in Some (_173_88))
end
| _76_207 -> begin
None
end)
in ((ok), (res)))
end))
end
end else begin
((false), (None))
end
end
| _76_210 -> begin
if (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2')) then begin
((true), (e))
end else begin
((false), (None))
end
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
if (path = path') then begin
if (FStar_List.forall2 (type_leq unfold_ty) args args') then begin
((true), (e))
end else begin
((false), (None))
end
end else begin
(match ((unfold_ty t)) with
| Some (t) -> begin
(type_leq_c unfold_ty e t t')
end
| None -> begin
(match ((unfold_ty t')) with
| None -> begin
((false), (None))
end
| Some (t') -> begin
(type_leq_c unfold_ty e t t')
end)
end)
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
if (FStar_List.forall2 (type_leq unfold_ty) ts ts') then begin
((true), (e))
end else begin
((false), (None))
end
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (_76_235), _76_238) -> begin
(match ((unfold_ty t)) with
| Some (t) -> begin
(type_leq_c unfold_ty e t t')
end
| _76_243 -> begin
((false), (None))
end)
end
| (_76_245, FStar_Extraction_ML_Syntax.MLTY_Named (_76_247)) -> begin
(match ((unfold_ty t')) with
| Some (t') -> begin
(type_leq_c unfold_ty e t t')
end
| _76_253 -> begin
((false), (None))
end)
end
| _76_255 -> begin
((false), (None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (let _173_92 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right _173_92 Prims.fst)))


let unit_binder : FStar_Absyn_Syntax.binder = (

let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))


let is_type_abstraction = (fun _76_4 -> (match (_76_4) with
| ((FStar_Util.Inl (_76_264), _76_267))::_76_262 -> begin
true
end
| _76_271 -> begin
false
end))


let mkTypFun : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None original.FStar_Absyn_Syntax.pos))


let mkTypApp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app ((typ), (arrgs)) None original.FStar_Absyn_Syntax.pos))


let tbinder_prefix : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun t -> (match ((let _173_108 = (FStar_Absyn_Util.compress_typ t)
in _173_108.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _76_5 -> (match (_76_5) with
| (FStar_Util.Inr (_76_285), _76_288) -> begin
true
end
| _76_291 -> begin
false
end)) bs)) with
| None -> begin
((bs), (t))
end
| Some (bs, b, rest) -> begin
(let _173_110 = (mkTypFun ((b)::rest) c t)
in ((bs), (_173_110)))
end)
end
| _76_299 -> begin
(([]), (t))
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _76_302 -> (match (_76_302) with
| (ns, n) -> begin
if (ns = ("Prims")::[]) then begin
if (FStar_Options.universes ()) then begin
(match (n) with
| "Mktuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "Mktuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "Mktuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "Mktuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "Mktuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "Mktuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "Mktuple8" -> begin
Some ((Prims.parse_int "8"))
end
| _76_311 -> begin
None
end)
end else begin
(match (n) with
| "MkTuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "MkTuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "MkTuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "MkTuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "MkTuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "MkTuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "MkTuple8" -> begin
Some ((Prims.parse_int "8"))
end
| _76_320 -> begin
None
end)
end
end else begin
None
end
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| _76_329 -> begin
e
end)
end
| _76_331 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun _76_6 -> (match (_76_6) with
| (f)::_76_334 -> begin
(

let _76_340 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (_76_340) with
| (ns, _76_339) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| _76_343 -> begin
(FStar_All.failwith "impos")
end))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let resugar_pat : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _76_357 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_76_359, fns)) -> begin
(

let p = (record_field_path fns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((p), (fs)))))
end
| _76_367 -> begin
p
end)
end)
end
| _76_369 -> begin
p
end))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun _76_372 -> (match (_76_372) with
| (ns, n) -> begin
if (ns = ("Prims")::[]) then begin
if (FStar_Options.universes ()) then begin
(match (n) with
| "tuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "tuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "tuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "tuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "tuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "tuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "tuple8" -> begin
Some ((Prims.parse_int "8"))
end
| _76_381 -> begin
None
end)
end else begin
(match (n) with
| "Tuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "Tuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "Tuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "Tuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "Tuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "Tuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "Tuple8" -> begin
Some ((Prims.parse_int "8"))
end
| _76_390 -> begin
None
end)
end
end else begin
None
end
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _76_399 -> begin
t
end)
end
| _76_401 -> begin
t
end))


let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun _76_402 -> (match (()) with
| () -> begin
((let _173_132 = (FStar_Options.codegen ())
in (FStar_Option.get _173_132)) = "FSharp")
end))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> if (codegen_fsharp ()) then begin
(FStar_String.concat "." ns)
end else begin
(FStar_String.concat "_" ns)
end)


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun _76_406 -> (match (_76_406) with
| (ns, n) -> begin
if (codegen_fsharp ()) then begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end else begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (let _173_140 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((_173_140), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> if (FStar_Extraction_ML_Env.erasableTypeNoDelta t) then begin
true
end else begin
(match ((unfold_ty t)) with
| Some (t) -> begin
(erasableType unfold_ty t)
end
| None -> begin
false
end)
end)


let rec eraseTypeDeep : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun unfold_ty t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
if (etag = FStar_Extraction_ML_Syntax.E_PURE) then begin
(let _173_151 = (let _173_150 = (eraseTypeDeep unfold_ty tyd)
in (let _173_149 = (eraseTypeDeep unfold_ty tycd)
in ((_173_150), (etag), (_173_149))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_173_151))
end else begin
t
end
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
if (erasableType unfold_ty t) then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
(let _173_153 = (let _173_152 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((_173_152), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_173_153))
end
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _173_154 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_173_154))
end
| _76_428 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (let _173_156 = (let _173_155 = ((mk_ty_fun ()) (((((("x"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((((("y"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty _173_155))
in (FStar_All.pipe_left _173_156 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App (((prims_op_amp_amp), ((e1)::(e2)::[]))))))


let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option = (fun e1 e2 -> (match (((e1), (e2))) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
(let _173_165 = (conjoin x y)
in Some (_173_165))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (let _173_168 = (FStar_Range.file_of_range r)
in ((line), (_173_168))))))


let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _76_454, b) -> begin
(let _173_171 = (argTypes b)
in (a)::_173_171)
end
| _76_459 -> begin
[]
end))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _76_463, b) -> begin
(

let _76_469 = (uncurry_mlty_fun b)
in (match (_76_469) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| _76_471 -> begin
(([]), (t))
end))




