
let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))

let mlconst_of_const = (fun sctt -> (match (sctt) with
| FStar_Absyn_Syntax.Const_unit -> begin
FStar_Extraction_ML_Syntax.MLC_Unit
end
| FStar_Absyn_Syntax.Const_char (c) -> begin
FStar_Extraction_ML_Syntax.MLC_Char (c)
end
| FStar_Absyn_Syntax.Const_uint8 (c) -> begin
FStar_Extraction_ML_Syntax.MLC_Byte (c)
end
| FStar_Absyn_Syntax.Const_int (c) -> begin
(let _127_7 = (let _127_6 = (FStar_Util.int_of_string c)
in (FStar_Util.int32_of_int _127_6))
in FStar_Extraction_ML_Syntax.MLC_Int32 (_127_7))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
FStar_Extraction_ML_Syntax.MLC_Int32 (i)
end
| FStar_Absyn_Syntax.Const_int64 (i) -> begin
FStar_Extraction_ML_Syntax.MLC_Int64 (i)
end
| FStar_Absyn_Syntax.Const_bool (b) -> begin
FStar_Extraction_ML_Syntax.MLC_Bool (b)
end
| FStar_Absyn_Syntax.Const_float (d) -> begin
FStar_Extraction_ML_Syntax.MLC_Float (d)
end
| FStar_Absyn_Syntax.Const_bytearray (bytes, _58_30) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Absyn_Syntax.Const_string (bytes, _58_35) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end))

let mlconst_of_const' = (fun p c -> (FStar_All.try_with (fun _58_41 -> (match (()) with
| () -> begin
(mlconst_of_const c)
end)) (fun _58_40 -> (match (_58_40) with
| _58_44 -> begin
(let _127_16 = (let _127_15 = (FStar_Range.string_of_range p)
in (let _127_14 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _127_15 _127_14)))
in (FStar_All.failwith _127_16))
end))))

let rec subst_aux = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _58_54 -> (match (_58_54) with
| (y, _58_53) -> begin
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
(let _127_24 = (let _127_23 = (subst_aux subst t1)
in (let _127_22 = (subst_aux subst t2)
in (_127_23, f, _127_22)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_127_24))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _127_26 = (let _127_25 = (FStar_List.map (subst_aux subst) args)
in (_127_25, path))
in FStar_Extraction_ML_Syntax.MLTY_Named (_127_26))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _127_27 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_127_27))
end
| FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let _127_30 = (let _127_29 = (subst_aux subst t1)
in (let _127_28 = (subst_aux subst t2)
in (_127_29, _127_28)))
in FStar_Extraction_ML_Syntax.MLTY_App (_127_30))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

let subst = (fun _58_76 args -> (match (_58_76) with
| (formals, t) -> begin
(match (((FStar_List.length formals) <> (FStar_List.length args))) with
| true -> begin
(FStar_All.failwith "Substitution must be fully applied")
end
| false -> begin
(let _127_35 = (FStar_List.zip formals args)
in (subst_aux _127_35 t))
end)
end))

let delta_unfold = (fun g _58_1 -> (match (_58_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _127_40 = (subst ts args)
in Some (_127_40))
end
| _58_87 -> begin
None
end)
end
| _58_89 -> begin
None
end))

let rec equiv = (fun g t t' -> (match ((t, t')) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
((Prims.fst x) = (Prims.fst y))
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
((equiv g t1 t1') && (equiv g t2 t2'))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((path = path')) with
| true -> begin
(FStar_List.forall2 (equiv g) args args')
end
| false -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(equiv g t t')
end
| None -> begin
(match ((delta_unfold g t')) with
| None -> begin
false
end
| Some (t') -> begin
(equiv g t t')
end)
end)
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
(FStar_List.forall2 (equiv g) ts ts')
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (_58_133), _58_136) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(equiv g t t')
end
| _58_141 -> begin
false
end)
end
| (_58_143, FStar_Extraction_ML_Syntax.MLTY_Named (_58_145)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(equiv g t t')
end
| _58_151 -> begin
false
end)
end
| _58_153 -> begin
false
end))

let unit_binder = (let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))

let is_type_abstraction = (fun _58_2 -> (match (_58_2) with
| (FStar_Util.Inl (_58_159), _58_162)::_58_157 -> begin
true
end
| _58_166 -> begin
false
end))

let mkTypFun = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.FStar_Absyn_Syntax.pos))

let mkTypApp = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.FStar_Absyn_Syntax.pos))

let tbinder_prefix = (fun t -> (match ((let _127_62 = (FStar_Absyn_Util.compress_typ t)
in _127_62.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _58_3 -> (match (_58_3) with
| (FStar_Util.Inr (_58_180), _58_183) -> begin
true
end
| _58_186 -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some (bs, b, rest) -> begin
(let _127_64 = (mkTypFun ((b)::rest) c t)
in (bs, _127_64))
end)
end
| _58_194 -> begin
([], t)
end))

let is_xtuple = (fun _58_197 -> (match (_58_197) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
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
| _58_205 -> begin
None
end)
end
| false -> begin
None
end)
end))

let resugar_exp = (fun e -> (match (e) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLE_Tuple (args)
end
| _58_214 -> begin
e
end)
end
| _58_216 -> begin
e
end))

let record_field_path = (fun _58_4 -> (match (_58_4) with
| f::_58_219 -> begin
(let _58_225 = (FStar_Util.prefix f.FStar_Absyn_Syntax.ns)
in (match (_58_225) with
| (ns, _58_224) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Absyn_Syntax.idText)))
end))
end
| _58_228 -> begin
(FStar_All.failwith "impos")
end))

let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> (f.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText, e)) fs vs))

let resugar_pat = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _58_242 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_58_244, fns)) -> begin
(let p = (record_field_path fns)
in (let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _58_252 -> begin
p
end)
end)
end
| _58_254 -> begin
p
end))

let is_xtuple_ty = (fun _58_257 -> (match (_58_257) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
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
| _58_265 -> begin
None
end)
end
| false -> begin
None
end)
end))

let resugar_mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _58_274 -> begin
t
end)
end
| _58_276 -> begin
t
end))

let codegen_fsharp = (fun _58_277 -> (match (()) with
| () -> begin
((let _127_86 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.get _127_86)) = "FSharp")
end))

let flatten_ns = (fun ns -> (match ((codegen_fsharp ())) with
| true -> begin
(FStar_String.concat "." ns)
end
| false -> begin
(FStar_String.concat "_" ns)
end))

let flatten_mlpath = (fun _58_281 -> (match (_58_281) with
| (ns, n) -> begin
(match ((codegen_fsharp ())) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end
| false -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end)
end))

let mlpath_of_lid = (fun l -> (let _127_94 = (FStar_All.pipe_right l.FStar_Absyn_Syntax.ns (FStar_List.map (fun i -> i.FStar_Absyn_Syntax.idText)))
in (_127_94, l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)))

let rec erasableType = (fun g t -> (match ((FStar_Extraction_ML_Env.erasableTypeNoDelta t)) with
| true -> begin
true
end
| false -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(erasableType g t)
end
| None -> begin
false
end)
end))

let rec eraseTypeDeep = (fun g t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
(match ((etag = FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(let _127_105 = (let _127_104 = (eraseTypeDeep g tyd)
in (let _127_103 = (eraseTypeDeep g tycd)
in (_127_104, etag, _127_103)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_127_105))
end
| false -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(match ((erasableType g t)) with
| true -> begin
FStar_Extraction_ML_Env.erasedContent
end
| false -> begin
(let _127_107 = (let _127_106 = (FStar_List.map (eraseTypeDeep g) lty)
in (_127_106, mlp))
in FStar_Extraction_ML_Syntax.MLTY_Named (_127_107))
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _127_108 = (FStar_List.map (eraseTypeDeep g) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_127_108))
end
| FStar_Extraction_ML_Syntax.MLTY_App (tyf, tyarg) -> begin
(let _127_111 = (let _127_110 = (eraseTypeDeep g tyf)
in (let _127_109 = (eraseTypeDeep g tyarg)
in (_127_110, _127_109)))
in FStar_Extraction_ML_Syntax.MLTY_App (_127_111))
end
| _58_307 -> begin
t
end))




