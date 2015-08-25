
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
(let _123_7 = (let _123_6 = (FStar_Util.int_of_string c)
in (FStar_Util.int32_of_int _123_6))
in FStar_Extraction_ML_Syntax.MLC_Int32 (_123_7))
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
| FStar_Absyn_Syntax.Const_bytearray (bytes, _57_30) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Absyn_Syntax.Const_string (bytes, _57_35) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end))

let rec subst_aux = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((FStar_Util.find_opt (fun _57_45 -> (match (_57_45) with
| (y, _57_44) -> begin
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
(let _123_15 = (let _123_14 = (subst_aux subst t1)
in (let _123_13 = (subst_aux subst t2)
in (_123_14, f, _123_13)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_123_15))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(let _123_17 = (let _123_16 = (FStar_List.map (subst_aux subst) args)
in (_123_16, path))
in FStar_Extraction_ML_Syntax.MLTY_Named (_123_17))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _123_18 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_123_18))
end
| FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let _123_21 = (let _123_20 = (subst_aux subst t1)
in (let _123_19 = (subst_aux subst t2)
in (_123_20, _123_19)))
in FStar_Extraction_ML_Syntax.MLTY_App (_123_21))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

let subst = (fun _57_67 args -> (match (_57_67) with
| (formals, t) -> begin
(match (((FStar_List.length formals) <> (FStar_List.length args))) with
| true -> begin
(FStar_All.failwith "Substitution must be fully applied")
end
| false -> begin
(let _123_26 = (FStar_List.zip formals args)
in (subst_aux _123_26 t))
end)
end))

let delta_unfold = (fun g _57_1 -> (match (_57_1) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(match ((FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _123_31 = (subst ts args)
in Some (_123_31))
end
| _57_78 -> begin
None
end)
end
| _57_80 -> begin
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
| (FStar_Extraction_ML_Syntax.MLTY_Named (_57_124), _57_127) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(equiv g t t')
end
| _57_132 -> begin
false
end)
end
| (_57_134, FStar_Extraction_ML_Syntax.MLTY_Named (_57_136)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(equiv g t t')
end
| _57_142 -> begin
false
end)
end
| _57_144 -> begin
false
end))

let unit_binder = (let x = (FStar_Absyn_Util.gen_bvar FStar_Tc_Recheck.t_unit)
in (FStar_Absyn_Syntax.v_binder x))

let is_type_abstraction = (fun _57_2 -> (match (_57_2) with
| (FStar_Util.Inl (_57_150), _57_153)::_57_148 -> begin
true
end
| _57_157 -> begin
false
end))

let mkTypFun = (fun bs c original -> (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.FStar_Absyn_Syntax.pos))

let mkTypApp = (fun typ arrgs original -> (FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.FStar_Absyn_Syntax.pos))

let tbinder_prefix = (fun t -> (match ((let _123_53 = (FStar_Absyn_Util.compress_typ t)
in _123_53.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((FStar_Util.prefix_until (fun _57_3 -> (match (_57_3) with
| (FStar_Util.Inr (_57_171), _57_174) -> begin
true
end
| _57_177 -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some (bs, b, rest) -> begin
(let _123_55 = (mkTypFun ((b)::rest) c t)
in (bs, _123_55))
end)
end
| _57_185 -> begin
([], t)
end))

let is_xtuple = (fun _57_188 -> (match (_57_188) with
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
| _57_196 -> begin
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
| _57_205 -> begin
e
end)
end
| _57_207 -> begin
e
end))

let record_field_path = (fun _57_4 -> (match (_57_4) with
| f::_57_210 -> begin
(let _57_216 = (FStar_Util.prefix f.FStar_Absyn_Syntax.ns)
in (match (_57_216) with
| (ns, _57_215) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Absyn_Syntax.idText)))
end))
end
| _57_219 -> begin
(FStar_All.failwith "impos")
end))

let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> (f.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText, e)) fs vs))

let resugar_pat = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _57_233 -> begin
(match (q) with
| Some (FStar_Absyn_Syntax.Record_ctor (_57_235, fns)) -> begin
(let p = (record_field_path fns)
in (let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _57_243 -> begin
p
end)
end)
end
| _57_245 -> begin
p
end))

let is_xtuple_ty = (fun _57_248 -> (match (_57_248) with
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
| _57_256 -> begin
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
| _57_265 -> begin
t
end)
end
| _57_267 -> begin
t
end))

let codegen_fsharp = (fun _57_268 -> (match (()) with
| () -> begin
((let _123_77 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.get _123_77)) = "FSharp")
end))

let flatten_ns = (fun ns -> (match ((codegen_fsharp ())) with
| true -> begin
(FStar_String.concat "." ns)
end
| false -> begin
(FStar_String.concat "_" ns)
end))

let flatten_mlpath = (fun _57_272 -> (match (_57_272) with
| (ns, n) -> begin
(match ((codegen_fsharp ())) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end
| false -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end)
end))

let mlpath_of_lid = (fun l -> (let _123_85 = (FStar_All.pipe_right l.FStar_Absyn_Syntax.ns (FStar_List.map (fun i -> i.FStar_Absyn_Syntax.idText)))
in (_123_85, l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)))

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
(let _123_96 = (let _123_95 = (eraseTypeDeep g tyd)
in (let _123_94 = (eraseTypeDeep g tycd)
in (_123_95, etag, _123_94)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_123_96))
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
(let _123_98 = (let _123_97 = (FStar_List.map (eraseTypeDeep g) lty)
in (_123_97, mlp))
in FStar_Extraction_ML_Syntax.MLTY_Named (_123_98))
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _123_99 = (FStar_List.map (eraseTypeDeep g) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (_123_99))
end
| FStar_Extraction_ML_Syntax.MLTY_App (tyf, tyarg) -> begin
(let _123_102 = (let _123_101 = (eraseTypeDeep g tyf)
in (let _123_100 = (eraseTypeDeep g tyarg)
in (_123_101, _123_100)))
in FStar_Extraction_ML_Syntax.MLTY_App (_123_102))
end
| _57_298 -> begin
t
end))




