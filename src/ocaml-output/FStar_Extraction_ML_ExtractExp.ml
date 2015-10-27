
open Prims
let fail = (fun r msg -> (let _62_8 = (let _127_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _127_3))
in (FStar_All.exit 1)))

let err_uninst = (fun e -> (let _127_6 = (let _127_5 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _127_5))
in (fail e.FStar_Absyn_Syntax.pos _127_6)))

let err_ill_typed_application = (fun e args t -> (let _127_12 = (let _127_11 = (FStar_Absyn_Print.exp_to_string e)
in (let _127_10 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _127_11 _127_10)))
in (fail e.FStar_Absyn_Syntax.pos _127_12)))

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun e f0 f1 -> (let _127_18 = (let _127_17 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _127_17 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _127_18)))

let is_constructor = (fun e -> (match ((let _127_21 = (FStar_Absyn_Util.compress_exp e)
in _127_21.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _62_34 -> begin
false
end))

let rec is_value_or_type_app = (fun e -> (match ((let _127_24 = (FStar_Absyn_Util.compress_exp e)
in _127_24.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _62_55 -> (match (_62_55) with
| (te, _62_54) -> begin
(match (te) with
| FStar_Util.Inl (_62_57) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _127_26 = (FStar_Absyn_Util.compress_exp head)
in _127_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _62_1 -> (match (_62_1) with
| (FStar_Util.Inl (te), _62_71) -> begin
true
end
| _62_74 -> begin
false
end))))
end
| _62_76 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _62_90 -> begin
false
end))

let rec is_ml_value = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_62_111, fields) -> begin
(FStar_Util.for_all (fun _62_118 -> (match (_62_118) with
| (_62_116, e) -> begin
(is_ml_value e)
end)) fields)
end
| _62_120 -> begin
false
end))

let translate_typ = (fun g t -> (let _127_35 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _127_35)))

let translate_typ_of_arg = (fun g a -> (let _127_40 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _127_40)))

let instantiate = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

let erasable = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

let erase = (fun g e f t -> if (erasable g f t) then begin
(let _62_135 = (FStar_Extraction_ML_Env.debug g (fun _62_134 -> (match (()) with
| () -> begin
(let _127_61 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _127_60 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.fprint2 "Erasing %s at type %s\n" _127_61 _127_60)))
end)))
in (let e_val = if (FStar_Extraction_ML_Util.type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t))))
end
in (e_val, f, t)))
end else begin
(e, f, t)
end)

let maybe_coerce = (fun g e tInferred etag tExpected -> (match ((FStar_Extraction_ML_Util.type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _62_148 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

let extract_pat = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_62_157) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _127_84 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _127_84))
in (let when_clause = (let _127_93 = (let _127_92 = (let _127_91 = (let _127_90 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _127_89 = (let _127_88 = (let _127_87 = (let _127_86 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Absyn_Syntax.Const_int (c)))
in (FStar_All.pipe_left (fun _127_85 -> FStar_Extraction_ML_Syntax.MLE_Const (_127_85)) _127_86))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _127_87))
in (_127_88)::[])
in (_127_90)::_127_89))
in (FStar_Extraction_ML_Util.prims_op_equality, _127_91))
in FStar_Extraction_ML_Syntax.MLE_App (_127_92))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _127_93))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _127_97 = (let _127_96 = (let _127_95 = (let _127_94 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_127_94))
in (_127_95, []))
in Some (_127_96))
in (g, _127_97))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _62_182 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _62_172}, ttys) -> begin
(n, ttys)
end
| _62_179 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_62_182) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _62_186 = (FStar_Util.first_N nTyVars pats)
in (match (_62_186) with
| (tysVarPats, restPats) -> begin
(let _62_193 = (FStar_Util.fold_map (fun g _62_190 -> (match (_62_190) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_62_193) with
| (g, tyMLPats) -> begin
(let _62_200 = (FStar_Util.fold_map (fun g _62_197 -> (match (_62_197) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_62_200) with
| (g, restMLPats) -> begin
(let _62_208 = (let _127_103 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _62_2 -> (match (_62_2) with
| Some (x) -> begin
(x)::[]
end
| _62_205 -> begin
[]
end))))
in (FStar_All.pipe_right _127_103 FStar_List.split))
in (match (_62_208) with
| (mlPats, when_clauses) -> begin
(let _127_107 = (let _127_106 = (let _127_105 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _127_104 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_127_105, _127_104)))
in Some (_127_106))
in (g, _127_107))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end)))
end
| FStar_Absyn_Syntax.Pat_wild (x) when disj -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_term (_62_220) -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (let g = (FStar_Extraction_ML_Env.extend_ty g a (Some (mlty)))
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Wild, []))
end)))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) -> begin
(g, None)
end))
in (let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _62_243 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _127_116 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_127_116))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _62_258 = (extract_one_pat true g p)
in (match (_62_258) with
| (g, p) -> begin
(let ps = (let _127_119 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _127_118 = (extract_one_pat true g x)
in (Prims.snd _127_118)))))
in (p)::_127_119)
in (let _62_274 = (FStar_All.pipe_right ps (FStar_List.partition (fun _62_3 -> (match (_62_3) with
| (_62_263, _62_267::_62_265) -> begin
true
end
| _62_271 -> begin
false
end))))
in (match (_62_274) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _62_277 -> (match (_62_277) with
| (x, whens) -> begin
(let _127_122 = (mk_when_clause whens)
in (x, _127_122))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _127_126 = (let _127_125 = (let _127_124 = (let _127_123 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_127_123))
in (_127_124, None))
in (_127_125)::ps)
in (g, _127_126))
end)
in res))
end)))
end))
end
| _62_283 -> begin
(let _62_288 = (extract_one_pat false g p)
in (match (_62_288) with
| (g, (p, whens)) -> begin
(let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

let normalize_abs = (fun e0 -> (let rec aux = (fun bs e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _62_300 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

let ffi_mltuple_mlp = (fun n -> (let name = if ((2 < n) && (n < 6)) then begin
(let _127_135 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _127_135))
end else begin
if (n = 2) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in (("Camlstack")::[], name)))

let fix_lalloc = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(let args = (FStar_List.map Prims.snd fields)
in (let tup = (let _127_142 = (let _127_141 = (let _127_140 = (let _127_139 = (let _127_138 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_127_138))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _127_139))
in (_127_140, args))
in FStar_Extraction_ML_Syntax.MLE_App (_127_141))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _127_142))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _62_319 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _62_329, t1) -> begin
(let x = (let _127_155 = (FStar_Absyn_Util.gensym ())
in (_127_155, (- (1))))
in (let _127_158 = (let _127_157 = (let _127_156 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _127_156))
in (_127_157)::more_args)
in (eta_args _127_158 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_62_335, _62_337) -> begin
((FStar_List.rev more_args), t)
end
| _62_341 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_62_346, args), Some (FStar_Absyn_Syntax.Record_ctor (_62_351, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _62_360 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let _62_366 = (eta_args [] residualType)
in (match (_62_366) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _127_167 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _127_167))
end
| _62_369 -> begin
(let _62_372 = (FStar_List.unzip eargs)
in (match (_62_372) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _127_169 = (let _127_168 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _127_168))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _127_169))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _62_379 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _62_381}, mlarg::[]), _62_390) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _62_393 = (FStar_Extraction_ML_Env.debug g (fun _62_392 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_62_396, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _62_400}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (let e = (match (args) with
| [] -> begin
proj
end
| _62_417 -> begin
(let _127_172 = (let _127_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_127_171, args))
in FStar_Extraction_ML_Syntax.MLE_App (_127_172))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _127_173 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _127_173))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _127_174 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _127_174))
end
| _62_453 -> begin
mlAppExpr
end)))))

let check_pats_for_ite = (fun l -> (let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _62_459 = (FStar_List.hd l)
in (match (_62_459) with
| (p1, w1, e1) -> begin
(let _62_463 = (let _127_177 = (FStar_List.tl l)
in (FStar_List.hd _127_177))
in (match (_62_463) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _62_483 -> begin
def
end)
end))
end))
end))

let rec check_exp = (fun g e f t -> (let _62_493 = (let _127_194 = (check_exp' g e f t)
in (erase g _127_194 f t))
in (match (_62_493) with
| (e, _62_490, _62_492) -> begin
e
end)))
and check_exp' = (fun g e f t -> (match ((let _127_199 = (FStar_Absyn_Util.compress_exp e)
in _127_199.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _62_505 = (synth_exp g scrutinee)
in (match (_62_505) with
| (e, f_e, t_e) -> begin
(let _62_509 = (check_pats_for_ite pats)
in (match (_62_509) with
| (b, then_e, else_e) -> begin
(let e' = if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(let then_mle = (check_exp g then_e f t)
in (let else_mle = (check_exp g else_e f t)
in FStar_Extraction_ML_Syntax.MLE_If ((e, then_mle, Some (else_mle)))))
end
| _62_518 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _62_522 -> (match (_62_522) with
| (pat, when_opt, branch) -> begin
(let _62_525 = (extract_pat g pat)
in (match (_62_525) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _127_201 = (check_exp env w FStar_Extraction_ML_Syntax.E_IMPURE FStar_Extraction_ML_Syntax.ml_bool_ty)
in Some (_127_201))
end)
in (let branch = (check_exp env branch f t)
in (FStar_All.pipe_right p (FStar_List.map (fun _62_533 -> (match (_62_533) with
| (p, wopt) -> begin
(let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, when_clause, branch))
end))))))
end))
end))))
in FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches)))
end
in if (FStar_Extraction_ML_Util.eff_leq f_e f) then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) e')
end else begin
(err_unexpected_eff scrutinee f f_e)
end)
end))
end))
end
| _62_538 -> begin
(let _62_542 = (synth_exp g e)
in (match (_62_542) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 f t)
end else begin
(err_unexpected_eff e f f0)
end
end))
end))
and synth_exp = (fun g e -> (let _62_548 = (synth_exp' g e)
in (match (_62_548) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun g e -> (let _62_552 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _127_209 = (let _127_208 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "now synthesizing expression :  %s \n" _127_208))
in (FStar_Util.print_string _127_209))))
in (match ((let _127_210 = (FStar_Absyn_Util.compress_exp e)
in _127_210.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let ml_ty = (translate_typ g t)
in (let _127_214 = (let _127_213 = (let _127_212 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _127_211 -> FStar_Extraction_ML_Syntax.MLE_Const (_127_211)) _127_212))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _127_213))
in (_127_214, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e0, t, f) -> begin
(let t = (translate_typ g t)
in (let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _62_579 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_62_579) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _127_215 = (maybe_lalloc_eta_data g qual t x)
in (_127_215, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_584 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _62_593 _62_596 restArgs -> (match ((_62_593, _62_596)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _62_600) -> begin
(let _62_611 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _127_224 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _127_224))
end else begin
(FStar_List.fold_left (fun _62_604 _62_607 -> (match ((_62_604, _62_607)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(let x = (let _127_227 = (FStar_Absyn_Util.gensym ())
in (_127_227, (- (1))))
in (let _127_229 = (let _127_228 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_127_228)::out_args)
in (((x, arg))::lbs, _127_229)))
end
end)) ([], []) mlargs_f)
end
in (match (_62_611) with
| (lbs, mlargs) -> begin
(let app = (let _127_230 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _127_230))
in (let l_app = (FStar_List.fold_right (fun _62_615 out -> (match (_62_615) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = ([], arg.FStar_Extraction_ML_Syntax.ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_62_620), _62_623)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _127_234 = (let _127_233 = (FStar_Extraction_ML_Util.join f f')
in (_127_233, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _127_234 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _62_636)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _62_648 = (synth_exp g e0)
in (match (_62_648) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred f' tExpected)
in (let _127_236 = (let _127_235 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_127_235, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _127_236 rest)))
end))
end
| _62_651 -> begin
(match ((FStar_Extraction_ML_Util.delta_unfold g t)) with
| Some (t) -> begin
(synth_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application e restArgs t)
end)
end)
end))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (match (head.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _62_668 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_62_668) with
| ((head, (vars, t)), qual) -> begin
(let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(let _62_672 = (FStar_Util.first_N n args)
in (match (_62_672) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (let head = (match (head.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(let _62_682 = head
in {FStar_Extraction_ML_Syntax.expr = _62_682.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _62_686}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((let _62_693 = head
in {FStar_Extraction_ML_Syntax.expr = _62_693.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t))}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _62_696 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (rest) with
| [] -> begin
(let _127_237 = (maybe_lalloc_eta_data g qual t head)
in (_127_237, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_700 -> begin
(synth_app qual (head, []) (FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end)))))
end))
end else begin
(err_uninst e)
end)
end))
end
| _62_702 -> begin
(let _62_706 = (synth_exp g head)
in (match (_62_706) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _62_729 = (FStar_List.fold_left (fun _62_713 _62_717 -> (match ((_62_713, _62_717)) with
| ((ml_bs, env), (b, _62_716)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _127_240 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_127_240, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_62_729) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _62_734 = (synth_exp env body)
in (match (_62_734) with
| (ml_body, f, t) -> begin
(let _62_744 = (FStar_List.fold_right (fun _62_738 _62_741 -> (match ((_62_738, _62_741)) with
| ((_62_736, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_62_744) with
| (f, tfun) -> begin
(let _127_243 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_127_243, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _62_756 -> (match (_62_756) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _62_780 = (match ((FStar_Util.prefix_until (fun _62_4 -> (match (_62_4) with
| (FStar_Util.Inr (_62_765), _62_768) -> begin
true
end
| _62_771 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _127_247 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _127_247))
end)
in (match (_62_780) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(let _62_789 = (FStar_Util.first_N n bs)
in (match (_62_789) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _62_5 -> (match (_62_5) with
| (FStar_Util.Inl (a), _62_798) -> begin
a
end
| _62_801 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _127_251 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_127_251, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _62_810 -> begin
false
end)
in (let rest_args = if add_unit then begin
(FStar_Extraction_ML_Util.unit_binder)::rest_args
end else begin
rest_args
end
in (let body = (match (rest_args) with
| [] -> begin
body
end
| _62_815 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _62_818 -> begin
(err_value_restriction e)
end)))
end))
end
| _62_820 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _62_835 -> (match (_62_835) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
in (let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (let e = (check_exp env e f expected_t)
in (f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = polytype; FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e}))))
end))
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (let _62_864 = (FStar_List.fold_right (fun lb _62_845 -> (match (_62_845) with
| (env, lbs) -> begin
(let _62_858 = lb
in (match (_62_858) with
| (lbname, _62_848, (t, (_62_851, polytype)), add_unit, _62_857) -> begin
(let _62_861 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_62_861) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_62_864) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _62_870 = (synth_exp env_body e')
in (match (_62_870) with
| (e', f', t') -> begin
(let f = (let _127_261 = (let _127_260 = (FStar_List.map Prims.fst lbs)
in (f')::_127_260)
in (FStar_Extraction_ML_Util.join_l _127_261))
in (let _127_266 = (let _127_265 = (let _127_264 = (let _127_263 = (let _127_262 = (FStar_List.map Prims.snd lbs)
in (is_rec, _127_262))
in (_127_263, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_127_264))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t') _127_265))
in (_127_266, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(FStar_All.failwith "Matches must be checked; missing a compiler-provided annotation")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _62_878)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(FStar_All.failwith "Unexpected expression")
end)))

let fresh = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _62_890 = (FStar_Util.incr c)
in (let _127_269 = (FStar_ST.read c)
in (x, _127_269)))))

let ind_discriminator_body = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _62_899 = (let _127_276 = (FStar_Absyn_Util.fv constrName)
in (FStar_Extraction_ML_Env.lookup_fv env _127_276))
in (match (_62_899) with
| (_62_897, ts) -> begin
(let _62_911 = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_62_901, _62_903, t) -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild)::[], ((Prims.fst ts), t))
end
| _62_908 -> begin
([], ts)
end)
in (match (_62_911) with
| (arg_pat, ts) -> begin
(let rid = constrName
in (let targ = (Prims.snd ts)
in (let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_bool_ty))
in (let discrBody = (let _127_291 = (let _127_290 = (let _127_289 = (let _127_288 = (let _127_287 = (let _127_286 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _127_285 = (let _127_284 = (let _127_280 = (let _127_278 = (let _127_277 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_127_277, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_127_278))
in (let _127_279 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_127_280, None, _127_279)))
in (let _127_283 = (let _127_282 = (let _127_281 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _127_281))
in (_127_282)::[])
in (_127_284)::_127_283))
in (_127_286, _127_285)))
in FStar_Extraction_ML_Syntax.MLE_Match (_127_287))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _127_288))
in (((mlid, targ))::[], _127_289))
in FStar_Extraction_ML_Syntax.MLE_Fun (_127_290))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _127_291))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Absyn_Syntax.ident); FStar_Extraction_ML_Syntax.mllb_tysc = ((Prims.fst ts), disc_ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[]))))))
end))
end))))




