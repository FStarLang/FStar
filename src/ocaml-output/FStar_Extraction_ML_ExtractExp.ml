
open Prims
let fail = (fun r msg -> (let _63_8 = (let _129_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _129_3))
in (FStar_All.exit 1)))

let err_uninst = (fun e -> (let _129_6 = (let _129_5 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _129_5))
in (fail e.FStar_Absyn_Syntax.pos _129_6)))

let err_ill_typed_application = (fun e args t -> (let _129_12 = (let _129_11 = (FStar_Absyn_Print.exp_to_string e)
in (let _129_10 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _129_11 _129_10)))
in (fail e.FStar_Absyn_Syntax.pos _129_12)))

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun e f0 f1 -> (let _129_18 = (let _129_17 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _129_17 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _129_18)))

let is_constructor = (fun e -> (match ((let _129_21 = (FStar_Absyn_Util.compress_exp e)
in _129_21.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _63_34 -> begin
false
end))

let rec is_value_or_type_app = (fun e -> (match ((let _129_24 = (FStar_Absyn_Util.compress_exp e)
in _129_24.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _63_55 -> (match (_63_55) with
| (te, _63_54) -> begin
(match (te) with
| FStar_Util.Inl (_63_57) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _129_26 = (FStar_Absyn_Util.compress_exp head)
in _129_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _63_1 -> (match (_63_1) with
| (FStar_Util.Inl (te), _63_71) -> begin
true
end
| _63_74 -> begin
false
end))))
end
| _63_76 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _63_90 -> begin
false
end))

let rec is_ml_value = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_63_111, fields) -> begin
(FStar_Util.for_all (fun _63_118 -> (match (_63_118) with
| (_63_116, e) -> begin
(is_ml_value e)
end)) fields)
end
| _63_120 -> begin
false
end))

let translate_typ = (fun g t -> (let _129_35 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _129_35)))

let translate_typ_of_arg = (fun g a -> (let _129_40 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _129_40)))

let instantiate = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

let erasable = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

let erase = (fun g e f t -> if (erasable g f t) then begin
(let _63_135 = (FStar_Extraction_ML_Env.debug g (fun _63_134 -> (match (()) with
| () -> begin
(let _129_61 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _129_60 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _129_61 _129_60)))
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

let maybe_coerce = (fun g e tInferred tExpected -> (match ((FStar_Extraction_ML_Util.type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _63_147 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

let extract_pat = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_63_156) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _129_82 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _129_82))
in (let when_clause = (let _129_91 = (let _129_90 = (let _129_89 = (let _129_88 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _129_87 = (let _129_86 = (let _129_85 = (let _129_84 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Absyn_Syntax.Const_int (c)))
in (FStar_All.pipe_left (fun _129_83 -> FStar_Extraction_ML_Syntax.MLE_Const (_129_83)) _129_84))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _129_85))
in (_129_86)::[])
in (_129_88)::_129_87))
in (FStar_Extraction_ML_Util.prims_op_equality, _129_89))
in FStar_Extraction_ML_Syntax.MLE_App (_129_90))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _129_91))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _129_95 = (let _129_94 = (let _129_93 = (let _129_92 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_129_92))
in (_129_93, []))
in Some (_129_94))
in (g, _129_95))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _63_181 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _63_171}, ttys) -> begin
(n, ttys)
end
| _63_178 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_63_181) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _63_185 = (FStar_Util.first_N nTyVars pats)
in (match (_63_185) with
| (tysVarPats, restPats) -> begin
(let _63_192 = (FStar_Util.fold_map (fun g _63_189 -> (match (_63_189) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_63_192) with
| (g, tyMLPats) -> begin
(let _63_199 = (FStar_Util.fold_map (fun g _63_196 -> (match (_63_196) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_63_199) with
| (g, restMLPats) -> begin
(let _63_207 = (let _129_101 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _63_2 -> (match (_63_2) with
| Some (x) -> begin
(x)::[]
end
| _63_204 -> begin
[]
end))))
in (FStar_All.pipe_right _129_101 FStar_List.split))
in (match (_63_207) with
| (mlPats, when_clauses) -> begin
(let _129_105 = (let _129_104 = (let _129_103 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _129_102 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_129_103, _129_102)))
in Some (_129_104))
in (g, _129_105))
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
| FStar_Absyn_Syntax.Pat_dot_term (_63_219) -> begin
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
| _63_242 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _129_114 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_129_114))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _63_257 = (extract_one_pat true g p)
in (match (_63_257) with
| (g, p) -> begin
(let ps = (let _129_117 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _129_116 = (extract_one_pat true g x)
in (Prims.snd _129_116)))))
in (p)::_129_117)
in (let _63_273 = (FStar_All.pipe_right ps (FStar_List.partition (fun _63_3 -> (match (_63_3) with
| (_63_262, _63_266::_63_264) -> begin
true
end
| _63_270 -> begin
false
end))))
in (match (_63_273) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _63_276 -> (match (_63_276) with
| (x, whens) -> begin
(let _129_120 = (mk_when_clause whens)
in (x, _129_120))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _129_124 = (let _129_123 = (let _129_122 = (let _129_121 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_129_121))
in (_129_122, None))
in (_129_123)::ps)
in (g, _129_124))
end)
in res))
end)))
end))
end
| _63_282 -> begin
(let _63_287 = (extract_one_pat false g p)
in (match (_63_287) with
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
| _63_299 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

let ffi_mltuple_mlp = (fun n -> (let name = if ((2 < n) && (n < 6)) then begin
(let _129_133 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _129_133))
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
in (let tup = (let _129_140 = (let _129_139 = (let _129_138 = (let _129_137 = (let _129_136 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_129_136))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _129_137))
in (_129_138, args))
in FStar_Extraction_ML_Syntax.MLE_App (_129_139))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _129_140))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _63_318 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _63_328, t1) -> begin
(let x = (let _129_153 = (FStar_Absyn_Util.gensym ())
in (_129_153, (- (1))))
in (let _129_156 = (let _129_155 = (let _129_154 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _129_154))
in (_129_155)::more_args)
in (eta_args _129_156 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_63_334, _63_336) -> begin
((FStar_List.rev more_args), t)
end
| _63_340 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_63_345, args), Some (FStar_Absyn_Syntax.Record_ctor (_63_350, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _63_359 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let _63_365 = (eta_args [] residualType)
in (match (_63_365) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _129_165 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _129_165))
end
| _63_368 -> begin
(let _63_371 = (FStar_List.unzip eargs)
in (match (_63_371) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _129_167 = (let _129_166 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _129_166))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _129_167))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _63_378 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _63_380}, mlarg::[]), _63_389) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _63_392 = (FStar_Extraction_ML_Env.debug g (fun _63_391 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_63_395, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _63_399}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (let e = (match (args) with
| [] -> begin
proj
end
| _63_416 -> begin
(let _129_170 = (let _129_169 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_129_169, args))
in FStar_Extraction_ML_Syntax.MLE_App (_129_170))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _129_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _129_171))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _129_172 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _129_172))
end
| _63_452 -> begin
mlAppExpr
end)))))

let check_pats_for_ite = (fun l -> (let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _63_458 = (FStar_List.hd l)
in (match (_63_458) with
| (p1, w1, e1) -> begin
(let _63_462 = (let _129_175 = (FStar_List.tl l)
in (FStar_List.hd _129_175))
in (match (_63_462) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _63_482 -> begin
def
end)
end))
end))
end))

let rec check_exp = (fun g e f t -> (let _63_492 = (let _129_192 = (check_exp' g e f t)
in (erase g _129_192 f t))
in (match (_63_492) with
| (e, _63_489, _63_491) -> begin
e
end)))
and check_exp' = (fun g e f t -> (let _63_500 = (synth_exp g e)
in (match (_63_500) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp = (fun g e -> (let _63_506 = (synth_exp' g e)
in (match (_63_506) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun g e -> (let _63_510 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _129_203 = (let _129_202 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "now synthesizing expression :  %s \n" _129_202))
in (FStar_Util.print_string _129_203))))
in (match ((let _129_204 = (FStar_Absyn_Util.compress_exp e)
in _129_204.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let ml_ty = (translate_typ g t)
in (let _129_208 = (let _129_207 = (let _129_206 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _129_205 -> FStar_Extraction_ML_Syntax.MLE_Const (_129_205)) _129_206))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _129_207))
in (_129_208, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
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
(let _63_537 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_63_537) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _129_209 = (maybe_lalloc_eta_data g qual t x)
in (_129_209, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _63_542 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _63_551 _63_554 restArgs -> (match ((_63_551, _63_554)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _63_558) -> begin
(let _63_569 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _129_218 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _129_218))
end else begin
(FStar_List.fold_left (fun _63_562 _63_565 -> (match ((_63_562, _63_565)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(let x = (let _129_221 = (FStar_Absyn_Util.gensym ())
in (_129_221, (- (1))))
in (let _129_223 = (let _129_222 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_129_222)::out_args)
in (((x, arg))::lbs, _129_223)))
end
end)) ([], []) mlargs_f)
end
in (match (_63_569) with
| (lbs, mlargs) -> begin
(let app = (let _129_224 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _129_224))
in (let l_app = (FStar_List.fold_right (fun _63_573 out -> (match (_63_573) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = ([], arg.FStar_Extraction_ML_Syntax.ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_63_578), _63_581)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _129_228 = (let _129_227 = (FStar_Extraction_ML_Util.join f f')
in (_129_227, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _129_228 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _63_594)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _63_606 = (synth_exp g e0)
in (match (_63_606) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _129_230 = (let _129_229 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_129_229, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _129_230 rest)))
end))
end
| _63_609 -> begin
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
(let _63_626 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_63_626) with
| ((head, (vars, t)), qual) -> begin
(let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(let _63_630 = (FStar_Util.first_N n args)
in (match (_63_630) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (let head = (match (head.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(let _63_640 = head
in {FStar_Extraction_ML_Syntax.expr = _63_640.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _63_644}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((let _63_651 = head
in {FStar_Extraction_ML_Syntax.expr = _63_651.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t))}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _63_654 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (rest) with
| [] -> begin
(let _129_231 = (maybe_lalloc_eta_data g qual t head)
in (_129_231, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _63_658 -> begin
(synth_app qual (head, []) (FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end)))))
end))
end else begin
(err_uninst e)
end)
end))
end
| _63_660 -> begin
(let _63_664 = (synth_exp g head)
in (match (_63_664) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _63_687 = (FStar_List.fold_left (fun _63_671 _63_675 -> (match ((_63_671, _63_675)) with
| ((ml_bs, env), (b, _63_674)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _129_234 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_129_234, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_63_687) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _63_692 = (synth_exp env body)
in (match (_63_692) with
| (ml_body, f, t) -> begin
(let _63_702 = (FStar_List.fold_right (fun _63_696 _63_699 -> (match ((_63_696, _63_699)) with
| ((_63_694, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_63_702) with
| (f, tfun) -> begin
(let _129_237 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_129_237, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _63_714 -> (match (_63_714) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _63_738 = (match ((FStar_Util.prefix_until (fun _63_4 -> (match (_63_4) with
| (FStar_Util.Inr (_63_723), _63_726) -> begin
true
end
| _63_729 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _129_241 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _129_241))
end)
in (match (_63_738) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(let _63_747 = (FStar_Util.first_N n bs)
in (match (_63_747) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _63_5 -> (match (_63_5) with
| (FStar_Util.Inl (a), _63_756) -> begin
a
end
| _63_759 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _129_245 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_129_245, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _63_768 -> begin
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
| _63_773 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _63_776 -> begin
(err_value_restriction e)
end)))
end))
end
| _63_778 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _63_793 -> (match (_63_793) with
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
in (let _63_822 = (FStar_List.fold_right (fun lb _63_803 -> (match (_63_803) with
| (env, lbs) -> begin
(let _63_816 = lb
in (match (_63_816) with
| (lbname, _63_806, (t, (_63_809, polytype)), add_unit, _63_815) -> begin
(let _63_819 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_63_819) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_63_822) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _63_828 = (synth_exp env_body e')
in (match (_63_828) with
| (e', f', t') -> begin
(let f = (let _129_255 = (let _129_254 = (FStar_List.map Prims.fst lbs)
in (f')::_129_254)
in (FStar_Extraction_ML_Util.join_l _129_255))
in (let _129_260 = (let _129_259 = (let _129_258 = (let _129_257 = (let _129_256 = (FStar_List.map Prims.snd lbs)
in (is_rec, _129_256))
in (_129_257, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_129_258))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t') _129_259))
in (_129_260, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _63_837 = (synth_exp g scrutinee)
in (match (_63_837) with
| (e, f_e, t_e) -> begin
(let _63_841 = (check_pats_for_ite pats)
in (match (_63_841) with
| (b, then_e, else_e) -> begin
(let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(let _63_853 = (synth_exp g then_e)
in (match (_63_853) with
| (then_mle, f_then, t_then) -> begin
(let _63_857 = (synth_exp g else_e)
in (match (_63_857) with
| (else_mle, f_else, t_else) -> begin
(let _63_860 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_63_860) with
| (t_branch, maybe_lift) -> begin
(let _129_291 = (let _129_289 = (let _129_288 = (let _129_287 = (maybe_lift then_mle t_then)
in (let _129_286 = (let _129_285 = (maybe_lift else_mle t_else)
in Some (_129_285))
in (e, _129_287, _129_286)))
in FStar_Extraction_ML_Syntax.MLE_If (_129_288))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _129_289))
in (let _129_290 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_129_291, _129_290, t_branch)))
end))
end))
end))
end
| _63_862 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _63_866 -> (match (_63_866) with
| (pat, when_opt, branch) -> begin
(let _63_869 = (extract_pat g pat)
in (match (_63_869) with
| (env, p) -> begin
(let _63_880 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(let _63_876 = (synth_exp env w)
in (match (_63_876) with
| (w, f_w, t_w) -> begin
(let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_63_880) with
| (when_opt, f_when) -> begin
(let _63_884 = (synth_exp env branch)
in (match (_63_884) with
| (branch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _63_887 -> (match (_63_887) with
| (p, wopt) -> begin
(let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (branch, f_branch, t_branch)))
end))))
end))
end))
end))
end))))
in (match (mlbranches) with
| [] -> begin
(let _63_894 = (let _129_294 = (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid)
in (FStar_Extraction_ML_Env.lookup_fv g _129_294))
in (match (_63_894) with
| (fw, _63_893) -> begin
(let _129_299 = (let _129_298 = (let _129_297 = (let _129_296 = (let _129_295 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_129_295)::[])
in (fw, _129_296))
in FStar_Extraction_ML_Syntax.MLE_App (_129_297))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _129_298))
in (_129_299, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_63_897, _63_899, (_63_901, f_first, t_first))::rest -> begin
(let _63_927 = (FStar_List.fold_left (fun _63_909 _63_919 -> (match ((_63_909, _63_919)) with
| ((topt, f), (_63_911, _63_913, (_63_915, f_branch, t_branch))) -> begin
(let f = (FStar_Extraction_ML_Util.join f f_branch)
in (let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
if (FStar_Extraction_ML_Util.type_leq g t t_branch) then begin
Some (t_branch)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_branch t) then begin
Some (t)
end else begin
None
end
end
end)
in (topt, f)))
end)) (Some (t_first), f_first) rest)
in (match (_63_927) with
| (topt, f_match) -> begin
(let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _63_938 -> (match (_63_938) with
| (p, (wopt, _63_931), (b, _63_935, t)) -> begin
(let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_63_941) -> begin
b
end)
in (p, wopt, b))
end))))
in (let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _129_303 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_129_303, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _63_951)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end)))

let fresh = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _63_963 = (FStar_Util.incr c)
in (let _129_306 = (FStar_ST.read c)
in (x, _129_306)))))

let ind_discriminator_body = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _63_972 = (let _129_313 = (FStar_Absyn_Util.fv constrName)
in (FStar_Extraction_ML_Env.lookup_fv env _129_313))
in (match (_63_972) with
| (_63_970, ts) -> begin
(let _63_984 = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_63_974, _63_976, t) -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild)::[], ((Prims.fst ts), t))
end
| _63_981 -> begin
([], ts)
end)
in (match (_63_984) with
| (arg_pat, ts) -> begin
(let rid = constrName
in (let targ = (Prims.snd ts)
in (let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_bool_ty))
in (let discrBody = (let _129_328 = (let _129_327 = (let _129_326 = (let _129_325 = (let _129_324 = (let _129_323 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _129_322 = (let _129_321 = (let _129_317 = (let _129_315 = (let _129_314 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_129_314, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_129_315))
in (let _129_316 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_129_317, None, _129_316)))
in (let _129_320 = (let _129_319 = (let _129_318 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _129_318))
in (_129_319)::[])
in (_129_321)::_129_320))
in (_129_323, _129_322)))
in FStar_Extraction_ML_Syntax.MLE_Match (_129_324))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _129_325))
in (((mlid, targ))::[], _129_326))
in FStar_Extraction_ML_Syntax.MLE_Fun (_129_327))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _129_328))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Absyn_Syntax.ident); FStar_Extraction_ML_Syntax.mllb_tysc = ((Prims.fst ts), disc_ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[]))))))
end))
end))))




