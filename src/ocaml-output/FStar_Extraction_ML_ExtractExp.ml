
open Prims
let fail = (fun r msg -> (let _75_8 = (let _166_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _166_3))
in (FStar_All.exit 1)))

let err_uninst = (fun e -> (let _166_6 = (let _166_5 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _166_5))
in (fail e.FStar_Absyn_Syntax.pos _166_6)))

let err_ill_typed_application = (fun e args t -> (let _166_12 = (let _166_11 = (FStar_Absyn_Print.exp_to_string e)
in (let _166_10 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _166_11 _166_10)))
in (fail e.FStar_Absyn_Syntax.pos _166_12)))

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun e f0 f1 -> (let _166_18 = (let _166_17 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _166_17 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _166_18)))

let is_constructor = (fun e -> (match ((let _166_21 = (FStar_Absyn_Util.compress_exp e)
in _166_21.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _75_34 -> begin
false
end))

let rec is_value_or_type_app = (fun e -> (match ((let _166_24 = (FStar_Absyn_Util.compress_exp e)
in _166_24.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _75_55 -> (match (_75_55) with
| (te, _75_54) -> begin
(match (te) with
| FStar_Util.Inl (_75_57) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _166_26 = (FStar_Absyn_Util.compress_exp head)
in _166_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _75_1 -> (match (_75_1) with
| (FStar_Util.Inl (te), _75_71) -> begin
true
end
| _75_74 -> begin
false
end))))
end
| _75_76 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _75_90 -> begin
false
end))

let rec is_ml_value = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_75_111, fields) -> begin
(FStar_Util.for_all (fun _75_118 -> (match (_75_118) with
| (_75_116, e) -> begin
(is_ml_value e)
end)) fields)
end
| _75_120 -> begin
false
end))

let translate_typ = (fun g t -> (let _166_35 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _166_35)))

let translate_typ_of_arg = (fun g a -> (let _166_40 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _166_40)))

let instantiate = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

let erasable = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

let erase = (fun g e f t -> if (erasable g f t) then begin
(let _75_135 = (FStar_Extraction_ML_Env.debug g (fun _75_134 -> (match (()) with
| () -> begin
(let _166_61 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _166_60 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _166_61 _166_60)))
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
| _75_147 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

let extract_pat = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_75_156) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _166_82 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _166_82))
in (let when_clause = (let _166_91 = (let _166_90 = (let _166_89 = (let _166_88 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _166_87 = (let _166_86 = (let _166_85 = (let _166_84 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _166_83 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_83)) _166_84))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _166_85))
in (_166_86)::[])
in (_166_88)::_166_87))
in (FStar_Extraction_ML_Util.prims_op_equality, _166_89))
in FStar_Extraction_ML_Syntax.MLE_App (_166_90))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_91))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _166_95 = (let _166_94 = (let _166_93 = (let _166_92 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_166_92))
in (_166_93, []))
in Some (_166_94))
in (g, _166_95))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _75_181 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _75_171}, ttys) -> begin
(n, ttys)
end
| _75_178 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_75_181) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _75_185 = (FStar_Util.first_N nTyVars pats)
in (match (_75_185) with
| (tysVarPats, restPats) -> begin
(let _75_192 = (FStar_Util.fold_map (fun g _75_189 -> (match (_75_189) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_75_192) with
| (g, tyMLPats) -> begin
(let _75_199 = (FStar_Util.fold_map (fun g _75_196 -> (match (_75_196) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_75_199) with
| (g, restMLPats) -> begin
(let _75_207 = (let _166_101 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _75_2 -> (match (_75_2) with
| Some (x) -> begin
(x)::[]
end
| _75_204 -> begin
[]
end))))
in (FStar_All.pipe_right _166_101 FStar_List.split))
in (match (_75_207) with
| (mlPats, when_clauses) -> begin
(let _166_105 = (let _166_104 = (let _166_103 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _166_102 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_166_103, _166_102)))
in Some (_166_104))
in (g, _166_105))
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
| FStar_Absyn_Syntax.Pat_dot_term (_75_219) -> begin
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
| _75_242 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _166_114 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_166_114))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _75_257 = (extract_one_pat true g p)
in (match (_75_257) with
| (g, p) -> begin
(let ps = (let _166_117 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _166_116 = (extract_one_pat true g x)
in (Prims.snd _166_116)))))
in (p)::_166_117)
in (let _75_273 = (FStar_All.pipe_right ps (FStar_List.partition (fun _75_3 -> (match (_75_3) with
| (_75_262, _75_266::_75_264) -> begin
true
end
| _75_270 -> begin
false
end))))
in (match (_75_273) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _75_276 -> (match (_75_276) with
| (x, whens) -> begin
(let _166_120 = (mk_when_clause whens)
in (x, _166_120))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _166_124 = (let _166_123 = (let _166_122 = (let _166_121 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_166_121))
in (_166_122, None))
in (_166_123)::ps)
in (g, _166_124))
end)
in res))
end)))
end))
end
| _75_282 -> begin
(let _75_287 = (extract_one_pat false g p)
in (match (_75_287) with
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
| _75_299 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

let ffi_mltuple_mlp = (fun n -> (let name = if ((2 < n) && (n < 6)) then begin
(let _166_133 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _166_133))
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
in (let tup = (let _166_140 = (let _166_139 = (let _166_138 = (let _166_137 = (let _166_136 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_166_136))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _166_137))
in (_166_138, args))
in FStar_Extraction_ML_Syntax.MLE_App (_166_139))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _166_140))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _75_318 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _75_328, t1) -> begin
(let x = (let _166_153 = (FStar_Absyn_Util.gensym ())
in (_166_153, (- (1))))
in (let _166_156 = (let _166_155 = (let _166_154 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _166_154))
in (_166_155)::more_args)
in (eta_args _166_156 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_75_334, _75_336) -> begin
((FStar_List.rev more_args), t)
end
| _75_340 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_75_345, args), Some (FStar_Absyn_Syntax.Record_ctor (_75_350, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _75_359 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let _75_365 = (eta_args [] residualType)
in (match (_75_365) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _166_165 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _166_165))
end
| _75_368 -> begin
(let _75_371 = (FStar_List.unzip eargs)
in (match (_75_371) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _166_167 = (let _166_166 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _166_166))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _166_167))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _75_378 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _75_380}, mlarg::[]), _75_389) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _75_392 = (FStar_Extraction_ML_Env.debug g (fun _75_391 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_75_395, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _75_399}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (let e = (match (args) with
| [] -> begin
proj
end
| _75_416 -> begin
(let _166_170 = (let _166_169 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_166_169, args))
in FStar_Extraction_ML_Syntax.MLE_App (_166_170))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _166_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_171))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _166_172 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_172))
end
| _75_452 -> begin
mlAppExpr
end)))))

let check_pats_for_ite = (fun l -> (let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _75_458 = (FStar_List.hd l)
in (match (_75_458) with
| (p1, w1, e1) -> begin
(let _75_462 = (let _166_175 = (FStar_List.tl l)
in (FStar_List.hd _166_175))
in (match (_75_462) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _75_482 -> begin
def
end)
end))
end))
end))

let rec check_exp = (fun g e f t -> (let _75_492 = (let _166_192 = (check_exp' g e f t)
in (erase g _166_192 f t))
in (match (_75_492) with
| (e, _75_489, _75_491) -> begin
e
end)))
and check_exp' = (fun g e f t -> (let _75_500 = (synth_exp g e)
in (match (_75_500) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp = (fun g e -> (let _75_506 = (synth_exp' g e)
in (match (_75_506) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun g e -> (let _75_510 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _166_203 = (let _166_202 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "now synthesizing expression :  %s \n" _166_202))
in (FStar_Util.print_string _166_203))))
in (match ((let _166_204 = (FStar_Absyn_Util.compress_exp e)
in _166_204.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let ml_ty = (translate_typ g t)
in (let _166_208 = (let _166_207 = (let _166_206 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _166_205 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_205)) _166_206))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _166_207))
in (_166_208, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
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
(let _75_537 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_75_537) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _166_209 = (maybe_lalloc_eta_data g qual t x)
in (_166_209, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _75_542 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _75_551 _75_554 restArgs -> (match ((_75_551, _75_554)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _75_558) -> begin
(let _75_569 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _166_218 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _166_218))
end else begin
(FStar_List.fold_left (fun _75_562 _75_565 -> (match ((_75_562, _75_565)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(let x = (let _166_221 = (FStar_Absyn_Util.gensym ())
in (_166_221, (- (1))))
in (let _166_223 = (let _166_222 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_166_222)::out_args)
in (((x, arg))::lbs, _166_223)))
end
end)) ([], []) mlargs_f)
end
in (match (_75_569) with
| (lbs, mlargs) -> begin
(let app = (let _166_224 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _166_224))
in (let l_app = (FStar_List.fold_right (fun _75_573 out -> (match (_75_573) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = ([], arg.FStar_Extraction_ML_Syntax.ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_75_578), _75_581)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _166_228 = (let _166_227 = (FStar_Extraction_ML_Util.join f f')
in (_166_227, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _166_228 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _75_594)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _75_606 = (synth_exp g e0)
in (match (_75_606) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _166_230 = (let _166_229 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_166_229, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _166_230 rest)))
end))
end
| _75_609 -> begin
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
(let _75_626 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_75_626) with
| ((head, (vars, t)), qual) -> begin
(let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(let _75_630 = (FStar_Util.first_N n args)
in (match (_75_630) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (let head = (match (head.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(let _75_640 = head
in {FStar_Extraction_ML_Syntax.expr = _75_640.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _75_644}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((let _75_651 = head
in {FStar_Extraction_ML_Syntax.expr = _75_651.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t))}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _75_654 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (rest) with
| [] -> begin
(let _166_231 = (maybe_lalloc_eta_data g qual t head)
in (_166_231, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _75_658 -> begin
(synth_app qual (head, []) (FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end)))))
end))
end else begin
(err_uninst e)
end)
end))
end
| _75_660 -> begin
(let _75_664 = (synth_exp g head)
in (match (_75_664) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _75_687 = (FStar_List.fold_left (fun _75_671 _75_675 -> (match ((_75_671, _75_675)) with
| ((ml_bs, env), (b, _75_674)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _166_234 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_166_234, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_75_687) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _75_692 = (synth_exp env body)
in (match (_75_692) with
| (ml_body, f, t) -> begin
(let _75_702 = (FStar_List.fold_right (fun _75_696 _75_699 -> (match ((_75_696, _75_699)) with
| ((_75_694, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_75_702) with
| (f, tfun) -> begin
(let _166_237 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_166_237, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _75_714 -> (match (_75_714) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _75_738 = (match ((FStar_Util.prefix_until (fun _75_4 -> (match (_75_4) with
| (FStar_Util.Inr (_75_723), _75_726) -> begin
true
end
| _75_729 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _166_241 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _166_241))
end)
in (match (_75_738) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(let _75_747 = (FStar_Util.first_N n bs)
in (match (_75_747) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _75_5 -> (match (_75_5) with
| (FStar_Util.Inl (a), _75_756) -> begin
a
end
| _75_759 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _166_245 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_166_245, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _75_768 -> begin
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
| _75_773 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _75_776 -> begin
(err_value_restriction e)
end)))
end))
end
| _75_778 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _75_793 -> (match (_75_793) with
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
in (let _75_822 = (FStar_List.fold_right (fun lb _75_803 -> (match (_75_803) with
| (env, lbs) -> begin
(let _75_816 = lb
in (match (_75_816) with
| (lbname, _75_806, (t, (_75_809, polytype)), add_unit, _75_815) -> begin
(let _75_819 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_75_819) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_75_822) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _75_828 = (synth_exp env_body e')
in (match (_75_828) with
| (e', f', t') -> begin
(let f = (let _166_255 = (let _166_254 = (FStar_List.map Prims.fst lbs)
in (f')::_166_254)
in (FStar_Extraction_ML_Util.join_l _166_255))
in (let _166_260 = (let _166_259 = (let _166_258 = (let _166_257 = (let _166_256 = (FStar_List.map Prims.snd lbs)
in (is_rec, _166_256))
in (_166_257, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_166_258))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t') _166_259))
in (_166_260, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _75_837 = (synth_exp g scrutinee)
in (match (_75_837) with
| (e, f_e, t_e) -> begin
(let _75_841 = (check_pats_for_ite pats)
in (match (_75_841) with
| (b, then_e, else_e) -> begin
(let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(let _75_853 = (synth_exp g then_e)
in (match (_75_853) with
| (then_mle, f_then, t_then) -> begin
(let _75_857 = (synth_exp g else_e)
in (match (_75_857) with
| (else_mle, f_else, t_else) -> begin
(let _75_860 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_75_860) with
| (t_branch, maybe_lift) -> begin
(let _166_291 = (let _166_289 = (let _166_288 = (let _166_287 = (maybe_lift then_mle t_then)
in (let _166_286 = (let _166_285 = (maybe_lift else_mle t_else)
in Some (_166_285))
in (e, _166_287, _166_286)))
in FStar_Extraction_ML_Syntax.MLE_If (_166_288))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _166_289))
in (let _166_290 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_166_291, _166_290, t_branch)))
end))
end))
end))
end
| _75_862 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _75_866 -> (match (_75_866) with
| (pat, when_opt, branch) -> begin
(let _75_869 = (extract_pat g pat)
in (match (_75_869) with
| (env, p) -> begin
(let _75_880 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(let _75_876 = (synth_exp env w)
in (match (_75_876) with
| (w, f_w, t_w) -> begin
(let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_75_880) with
| (when_opt, f_when) -> begin
(let _75_884 = (synth_exp env branch)
in (match (_75_884) with
| (branch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _75_887 -> (match (_75_887) with
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
(let _75_894 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_75_894) with
| (fw, _75_893) -> begin
(let _166_298 = (let _166_297 = (let _166_296 = (let _166_295 = (let _166_294 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_166_294)::[])
in (fw, _166_295))
in FStar_Extraction_ML_Syntax.MLE_App (_166_296))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _166_297))
in (_166_298, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_75_897, _75_899, (_75_901, f_first, t_first))::rest -> begin
(let _75_927 = (FStar_List.fold_left (fun _75_909 _75_919 -> (match ((_75_909, _75_919)) with
| ((topt, f), (_75_911, _75_913, (_75_915, f_branch, t_branch))) -> begin
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
in (match (_75_927) with
| (topt, f_match) -> begin
(let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _75_938 -> (match (_75_938) with
| (p, (wopt, _75_931), (b, _75_935, t)) -> begin
(let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_75_941) -> begin
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
in (let _166_302 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_166_302, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _75_951)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(FStar_All.failwith "Unexpected expression")
end)))

let fresh = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _75_963 = (FStar_Util.incr c)
in (let _166_305 = (FStar_ST.read c)
in (x, _166_305)))))

let ind_discriminator_body = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _75_972 = (FStar_Extraction_ML_Env.lookup_fv env (FStar_Absyn_Util.fv constrName))
in (match (_75_972) with
| (_75_970, ts) -> begin
(let _75_984 = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_75_974, _75_976, t) -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild)::[], ((Prims.fst ts), t))
end
| _75_981 -> begin
([], ts)
end)
in (match (_75_984) with
| (arg_pat, ts) -> begin
(let rid = constrName
in (let targ = (Prims.snd ts)
in (let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_bool_ty))
in (let discrBody = (let _166_326 = (let _166_325 = (let _166_324 = (let _166_323 = (let _166_322 = (let _166_321 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _166_320 = (let _166_319 = (let _166_315 = (let _166_313 = (let _166_312 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_166_312, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_166_313))
in (let _166_314 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_166_315, None, _166_314)))
in (let _166_318 = (let _166_317 = (let _166_316 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _166_316))
in (_166_317)::[])
in (_166_319)::_166_318))
in (_166_321, _166_320)))
in FStar_Extraction_ML_Syntax.MLE_Match (_166_322))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_323))
in (((mlid, targ))::[], _166_324))
in FStar_Extraction_ML_Syntax.MLE_Fun (_166_325))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _166_326))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = ((Prims.fst ts), disc_ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[]))))))
end))
end))))




