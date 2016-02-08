
open Prims
let fail = (fun r msg -> (let _79_9 = (let _181_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _181_3))
in (FStar_All.exit 1)))

let err_uninst = (fun e -> (let _181_6 = (let _181_5 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _181_5))
in (fail e.FStar_Absyn_Syntax.pos _181_6)))

let err_ill_typed_application = (fun e args t -> (let _181_12 = (let _181_11 = (FStar_Absyn_Print.exp_to_string e)
in (let _181_10 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _181_11 _181_10)))
in (fail e.FStar_Absyn_Syntax.pos _181_12)))

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun e f0 f1 -> (let _181_18 = (let _181_17 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _181_17 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _181_18)))

let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _181_21 = (FStar_Absyn_Util.compress_exp e)
in _181_21.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _79_35 -> begin
false
end))

let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _181_24 = (FStar_Absyn_Util.compress_exp e)
in _181_24.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_56 -> (match (_79_56) with
| (te, _79_55) -> begin
(match (te) with
| FStar_Util.Inl (_79_58) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _181_26 = (FStar_Absyn_Util.compress_exp head)
in _181_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_1 -> (match (_79_1) with
| (FStar_Util.Inl (te), _79_72) -> begin
true
end
| _79_75 -> begin
false
end))))
end
| _79_77 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _79_91 -> begin
false
end))

let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_112, fields) -> begin
(FStar_Util.for_all (fun _79_119 -> (match (_79_119) with
| (_79_117, e) -> begin
(is_ml_value e)
end)) fields)
end
| _79_121 -> begin
false
end))

let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _181_35 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _181_35)))

let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _181_40 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _181_40)))

let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(let _79_136 = (FStar_Extraction_ML_Env.debug g (fun _79_135 -> (match (()) with
| () -> begin
(let _181_61 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _181_60 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _181_61 _181_60)))
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

let maybe_coerce : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e tInferred tExpected -> (match ((FStar_Extraction_ML_Util.type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _79_148 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_79_157) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _181_82 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _181_82))
in (let when_clause = (let _181_91 = (let _181_90 = (let _181_89 = (let _181_88 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _181_87 = (let _181_86 = (let _181_85 = (let _181_84 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _181_83 -> FStar_Extraction_ML_Syntax.MLE_Const (_181_83)) _181_84))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _181_85))
in (_181_86)::[])
in (_181_88)::_181_87))
in (FStar_Extraction_ML_Util.prims_op_equality, _181_89))
in FStar_Extraction_ML_Syntax.MLE_App (_181_90))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _181_91))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _181_95 = (let _181_94 = (let _181_93 = (let _181_92 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_181_92))
in (_181_93, []))
in Some (_181_94))
in (g, _181_95))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _79_184 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _79_172}, ttys, _79_178) -> begin
(n, ttys)
end
| _79_181 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_79_184) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _79_188 = (FStar_Util.first_N nTyVars pats)
in (match (_79_188) with
| (tysVarPats, restPats) -> begin
(let _79_195 = (FStar_Util.fold_map (fun g _79_192 -> (match (_79_192) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_79_195) with
| (g, tyMLPats) -> begin
(let _79_202 = (FStar_Util.fold_map (fun g _79_199 -> (match (_79_199) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_79_202) with
| (g, restMLPats) -> begin
(let _79_210 = (let _181_101 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| Some (x) -> begin
(x)::[]
end
| _79_207 -> begin
[]
end))))
in (FStar_All.pipe_right _181_101 FStar_List.split))
in (match (_79_210) with
| (mlPats, when_clauses) -> begin
(let _181_105 = (let _181_104 = (let _181_103 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _181_102 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_181_103, _181_102)))
in Some (_181_104))
in (g, _181_105))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false false imp)
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
in (let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_term (_79_222) -> begin
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
| _79_245 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _181_114 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_181_114))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _79_260 = (extract_one_pat true g p)
in (match (_79_260) with
| (g, p) -> begin
(let ps = (let _181_117 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _181_116 = (extract_one_pat true g x)
in (Prims.snd _181_116)))))
in (p)::_181_117)
in (let _79_276 = (FStar_All.pipe_right ps (FStar_List.partition (fun _79_3 -> (match (_79_3) with
| (_79_265, _79_269::_79_267) -> begin
true
end
| _79_273 -> begin
false
end))))
in (match (_79_276) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _79_279 -> (match (_79_279) with
| (x, whens) -> begin
(let _181_120 = (mk_when_clause whens)
in (x, _181_120))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _181_124 = (let _181_123 = (let _181_122 = (let _181_121 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_181_121))
in (_181_122, None))
in (_181_123)::ps)
in (g, _181_124))
end)
in res))
end)))
end))
end
| _79_285 -> begin
(let _79_290 = (extract_one_pat false g p)
in (match (_79_290) with
| (g, (p, whens)) -> begin
(let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

let normalize_abs : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun e0 -> (let rec aux = (fun bs e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _79_302 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (let name = if ((2 < n) && (n < 6)) then begin
(let _181_133 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _181_133))
end else begin
if (n = 2) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in (("Camlstack")::[], name)))

let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(let args = (FStar_List.map Prims.snd fields)
in (let tup = (let _181_140 = (let _181_139 = (let _181_138 = (let _181_137 = (let _181_136 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_181_136))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _181_137))
in (_181_138, args))
in FStar_Extraction_ML_Syntax.MLE_App (_181_139))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _181_140))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _79_321 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _79_331, t1) -> begin
(let x = (let _181_153 = (FStar_Absyn_Util.gensym ())
in (_181_153, (- (1))))
in (let _181_156 = (let _181_155 = (let _181_154 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _181_154))
in (_181_155)::more_args)
in (eta_args _181_156 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_337, _79_339) -> begin
((FStar_List.rev more_args), t)
end
| _79_343 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_79_348, args), Some (FStar_Absyn_Syntax.Record_ctor (_79_353, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _79_362 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let _79_368 = (eta_args [] residualType)
in (match (_79_368) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _181_165 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _181_165))
end
| _79_371 -> begin
(let _79_374 = (FStar_List.unzip eargs)
in (match (_79_374) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _181_167 = (let _181_166 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _181_166))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _181_167))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _79_381 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _79_383}, mlarg::[]), _79_392) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _79_395 = (FStar_Extraction_ML_Env.debug g (fun _79_394 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_79_398, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _79_402}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (let e = (match (args) with
| [] -> begin
proj
end
| _79_419 -> begin
(let _181_170 = (let _181_169 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_181_169, args))
in FStar_Extraction_ML_Syntax.MLE_App (_181_170))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _181_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _181_171))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _181_172 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _181_172))
end
| _79_455 -> begin
mlAppExpr
end)))))

let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _79_461 = (FStar_List.hd l)
in (match (_79_461) with
| (p1, w1, e1) -> begin
(let _79_465 = (let _181_175 = (FStar_List.tl l)
in (FStar_List.hd _181_175))
in (match (_79_465) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _79_485 -> begin
def
end)
end))
end))
end))

let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (let _79_495 = (let _181_192 = (check_exp' g e f t)
in (erase g _181_192 f t))
in (match (_79_495) with
| (e, _79_492, _79_494) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (let _79_503 = (synth_exp g e)
in (match (_79_503) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (let _79_509 = (synth_exp' g e)
in (match (_79_509) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (let _79_513 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _181_204 = (let _181_203 = (FStar_Absyn_Print.tag_of_exp e)
in (let _181_202 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _181_203 _181_202)))
in (FStar_Util.print_string _181_204))))
in (match ((let _181_205 = (FStar_Absyn_Util.compress_exp e)
in _181_205.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let ml_ty = (translate_typ g t)
in (let _181_209 = (let _181_208 = (let _181_207 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _181_206 -> FStar_Extraction_ML_Syntax.MLE_Const (_181_206)) _181_207))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _181_208))
in (_181_209, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
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
(let _79_542 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_79_542) with
| ((x, mltys, _79_539), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _181_210 = (maybe_lalloc_eta_data g qual t x)
in (_181_210, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _79_547 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _79_556 _79_559 restArgs -> (match ((_79_556, _79_559)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _79_563) -> begin
(let _79_574 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _181_219 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _181_219))
end else begin
(FStar_List.fold_left (fun _79_567 _79_570 -> (match ((_79_567, _79_570)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(let x = (let _181_222 = (FStar_Absyn_Util.gensym ())
in (_181_222, (- (1))))
in (let _181_224 = (let _181_223 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_181_223)::out_args)
in (((x, arg))::lbs, _181_224)))
end
end)) ([], []) mlargs_f)
end
in (match (_79_574) with
| (lbs, mlargs) -> begin
(let app = (let _181_225 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _181_225))
in (let l_app = (FStar_List.fold_right (fun _79_578 out -> (match (_79_578) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = ([], arg.FStar_Extraction_ML_Syntax.ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_79_583), _79_586)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _181_229 = (let _181_228 = (FStar_Extraction_ML_Util.join f f')
in (_181_228, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _181_229 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _79_599)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _79_611 = (synth_exp g e0)
in (match (_79_611) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _181_231 = (let _181_230 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_181_230, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _181_231 rest)))
end))
end
| _79_614 -> begin
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
(let _79_632 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_79_632) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(let has_typ_apps = (match (args) with
| (FStar_Util.Inl (_79_636), _79_639)::_79_634 -> begin
true
end
| _79_643 -> begin
false
end)
in (let _79_694 = (match (vars) with
| _79_648::_79_646 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _79_651 -> begin
(let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(let _79_655 = (FStar_Util.first_N n args)
in (match (_79_655) with
| (prefix, rest) -> begin
(let _79_665 = if (FStar_All.pipe_right prefix (FStar_Util.for_some (fun _79_4 -> (match (_79_4) with
| (FStar_Util.Inr (_79_658), _79_661) -> begin
true
end
| _79_664 -> begin
false
end)))) then begin
(err_uninst head)
end else begin
()
end
in (let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(let _79_675 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _79_675.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _79_679}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((let _79_686 = head
in {FStar_Extraction_ML_Syntax.expr = _79_686.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t))}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _79_689 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest)))))
end))
end else begin
(err_uninst head)
end)
end)
in (match (_79_694) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _181_233 = (maybe_lalloc_eta_data g qual head_t head_ml)
in (_181_233, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _79_697 -> begin
(synth_app qual (head_ml, []) (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _79_699 -> begin
(let _79_703 = (synth_exp g head)
in (match (_79_703) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _79_726 = (FStar_List.fold_left (fun _79_710 _79_714 -> (match ((_79_710, _79_714)) with
| ((ml_bs, env), (b, _79_713)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _181_236 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_181_236, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_79_726) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _79_731 = (synth_exp env body)
in (match (_79_731) with
| (ml_body, f, t) -> begin
(let _79_741 = (FStar_List.fold_right (fun _79_735 _79_738 -> (match ((_79_735, _79_738)) with
| ((_79_733, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_79_741) with
| (f, tfun) -> begin
(let _181_239 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_181_239, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _79_753 -> (match (_79_753) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _79_777 = (match ((FStar_Util.prefix_until (fun _79_5 -> (match (_79_5) with
| (FStar_Util.Inr (_79_762), _79_765) -> begin
true
end
| _79_768 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _181_243 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _181_243))
end)
in (match (_79_777) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(let _79_786 = (FStar_Util.first_N n bs)
in (match (_79_786) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _79_6 -> (match (_79_6) with
| (FStar_Util.Inl (a), _79_795) -> begin
a
end
| _79_798 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _181_247 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_181_247, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _79_807 -> begin
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
| _79_812 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _79_815 -> begin
(err_value_restriction e)
end)))
end))
end
| _79_817 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _79_832 -> (match (_79_832) with
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
in (let _79_861 = (FStar_List.fold_right (fun lb _79_842 -> (match (_79_842) with
| (env, lbs) -> begin
(let _79_855 = lb
in (match (_79_855) with
| (lbname, _79_845, (t, (_79_848, polytype)), add_unit, _79_854) -> begin
(let _79_858 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_79_858) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_79_861) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _79_867 = (synth_exp env_body e')
in (match (_79_867) with
| (e', f', t') -> begin
(let f = (let _181_257 = (let _181_256 = (FStar_List.map Prims.fst lbs)
in (f')::_181_256)
in (FStar_Extraction_ML_Util.join_l _181_257))
in (let _181_262 = (let _181_261 = (let _181_260 = (let _181_259 = (let _181_258 = (FStar_List.map Prims.snd lbs)
in (is_rec, _181_258))
in (_181_259, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_181_260))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t') _181_261))
in (_181_262, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _79_876 = (synth_exp g scrutinee)
in (match (_79_876) with
| (e, f_e, t_e) -> begin
(let _79_880 = (check_pats_for_ite pats)
in (match (_79_880) with
| (b, then_e, else_e) -> begin
(let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(let _79_892 = (synth_exp g then_e)
in (match (_79_892) with
| (then_mle, f_then, t_then) -> begin
(let _79_896 = (synth_exp g else_e)
in (match (_79_896) with
| (else_mle, f_else, t_else) -> begin
(let _79_899 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_79_899) with
| (t_branch, maybe_lift) -> begin
(let _181_293 = (let _181_291 = (let _181_290 = (let _181_289 = (maybe_lift then_mle t_then)
in (let _181_288 = (let _181_287 = (maybe_lift else_mle t_else)
in Some (_181_287))
in (e, _181_289, _181_288)))
in FStar_Extraction_ML_Syntax.MLE_If (_181_290))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _181_291))
in (let _181_292 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_181_293, _181_292, t_branch)))
end))
end))
end))
end
| _79_901 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _79_905 -> (match (_79_905) with
| (pat, when_opt, branch) -> begin
(let _79_908 = (extract_pat g pat)
in (match (_79_908) with
| (env, p) -> begin
(let _79_919 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(let _79_915 = (synth_exp env w)
in (match (_79_915) with
| (w, f_w, t_w) -> begin
(let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_79_919) with
| (when_opt, f_when) -> begin
(let _79_923 = (synth_exp env branch)
in (match (_79_923) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _79_926 -> (match (_79_926) with
| (p, wopt) -> begin
(let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
end))))
end))
end))
end))
end))))
in (match (mlbranches) with
| [] -> begin
(let _79_935 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_79_935) with
| (fw, _79_932, _79_934) -> begin
(let _181_300 = (let _181_299 = (let _181_298 = (let _181_297 = (let _181_296 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_181_296)::[])
in (fw, _181_297))
in FStar_Extraction_ML_Syntax.MLE_App (_181_298))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _181_299))
in (_181_300, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_79_938, _79_940, (_79_942, f_first, t_first))::rest -> begin
(let _79_968 = (FStar_List.fold_left (fun _79_950 _79_960 -> (match ((_79_950, _79_960)) with
| ((topt, f), (_79_952, _79_954, (_79_956, f_branch, t_branch))) -> begin
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
in (match (_79_968) with
| (topt, f_match) -> begin
(let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _79_979 -> (match (_79_979) with
| (p, (wopt, _79_972), (b, _79_976, t)) -> begin
(let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_79_982) -> begin
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
in (let _181_304 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_181_304, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _79_992)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end)))

let fresh : Prims.string  ->  (Prims.string * Prims.int) = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _79_1004 = (FStar_Util.incr c)
in (let _181_307 = (FStar_ST.read c)
in (x, _181_307)))))

let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _79_1015 = (FStar_Extraction_ML_Env.lookup_fv env (FStar_Absyn_Util.fv constrName))
in (match (_79_1015) with
| (_79_1011, ts, _79_1014) -> begin
(let _79_1027 = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_1017, _79_1019, t) -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild)::[], ((Prims.fst ts), t))
end
| _79_1024 -> begin
([], ts)
end)
in (match (_79_1027) with
| (arg_pat, ts) -> begin
(let rid = constrName
in (let targ = (Prims.snd ts)
in (let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_bool_ty))
in (let discrBody = (let _181_328 = (let _181_327 = (let _181_326 = (let _181_325 = (let _181_324 = (let _181_323 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _181_322 = (let _181_321 = (let _181_317 = (let _181_315 = (let _181_314 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_181_314, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_181_315))
in (let _181_316 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_181_317, None, _181_316)))
in (let _181_320 = (let _181_319 = (let _181_318 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _181_318))
in (_181_319)::[])
in (_181_321)::_181_320))
in (_181_323, _181_322)))
in FStar_Extraction_ML_Syntax.MLE_Match (_181_324))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _181_325))
in (((mlid, targ))::[], _181_326))
in FStar_Extraction_ML_Syntax.MLE_Fun (_181_327))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _181_328))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = ((Prims.fst ts), disc_ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[]))))))
end))
end))))




