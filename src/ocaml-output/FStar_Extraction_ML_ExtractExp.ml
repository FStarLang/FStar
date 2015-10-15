
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
(match ((is_constructor head)) with
| true -> begin
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
end
| false -> begin
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
end)
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _62_90 -> begin
false
end))

let rec is_ml_value = (fun e -> (match (e) with
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

let erase = (fun g e f t -> (match ((erasable g f t)) with
| true -> begin
(let _62_135 = (FStar_Extraction_ML_Env.debug g (fun _62_134 -> (match (()) with
| () -> begin
(let _127_61 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _127_60 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.fprint2 "Erasing %s at type %s\n" _127_61 _127_60)))
end)))
in (let e_val = (match ((FStar_Extraction_ML_Util.type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| false -> begin
FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t))
end)
in (e_val, f, t)))
end
| false -> begin
(e, f, t)
end))

let maybe_coerce = (fun g e tInferred etag tExpected -> (match ((FStar_Extraction_ML_Util.type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _62_148 -> begin
FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))
end))

let extract_pat = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_62_157) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _127_84 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _127_84))
in (let eq = (("Prims")::[], "op_Equality")
in (let when_clause = (let _127_90 = (let _127_89 = (let _127_88 = (let _127_87 = (let _127_86 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Absyn_Syntax.Const_int (c)))
in (FStar_All.pipe_left (fun _127_85 -> FStar_Extraction_ML_Syntax.MLE_Const (_127_85)) _127_86))
in (_127_87)::[])
in (FStar_Extraction_ML_Syntax.MLE_Var (x))::_127_88)
in (FStar_Extraction_ML_Syntax.MLE_Name (eq), _127_89))
in FStar_Extraction_ML_Syntax.MLE_App (_127_90))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[]))))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _127_94 = (let _127_93 = (let _127_92 = (let _127_91 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_127_91))
in (_127_92, []))
in Some (_127_93))
in (g, _127_94))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _62_180 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (n), ttys) -> begin
(n, ttys)
end
| _62_177 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_62_180) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _62_184 = (FStar_Util.first_N nTyVars pats)
in (match (_62_184) with
| (tysVarPats, restPats) -> begin
(let _62_191 = (FStar_Util.fold_map (fun g _62_188 -> (match (_62_188) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_62_191) with
| (g, tyMLPats) -> begin
(let _62_198 = (FStar_Util.fold_map (fun g _62_195 -> (match (_62_195) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_62_198) with
| (g, restMLPats) -> begin
(let _62_206 = (let _127_100 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _62_2 -> (match (_62_2) with
| Some (x) -> begin
(x)::[]
end
| _62_203 -> begin
[]
end))))
in (FStar_All.pipe_right _127_100 FStar_List.split))
in (match (_62_206) with
| (mlPats, when_clauses) -> begin
(let _127_104 = (let _127_103 = (let _127_102 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _127_101 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_127_102, _127_101)))
in Some (_127_103))
in (g, _127_104))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false imp)
in (g, (match (imp) with
| true -> begin
None
end
| false -> begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end))))
end
| FStar_Absyn_Syntax.Pat_wild (x) when disj -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false imp)
in (g, (match (imp) with
| true -> begin
None
end
| false -> begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end))))
end
| FStar_Absyn_Syntax.Pat_dot_term (_62_218) -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (let g = (FStar_Extraction_ML_Env.extend_ty g a (Some (mlty)))
in (g, (match (imp) with
| true -> begin
None
end
| false -> begin
Some ((FStar_Extraction_ML_Syntax.MLP_Wild, []))
end))))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) -> begin
(g, None)
end))
in (let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _62_241 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _127_113 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_127_113))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _62_256 = (extract_one_pat true g p)
in (match (_62_256) with
| (g, p) -> begin
(let ps = (let _127_116 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _127_115 = (extract_one_pat true g x)
in (Prims.snd _127_115)))))
in (p)::_127_116)
in (let _62_272 = (FStar_All.pipe_right ps (FStar_List.partition (fun _62_3 -> (match (_62_3) with
| (_62_261, _62_265::_62_263) -> begin
true
end
| _62_269 -> begin
false
end))))
in (match (_62_272) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _62_275 -> (match (_62_275) with
| (x, whens) -> begin
(let _127_119 = (mk_when_clause whens)
in (x, _127_119))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _127_123 = (let _127_122 = (let _127_121 = (let _127_120 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_127_120))
in (_127_121, None))
in (_127_122)::ps)
in (g, _127_123))
end)
in res))
end)))
end))
end
| _62_281 -> begin
(let _62_286 = (extract_one_pat false g p)
in (match (_62_286) with
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
| _62_298 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in (match ((FStar_Absyn_Util.is_fun e')) with
| true -> begin
(aux bs e')
end
| false -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end))
end)))
in (aux [] e0)))

let ffi_mltuple_mlp = (fun n -> (let name = (match (((2 < n) && (n < 6))) with
| true -> begin
(let _127_132 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _127_132))
end
| false -> begin
(match ((n = 2)) with
| true -> begin
"mkpair"
end
| false -> begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end)
end)
in (("Camlstack")::[], name)))

let fix_lalloc = (fun arg -> (match (arg) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(let args = (FStar_List.map Prims.snd fields)
in (let tup = (let _127_137 = (let _127_136 = (let _127_135 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_127_135))
in (_127_136, args))
in FStar_Extraction_ML_Syntax.MLE_App (_127_137))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _62_317 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _62_327, t1) -> begin
(let x = (let _127_150 = (FStar_Absyn_Util.gensym ())
in (_127_150, (- (1))))
in (eta_args ((((x, Some (t0)), FStar_Extraction_ML_Syntax.MLE_Var (x)))::more_args) t1))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_62_333, _62_335) -> begin
(FStar_List.rev more_args)
end
| _62_339 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_62_344, args), Some (FStar_Absyn_Syntax.Record_ctor (_62_349, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))
end
| _62_358 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let eargs = (eta_args [] residualType)
in (match (eargs) with
| [] -> begin
(let _127_159 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _127_159))
end
| _62_365 -> begin
(let _62_368 = (FStar_List.unzip eargs)
in (match (_62_368) with
| (binders, eargs) -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _127_160 = (FStar_All.pipe_left (as_record qual) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _127_160))
in FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))
end
| _62_375 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)))
in (match ((mlAppExpr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlarg::[]), _62_383) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _62_386 = (FStar_Extraction_ML_Env.debug g (fun _62_385 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_62_389, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (match (args) with
| [] -> begin
proj
end
| _62_407 -> begin
FStar_Extraction_ML_Syntax.MLE_App ((proj, args))
end)))
end
| ((FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(FStar_All.pipe_left (resugar_and_maybe_eta qual) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(FStar_All.pipe_left (resugar_and_maybe_eta qual) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
end
| _62_436 -> begin
mlAppExpr
end)))))

let rec check_exp = (fun g e f t -> (let _62_446 = (let _127_178 = (check_exp' g e f t)
in (erase g _127_178 f t))
in (match (_62_446) with
| (e, _62_443, _62_445) -> begin
e
end)))
and check_exp' = (fun g e f t -> (match ((let _127_183 = (FStar_Absyn_Util.compress_exp e)
in _127_183.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _62_458 = (synth_exp g scrutinee)
in (match (_62_458) with
| (e, f_e, t_e) -> begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _62_462 -> (match (_62_462) with
| (pat, when_opt, branch) -> begin
(let _62_465 = (extract_pat g pat)
in (match (_62_465) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _127_185 = (check_exp env w FStar_Extraction_ML_Syntax.E_IMPURE FStar_Extraction_ML_Syntax.ml_bool_ty)
in Some (_127_185))
end)
in (let branch = (check_exp env branch f t)
in (FStar_All.pipe_right p (FStar_List.map (fun _62_473 -> (match (_62_473) with
| (p, wopt) -> begin
(let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, when_clause, branch))
end))))))
end))
end))))
in (match ((FStar_Extraction_ML_Util.eff_leq f_e f)) with
| true -> begin
FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))
end
| false -> begin
(err_unexpected_eff scrutinee f f_e)
end))
end))
end
| _62_477 -> begin
(let _62_481 = (synth_exp g e)
in (match (_62_481) with
| (e0, f0, t0) -> begin
(match ((FStar_Extraction_ML_Util.eff_leq f0 f)) with
| true -> begin
(maybe_coerce g e0 t0 f t)
end
| false -> begin
(err_unexpected_eff e f f0)
end)
end))
end))
and synth_exp = (fun g e -> (let _62_487 = (synth_exp' g e)
in (match (_62_487) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun g e -> (let _62_491 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _127_193 = (let _127_192 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "now synthesizing expression :  %s \n" _127_192))
in (FStar_Util.print_string _127_193))))
in (match ((let _127_194 = (FStar_Absyn_Util.compress_exp e)
in _127_194.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let _127_198 = (let _127_196 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _127_195 -> FStar_Extraction_ML_Syntax.MLE_Const (_127_195)) _127_196))
in (let _127_197 = (translate_typ g t)
in (_127_198, FStar_Extraction_ML_Syntax.E_PURE, _127_197))))
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
(let _62_517 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_62_517) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _127_199 = (maybe_lalloc_eta_data g qual t x)
in (_127_199, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_522 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _62_531 _62_534 restArgs -> (match ((_62_531, _62_534)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _62_538) -> begin
(let _62_549 = (match (((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ()))) with
| true -> begin
(let _127_208 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _127_208))
end
| false -> begin
(FStar_List.fold_left (fun _62_542 _62_545 -> (match ((_62_542, _62_545)) with
| ((lbs, out_args), (arg, f)) -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(lbs, (arg)::out_args)
end
| false -> begin
(let x = (let _127_211 = (FStar_Absyn_Util.gensym ())
in (_127_211, (- (1))))
in (((x, arg))::lbs, (FStar_Extraction_ML_Syntax.MLE_Var (x))::out_args))
end)
end)) ([], []) mlargs_f)
end)
in (match (_62_549) with
| (lbs, mlargs) -> begin
(let app = (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (let l_app = (FStar_List.fold_right (fun _62_553 out -> (match (_62_553) with
| (x, arg) -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_62_558), _62_561)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
(match ((FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
(let _127_215 = (let _127_214 = (FStar_Extraction_ML_Util.join f f')
in (_127_214, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _127_215 rest))
end
| false -> begin
(FStar_All.failwith "Impossible: ill-typed application")
end)
end
| ((FStar_Util.Inr (e0), _62_574)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _62_586 = (synth_exp g e0)
in (match (_62_586) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred f' tExpected)
in (let _127_217 = (let _127_216 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_127_216, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _127_217 rest)))
end))
end
| _62_589 -> begin
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
(let _62_606 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_62_606) with
| ((head, (vars, t)), qual) -> begin
(let n = (FStar_List.length vars)
in (match ((n <= (FStar_List.length args))) with
| true -> begin
(let _62_610 = (FStar_Util.first_N n args)
in (match (_62_610) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (match (rest) with
| [] -> begin
(let _127_218 = (maybe_lalloc_eta_data g qual t head)
in (_127_218, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_616 -> begin
(synth_app qual (head, []) (FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end))))
end))
end
| false -> begin
(err_uninst e)
end))
end))
end
| _62_618 -> begin
(let _62_622 = (synth_exp g head)
in (match (_62_622) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _62_645 = (FStar_List.fold_left (fun _62_629 _62_633 -> (match ((_62_629, _62_633)) with
| ((ml_bs, env), (b, _62_632)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _127_223 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (let _127_222 = (FStar_All.pipe_left (fun _127_221 -> Some (_127_221)) FStar_Extraction_ML_Syntax.ml_unit_ty)
in (_127_223, _127_222)))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), Some (t))
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_62_645) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _62_650 = (synth_exp env body)
in (match (_62_650) with
| (ml_body, f, t) -> begin
(let _62_660 = (FStar_List.fold_right (fun _62_654 _62_657 -> (match ((_62_654, _62_657)) with
| ((_62_652, targ), (f, t)) -> begin
(let _127_228 = (let _127_227 = (let _127_226 = (FStar_Util.must targ)
in (_127_226, f, t))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_127_227))
in (FStar_Extraction_ML_Syntax.E_PURE, _127_228))
end)) ml_bs (f, t))
in (match (_62_660) with
| (f, tfun) -> begin
(FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body)), f, tfun)
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _62_672 -> (match (_62_672) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _62_696 = (match ((FStar_Util.prefix_until (fun _62_4 -> (match (_62_4) with
| (FStar_Util.Inr (_62_681), _62_684) -> begin
true
end
| _62_687 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _127_232 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _127_232))
end)
in (match (_62_696) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(match ((n <= (FStar_List.length bs))) with
| true -> begin
(let _62_705 = (FStar_Util.first_N n bs)
in (match (_62_705) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _62_5 -> (match (_62_5) with
| (FStar_Util.Inl (a), _62_714) -> begin
a
end
| _62_717 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _127_236 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_127_236, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _62_726 -> begin
false
end)
in (let rest_args = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Util.unit_binder)::rest_args
end
| false -> begin
rest_args
end)
in (let body = (match (rest_args) with
| [] -> begin
body
end
| _62_731 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end
| false -> begin
(FStar_All.failwith "Not enough type binders")
end)
end
| _62_734 -> begin
(err_value_restriction e)
end)))
end))
end
| _62_736 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _62_751 -> (match (_62_751) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
in (let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end
| false -> begin
(Prims.snd polytype)
end)
in (let e = (check_exp env e f expected_t)
in (f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e}))))
end))
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (let _62_780 = (FStar_List.fold_right (fun lb _62_761 -> (match (_62_761) with
| (env, lbs) -> begin
(let _62_774 = lb
in (match (_62_774) with
| (lbname, _62_764, (t, (_62_767, polytype)), add_unit, _62_773) -> begin
(let _62_777 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_62_777) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_62_780) with
| (env_body, lbs) -> begin
(let env_def = (match (is_rec) with
| true -> begin
env_body
end
| false -> begin
g
end)
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _62_786 = (synth_exp env_body e')
in (match (_62_786) with
| (e', f', t') -> begin
(let f = (let _127_246 = (let _127_245 = (FStar_List.map Prims.fst lbs)
in (f')::_127_245)
in (FStar_Extraction_ML_Util.join_l _127_246))
in (let _127_250 = (let _127_249 = (let _127_248 = (let _127_247 = (FStar_List.map Prims.snd lbs)
in (is_rec, _127_247))
in (_127_248, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_127_249))
in (_127_250, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(FStar_All.failwith "Matches must be checked; missing a compiler-provided annotation")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _62_794)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(FStar_All.failwith "Unexpected expression")
end)))

let fresh = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _62_806 = (FStar_Util.incr c)
in (let _127_253 = (FStar_ST.read c)
in (x, _127_253)))))

let ind_discriminator_body = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _62_815 = (let _127_260 = (FStar_Absyn_Util.fv constrName)
in (FStar_Extraction_ML_Env.lookup_fv env _127_260))
in (match (_62_815) with
| (_62_813, ts) -> begin
(let arg_pat = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_62_817) -> begin
(FStar_Extraction_ML_Syntax.MLP_Wild)::[]
end
| _62_820 -> begin
[]
end)
in (let rid = constrName
in (let discrBody = (let _127_268 = (let _127_267 = (let _127_266 = (let _127_265 = (let _127_264 = (let _127_263 = (let _127_262 = (let _127_261 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_127_261, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_127_262))
in (_127_263, None, FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_127_264)::((FStar_Extraction_ML_Syntax.MLP_Wild, None, FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))::[])
in (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid))), _127_265))
in FStar_Extraction_ML_Syntax.MLE_Match (_127_266))
in (((mlid, None))::[], _127_267))
in FStar_Extraction_ML_Syntax.MLE_Fun (_127_268))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Absyn_Syntax.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[])))))
end))))
