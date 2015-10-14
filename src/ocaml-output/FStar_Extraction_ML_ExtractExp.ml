
open Prims
let eff_to_string = (fun _62_1 -> (match (_62_1) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

let fail = (fun r msg -> (let _62_13 = (let _127_5 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _127_5))
in (FStar_All.exit 1)))

let err_uninst = (fun e -> (let _127_8 = (let _127_7 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _127_7))
in (fail e.FStar_Absyn_Syntax.pos _127_8)))

let err_ill_typed_application = (fun e args t -> (let _127_14 = (let _127_13 = (FStar_Absyn_Print.exp_to_string e)
in (let _127_12 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _127_13 _127_12)))
in (fail e.FStar_Absyn_Syntax.pos _127_14)))

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun e f0 f1 -> (let _127_20 = (let _127_19 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _127_19 (eff_to_string f0) (eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _127_20)))

let is_constructor = (fun e -> (match ((let _127_23 = (FStar_Absyn_Util.compress_exp e)
in _127_23.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _62_39 -> begin
false
end))

let rec is_value_or_type_app = (fun e -> (match ((let _127_26 = (FStar_Absyn_Util.compress_exp e)
in _127_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(match ((is_constructor head)) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _62_60 -> (match (_62_60) with
| (te, _62_59) -> begin
(match (te) with
| FStar_Util.Inl (_62_62) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end
| false -> begin
(match ((let _127_28 = (FStar_Absyn_Util.compress_exp head)
in _127_28.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _62_2 -> (match (_62_2) with
| (FStar_Util.Inl (te), _62_76) -> begin
true
end
| _62_79 -> begin
false
end))))
end
| _62_81 -> begin
false
end)
end)
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _62_95 -> begin
false
end))

let rec is_ml_value = (fun e -> (match (e) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_62_116, fields) -> begin
(FStar_Util.for_all (fun _62_123 -> (match (_62_123) with
| (_62_121, e) -> begin
(is_ml_value e)
end)) fields)
end
| _62_125 -> begin
false
end))

let translate_typ = (fun g t -> (let _127_37 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _127_37)))

let translate_typ_of_arg = (fun g a -> (let _127_42 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _127_42)))

let instantiate = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

let erasable = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

let erase = (fun g e f t -> (match ((erasable g f t)) with
| true -> begin
(let _62_140 = (FStar_Extraction_ML_Env.debug g (fun _62_139 -> (match (()) with
| () -> begin
(let _127_63 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _127_62 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.fprint2 "Erasing %s at type %s\n" _127_63 _127_62)))
end)))
in (FStar_Extraction_ML_Syntax.ml_unit, f, FStar_Extraction_ML_Env.erasedContent))
end
| false -> begin
(e, f, t)
end))

let maybe_coerce = (fun g e tInferred etag tExpected -> (match ((FStar_Extraction_ML_Util.equiv g tInferred tExpected)) with
| true -> begin
e
end
| false -> begin
FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))
end))

let eff_leq = (fun f f' -> (match ((f, f')) with
| (FStar_Extraction_ML_Syntax.E_PURE, _62_151) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| _62_160 -> begin
false
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
| _62_185 -> begin
(let _127_82 = (FStar_Util.format2 "Impossible: Inconsistent effects %s and %s" (eff_to_string f) (eff_to_string f'))
in (FStar_All.failwith _127_82))
end))

let join_l = (fun fs -> (FStar_List.fold_left join FStar_Extraction_ML_Syntax.E_PURE fs))

let extract_pat = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_62_195) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Absyn_Syntax.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _127_97 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _127_97))
in (let eq = (("Prims")::[], "op_Equality")
in (let when_clause = (let _127_103 = (let _127_102 = (let _127_101 = (let _127_100 = (let _127_99 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Absyn_Syntax.Const_int (c)))
in (FStar_All.pipe_left (fun _127_98 -> FStar_Extraction_ML_Syntax.MLE_Const (_127_98)) _127_99))
in (_127_100)::[])
in (FStar_Extraction_ML_Syntax.MLE_Var (x))::_127_101)
in (FStar_Extraction_ML_Syntax.MLE_Name (eq), _127_102))
in FStar_Extraction_ML_Syntax.MLE_App (_127_103))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[]))))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _127_107 = (let _127_106 = (let _127_105 = (let _127_104 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_127_104))
in (_127_105, []))
in Some (_127_106))
in (g, _127_107))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _62_218 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (n), ttys) -> begin
(n, ttys)
end
| _62_215 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_62_218) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _62_222 = (FStar_Util.first_N nTyVars pats)
in (match (_62_222) with
| (tysVarPats, restPats) -> begin
(let _62_229 = (FStar_Util.fold_map (fun g _62_226 -> (match (_62_226) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_62_229) with
| (g, tyMLPats) -> begin
(let _62_236 = (FStar_Util.fold_map (fun g _62_233 -> (match (_62_233) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_62_236) with
| (g, restMLPats) -> begin
(let _62_244 = (let _127_113 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _62_3 -> (match (_62_3) with
| Some (x) -> begin
(x)::[]
end
| _62_241 -> begin
[]
end))))
in (FStar_All.pipe_right _127_113 FStar_List.split))
in (match (_62_244) with
| (mlPats, when_clauses) -> begin
(let _127_117 = (let _127_116 = (let _127_115 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _127_114 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_127_115, _127_114)))
in Some (_127_116))
in (g, _127_117))
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
| FStar_Absyn_Syntax.Pat_dot_term (_62_256) -> begin
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
| _62_279 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _127_126 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_127_126))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _62_294 = (extract_one_pat true g p)
in (match (_62_294) with
| (g, p) -> begin
(let ps = (let _127_129 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _127_128 = (extract_one_pat true g x)
in (Prims.snd _127_128)))))
in (p)::_127_129)
in (let _62_310 = (FStar_All.pipe_right ps (FStar_List.partition (fun _62_4 -> (match (_62_4) with
| (_62_299, _62_303::_62_301) -> begin
true
end
| _62_307 -> begin
false
end))))
in (match (_62_310) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _62_313 -> (match (_62_313) with
| (x, whens) -> begin
(let _127_132 = (mk_when_clause whens)
in (x, _127_132))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _127_136 = (let _127_135 = (let _127_134 = (let _127_133 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_127_133))
in (_127_134, None))
in (_127_135)::ps)
in (g, _127_136))
end)
in res))
end)))
end))
end
| _62_319 -> begin
(let _62_324 = (extract_one_pat false g p)
in (match (_62_324) with
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
| _62_336 -> begin
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
(let _127_145 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _127_145))
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
in (let tup = (let _127_150 = (let _127_149 = (let _127_148 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_127_148))
in (_127_149, args))
in FStar_Extraction_ML_Syntax.MLE_App (_127_150))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _62_355 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _62_365, t1) -> begin
(let x = (let _127_163 = (FStar_Absyn_Util.gensym ())
in (_127_163, (- (1))))
in (eta_args ((((x, Some (t0)), FStar_Extraction_ML_Syntax.MLE_Var (x)))::more_args) t1))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_62_371, _62_373) -> begin
(FStar_List.rev more_args)
end
| _62_377 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_62_382, args), Some (FStar_Absyn_Syntax.Record_ctor (_62_387, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))
end
| _62_396 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let eargs = (eta_args [] residualType)
in (match (eargs) with
| [] -> begin
(let _127_172 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _127_172))
end
| _62_403 -> begin
(let _62_406 = (FStar_List.unzip eargs)
in (match (_62_406) with
| (binders, eargs) -> begin
(match (e) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _127_173 = (FStar_All.pipe_left (as_record qual) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _127_173))
in FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))
end
| _62_413 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)))
in (match ((mlAppExpr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlarg::[]), _62_421) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _62_424 = (FStar_Extraction_ML_Env.debug g (fun _62_423 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_62_427, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (match (args) with
| [] -> begin
proj
end
| _62_445 -> begin
FStar_Extraction_ML_Syntax.MLE_App ((proj, args))
end)))
end
| ((FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(FStar_All.pipe_left (resugar_and_maybe_eta qual) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(FStar_All.pipe_left (resugar_and_maybe_eta qual) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
end
| _62_474 -> begin
mlAppExpr
end)))))

let rec check_exp = (fun g e f t -> (let _62_484 = (let _127_191 = (check_exp' g e f t)
in (erase g _127_191 f t))
in (match (_62_484) with
| (e, _62_481, _62_483) -> begin
e
end)))
and check_exp' = (fun g e f t -> (match ((let _127_196 = (FStar_Absyn_Util.compress_exp e)
in _127_196.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _62_496 = (synth_exp g scrutinee)
in (match (_62_496) with
| (e, f_e, t_e) -> begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _62_500 -> (match (_62_500) with
| (pat, when_opt, branch) -> begin
(let _62_503 = (extract_pat g pat)
in (match (_62_503) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _127_198 = (check_exp env w FStar_Extraction_ML_Syntax.E_IMPURE FStar_Extraction_ML_Syntax.ml_bool_ty)
in Some (_127_198))
end)
in (let branch = (check_exp env branch f t)
in (FStar_All.pipe_right p (FStar_List.map (fun _62_511 -> (match (_62_511) with
| (p, wopt) -> begin
(let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, when_clause, branch))
end))))))
end))
end))))
in (match ((eff_leq f_e f)) with
| true -> begin
FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))
end
| false -> begin
(err_unexpected_eff scrutinee f f_e)
end))
end))
end
| _62_515 -> begin
(let _62_519 = (synth_exp g e)
in (match (_62_519) with
| (e0, f0, t0) -> begin
(match ((eff_leq f0 f)) with
| true -> begin
(maybe_coerce g e0 t0 f t)
end
| false -> begin
(err_unexpected_eff e f f0)
end)
end))
end))
and synth_exp = (fun g e -> (let _62_525 = (synth_exp' g e)
in (match (_62_525) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun g e -> (let _62_529 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _127_206 = (let _127_205 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "now synthesizing expression :  %s \n" _127_205))
in (FStar_Util.print_string _127_206))))
in (match ((let _127_207 = (FStar_Absyn_Util.compress_exp e)
in _127_207.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let _127_211 = (let _127_209 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _127_208 -> FStar_Extraction_ML_Syntax.MLE_Const (_127_208)) _127_209))
in (let _127_210 = (translate_typ g t)
in (_127_211, FStar_Extraction_ML_Syntax.E_PURE, _127_210))))
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
(let _62_555 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_62_555) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _127_212 = (maybe_lalloc_eta_data g qual t x)
in (_127_212, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_560 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _62_569 _62_572 restArgs -> (match ((_62_569, _62_572)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _62_576) -> begin
(let _62_587 = (match (((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ()))) with
| true -> begin
(let _127_221 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _127_221))
end
| false -> begin
(FStar_List.fold_left (fun _62_580 _62_583 -> (match ((_62_580, _62_583)) with
| ((lbs, out_args), (arg, f)) -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(lbs, (arg)::out_args)
end
| false -> begin
(let x = (let _127_224 = (FStar_Absyn_Util.gensym ())
in (_127_224, (- (1))))
in (((x, arg))::lbs, (FStar_Extraction_ML_Syntax.MLE_Var (x))::out_args))
end)
end)) ([], []) mlargs_f)
end)
in (match (_62_587) with
| (lbs, mlargs) -> begin
(let app = (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (let l_app = (FStar_List.fold_right (fun _62_591 out -> (match (_62_591) with
| (x, arg) -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_62_596), _62_599)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
(match ((FStar_Extraction_ML_Util.equiv g tunit FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
(let _127_228 = (let _127_227 = (join f f')
in (_127_227, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _127_228 rest))
end
| false -> begin
(FStar_All.failwith "Impossible: ill-typed application")
end)
end
| ((FStar_Util.Inr (e0), _62_612)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _62_624 = (synth_exp g e0)
in (match (_62_624) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred f' tExpected)
in (let _127_230 = (let _127_229 = (join_l ((f)::(f')::(f0)::[]))
in (_127_229, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _127_230 rest)))
end))
end
| _62_627 -> begin
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
(let _62_644 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_62_644) with
| ((head, (vars, t)), qual) -> begin
(let n = (FStar_List.length vars)
in (match ((n <= (FStar_List.length args))) with
| true -> begin
(let _62_648 = (FStar_Util.first_N n args)
in (match (_62_648) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (match (rest) with
| [] -> begin
(let _127_231 = (maybe_lalloc_eta_data g qual t head)
in (_127_231, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_654 -> begin
(synth_app qual (head, []) (FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end))))
end))
end
| false -> begin
(err_uninst e)
end))
end))
end
| _62_656 -> begin
(let _62_660 = (synth_exp g head)
in (match (_62_660) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _62_683 = (FStar_List.fold_left (fun _62_667 _62_671 -> (match ((_62_667, _62_671)) with
| ((ml_bs, env), (b, _62_670)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _127_236 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (let _127_235 = (FStar_All.pipe_left (fun _127_234 -> Some (_127_234)) FStar_Extraction_ML_Syntax.ml_unit_ty)
in (_127_236, _127_235)))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), Some (t))
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_62_683) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _62_688 = (synth_exp env body)
in (match (_62_688) with
| (ml_body, f, t) -> begin
(let _62_698 = (FStar_List.fold_right (fun _62_692 _62_695 -> (match ((_62_692, _62_695)) with
| ((_62_690, targ), (f, t)) -> begin
(let _127_241 = (let _127_240 = (let _127_239 = (FStar_Util.must targ)
in (_127_239, f, t))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_127_240))
in (FStar_Extraction_ML_Syntax.E_PURE, _127_241))
end)) ml_bs (f, t))
in (match (_62_698) with
| (f, tfun) -> begin
(FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body)), f, tfun)
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _62_710 -> (match (_62_710) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _62_734 = (match ((FStar_Util.prefix_until (fun _62_5 -> (match (_62_5) with
| (FStar_Util.Inr (_62_719), _62_722) -> begin
true
end
| _62_725 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _127_245 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _127_245))
end)
in (match (_62_734) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(match ((n <= (FStar_List.length bs))) with
| true -> begin
(let _62_743 = (FStar_Util.first_N n bs)
in (match (_62_743) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _62_6 -> (match (_62_6) with
| (FStar_Util.Inl (a), _62_752) -> begin
a
end
| _62_755 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _127_249 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_127_249, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _62_764 -> begin
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
| _62_769 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end
| false -> begin
(FStar_All.failwith "Not enough type binders")
end)
end
| _62_772 -> begin
(err_value_restriction e)
end)))
end))
end
| _62_774 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _62_789 -> (match (_62_789) with
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
in (let _62_818 = (FStar_List.fold_right (fun lb _62_799 -> (match (_62_799) with
| (env, lbs) -> begin
(let _62_812 = lb
in (match (_62_812) with
| (lbname, _62_802, (t, (_62_805, polytype)), add_unit, _62_811) -> begin
(let _62_815 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_62_815) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_62_818) with
| (env_body, lbs) -> begin
(let env_def = (match (is_rec) with
| true -> begin
env_body
end
| false -> begin
g
end)
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _62_824 = (synth_exp env_body e')
in (match (_62_824) with
| (e', f', t') -> begin
(let f = (let _127_259 = (let _127_258 = (FStar_List.map Prims.fst lbs)
in (f')::_127_258)
in (join_l _127_259))
in (let _127_263 = (let _127_262 = (let _127_261 = (let _127_260 = (FStar_List.map Prims.snd lbs)
in (is_rec, _127_260))
in (_127_261, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_127_262))
in (_127_263, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(FStar_All.failwith "Matches must be checked; missing a compiler-provided annotation")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _62_832)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(FStar_All.failwith "Unexpected expression")
end)))

let fresh = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _62_844 = (FStar_Util.incr c)
in (let _127_266 = (FStar_ST.read c)
in (x, _127_266)))))

let ind_discriminator_body = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _62_853 = (let _127_273 = (FStar_Absyn_Util.fv constrName)
in (FStar_Extraction_ML_Env.lookup_fv env _127_273))
in (match (_62_853) with
| (_62_851, ts) -> begin
(let arg_pat = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_62_855) -> begin
(FStar_Extraction_ML_Syntax.MLP_Wild)::[]
end
| _62_858 -> begin
[]
end)
in (let rid = constrName
in (let discrBody = (let _127_281 = (let _127_280 = (let _127_279 = (let _127_278 = (let _127_277 = (let _127_276 = (let _127_275 = (let _127_274 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_127_274, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_127_275))
in (_127_276, None, FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_127_277)::((FStar_Extraction_ML_Syntax.MLP_Wild, None, FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))::[])
in (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid))), _127_278))
in FStar_Extraction_ML_Syntax.MLE_Match (_127_279))
in (((mlid, None))::[], _127_280))
in FStar_Extraction_ML_Syntax.MLE_Fun (_127_281))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Absyn_Syntax.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[])))))
end))))




