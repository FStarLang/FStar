
open Prims
let fail = (fun r msg -> (let _80_9 = (let _183_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _183_3))
in (FStar_All.exit 1)))

let err_uninst = (fun e -> (let _183_6 = (let _183_5 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _183_5))
in (fail e.FStar_Absyn_Syntax.pos _183_6)))

let err_ill_typed_application = (fun e args t -> (let _183_12 = (let _183_11 = (FStar_Absyn_Print.exp_to_string e)
in (let _183_10 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _183_11 _183_10)))
in (fail e.FStar_Absyn_Syntax.pos _183_12)))

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun e f0 f1 -> (let _183_18 = (let _183_17 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _183_17 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _183_18)))

let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _183_21 = (FStar_Absyn_Util.compress_exp e)
in _183_21.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _80_35 -> begin
false
end))

let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _183_24 = (FStar_Absyn_Util.compress_exp e)
in _183_24.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _80_56 -> (match (_80_56) with
| (te, _80_55) -> begin
(match (te) with
| FStar_Util.Inl (_80_58) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _183_26 = (FStar_Absyn_Util.compress_exp head)
in _183_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _80_1 -> (match (_80_1) with
| (FStar_Util.Inl (te), _80_72) -> begin
true
end
| _80_75 -> begin
false
end))))
end
| _80_77 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _80_91 -> begin
false
end))

let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_80_112, fields) -> begin
(FStar_Util.for_all (fun _80_119 -> (match (_80_119) with
| (_80_117, e) -> begin
(is_ml_value e)
end)) fields)
end
| _80_121 -> begin
false
end))

let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _183_35 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _183_35)))

let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _183_40 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _183_40)))

let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(let _80_136 = (FStar_Extraction_ML_Env.debug g (fun _80_135 -> (match (()) with
| () -> begin
(let _183_61 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _183_60 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _183_61 _183_60)))
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
| _80_148 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_80_157) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _183_82 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _183_82))
in (let when_clause = (let _183_91 = (let _183_90 = (let _183_89 = (let _183_88 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _183_87 = (let _183_86 = (let _183_85 = (let _183_84 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _183_83 -> FStar_Extraction_ML_Syntax.MLE_Const (_183_83)) _183_84))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _183_85))
in (_183_86)::[])
in (_183_88)::_183_87))
in (FStar_Extraction_ML_Util.prims_op_equality, _183_89))
in FStar_Extraction_ML_Syntax.MLE_App (_183_90))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _183_91))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _183_95 = (let _183_94 = (let _183_93 = (let _183_92 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_183_92))
in (_183_93, []))
in Some (_183_94))
in (g, _183_95))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _80_184 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _80_172}, ttys, _80_178) -> begin
(n, ttys)
end
| _80_181 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_80_184) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _80_188 = (FStar_Util.first_N nTyVars pats)
in (match (_80_188) with
| (tysVarPats, restPats) -> begin
(let _80_195 = (FStar_Util.fold_map (fun g _80_192 -> (match (_80_192) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_80_195) with
| (g, tyMLPats) -> begin
(let _80_202 = (FStar_Util.fold_map (fun g _80_199 -> (match (_80_199) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_80_202) with
| (g, restMLPats) -> begin
(let _80_210 = (let _183_101 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _80_2 -> (match (_80_2) with
| Some (x) -> begin
(x)::[]
end
| _80_207 -> begin
[]
end))))
in (FStar_All.pipe_right _183_101 FStar_List.split))
in (match (_80_210) with
| (mlPats, when_clauses) -> begin
(let _183_105 = (let _183_104 = (let _183_103 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _183_102 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_183_103, _183_102)))
in Some (_183_104))
in (g, _183_105))
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
| FStar_Absyn_Syntax.Pat_dot_term (_80_222) -> begin
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
| _80_245 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _183_114 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_183_114))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _80_260 = (extract_one_pat true g p)
in (match (_80_260) with
| (g, p) -> begin
(let ps = (let _183_117 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _183_116 = (extract_one_pat true g x)
in (Prims.snd _183_116)))))
in (p)::_183_117)
in (let _80_276 = (FStar_All.pipe_right ps (FStar_List.partition (fun _80_3 -> (match (_80_3) with
| (_80_265, _80_269::_80_267) -> begin
true
end
| _80_273 -> begin
false
end))))
in (match (_80_276) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _80_279 -> (match (_80_279) with
| (x, whens) -> begin
(let _183_120 = (mk_when_clause whens)
in (x, _183_120))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _183_124 = (let _183_123 = (let _183_122 = (let _183_121 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_183_121))
in (_183_122, None))
in (_183_123)::ps)
in (g, _183_124))
end)
in res))
end)))
end))
end
| _80_285 -> begin
(let _80_290 = (extract_one_pat false g p)
in (match (_80_290) with
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
| _80_302 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (let name = if ((2 < n) && (n < 6)) then begin
(let _183_133 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _183_133))
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
in (let tup = (let _183_140 = (let _183_139 = (let _183_138 = (let _183_137 = (let _183_136 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_183_136))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _183_137))
in (_183_138, args))
in FStar_Extraction_ML_Syntax.MLE_App (_183_139))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _183_140))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _80_321 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _80_331, t1) -> begin
(let x = (let _183_153 = (FStar_Absyn_Util.gensym ())
in (_183_153, (- (1))))
in (let _183_156 = (let _183_155 = (let _183_154 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _183_154))
in (_183_155)::more_args)
in (eta_args _183_156 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_337, _80_339) -> begin
((FStar_List.rev more_args), t)
end
| _80_343 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_80_348, args), Some (FStar_Absyn_Syntax.Record_ctor (_80_353, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _80_362 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let _80_368 = (eta_args [] residualType)
in (match (_80_368) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _183_165 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _183_165))
end
| _80_371 -> begin
(let _80_374 = (FStar_List.unzip eargs)
in (match (_80_374) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _183_167 = (let _183_166 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _183_166))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _183_167))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _80_381 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _80_383}, mlarg::[]), _80_392) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _80_395 = (FStar_Extraction_ML_Env.debug g (fun _80_394 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_80_398, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _80_402}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (let e = (match (args) with
| [] -> begin
proj
end
| _80_419 -> begin
(let _183_170 = (let _183_169 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_183_169, args))
in FStar_Extraction_ML_Syntax.MLE_App (_183_170))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _183_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _183_171))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _183_172 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _183_172))
end
| _80_455 -> begin
mlAppExpr
end)))))

let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _80_461 = (FStar_List.hd l)
in (match (_80_461) with
| (p1, w1, e1) -> begin
(let _80_465 = (let _183_175 = (FStar_List.tl l)
in (FStar_List.hd _183_175))
in (match (_80_465) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _80_485 -> begin
def
end)
end))
end))
end))

let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (let _80_495 = (let _183_192 = (check_exp' g e f t)
in (erase g _183_192 f t))
in (match (_80_495) with
| (e, _80_492, _80_494) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (let _80_503 = (synth_exp g e)
in (match (_80_503) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (let _80_509 = (synth_exp' g e)
in (match (_80_509) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (let _80_513 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _183_204 = (let _183_203 = (FStar_Absyn_Print.tag_of_exp e)
in (let _183_202 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _183_203 _183_202)))
in (FStar_Util.print_string _183_204))))
in (match ((let _183_205 = (FStar_Absyn_Util.compress_exp e)
in _183_205.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let ml_ty = (translate_typ g t)
in (let _183_209 = (let _183_208 = (let _183_207 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _183_206 -> FStar_Extraction_ML_Syntax.MLE_Const (_183_206)) _183_207))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _183_208))
in (_183_209, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
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
(let _80_542 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_80_542) with
| ((x, mltys, _80_539), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _183_210 = (maybe_lalloc_eta_data g qual t x)
in (_183_210, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _80_547 -> begin
(err_uninst e)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _80_556 _80_559 restArgs -> (match ((_80_556, _80_559)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _80_563) -> begin
(let _80_574 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _183_219 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _183_219))
end else begin
(FStar_List.fold_left (fun _80_567 _80_570 -> (match ((_80_567, _80_570)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(let x = (let _183_222 = (FStar_Absyn_Util.gensym ())
in (_183_222, (- (1))))
in (let _183_224 = (let _183_223 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_183_223)::out_args)
in (((x, arg))::lbs, _183_224)))
end
end)) ([], []) mlargs_f)
end
in (match (_80_574) with
| (lbs, mlargs) -> begin
(let app = (let _183_225 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _183_225))
in (let l_app = (FStar_List.fold_right (fun _80_578 out -> (match (_80_578) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = ([], arg.FStar_Extraction_ML_Syntax.ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_80_583), _80_586)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _183_229 = (let _183_228 = (FStar_Extraction_ML_Util.join f f')
in (_183_228, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _183_229 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _80_599)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _80_611 = (synth_exp g e0)
in (match (_80_611) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _183_231 = (let _183_230 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_183_230, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _183_231 rest)))
end))
end
| _80_614 -> begin
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
(let _80_632 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_80_632) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(let has_typ_apps = (match (args) with
| (FStar_Util.Inl (_80_636), _80_639)::_80_634 -> begin
true
end
| _80_643 -> begin
false
end)
in (let _80_694 = (match (vars) with
| _80_648::_80_646 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _80_651 -> begin
(let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(let _80_655 = (FStar_Util.first_N n args)
in (match (_80_655) with
| (prefix, rest) -> begin
(let _80_665 = if (FStar_All.pipe_right prefix (FStar_Util.for_some (fun _80_4 -> (match (_80_4) with
| (FStar_Util.Inr (_80_658), _80_661) -> begin
true
end
| _80_664 -> begin
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
(let _80_675 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _80_675.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _80_679}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((let _80_686 = head
in {FStar_Extraction_ML_Syntax.expr = _80_686.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t))}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _80_689 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest)))))
end))
end else begin
(err_uninst head)
end)
end)
in (match (_80_694) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _183_233 = (maybe_lalloc_eta_data g qual head_t head_ml)
in (_183_233, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _80_697 -> begin
(synth_app qual (head_ml, []) (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _80_699 -> begin
(let _80_703 = (synth_exp g head)
in (match (_80_703) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _80_726 = (FStar_List.fold_left (fun _80_710 _80_714 -> (match ((_80_710, _80_714)) with
| ((ml_bs, env), (b, _80_713)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _183_236 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_183_236, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_80_726) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _80_731 = (synth_exp env body)
in (match (_80_731) with
| (ml_body, f, t) -> begin
(let _80_741 = (FStar_List.fold_right (fun _80_735 _80_738 -> (match ((_80_735, _80_738)) with
| ((_80_733, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_80_741) with
| (f, tfun) -> begin
(let _183_239 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_183_239, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _80_753 -> (match (_80_753) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _80_777 = (match ((FStar_Util.prefix_until (fun _80_5 -> (match (_80_5) with
| (FStar_Util.Inr (_80_762), _80_765) -> begin
true
end
| _80_768 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _183_243 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _183_243))
end)
in (match (_80_777) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(let _80_786 = (FStar_Util.first_N n bs)
in (match (_80_786) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _80_6 -> (match (_80_6) with
| (FStar_Util.Inl (a), _80_795) -> begin
a
end
| _80_798 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _183_247 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_183_247, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _80_807 -> begin
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
| _80_812 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _80_815 -> begin
(err_value_restriction e)
end)))
end))
end
| _80_817 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _80_832 -> (match (_80_832) with
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
in (let _80_861 = (FStar_List.fold_right (fun lb _80_842 -> (match (_80_842) with
| (env, lbs) -> begin
(let _80_855 = lb
in (match (_80_855) with
| (lbname, _80_845, (t, (_80_848, polytype)), add_unit, _80_854) -> begin
(let _80_858 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_80_858) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_80_861) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _80_867 = (synth_exp env_body e')
in (match (_80_867) with
| (e', f', t') -> begin
(let f = (let _183_257 = (let _183_256 = (FStar_List.map Prims.fst lbs)
in (f')::_183_256)
in (FStar_Extraction_ML_Util.join_l _183_257))
in (let _183_262 = (let _183_261 = (let _183_260 = (let _183_259 = (let _183_258 = (FStar_List.map Prims.snd lbs)
in (is_rec, _183_258))
in (_183_259, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_183_260))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t') _183_261))
in (_183_262, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _80_876 = (synth_exp g scrutinee)
in (match (_80_876) with
| (e, f_e, t_e) -> begin
(let _80_880 = (check_pats_for_ite pats)
in (match (_80_880) with
| (b, then_e, else_e) -> begin
(let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(let _80_892 = (synth_exp g then_e)
in (match (_80_892) with
| (then_mle, f_then, t_then) -> begin
(let _80_896 = (synth_exp g else_e)
in (match (_80_896) with
| (else_mle, f_else, t_else) -> begin
(let _80_899 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_80_899) with
| (t_branch, maybe_lift) -> begin
(let _183_293 = (let _183_291 = (let _183_290 = (let _183_289 = (maybe_lift then_mle t_then)
in (let _183_288 = (let _183_287 = (maybe_lift else_mle t_else)
in Some (_183_287))
in (e, _183_289, _183_288)))
in FStar_Extraction_ML_Syntax.MLE_If (_183_290))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _183_291))
in (let _183_292 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_183_293, _183_292, t_branch)))
end))
end))
end))
end
| _80_901 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _80_905 -> (match (_80_905) with
| (pat, when_opt, branch) -> begin
(let _80_908 = (extract_pat g pat)
in (match (_80_908) with
| (env, p) -> begin
(let _80_919 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(let _80_915 = (synth_exp env w)
in (match (_80_915) with
| (w, f_w, t_w) -> begin
(let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_80_919) with
| (when_opt, f_when) -> begin
(let _80_923 = (synth_exp env branch)
in (match (_80_923) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _80_926 -> (match (_80_926) with
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
(let _80_935 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_80_935) with
| (fw, _80_932, _80_934) -> begin
(let _183_300 = (let _183_299 = (let _183_298 = (let _183_297 = (let _183_296 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_183_296)::[])
in (fw, _183_297))
in FStar_Extraction_ML_Syntax.MLE_App (_183_298))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _183_299))
in (_183_300, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_80_938, _80_940, (_80_942, f_first, t_first))::rest -> begin
(let _80_968 = (FStar_List.fold_left (fun _80_950 _80_960 -> (match ((_80_950, _80_960)) with
| ((topt, f), (_80_952, _80_954, (_80_956, f_branch, t_branch))) -> begin
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
in (match (_80_968) with
| (topt, f_match) -> begin
(let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _80_979 -> (match (_80_979) with
| (p, (wopt, _80_972), (b, _80_976, t)) -> begin
(let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_80_982) -> begin
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
in (let _183_304 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_183_304, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _80_992)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(FStar_All.failwith "Unexpected expression")
end)))

let fresh : Prims.string  ->  (Prims.string * Prims.int) = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _80_1004 = (FStar_Util.incr c)
in (let _183_307 = (FStar_ST.read c)
in (x, _183_307)))))

let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (let mlid = (fresh "_discr_")
in (let _80_1015 = (FStar_Extraction_ML_Env.lookup_fv env (FStar_Absyn_Util.fv constrName))
in (match (_80_1015) with
| (_80_1011, ts, _80_1014) -> begin
(let _80_1027 = (match ((Prims.snd ts)) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_80_1017, _80_1019, t) -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild)::[], ((Prims.fst ts), t))
end
| _80_1024 -> begin
([], ts)
end)
in (match (_80_1027) with
| (arg_pat, ts) -> begin
(let rid = constrName
in (let targ = (Prims.snd ts)
in (let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_bool_ty))
in (let discrBody = (let _183_328 = (let _183_327 = (let _183_326 = (let _183_325 = (let _183_324 = (let _183_323 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _183_322 = (let _183_321 = (let _183_317 = (let _183_315 = (let _183_314 = (FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_183_314, arg_pat))
in FStar_Extraction_ML_Syntax.MLP_CTor (_183_315))
in (let _183_316 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_183_317, None, _183_316)))
in (let _183_320 = (let _183_319 = (let _183_318 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _183_318))
in (_183_319)::[])
in (_183_321)::_183_320))
in (_183_323, _183_322)))
in FStar_Extraction_ML_Syntax.MLE_Match (_183_324))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _183_325))
in (((mlid, targ))::[], _183_326))
in FStar_Extraction_ML_Syntax.MLE_Fun (_183_327))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _183_328))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = ((Prims.fst ts), disc_ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[]))))))
end))
end))))




