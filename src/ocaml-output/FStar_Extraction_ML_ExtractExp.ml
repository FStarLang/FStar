
open Prims
# 29 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let fail = (fun r msg -> (let _79_9 = (let _181_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _181_3))
in (FStar_All.failwith msg)))

# 33 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let err_uninst = (fun env e _79_15 -> (match (_79_15) with
| (vars, t) -> begin
(let _181_11 = (let _181_10 = (FStar_Absyn_Print.exp_to_string e)
in (let _181_9 = (let _181_7 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _181_7 (FStar_String.concat ", ")))
in (let _181_8 = (FStar_Extraction_ML_Code.string_of_mlty env t)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _181_10 _181_9 _181_8))))
in (fail e.FStar_Absyn_Syntax.pos _181_11))
end))

# 39 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let err_ill_typed_application = (fun e args t -> (let _181_17 = (let _181_16 = (FStar_Absyn_Print.exp_to_string e)
in (let _181_15 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _181_16 _181_15)))
in (fail e.FStar_Absyn_Syntax.pos _181_17)))

# 46 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

# 49 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let err_unexpected_eff = (fun e f0 f1 -> (let _181_23 = (let _181_22 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _181_22 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _181_23)))

# 52 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _181_26 = (FStar_Absyn_Util.compress_exp e)
in _181_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _79_39 -> begin
false
end))

# 58 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _181_29 = (FStar_Absyn_Util.compress_exp e)
in _181_29.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_60 -> (match (_79_60) with
| (te, _79_59) -> begin
(match (te) with
| FStar_Util.Inl (_79_62) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _181_31 = (FStar_Absyn_Util.compress_exp head)
in _181_31.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_1 -> (match (_79_1) with
| (FStar_Util.Inl (te), _79_76) -> begin
true
end
| _79_79 -> begin
false
end))))
end
| _79_81 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _79_95 -> begin
false
end))

# 77 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_116, fields) -> begin
(FStar_Util.for_all (fun _79_123 -> (match (_79_123) with
| (_79_121, e) -> begin
(is_ml_value e)
end)) fields)
end
| _79_125 -> begin
false
end))

# 89 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _181_40 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _181_40)))

# 90 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _181_45 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _181_45)))

# 94 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 96 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

# 100 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(let _79_140 = (FStar_Extraction_ML_Env.debug g (fun _79_139 -> (match (()) with
| () -> begin
(let _181_66 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _181_65 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _181_66 _181_65)))
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

# 107 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let maybe_coerce : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e tInferred tExpected -> (match ((FStar_Extraction_ML_Util.type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _79_152 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

# 116 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_79_161) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(let x = (let _181_87 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _181_87))
in (let when_clause = (let _181_96 = (let _181_95 = (let _181_94 = (let _181_93 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _181_92 = (let _181_91 = (let _181_90 = (let _181_89 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _181_88 -> FStar_Extraction_ML_Syntax.MLE_Const (_181_88)) _181_89))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _181_90))
in (_181_91)::[])
in (_181_93)::_181_92))
in (FStar_Extraction_ML_Util.prims_op_equality, _181_94))
in FStar_Extraction_ML_Syntax.MLE_App (_181_95))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _181_96))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _181_100 = (let _181_99 = (let _181_98 = (let _181_97 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_181_97))
in (_181_98, []))
in Some (_181_99))
in (g, _181_100))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(let _79_188 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _79_176}, ttys, _79_182) -> begin
(n, ttys)
end
| _79_185 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_79_188) with
| (d, tys) -> begin
(let nTyVars = (FStar_List.length (Prims.fst tys))
in (let _79_192 = (FStar_Util.first_N nTyVars pats)
in (match (_79_192) with
| (tysVarPats, restPats) -> begin
(let _79_199 = (FStar_Util.fold_map (fun g _79_196 -> (match (_79_196) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_79_199) with
| (g, tyMLPats) -> begin
(let _79_206 = (FStar_Util.fold_map (fun g _79_203 -> (match (_79_203) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_79_206) with
| (g, restMLPats) -> begin
(let _79_214 = (let _181_106 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| Some (x) -> begin
(x)::[]
end
| _79_211 -> begin
[]
end))))
in (FStar_All.pipe_right _181_106 FStar_List.split))
in (match (_79_214) with
| (mlPats, when_clauses) -> begin
(let _181_110 = (let _181_109 = (let _181_108 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _181_107 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_181_108, _181_107)))
in Some (_181_109))
in (g, _181_110))
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
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (let g = (FStar_Extraction_ML_Env.extend_ty g a (Some (mlty)))
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Wild, []))
end)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) -> begin
(g, None)
end))
in (let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _79_249 -> begin
(FStar_All.failwith "Impossible")
end))
in (let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _181_119 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_181_119))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _79_264 = (extract_one_pat true g p)
in (match (_79_264) with
| (g, p) -> begin
(let ps = (let _181_122 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _181_121 = (extract_one_pat true g x)
in (Prims.snd _181_121)))))
in (p)::_181_122)
in (let _79_280 = (FStar_All.pipe_right ps (FStar_List.partition (fun _79_3 -> (match (_79_3) with
| (_79_269, _79_273::_79_271) -> begin
true
end
| _79_277 -> begin
false
end))))
in (match (_79_280) with
| (ps_when, rest) -> begin
(let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _79_283 -> (match (_79_283) with
| (x, whens) -> begin
(let _181_125 = (mk_when_clause whens)
in (x, _181_125))
end))))
in (let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _181_129 = (let _181_128 = (let _181_127 = (let _181_126 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_181_126))
in (_181_127, None))
in (_181_128)::ps)
in (g, _181_129))
end)
in res))
end)))
end))
end
| _79_289 -> begin
(let _79_294 = (extract_one_pat false g p)
in (match (_79_294) with
| (g, (p, whens)) -> begin
(let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 195 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let normalize_abs : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun e0 -> (let rec aux = (fun bs e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _79_306 -> begin
(let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

# 207 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (let name = if ((2 < n) && (n < 6)) then begin
(let _181_138 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _181_138))
end else begin
if (n = 2) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in (("Camlstack")::[], name)))

# 212 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(let args = (FStar_List.map Prims.snd fields)
in (let tup = (let _181_145 = (let _181_144 = (let _181_143 = (let _181_142 = (let _181_141 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_181_141))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _181_142))
in (_181_143, args))
in FStar_Extraction_ML_Syntax.MLE_App (_181_144))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _181_145))
in (let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _79_325 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

# 232 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _79_335, t1) -> begin
(let x = (let _181_158 = (FStar_Absyn_Util.gensym ())
in (_181_158, (- (1))))
in (let _181_161 = (let _181_160 = (let _181_159 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _181_159))
in (_181_160)::more_args)
in (eta_args _181_161 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_341, _79_343) -> begin
((FStar_List.rev more_args), t)
end
| _79_347 -> begin
(FStar_All.failwith "Impossible")
end))
in (let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_79_352, args), Some (FStar_Absyn_Syntax.Record_ctor (_79_357, fields))) -> begin
(let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _79_366 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun qual e -> (let _79_372 = (eta_args [] residualType)
in (match (_79_372) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _181_170 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _181_170))
end
| _79_375 -> begin
(let _79_378 = (FStar_List.unzip eargs)
in (match (_79_378) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(let body = (let _181_172 = (let _181_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _181_171))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _181_172))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _79_385 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _79_387}, mlarg::[]), _79_396) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _79_399 = (FStar_Extraction_ML_Env.debug g (fun _79_398 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_79_402, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _79_406}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (let e = (match (args) with
| [] -> begin
proj
end
| _79_423 -> begin
(let _181_175 = (let _181_174 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_181_174, args))
in FStar_Extraction_ML_Syntax.MLE_App (_181_175))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _181_176 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _181_176))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _181_177 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _181_177))
end
| _79_459 -> begin
mlAppExpr
end)))))

# 285 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(let _79_465 = (FStar_List.hd l)
in (match (_79_465) with
| (p1, w1, e1) -> begin
(let _79_469 = (let _181_180 = (FStar_List.tl l)
in (FStar_List.hd _181_180))
in (match (_79_469) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _79_489 -> begin
def
end)
end))
end))
end))

# 297 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (let _79_499 = (let _181_197 = (check_exp' g e f t)
in (erase g _181_197 f t))
in (match (_79_499) with
| (e, _79_496, _79_498) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (let _79_507 = (synth_exp g e)
in (match (_79_507) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (let _79_513 = (synth_exp' g e)
in (match (_79_513) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (let _79_517 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _181_209 = (let _181_208 = (FStar_Absyn_Print.tag_of_exp e)
in (let _181_207 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _181_208 _181_207)))
in (FStar_Util.print_string _181_209))))
in (match ((let _181_210 = (FStar_Absyn_Util.compress_exp e)
in _181_210.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let ml_ty = (translate_typ g t)
in (let _181_214 = (let _181_213 = (let _181_212 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _181_211 -> FStar_Extraction_ML_Syntax.MLE_Const (_181_211)) _181_212))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _181_213))
in (_181_214, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
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
(let _79_546 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_79_546) with
| ((x, mltys, _79_543), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _181_215 = (maybe_lalloc_eta_data g qual t x)
in (_181_215, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _79_551 -> begin
(err_uninst g e mltys)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let rec synth_app = (fun is_data _79_560 _79_563 restArgs -> (match ((_79_560, _79_563)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _79_567) -> begin
(let _79_578 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _181_224 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _181_224))
end else begin
(FStar_List.fold_left (fun _79_571 _79_574 -> (match ((_79_571, _79_574)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(let x = (let _181_227 = (FStar_Absyn_Util.gensym ())
in (_181_227, (- (1))))
in (let _181_229 = (let _181_228 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_181_228)::out_args)
in (((x, arg))::lbs, _181_229)))
end
end)) ([], []) mlargs_f)
end
in (match (_79_578) with
| (lbs, mlargs) -> begin
(let app = (let _181_230 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _181_230))
in (let l_app = (FStar_List.fold_right (fun _79_582 out -> (match (_79_582) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = ([], arg.FStar_Extraction_ML_Syntax.ty); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_79_587), _79_590)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _181_234 = (let _181_233 = (FStar_Extraction_ML_Util.join f f')
in (_181_233, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _181_234 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _79_603)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(let _79_615 = (synth_exp g e0)
in (match (_79_615) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _181_236 = (let _181_235 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_181_235, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _181_236 rest)))
end))
end
| _79_618 -> begin
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
(let _79_636 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_79_636) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(let has_typ_apps = (match (args) with
| (FStar_Util.Inl (_79_640), _79_643)::_79_638 -> begin
true
end
| _79_647 -> begin
false
end)
in (let _79_687 = (match (vars) with
| _79_652::_79_650 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _79_655 -> begin
(let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(let _79_659 = (FStar_Util.first_N n args)
in (match (_79_659) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(let _79_668 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _79_668.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _79_672}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((let _79_679 = head
in {FStar_Extraction_ML_Syntax.expr = _79_679.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t))}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _79_682 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_79_687) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _181_237 = (maybe_lalloc_eta_data g qual head_t head_ml)
in (_181_237, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _79_690 -> begin
(synth_app qual (head_ml, []) (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _79_692 -> begin
(let _79_696 = (synth_exp g head)
in (match (_79_696) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _79_719 = (FStar_List.fold_left (fun _79_703 _79_707 -> (match ((_79_703, _79_707)) with
| ((ml_bs, env), (b, _79_706)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _181_240 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_181_240, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false false)
in (let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_79_719) with
| (ml_bs, env) -> begin
(let ml_bs = (FStar_List.rev ml_bs)
in (let _79_724 = (synth_exp env body)
in (match (_79_724) with
| (ml_body, f, t) -> begin
(let _79_734 = (FStar_List.fold_right (fun _79_728 _79_731 -> (match ((_79_728, _79_731)) with
| ((_79_726, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_79_734) with
| (f, tfun) -> begin
(let _181_243 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_181_243, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(let maybe_generalize = (fun _79_746 -> (match (_79_746) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _79_770 = (match ((FStar_Util.prefix_until (fun _79_4 -> (match (_79_4) with
| (FStar_Util.Inr (_79_755), _79_758) -> begin
true
end
| _79_761 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _181_247 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _181_247))
end)
in (match (_79_770) with
| (tbinders, tbody) -> begin
(let n = (FStar_List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(let _79_779 = (FStar_Util.first_N n bs)
in (match (_79_779) with
| (targs, rest_args) -> begin
(let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _79_5 -> (match (_79_5) with
| (FStar_Util.Inl (a), _79_788) -> begin
a
end
| _79_791 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _181_251 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_181_251, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _79_800 -> begin
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
| _79_805 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _79_808 -> begin
(err_value_restriction e)
end)))
end))
end
| _79_810 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun env _79_825 -> (match (_79_825) with
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
in (let _79_854 = (FStar_List.fold_right (fun lb _79_835 -> (match (_79_835) with
| (env, lbs) -> begin
(let _79_848 = lb
in (match (_79_848) with
| (lbname, _79_838, (t, (_79_841, polytype)), add_unit, _79_847) -> begin
(let _79_851 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_79_851) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_79_854) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (let _79_860 = (synth_exp env_body e')
in (match (_79_860) with
| (e', f', t') -> begin
(let f = (let _181_261 = (let _181_260 = (FStar_List.map Prims.fst lbs)
in (f')::_181_260)
in (FStar_Extraction_ML_Util.join_l _181_261))
in (let _181_266 = (let _181_265 = (let _181_264 = (let _181_263 = (let _181_262 = (FStar_List.map Prims.snd lbs)
in (is_rec, _181_262))
in (_181_263, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_181_264))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t') _181_265))
in (_181_266, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(let _79_869 = (synth_exp g scrutinee)
in (match (_79_869) with
| (e, f_e, t_e) -> begin
(let _79_873 = (check_pats_for_ite pats)
in (match (_79_873) with
| (b, then_e, else_e) -> begin
(let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(let _79_885 = (synth_exp g then_e)
in (match (_79_885) with
| (then_mle, f_then, t_then) -> begin
(let _79_889 = (synth_exp g else_e)
in (match (_79_889) with
| (else_mle, f_else, t_else) -> begin
(let _79_892 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_79_892) with
| (t_branch, maybe_lift) -> begin
(let _181_297 = (let _181_295 = (let _181_294 = (let _181_293 = (maybe_lift then_mle t_then)
in (let _181_292 = (let _181_291 = (maybe_lift else_mle t_else)
in Some (_181_291))
in (e, _181_293, _181_292)))
in FStar_Extraction_ML_Syntax.MLE_If (_181_294))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _181_295))
in (let _181_296 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_181_297, _181_296, t_branch)))
end))
end))
end))
end
| _79_894 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _79_898 -> (match (_79_898) with
| (pat, when_opt, branch) -> begin
(let _79_901 = (extract_pat g pat)
in (match (_79_901) with
| (env, p) -> begin
(let _79_912 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(let _79_908 = (synth_exp env w)
in (match (_79_908) with
| (w, f_w, t_w) -> begin
(let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_79_912) with
| (when_opt, f_when) -> begin
(let _79_916 = (synth_exp env branch)
in (match (_79_916) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _79_919 -> (match (_79_919) with
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
(let _79_928 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_79_928) with
| (fw, _79_925, _79_927) -> begin
(let _181_304 = (let _181_303 = (let _181_302 = (let _181_301 = (let _181_300 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_181_300)::[])
in (fw, _181_301))
in FStar_Extraction_ML_Syntax.MLE_App (_181_302))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _181_303))
in (_181_304, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_79_931, _79_933, (_79_935, f_first, t_first))::rest -> begin
(let _79_961 = (FStar_List.fold_left (fun _79_943 _79_953 -> (match ((_79_943, _79_953)) with
| ((topt, f), (_79_945, _79_947, (_79_949, f_branch, t_branch))) -> begin
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
in (match (_79_961) with
| (topt, f_match) -> begin
(let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _79_972 -> (match (_79_972) with
| (p, (wopt, _79_965), (b, _79_969, t)) -> begin
(let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_79_975) -> begin
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
in (let _181_308 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_181_308, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _79_985)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end)))

# 621 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let fresh : Prims.string  ->  (Prims.string * Prims.int) = (let c = (FStar_Util.mk_ref 0)
in (fun x -> (let _79_997 = (FStar_Util.incr c)
in (let _181_311 = (FStar_ST.read c)
in (x, _181_311)))))

# 624 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\extractexp.fs"

let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (let fstar_disc_type = (FStar_Tc_Env.lookup_lid env.FStar_Extraction_ML_Env.tcenv discName)
in (let wildcards = (match (fstar_disc_type.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _79_1005) -> begin
(let _181_321 = (FStar_All.pipe_right binders (FStar_List.filter (fun _79_6 -> (match (_79_6) with
| (_79_1010, Some (FStar_Absyn_Syntax.Implicit (_79_1012))) -> begin
true
end
| _79_1017 -> begin
false
end))))
in (FStar_All.pipe_right _181_321 (FStar_List.map (fun _79_1018 -> (let _181_320 = (fresh "_")
in (_181_320, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _79_1021 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (let mlid = (fresh "_discr_")
in (let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (let discrBody = (let _181_336 = (let _181_335 = (let _181_334 = (let _181_333 = (let _181_332 = (let _181_331 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _181_330 = (let _181_329 = (let _181_325 = (let _181_323 = (let _181_322 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_181_322, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_181_323))
in (let _181_324 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_181_325, None, _181_324)))
in (let _181_328 = (let _181_327 = (let _181_326 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _181_326))
in (_181_327)::[])
in (_181_329)::_181_328))
in (_181_331, _181_330)))
in FStar_Extraction_ML_Syntax.MLE_Match (_181_332))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _181_333))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _181_334))
in FStar_Extraction_ML_Syntax.MLE_Fun (_181_335))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _181_336))
in (let _181_342 = (let _181_341 = (let _181_340 = (let _181_339 = (let _181_338 = (let _181_337 = (fresh "dummy_ensures_is_polymorphic_hence_not_printed")
in (_181_337)::[])
in (_181_338, disc_ty))
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = _181_339; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})
in (_181_340)::[])
in (false, _181_341))
in FStar_Extraction_ML_Syntax.MLM_Let (_181_342)))))))))




