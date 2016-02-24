
open Prims
# 29 "FStar.Extraction.ML.ExtractExp.fst"
let fail = (fun r msg -> (
# 30 "FStar.Extraction.ML.ExtractExp.fst"
let _63_9 = (let _142_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _142_3))
in (FStar_All.failwith msg)))

# 33 "FStar.Extraction.ML.ExtractExp.fst"
let err_uninst = (fun env e _63_15 -> (match (_63_15) with
| (vars, t) -> begin
(let _142_11 = (let _142_10 = (FStar_Absyn_Print.exp_to_string e)
in (let _142_9 = (let _142_7 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _142_7 (FStar_String.concat ", ")))
in (let _142_8 = (FStar_Extraction_ML_Code.string_of_mlty env t)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _142_10 _142_9 _142_8))))
in (fail e.FStar_Absyn_Syntax.pos _142_11))
end))

# 39 "FStar.Extraction.ML.ExtractExp.fst"
let err_ill_typed_application = (fun e args t -> (let _142_17 = (let _142_16 = (FStar_Absyn_Print.exp_to_string e)
in (let _142_15 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _142_16 _142_15)))
in (fail e.FStar_Absyn_Syntax.pos _142_17)))

# 46 "FStar.Extraction.ML.ExtractExp.fst"
let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

# 49 "FStar.Extraction.ML.ExtractExp.fst"
let err_unexpected_eff = (fun e f0 f1 -> (let _142_23 = (let _142_22 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _142_22 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _142_23)))

# 52 "FStar.Extraction.ML.ExtractExp.fst"
let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _142_26 = (FStar_Absyn_Util.compress_exp e)
in _142_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _63_39 -> begin
false
end))

# 58 "FStar.Extraction.ML.ExtractExp.fst"
let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _142_29 = (FStar_Absyn_Util.compress_exp e)
in _142_29.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _63_60 -> (match (_63_60) with
| (te, _63_59) -> begin
(match (te) with
| FStar_Util.Inl (_63_62) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _142_31 = (FStar_Absyn_Util.compress_exp head)
in _142_31.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _63_1 -> (match (_63_1) with
| (FStar_Util.Inl (te), _63_76) -> begin
true
end
| _63_79 -> begin
false
end))))
end
| _63_81 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _63_95 -> begin
false
end))

# 77 "FStar.Extraction.ML.ExtractExp.fst"
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_63_116, fields) -> begin
(FStar_Util.for_all (fun _63_123 -> (match (_63_123) with
| (_63_121, e) -> begin
(is_ml_value e)
end)) fields)
end
| _63_125 -> begin
false
end))

# 89 "FStar.Extraction.ML.ExtractExp.fst"
let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _142_40 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _142_40)))

# 90 "FStar.Extraction.ML.ExtractExp.fst"
let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _142_45 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _142_45)))

# 94 "FStar.Extraction.ML.ExtractExp.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 96 "FStar.Extraction.ML.ExtractExp.fst"
let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

# 100 "FStar.Extraction.ML.ExtractExp.fst"
let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(
# 102 "FStar.Extraction.ML.ExtractExp.fst"
let _63_140 = (FStar_Extraction_ML_Env.debug g (fun _63_139 -> (match (()) with
| () -> begin
(let _142_66 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _142_65 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _142_66 _142_65)))
end)))
in (
# 103 "FStar.Extraction.ML.ExtractExp.fst"
let e_val = if (FStar_Extraction_ML_Util.type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t))))
end
in (e_val, f, t)))
end else begin
(e, f, t)
end)

# 107 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_coerce : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e tInferred tExpected -> (match ((FStar_Extraction_ML_Util.type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _63_152 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

# 116 "FStar.Extraction.ML.ExtractExp.fst"
let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 118 "FStar.Extraction.ML.ExtractExp.fst"
let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_63_161) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 124 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _142_87 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _142_87))
in (
# 125 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (let _142_96 = (let _142_95 = (let _142_94 = (let _142_93 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _142_92 = (let _142_91 = (let _142_90 = (let _142_89 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _142_88 -> FStar_Extraction_ML_Syntax.MLE_Const (_142_88)) _142_89))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _142_90))
in (_142_91)::[])
in (_142_93)::_142_92))
in (FStar_Extraction_ML_Util.prims_op_equality, _142_94))
in FStar_Extraction_ML_Syntax.MLE_App (_142_95))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _142_96))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _142_100 = (let _142_99 = (let _142_98 = (let _142_97 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_142_97))
in (_142_98, []))
in Some (_142_99))
in (g, _142_100))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(
# 133 "FStar.Extraction.ML.ExtractExp.fst"
let _63_190 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _63_178; FStar_Extraction_ML_Syntax.loc = _63_176}, ttys, _63_184) -> begin
(n, ttys)
end
| _63_187 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_63_190) with
| (d, tys) -> begin
(
# 136 "FStar.Extraction.ML.ExtractExp.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 137 "FStar.Extraction.ML.ExtractExp.fst"
let _63_194 = (FStar_Util.first_N nTyVars pats)
in (match (_63_194) with
| (tysVarPats, restPats) -> begin
(
# 138 "FStar.Extraction.ML.ExtractExp.fst"
let _63_201 = (FStar_Util.fold_map (fun g _63_198 -> (match (_63_198) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_63_201) with
| (g, tyMLPats) -> begin
(
# 139 "FStar.Extraction.ML.ExtractExp.fst"
let _63_208 = (FStar_Util.fold_map (fun g _63_205 -> (match (_63_205) with
| (p, imp) -> begin
(extract_one_pat disj false g p)
end)) g restPats)
in (match (_63_208) with
| (g, restMLPats) -> begin
(
# 140 "FStar.Extraction.ML.ExtractExp.fst"
let _63_216 = (let _142_106 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _63_2 -> (match (_63_2) with
| Some (x) -> begin
(x)::[]
end
| _63_213 -> begin
[]
end))))
in (FStar_All.pipe_right _142_106 FStar_List.split))
in (match (_63_216) with
| (mlPats, when_clauses) -> begin
(let _142_110 = (let _142_109 = (let _142_108 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _142_107 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_142_108, _142_107)))
in Some (_142_109))
in (g, _142_110))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(
# 144 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (
# 145 "FStar.Extraction.ML.ExtractExp.fst"
let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false false imp)
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
(
# 152 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (
# 153 "FStar.Extraction.ML.ExtractExp.fst"
let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end)))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(
# 157 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 158 "FStar.Extraction.ML.ExtractExp.fst"
let g = (FStar_Extraction_ML_Env.extend_ty g a (Some (mlty)))
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Wild, []))
end)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) -> begin
(g, None)
end))
in (
# 166 "FStar.Extraction.ML.ExtractExp.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _63_251 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 171 "FStar.Extraction.ML.ExtractExp.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _142_119 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_142_119))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(
# 180 "FStar.Extraction.ML.ExtractExp.fst"
let _63_266 = (extract_one_pat true g p)
in (match (_63_266) with
| (g, p) -> begin
(
# 181 "FStar.Extraction.ML.ExtractExp.fst"
let ps = (let _142_122 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _142_121 = (extract_one_pat true g x)
in (Prims.snd _142_121)))))
in (p)::_142_122)
in (
# 182 "FStar.Extraction.ML.ExtractExp.fst"
let _63_282 = (FStar_All.pipe_right ps (FStar_List.partition (fun _63_3 -> (match (_63_3) with
| (_63_271, _63_275::_63_273) -> begin
true
end
| _63_279 -> begin
false
end))))
in (match (_63_282) with
| (ps_when, rest) -> begin
(
# 183 "FStar.Extraction.ML.ExtractExp.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _63_285 -> (match (_63_285) with
| (x, whens) -> begin
(let _142_125 = (mk_when_clause whens)
in (x, _142_125))
end))))
in (
# 185 "FStar.Extraction.ML.ExtractExp.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _142_129 = (let _142_128 = (let _142_127 = (let _142_126 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_142_126))
in (_142_127, None))
in (_142_128)::ps)
in (g, _142_129))
end)
in res))
end)))
end))
end
| _63_291 -> begin
(
# 191 "FStar.Extraction.ML.ExtractExp.fst"
let _63_296 = (extract_one_pat false g p)
in (match (_63_296) with
| (g, (p, whens)) -> begin
(
# 192 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 195 "FStar.Extraction.ML.ExtractExp.fst"
let normalize_abs : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun e0 -> (
# 196 "FStar.Extraction.ML.ExtractExp.fst"
let rec aux = (fun bs e -> (
# 197 "FStar.Extraction.ML.ExtractExp.fst"
let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _63_308 -> begin
(
# 201 "FStar.Extraction.ML.ExtractExp.fst"
let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

# 207 "FStar.Extraction.ML.ExtractExp.fst"
let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (
# 208 "FStar.Extraction.ML.ExtractExp.fst"
let name = if ((2 < n) && (n < 6)) then begin
(let _142_138 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _142_138))
end else begin
if (n = 2) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in (("Camlstack")::[], name)))

# 212 "FStar.Extraction.ML.ExtractExp.fst"
let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(
# 216 "FStar.Extraction.ML.ExtractExp.fst"
let args = (FStar_List.map Prims.snd fields)
in (
# 217 "FStar.Extraction.ML.ExtractExp.fst"
let tup = (let _142_145 = (let _142_144 = (let _142_143 = (let _142_142 = (let _142_141 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_142_141))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _142_142))
in (_142_143, args))
in FStar_Extraction_ML_Syntax.MLE_App (_142_144))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _142_145))
in (
# 218 "FStar.Extraction.ML.ExtractExp.fst"
let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _63_327 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

# 232 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 233 "FStar.Extraction.ML.ExtractExp.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _63_337, t1) -> begin
(
# 235 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _142_158 = (FStar_Absyn_Util.gensym ())
in (_142_158, (- (1))))
in (let _142_161 = (let _142_160 = (let _142_159 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _142_159))
in (_142_160)::more_args)
in (eta_args _142_161 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_63_343, _63_345) -> begin
((FStar_List.rev more_args), t)
end
| _63_349 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 240 "FStar.Extraction.ML.ExtractExp.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_63_354, args), Some (FStar_Absyn_Syntax.Record_ctor (_63_359, fields))) -> begin
(
# 243 "FStar.Extraction.ML.ExtractExp.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 244 "FStar.Extraction.ML.ExtractExp.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _63_368 -> begin
e
end))
in (
# 248 "FStar.Extraction.ML.ExtractExp.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 249 "FStar.Extraction.ML.ExtractExp.fst"
let _63_374 = (eta_args [] residualType)
in (match (_63_374) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _142_170 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _142_170))
end
| _63_377 -> begin
(
# 253 "FStar.Extraction.ML.ExtractExp.fst"
let _63_380 = (FStar_List.unzip eargs)
in (match (_63_380) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 256 "FStar.Extraction.ML.ExtractExp.fst"
let body = (let _142_172 = (let _142_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _142_171))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _142_172))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _63_387 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _63_391; FStar_Extraction_ML_Syntax.loc = _63_389}, mlarg::[]), _63_400) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(
# 262 "FStar.Extraction.ML.ExtractExp.fst"
let _63_403 = (FStar_Extraction_ML_Env.debug g (fun _63_402 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_63_406, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _63_412; FStar_Extraction_ML_Syntax.loc = _63_410}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(
# 268 "FStar.Extraction.ML.ExtractExp.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 269 "FStar.Extraction.ML.ExtractExp.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 270 "FStar.Extraction.ML.ExtractExp.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _63_429 -> begin
(let _142_175 = (let _142_174 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_142_174, args))
in FStar_Extraction_ML_Syntax.MLE_App (_142_175))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _142_176 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _142_176))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _142_177 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _142_177))
end
| _63_469 -> begin
mlAppExpr
end)))))

# 285 "FStar.Extraction.ML.ExtractExp.fst"
let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (
# 286 "FStar.Extraction.ML.ExtractExp.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 289 "FStar.Extraction.ML.ExtractExp.fst"
let _63_475 = (FStar_List.hd l)
in (match (_63_475) with
| (p1, w1, e1) -> begin
(
# 290 "FStar.Extraction.ML.ExtractExp.fst"
let _63_479 = (let _142_180 = (FStar_List.tl l)
in (FStar_List.hd _142_180))
in (match (_63_479) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _63_499 -> begin
def
end)
end))
end))
end))

# 297 "FStar.Extraction.ML.ExtractExp.fst"
let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (
# 299 "FStar.Extraction.ML.ExtractExp.fst"
let _63_509 = (let _142_197 = (check_exp' g e f t)
in (erase g _142_197 f t))
in (match (_63_509) with
| (e, _63_506, _63_508) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (
# 303 "FStar.Extraction.ML.ExtractExp.fst"
let _63_517 = (synth_exp g e)
in (match (_63_517) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (
# 309 "FStar.Extraction.ML.ExtractExp.fst"
let _63_523 = (synth_exp' g e)
in (match (_63_523) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (
# 316 "FStar.Extraction.ML.ExtractExp.fst"
let _63_527 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _142_209 = (let _142_208 = (FStar_Absyn_Print.tag_of_exp e)
in (let _142_207 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _142_208 _142_207)))
in (FStar_Util.print_string _142_209))))
in (match ((let _142_210 = (FStar_Absyn_Util.compress_exp e)
in _142_210.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(
# 320 "FStar.Extraction.ML.ExtractExp.fst"
let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (
# 321 "FStar.Extraction.ML.ExtractExp.fst"
let ml_ty = (translate_typ g t)
in (let _142_214 = (let _142_213 = (let _142_212 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _142_211 -> FStar_Extraction_ML_Syntax.MLE_Const (_142_211)) _142_212))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _142_213))
in (_142_214, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e0, t, f) -> begin
(
# 325 "FStar.Extraction.ML.ExtractExp.fst"
let t = (translate_typ g t)
in (
# 326 "FStar.Extraction.ML.ExtractExp.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (
# 329 "FStar.Extraction.ML.ExtractExp.fst"
let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(
# 334 "FStar.Extraction.ML.ExtractExp.fst"
let _63_556 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_63_556) with
| ((x, mltys, _63_553), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _142_215 = (maybe_lalloc_eta_data g qual t x)
in (_142_215, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _63_561 -> begin
(err_uninst g e mltys)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 342 "FStar.Extraction.ML.ExtractExp.fst"
let rec synth_app = (fun is_data _63_570 _63_573 restArgs -> (match ((_63_570, _63_573)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _63_577) -> begin
(
# 350 "FStar.Extraction.ML.ExtractExp.fst"
let _63_588 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _142_224 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _142_224))
end else begin
(FStar_List.fold_left (fun _63_581 _63_584 -> (match ((_63_581, _63_584)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 356 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _142_227 = (FStar_Absyn_Util.gensym ())
in (_142_227, (- (1))))
in (let _142_229 = (let _142_228 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_142_228)::out_args)
in (((x, arg))::lbs, _142_229)))
end
end)) ([], []) mlargs_f)
end
in (match (_63_588) with
| (lbs, mlargs) -> begin
(
# 359 "FStar.Extraction.ML.ExtractExp.fst"
let app = (let _142_230 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _142_230))
in (
# 360 "FStar.Extraction.ML.ExtractExp.fst"
let l_app = (FStar_List.fold_right (fun _63_592 out -> (match (_63_592) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.ty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_63_597), _63_600)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _142_234 = (let _142_233 = (FStar_Extraction_ML_Util.join f f')
in (_142_233, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _142_234 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _63_613)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 373 "FStar.Extraction.ML.ExtractExp.fst"
let _63_625 = (synth_exp g e0)
in (match (_63_625) with
| (e0, f0, tInferred) -> begin
(
# 374 "FStar.Extraction.ML.ExtractExp.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _142_236 = (let _142_235 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_142_235, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _142_236 rest)))
end))
end
| _63_628 -> begin
(match ((FStar_Extraction_ML_Util.delta_unfold g t)) with
| Some (t) -> begin
(synth_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application e restArgs t)
end)
end)
end))
in (
# 383 "FStar.Extraction.ML.ExtractExp.fst"
let head = (FStar_Absyn_Util.compress_exp head)
in (match (head.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(
# 388 "FStar.Extraction.ML.ExtractExp.fst"
let _63_646 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_63_646) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 389 "FStar.Extraction.ML.ExtractExp.fst"
let has_typ_apps = (match (args) with
| (FStar_Util.Inl (_63_650), _63_653)::_63_648 -> begin
true
end
| _63_657 -> begin
false
end)
in (
# 393 "FStar.Extraction.ML.ExtractExp.fst"
let _63_699 = (match (vars) with
| _63_662::_63_660 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _63_665 -> begin
(
# 400 "FStar.Extraction.ML.ExtractExp.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 402 "FStar.Extraction.ML.ExtractExp.fst"
let _63_669 = (FStar_Util.first_N n args)
in (match (_63_669) with
| (prefix, rest) -> begin
(
# 404 "FStar.Extraction.ML.ExtractExp.fst"
let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (
# 406 "FStar.Extraction.ML.ExtractExp.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 407 "FStar.Extraction.ML.ExtractExp.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 409 "FStar.Extraction.ML.ExtractExp.fst"
let _63_678 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _63_678.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t; FStar_Extraction_ML_Syntax.loc = _63_678.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _63_684; FStar_Extraction_ML_Syntax.loc = _63_682}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 410 "FStar.Extraction.ML.ExtractExp.fst"
let _63_691 = head
in {FStar_Extraction_ML_Syntax.expr = _63_691.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _63_691.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _63_694 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_63_699) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _142_237 = (maybe_lalloc_eta_data g qual head_t head_ml)
in (_142_237, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _63_702 -> begin
(synth_app qual (head_ml, []) (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _63_704 -> begin
(
# 421 "FStar.Extraction.ML.ExtractExp.fst"
let _63_708 = (synth_exp g head)
in (match (_63_708) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 426 "FStar.Extraction.ML.ExtractExp.fst"
let _63_731 = (FStar_List.fold_left (fun _63_715 _63_719 -> (match ((_63_715, _63_719)) with
| ((ml_bs, env), (b, _63_718)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(
# 428 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 429 "FStar.Extraction.ML.ExtractExp.fst"
let ml_b = (let _142_240 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_142_240, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(
# 433 "FStar.Extraction.ML.ExtractExp.fst"
let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (
# 434 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false false)
in (
# 435 "FStar.Extraction.ML.ExtractExp.fst"
let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_63_731) with
| (ml_bs, env) -> begin
(
# 437 "FStar.Extraction.ML.ExtractExp.fst"
let ml_bs = (FStar_List.rev ml_bs)
in (
# 438 "FStar.Extraction.ML.ExtractExp.fst"
let _63_736 = (synth_exp env body)
in (match (_63_736) with
| (ml_body, f, t) -> begin
(
# 440 "FStar.Extraction.ML.ExtractExp.fst"
let _63_746 = (FStar_List.fold_right (fun _63_740 _63_743 -> (match ((_63_740, _63_743)) with
| ((_63_738, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_63_746) with
| (f, tfun) -> begin
(let _142_243 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_142_243, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(
# 448 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_generalize = (fun _63_758 -> (match (_63_758) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(
# 449 "FStar.Extraction.ML.ExtractExp.fst"
let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (
# 450 "FStar.Extraction.ML.ExtractExp.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(
# 457 "FStar.Extraction.ML.ExtractExp.fst"
let _63_782 = (match ((FStar_Util.prefix_until (fun _63_4 -> (match (_63_4) with
| (FStar_Util.Inr (_63_767), _63_770) -> begin
true
end
| _63_773 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _142_247 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _142_247))
end)
in (match (_63_782) with
| (tbinders, tbody) -> begin
(
# 462 "FStar.Extraction.ML.ExtractExp.fst"
let n = (FStar_List.length tbinders)
in (
# 463 "FStar.Extraction.ML.ExtractExp.fst"
let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(
# 467 "FStar.Extraction.ML.ExtractExp.fst"
let _63_791 = (FStar_Util.first_N n bs)
in (match (_63_791) with
| (targs, rest_args) -> begin
(
# 471 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (
# 475 "FStar.Extraction.ML.ExtractExp.fst"
let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _63_5 -> (match (_63_5) with
| (FStar_Util.Inl (a), _63_800) -> begin
a
end
| _63_803 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 476 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (
# 477 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (translate_typ env expected_t)
in (
# 478 "FStar.Extraction.ML.ExtractExp.fst"
let polytype = (let _142_251 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_142_251, expected_t))
in (
# 479 "FStar.Extraction.ML.ExtractExp.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _63_812 -> begin
false
end)
in (
# 482 "FStar.Extraction.ML.ExtractExp.fst"
let rest_args = if add_unit then begin
(FStar_Extraction_ML_Util.unit_binder)::rest_args
end else begin
rest_args
end
in (
# 483 "FStar.Extraction.ML.ExtractExp.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _63_817 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _63_820 -> begin
(err_value_restriction e)
end)))
end))
end
| _63_822 -> begin
(
# 512 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 515 "FStar.Extraction.ML.ExtractExp.fst"
let check_lb = (fun env _63_837 -> (match (_63_837) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 516 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
in (
# 517 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 518 "FStar.Extraction.ML.ExtractExp.fst"
let e = (check_exp env e f expected_t)
in (f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e}))))
end))
in (
# 522 "FStar.Extraction.ML.ExtractExp.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 524 "FStar.Extraction.ML.ExtractExp.fst"
let _63_866 = (FStar_List.fold_right (fun lb _63_847 -> (match (_63_847) with
| (env, lbs) -> begin
(
# 525 "FStar.Extraction.ML.ExtractExp.fst"
let _63_860 = lb
in (match (_63_860) with
| (lbname, _63_850, (t, (_63_853, polytype)), add_unit, _63_859) -> begin
(
# 526 "FStar.Extraction.ML.ExtractExp.fst"
let _63_863 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_63_863) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_63_866) with
| (env_body, lbs) -> begin
(
# 529 "FStar.Extraction.ML.ExtractExp.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 531 "FStar.Extraction.ML.ExtractExp.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 533 "FStar.Extraction.ML.ExtractExp.fst"
let _63_872 = (synth_exp env_body e')
in (match (_63_872) with
| (e', f', t') -> begin
(
# 535 "FStar.Extraction.ML.ExtractExp.fst"
let f = (let _142_261 = (let _142_260 = (FStar_List.map Prims.fst lbs)
in (f')::_142_260)
in (FStar_Extraction_ML_Util.join_l _142_261))
in (let _142_267 = (let _142_266 = (let _142_264 = (let _142_263 = (let _142_262 = (FStar_List.map Prims.snd lbs)
in (is_rec, _142_262))
in (_142_263, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_142_264))
in (let _142_265 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range e.FStar_Absyn_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _142_266 _142_265)))
in (_142_267, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(
# 540 "FStar.Extraction.ML.ExtractExp.fst"
let _63_881 = (synth_exp g scrutinee)
in (match (_63_881) with
| (e, f_e, t_e) -> begin
(
# 541 "FStar.Extraction.ML.ExtractExp.fst"
let _63_885 = (check_pats_for_ite pats)
in (match (_63_885) with
| (b, then_e, else_e) -> begin
(
# 542 "FStar.Extraction.ML.ExtractExp.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 546 "FStar.Extraction.ML.ExtractExp.fst"
let _63_897 = (synth_exp g then_e)
in (match (_63_897) with
| (then_mle, f_then, t_then) -> begin
(
# 547 "FStar.Extraction.ML.ExtractExp.fst"
let _63_901 = (synth_exp g else_e)
in (match (_63_901) with
| (else_mle, f_else, t_else) -> begin
(
# 548 "FStar.Extraction.ML.ExtractExp.fst"
let _63_904 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_63_904) with
| (t_branch, maybe_lift) -> begin
(let _142_298 = (let _142_296 = (let _142_295 = (let _142_294 = (maybe_lift then_mle t_then)
in (let _142_293 = (let _142_292 = (maybe_lift else_mle t_else)
in Some (_142_292))
in (e, _142_294, _142_293)))
in FStar_Extraction_ML_Syntax.MLE_If (_142_295))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _142_296))
in (let _142_297 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_142_298, _142_297, t_branch)))
end))
end))
end))
end
| _63_906 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 559 "FStar.Extraction.ML.ExtractExp.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _63_910 -> (match (_63_910) with
| (pat, when_opt, branch) -> begin
(
# 560 "FStar.Extraction.ML.ExtractExp.fst"
let _63_913 = (extract_pat g pat)
in (match (_63_913) with
| (env, p) -> begin
(
# 561 "FStar.Extraction.ML.ExtractExp.fst"
let _63_924 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 564 "FStar.Extraction.ML.ExtractExp.fst"
let _63_920 = (synth_exp env w)
in (match (_63_920) with
| (w, f_w, t_w) -> begin
(
# 565 "FStar.Extraction.ML.ExtractExp.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_63_924) with
| (when_opt, f_when) -> begin
(
# 567 "FStar.Extraction.ML.ExtractExp.fst"
let _63_928 = (synth_exp env branch)
in (match (_63_928) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _63_931 -> (match (_63_931) with
| (p, wopt) -> begin
(
# 570 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
end))))
end))
end))
end))
end))))
in (match (mlbranches) with
| [] -> begin
(
# 575 "FStar.Extraction.ML.ExtractExp.fst"
let _63_940 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_63_940) with
| (fw, _63_937, _63_939) -> begin
(let _142_305 = (let _142_304 = (let _142_303 = (let _142_302 = (let _142_301 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_142_301)::[])
in (fw, _142_302))
in FStar_Extraction_ML_Syntax.MLE_App (_142_303))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _142_304))
in (_142_305, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_63_943, _63_945, (_63_947, f_first, t_first))::rest -> begin
(
# 582 "FStar.Extraction.ML.ExtractExp.fst"
let _63_973 = (FStar_List.fold_left (fun _63_955 _63_965 -> (match ((_63_955, _63_965)) with
| ((topt, f), (_63_957, _63_959, (_63_961, f_branch, t_branch))) -> begin
(
# 586 "FStar.Extraction.ML.ExtractExp.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 587 "FStar.Extraction.ML.ExtractExp.fst"
let topt = (match (topt) with
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
in (match (_63_973) with
| (topt, f_match) -> begin
(
# 600 "FStar.Extraction.ML.ExtractExp.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _63_984 -> (match (_63_984) with
| (p, (wopt, _63_977), (b, _63_981, t)) -> begin
(
# 601 "FStar.Extraction.ML.ExtractExp.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_63_987) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 607 "FStar.Extraction.ML.ExtractExp.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _142_309 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_142_309, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _63_997)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end)))

# 621 "FStar.Extraction.ML.ExtractExp.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 621 "FStar.Extraction.ML.ExtractExp.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 622 "FStar.Extraction.ML.ExtractExp.fst"
let _63_1009 = (FStar_Util.incr c)
in (let _142_312 = (FStar_ST.read c)
in (x, _142_312)))))

# 624 "FStar.Extraction.ML.ExtractExp.fst"
let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 626 "FStar.Extraction.ML.ExtractExp.fst"
let fstar_disc_type = (FStar_Tc_Env.lookup_lid env.FStar_Extraction_ML_Env.tcenv discName)
in (
# 627 "FStar.Extraction.ML.ExtractExp.fst"
let wildcards = (match (fstar_disc_type.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _63_1017) -> begin
(let _142_322 = (FStar_All.pipe_right binders (FStar_List.filter (fun _63_6 -> (match (_63_6) with
| (_63_1022, Some (FStar_Absyn_Syntax.Implicit (_63_1024))) -> begin
true
end
| _63_1029 -> begin
false
end))))
in (FStar_All.pipe_right _142_322 (FStar_List.map (fun _63_1030 -> (let _142_321 = (fresh "_")
in (_142_321, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _63_1033 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 638 "FStar.Extraction.ML.ExtractExp.fst"
let mlid = (fresh "_discr_")
in (
# 639 "FStar.Extraction.ML.ExtractExp.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 642 "FStar.Extraction.ML.ExtractExp.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 643 "FStar.Extraction.ML.ExtractExp.fst"
let discrBody = (let _142_337 = (let _142_336 = (let _142_335 = (let _142_334 = (let _142_333 = (let _142_332 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _142_331 = (let _142_330 = (let _142_326 = (let _142_324 = (let _142_323 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_142_323, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_142_324))
in (let _142_325 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_142_326, None, _142_325)))
in (let _142_329 = (let _142_328 = (let _142_327 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _142_327))
in (_142_328)::[])
in (_142_330)::_142_329))
in (_142_332, _142_331)))
in FStar_Extraction_ML_Syntax.MLE_Match (_142_333))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _142_334))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _142_335))
in FStar_Extraction_ML_Syntax.MLE_Fun (_142_336))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _142_337))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[])))))))))




