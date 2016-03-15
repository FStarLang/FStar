
open Prims
# 29 "FStar.Extraction.ML.ExtractExp.fst"
let fail = (fun r msg -> (
# 30 "FStar.Extraction.ML.ExtractExp.fst"
let _62_9 = (let _143_3 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _143_3))
in (FStar_All.failwith msg)))

# 33 "FStar.Extraction.ML.ExtractExp.fst"
let err_uninst = (fun env e _62_15 -> (match (_62_15) with
| (vars, t) -> begin
(let _143_11 = (let _143_10 = (FStar_Absyn_Print.exp_to_string e)
in (let _143_9 = (let _143_7 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _143_7 (FStar_String.concat ", ")))
in (let _143_8 = (FStar_Extraction_ML_Code.string_of_mlty env t)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _143_10 _143_9 _143_8))))
in (fail e.FStar_Absyn_Syntax.pos _143_11))
end))

# 39 "FStar.Extraction.ML.ExtractExp.fst"
let err_ill_typed_application = (fun e args t -> (let _143_17 = (let _143_16 = (FStar_Absyn_Print.exp_to_string e)
in (let _143_15 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _143_16 _143_15)))
in (fail e.FStar_Absyn_Syntax.pos _143_17)))

# 46 "FStar.Extraction.ML.ExtractExp.fst"
let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

# 49 "FStar.Extraction.ML.ExtractExp.fst"
let err_unexpected_eff = (fun e f0 f1 -> (let _143_23 = (let _143_22 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _143_22 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _143_23)))

# 52 "FStar.Extraction.ML.ExtractExp.fst"
let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _143_26 = (FStar_Absyn_Util.compress_exp e)
in _143_26.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _62_39 -> begin
false
end))

# 58 "FStar.Extraction.ML.ExtractExp.fst"
let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _143_29 = (FStar_Absyn_Util.compress_exp e)
in _143_29.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
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
end else begin
(match ((let _143_31 = (FStar_Absyn_Util.compress_exp head)
in _143_31.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _62_1 -> (match (_62_1) with
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
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _62_95 -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Record (_62_116, fields) -> begin
(FStar_Util.for_all (fun _62_123 -> (match (_62_123) with
| (_62_121, e) -> begin
(is_ml_value e)
end)) fields)
end
| _62_125 -> begin
false
end))

# 89 "FStar.Extraction.ML.ExtractExp.fst"
let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _143_40 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _143_40)))

# 90 "FStar.Extraction.ML.ExtractExp.fst"
let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _143_45 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (FStar_Extraction_ML_Util.eraseTypeDeep g _143_45)))

# 94 "FStar.Extraction.ML.ExtractExp.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 96 "FStar.Extraction.ML.ExtractExp.fst"
let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (FStar_Extraction_ML_Util.erasableType g t))))

# 100 "FStar.Extraction.ML.ExtractExp.fst"
let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(
# 102 "FStar.Extraction.ML.ExtractExp.fst"
let _62_140 = (FStar_Extraction_ML_Env.debug g (fun _62_139 -> (match (()) with
| () -> begin
(let _143_66 = (FStar_Extraction_ML_Code.string_of_mlexpr g e)
in (let _143_65 = (FStar_Extraction_ML_Code.string_of_mlty g t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _143_66 _143_65)))
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
| _62_152 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

# 116 "FStar.Extraction.ML.ExtractExp.fst"
let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 118 "FStar.Extraction.ML.ExtractExp.fst"
let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_62_161) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 124 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _143_87 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _143_87))
in (
# 125 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (let _143_96 = (let _143_95 = (let _143_94 = (let _143_93 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _143_92 = (let _143_91 = (let _143_90 = (let _143_89 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _143_88 -> FStar_Extraction_ML_Syntax.MLE_Const (_143_88)) _143_89))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _143_90))
in (_143_91)::[])
in (_143_93)::_143_92))
in (FStar_Extraction_ML_Util.prims_op_equality, _143_94))
in FStar_Extraction_ML_Syntax.MLE_App (_143_95))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _143_96))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _143_100 = (let _143_99 = (let _143_98 = (let _143_97 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_143_97))
in (_143_98, []))
in Some (_143_99))
in (g, _143_100))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(
# 133 "FStar.Extraction.ML.ExtractExp.fst"
let _62_190 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.ty = _62_178; FStar_Extraction_ML_Syntax.loc = _62_176}, ttys, _62_184) -> begin
(n, ttys)
end
| _62_187 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_62_190) with
| (d, tys) -> begin
(
# 136 "FStar.Extraction.ML.ExtractExp.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 137 "FStar.Extraction.ML.ExtractExp.fst"
let _62_194 = (FStar_Util.first_N nTyVars pats)
in (match (_62_194) with
| (tysVarPats, restPats) -> begin
(
# 138 "FStar.Extraction.ML.ExtractExp.fst"
let _62_201 = (FStar_Util.fold_map (fun g _62_198 -> (match (_62_198) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_62_201) with
| (g, tyMLPats) -> begin
(
# 139 "FStar.Extraction.ML.ExtractExp.fst"
let _62_215 = (FStar_Util.fold_map (fun g _62_205 -> (match (_62_205) with
| (p, imp) -> begin
(
# 140 "FStar.Extraction.ML.ExtractExp.fst"
let _62_208 = (extract_one_pat disj false g p)
in (match (_62_208) with
| (env, popt) -> begin
(
# 141 "FStar.Extraction.ML.ExtractExp.fst"
let popt = (match (popt) with
| None -> begin
Some ((FStar_Extraction_ML_Syntax.MLP_Wild, []))
end
| _62_211 -> begin
popt
end)
in (env, popt))
end))
end)) g restPats)
in (match (_62_215) with
| (g, restMLPats) -> begin
(
# 145 "FStar.Extraction.ML.ExtractExp.fst"
let _62_223 = (let _143_106 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _62_2 -> (match (_62_2) with
| Some (x) -> begin
(x)::[]
end
| _62_220 -> begin
[]
end))))
in (FStar_All.pipe_right _143_106 FStar_List.split))
in (match (_62_223) with
| (mlPats, when_clauses) -> begin
(let _143_110 = (let _143_109 = (let _143_108 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _143_107 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_143_108, _143_107)))
in Some (_143_109))
in (g, _143_110))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(
# 149 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (
# 150 "FStar.Extraction.ML.ExtractExp.fst"
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
# 157 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (
# 158 "FStar.Extraction.ML.ExtractExp.fst"
let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end)))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(
# 162 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 163 "FStar.Extraction.ML.ExtractExp.fst"
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
# 171 "FStar.Extraction.ML.ExtractExp.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _62_258 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 176 "FStar.Extraction.ML.ExtractExp.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _143_119 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_143_119))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(
# 185 "FStar.Extraction.ML.ExtractExp.fst"
let _62_273 = (extract_one_pat true g p)
in (match (_62_273) with
| (g, p) -> begin
(
# 186 "FStar.Extraction.ML.ExtractExp.fst"
let ps = (let _143_122 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _143_121 = (extract_one_pat true g x)
in (Prims.snd _143_121)))))
in (p)::_143_122)
in (
# 187 "FStar.Extraction.ML.ExtractExp.fst"
let _62_289 = (FStar_All.pipe_right ps (FStar_List.partition (fun _62_3 -> (match (_62_3) with
| (_62_278, _62_282::_62_280) -> begin
true
end
| _62_286 -> begin
false
end))))
in (match (_62_289) with
| (ps_when, rest) -> begin
(
# 188 "FStar.Extraction.ML.ExtractExp.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _62_292 -> (match (_62_292) with
| (x, whens) -> begin
(let _143_125 = (mk_when_clause whens)
in (x, _143_125))
end))))
in (
# 190 "FStar.Extraction.ML.ExtractExp.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _143_129 = (let _143_128 = (let _143_127 = (let _143_126 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_143_126))
in (_143_127, None))
in (_143_128)::ps)
in (g, _143_129))
end)
in res))
end)))
end))
end
| _62_298 -> begin
(
# 196 "FStar.Extraction.ML.ExtractExp.fst"
let _62_303 = (extract_one_pat false g p)
in (match (_62_303) with
| (g, (p, whens)) -> begin
(
# 197 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 200 "FStar.Extraction.ML.ExtractExp.fst"
let normalize_abs : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun e0 -> (
# 201 "FStar.Extraction.ML.ExtractExp.fst"
let rec aux = (fun bs e -> (
# 202 "FStar.Extraction.ML.ExtractExp.fst"
let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _62_315 -> begin
(
# 206 "FStar.Extraction.ML.ExtractExp.fst"
let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

# 212 "FStar.Extraction.ML.ExtractExp.fst"
let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (
# 213 "FStar.Extraction.ML.ExtractExp.fst"
let name = if ((2 < n) && (n < 6)) then begin
(let _143_138 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _143_138))
end else begin
if (n = 2) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in (("Camlstack")::[], name)))

# 217 "FStar.Extraction.ML.ExtractExp.fst"
let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(
# 221 "FStar.Extraction.ML.ExtractExp.fst"
let args = (FStar_List.map Prims.snd fields)
in (
# 222 "FStar.Extraction.ML.ExtractExp.fst"
let tup = (let _143_145 = (let _143_144 = (let _143_143 = (let _143_142 = (let _143_141 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_143_141))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _143_142))
in (_143_143, args))
in FStar_Extraction_ML_Syntax.MLE_App (_143_144))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _143_145))
in (
# 223 "FStar.Extraction.ML.ExtractExp.fst"
let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _62_334 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

# 237 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 238 "FStar.Extraction.ML.ExtractExp.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _62_344, t1) -> begin
(
# 240 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _143_158 = (FStar_Absyn_Util.gensym ())
in (_143_158, (- (1))))
in (let _143_161 = (let _143_160 = (let _143_159 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _143_159))
in (_143_160)::more_args)
in (eta_args _143_161 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_62_350, _62_352) -> begin
((FStar_List.rev more_args), t)
end
| _62_356 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 245 "FStar.Extraction.ML.ExtractExp.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_62_361, args), Some (FStar_Absyn_Syntax.Record_ctor (_62_366, fields))) -> begin
(
# 248 "FStar.Extraction.ML.ExtractExp.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 249 "FStar.Extraction.ML.ExtractExp.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _62_375 -> begin
e
end))
in (
# 253 "FStar.Extraction.ML.ExtractExp.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 254 "FStar.Extraction.ML.ExtractExp.fst"
let _62_381 = (eta_args [] residualType)
in (match (_62_381) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _143_170 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _143_170))
end
| _62_384 -> begin
(
# 258 "FStar.Extraction.ML.ExtractExp.fst"
let _62_387 = (FStar_List.unzip eargs)
in (match (_62_387) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 261 "FStar.Extraction.ML.ExtractExp.fst"
let body = (let _143_172 = (let _143_171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _143_171))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _143_172))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _62_394 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _62_398; FStar_Extraction_ML_Syntax.loc = _62_396}, mlarg::[]), _62_407) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(
# 267 "FStar.Extraction.ML.ExtractExp.fst"
let _62_410 = (FStar_Extraction_ML_Env.debug g (fun _62_409 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_62_413, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _62_419; FStar_Extraction_ML_Syntax.loc = _62_417}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(
# 273 "FStar.Extraction.ML.ExtractExp.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 274 "FStar.Extraction.ML.ExtractExp.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 275 "FStar.Extraction.ML.ExtractExp.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _62_436 -> begin
(let _143_175 = (let _143_174 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_143_174, args))
in FStar_Extraction_ML_Syntax.MLE_App (_143_175))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.ty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _143_176 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _143_176))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _143_177 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _143_177))
end
| _62_476 -> begin
mlAppExpr
end)))))

# 291 "FStar.Extraction.ML.ExtractExp.fst"
let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (
# 292 "FStar.Extraction.ML.ExtractExp.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 295 "FStar.Extraction.ML.ExtractExp.fst"
let _62_482 = (FStar_List.hd l)
in (match (_62_482) with
| (p1, w1, e1) -> begin
(
# 296 "FStar.Extraction.ML.ExtractExp.fst"
let _62_486 = (let _143_180 = (FStar_List.tl l)
in (FStar_List.hd _143_180))
in (match (_62_486) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _62_506 -> begin
def
end)
end))
end))
end))

# 303 "FStar.Extraction.ML.ExtractExp.fst"
let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (
# 305 "FStar.Extraction.ML.ExtractExp.fst"
let _62_516 = (let _143_197 = (check_exp' g e f t)
in (erase g _143_197 f t))
in (match (_62_516) with
| (e, _62_513, _62_515) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (
# 309 "FStar.Extraction.ML.ExtractExp.fst"
let _62_524 = (synth_exp g e)
in (match (_62_524) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (
# 315 "FStar.Extraction.ML.ExtractExp.fst"
let _62_530 = (synth_exp' g e)
in (match (_62_530) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (
# 322 "FStar.Extraction.ML.ExtractExp.fst"
let _62_534 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _143_209 = (let _143_208 = (FStar_Absyn_Print.tag_of_exp e)
in (let _143_207 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _143_208 _143_207)))
in (FStar_Util.print_string _143_209))))
in (match ((let _143_210 = (FStar_Absyn_Util.compress_exp e)
in _143_210.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(
# 326 "FStar.Extraction.ML.ExtractExp.fst"
let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (
# 327 "FStar.Extraction.ML.ExtractExp.fst"
let ml_ty = (translate_typ g t)
in (let _143_214 = (let _143_213 = (let _143_212 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _143_211 -> FStar_Extraction_ML_Syntax.MLE_Const (_143_211)) _143_212))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _143_213))
in (_143_214, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e0, t, f) -> begin
(
# 331 "FStar.Extraction.ML.ExtractExp.fst"
let t = (translate_typ g t)
in (
# 332 "FStar.Extraction.ML.ExtractExp.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (
# 335 "FStar.Extraction.ML.ExtractExp.fst"
let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(
# 340 "FStar.Extraction.ML.ExtractExp.fst"
let _62_563 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_62_563) with
| ((x, mltys, _62_560), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _143_215 = (maybe_lalloc_eta_data g qual t x)
in (_143_215, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _62_568 -> begin
(err_uninst g e mltys)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 348 "FStar.Extraction.ML.ExtractExp.fst"
let rec synth_app = (fun is_data _62_577 _62_580 restArgs -> (match ((_62_577, _62_580)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _62_584) -> begin
(
# 356 "FStar.Extraction.ML.ExtractExp.fst"
let _62_595 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _143_224 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _143_224))
end else begin
(FStar_List.fold_left (fun _62_588 _62_591 -> (match ((_62_588, _62_591)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 362 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _143_227 = (FStar_Absyn_Util.gensym ())
in (_143_227, (- (1))))
in (let _143_229 = (let _143_228 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_143_228)::out_args)
in (((x, arg))::lbs, _143_229)))
end
end)) ([], []) mlargs_f)
end
in (match (_62_595) with
| (lbs, mlargs) -> begin
(
# 365 "FStar.Extraction.ML.ExtractExp.fst"
let app = (let _143_230 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _143_230))
in (
# 366 "FStar.Extraction.ML.ExtractExp.fst"
let l_app = (FStar_List.fold_right (fun _62_599 out -> (match (_62_599) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.ty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.ty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_62_604), _62_607)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (FStar_Extraction_ML_Util.type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _143_234 = (let _143_233 = (FStar_Extraction_ML_Util.join f f')
in (_143_233, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _143_234 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _62_620)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 380 "FStar.Extraction.ML.ExtractExp.fst"
let _62_632 = (synth_exp g e0)
in (match (_62_632) with
| (e0, f0, tInferred) -> begin
(
# 381 "FStar.Extraction.ML.ExtractExp.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _143_236 = (let _143_235 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_143_235, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _143_236 rest)))
end))
end
| _62_635 -> begin
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
# 390 "FStar.Extraction.ML.ExtractExp.fst"
let synth_app_maybe_projector = (fun is_data mlhead _62_644 args -> (match (_62_644) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Absyn_Syntax.Record_projector (_62_647)) -> begin
(
# 393 "FStar.Extraction.ML.ExtractExp.fst"
let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((FStar_Util.Inr (_62_656), Some (FStar_Absyn_Syntax.Implicit (_62_659)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_62_665, f', t)) -> begin
(let _143_251 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _143_251 t))
end
| _62_672 -> begin
(args, f, t)
end))
in (
# 398 "FStar.Extraction.ML.ExtractExp.fst"
let _62_676 = (remove_implicits args f t)
in (match (_62_676) with
| (args, f, t) -> begin
(synth_app is_data (mlhead, []) (f, t) args)
end)))
end
| _62_678 -> begin
(synth_app is_data (mlhead, []) (f, t) args)
end)
end))
in (
# 403 "FStar.Extraction.ML.ExtractExp.fst"
let head = (FStar_Absyn_Util.compress_exp head)
in (match (head.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(
# 408 "FStar.Extraction.ML.ExtractExp.fst"
let _62_693 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_62_693) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 409 "FStar.Extraction.ML.ExtractExp.fst"
let has_typ_apps = (match (args) with
| (FStar_Util.Inl (_62_697), _62_700)::_62_695 -> begin
true
end
| _62_704 -> begin
false
end)
in (
# 413 "FStar.Extraction.ML.ExtractExp.fst"
let _62_746 = (match (vars) with
| _62_709::_62_707 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _62_712 -> begin
(
# 420 "FStar.Extraction.ML.ExtractExp.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 422 "FStar.Extraction.ML.ExtractExp.fst"
let _62_716 = (FStar_Util.first_N n args)
in (match (_62_716) with
| (prefix, rest) -> begin
(
# 424 "FStar.Extraction.ML.ExtractExp.fst"
let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (
# 426 "FStar.Extraction.ML.ExtractExp.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 427 "FStar.Extraction.ML.ExtractExp.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 429 "FStar.Extraction.ML.ExtractExp.fst"
let _62_725 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _62_725.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = t; FStar_Extraction_ML_Syntax.loc = _62_725.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.ty = _62_731; FStar_Extraction_ML_Syntax.loc = _62_729}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 430 "FStar.Extraction.ML.ExtractExp.fst"
let _62_738 = head
in {FStar_Extraction_ML_Syntax.expr = _62_738.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.ty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _62_738.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _62_741 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_62_746) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _143_252 = (maybe_lalloc_eta_data g qual head_t head_ml)
in (_143_252, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _62_749 -> begin
(synth_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _62_751 -> begin
(
# 441 "FStar.Extraction.ML.ExtractExp.fst"
let _62_755 = (synth_exp g head)
in (match (_62_755) with
| (head, f, t) -> begin
(synth_app_maybe_projector None head (f, t) args)
end))
end))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 446 "FStar.Extraction.ML.ExtractExp.fst"
let _62_778 = (FStar_List.fold_left (fun _62_762 _62_766 -> (match ((_62_762, _62_766)) with
| ((ml_bs, env), (b, _62_765)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(
# 448 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 449 "FStar.Extraction.ML.ExtractExp.fst"
let ml_b = (let _143_255 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_143_255, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(
# 453 "FStar.Extraction.ML.ExtractExp.fst"
let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (
# 454 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false false)
in (
# 455 "FStar.Extraction.ML.ExtractExp.fst"
let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_62_778) with
| (ml_bs, env) -> begin
(
# 457 "FStar.Extraction.ML.ExtractExp.fst"
let ml_bs = (FStar_List.rev ml_bs)
in (
# 458 "FStar.Extraction.ML.ExtractExp.fst"
let _62_783 = (synth_exp env body)
in (match (_62_783) with
| (ml_body, f, t) -> begin
(
# 460 "FStar.Extraction.ML.ExtractExp.fst"
let _62_793 = (FStar_List.fold_right (fun _62_787 _62_790 -> (match ((_62_787, _62_790)) with
| ((_62_785, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_62_793) with
| (f, tfun) -> begin
(let _143_258 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_143_258, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(
# 468 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_generalize = (fun _62_805 -> (match (_62_805) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(
# 469 "FStar.Extraction.ML.ExtractExp.fst"
let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (
# 470 "FStar.Extraction.ML.ExtractExp.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(
# 477 "FStar.Extraction.ML.ExtractExp.fst"
let _62_829 = (match ((FStar_Util.prefix_until (fun _62_4 -> (match (_62_4) with
| (FStar_Util.Inr (_62_814), _62_817) -> begin
true
end
| _62_820 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _143_262 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _143_262))
end)
in (match (_62_829) with
| (tbinders, tbody) -> begin
(
# 482 "FStar.Extraction.ML.ExtractExp.fst"
let n = (FStar_List.length tbinders)
in (
# 483 "FStar.Extraction.ML.ExtractExp.fst"
let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(
# 487 "FStar.Extraction.ML.ExtractExp.fst"
let _62_838 = (FStar_Util.first_N n bs)
in (match (_62_838) with
| (targs, rest_args) -> begin
(
# 491 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (
# 495 "FStar.Extraction.ML.ExtractExp.fst"
let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _62_5 -> (match (_62_5) with
| (FStar_Util.Inl (a), _62_847) -> begin
a
end
| _62_850 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 496 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (
# 497 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (translate_typ env expected_t)
in (
# 498 "FStar.Extraction.ML.ExtractExp.fst"
let polytype = (let _143_266 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_143_266, expected_t))
in (
# 499 "FStar.Extraction.ML.ExtractExp.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _62_859 -> begin
false
end)
in (
# 502 "FStar.Extraction.ML.ExtractExp.fst"
let rest_args = if add_unit then begin
(FStar_Extraction_ML_Util.unit_binder)::rest_args
end else begin
rest_args
end
in (
# 503 "FStar.Extraction.ML.ExtractExp.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _62_864 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _62_867 -> begin
(err_value_restriction e)
end)))
end))
end
| _62_869 -> begin
(
# 532 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 535 "FStar.Extraction.ML.ExtractExp.fst"
let check_lb = (fun env _62_884 -> (match (_62_884) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 536 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
in (
# 537 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 538 "FStar.Extraction.ML.ExtractExp.fst"
let e = (check_exp env e f expected_t)
in (f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true}))))
end))
in (
# 542 "FStar.Extraction.ML.ExtractExp.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 544 "FStar.Extraction.ML.ExtractExp.fst"
let _62_913 = (FStar_List.fold_right (fun lb _62_894 -> (match (_62_894) with
| (env, lbs) -> begin
(
# 545 "FStar.Extraction.ML.ExtractExp.fst"
let _62_907 = lb
in (match (_62_907) with
| (lbname, _62_897, (t, (_62_900, polytype)), add_unit, _62_906) -> begin
(
# 546 "FStar.Extraction.ML.ExtractExp.fst"
let _62_910 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_62_910) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_62_913) with
| (env_body, lbs) -> begin
(
# 549 "FStar.Extraction.ML.ExtractExp.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 551 "FStar.Extraction.ML.ExtractExp.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 553 "FStar.Extraction.ML.ExtractExp.fst"
let _62_919 = (synth_exp env_body e')
in (match (_62_919) with
| (e', f', t') -> begin
(
# 555 "FStar.Extraction.ML.ExtractExp.fst"
let f = (let _143_276 = (let _143_275 = (FStar_List.map Prims.fst lbs)
in (f')::_143_275)
in (FStar_Extraction_ML_Util.join_l _143_276))
in (let _143_282 = (let _143_281 = (let _143_279 = (let _143_278 = (let _143_277 = (FStar_List.map Prims.snd lbs)
in (is_rec, _143_277))
in (_143_278, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_143_279))
in (let _143_280 = (FStar_Extraction_ML_ExtractTyp.mlloc_of_range e.FStar_Absyn_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _143_281 _143_280)))
in (_143_282, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(
# 560 "FStar.Extraction.ML.ExtractExp.fst"
let _62_928 = (synth_exp g scrutinee)
in (match (_62_928) with
| (e, f_e, t_e) -> begin
(
# 561 "FStar.Extraction.ML.ExtractExp.fst"
let _62_932 = (check_pats_for_ite pats)
in (match (_62_932) with
| (b, then_e, else_e) -> begin
(
# 562 "FStar.Extraction.ML.ExtractExp.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 566 "FStar.Extraction.ML.ExtractExp.fst"
let _62_944 = (synth_exp g then_e)
in (match (_62_944) with
| (then_mle, f_then, t_then) -> begin
(
# 567 "FStar.Extraction.ML.ExtractExp.fst"
let _62_948 = (synth_exp g else_e)
in (match (_62_948) with
| (else_mle, f_else, t_else) -> begin
(
# 568 "FStar.Extraction.ML.ExtractExp.fst"
let _62_951 = if (FStar_Extraction_ML_Util.type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (FStar_Extraction_ML_Util.type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_62_951) with
| (t_branch, maybe_lift) -> begin
(let _143_313 = (let _143_311 = (let _143_310 = (let _143_309 = (maybe_lift then_mle t_then)
in (let _143_308 = (let _143_307 = (maybe_lift else_mle t_else)
in Some (_143_307))
in (e, _143_309, _143_308)))
in FStar_Extraction_ML_Syntax.MLE_If (_143_310))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _143_311))
in (let _143_312 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_143_313, _143_312, t_branch)))
end))
end))
end))
end
| _62_953 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 579 "FStar.Extraction.ML.ExtractExp.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _62_957 -> (match (_62_957) with
| (pat, when_opt, branch) -> begin
(
# 580 "FStar.Extraction.ML.ExtractExp.fst"
let _62_960 = (extract_pat g pat)
in (match (_62_960) with
| (env, p) -> begin
(
# 581 "FStar.Extraction.ML.ExtractExp.fst"
let _62_971 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 584 "FStar.Extraction.ML.ExtractExp.fst"
let _62_967 = (synth_exp env w)
in (match (_62_967) with
| (w, f_w, t_w) -> begin
(
# 585 "FStar.Extraction.ML.ExtractExp.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_62_971) with
| (when_opt, f_when) -> begin
(
# 587 "FStar.Extraction.ML.ExtractExp.fst"
let _62_975 = (synth_exp env branch)
in (match (_62_975) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _62_978 -> (match (_62_978) with
| (p, wopt) -> begin
(
# 590 "FStar.Extraction.ML.ExtractExp.fst"
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
# 595 "FStar.Extraction.ML.ExtractExp.fst"
let _62_987 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_62_987) with
| (fw, _62_984, _62_986) -> begin
(let _143_320 = (let _143_319 = (let _143_318 = (let _143_317 = (let _143_316 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_143_316)::[])
in (fw, _143_317))
in FStar_Extraction_ML_Syntax.MLE_App (_143_318))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _143_319))
in (_143_320, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_62_990, _62_992, (_62_994, f_first, t_first))::rest -> begin
(
# 602 "FStar.Extraction.ML.ExtractExp.fst"
let _62_1020 = (FStar_List.fold_left (fun _62_1002 _62_1012 -> (match ((_62_1002, _62_1012)) with
| ((topt, f), (_62_1004, _62_1006, (_62_1008, f_branch, t_branch))) -> begin
(
# 606 "FStar.Extraction.ML.ExtractExp.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 607 "FStar.Extraction.ML.ExtractExp.fst"
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
in (match (_62_1020) with
| (topt, f_match) -> begin
(
# 620 "FStar.Extraction.ML.ExtractExp.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _62_1031 -> (match (_62_1031) with
| (p, (wopt, _62_1024), (b, _62_1028, t)) -> begin
(
# 621 "FStar.Extraction.ML.ExtractExp.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_62_1034) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 627 "FStar.Extraction.ML.ExtractExp.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _143_324 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_143_324, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _62_1044)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end)))

# 641 "FStar.Extraction.ML.ExtractExp.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 641 "FStar.Extraction.ML.ExtractExp.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 642 "FStar.Extraction.ML.ExtractExp.fst"
let _62_1056 = (FStar_Util.incr c)
in (let _143_327 = (FStar_ST.read c)
in (x, _143_327)))))

# 644 "FStar.Extraction.ML.ExtractExp.fst"
let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 646 "FStar.Extraction.ML.ExtractExp.fst"
let fstar_disc_type = (FStar_Tc_Env.lookup_lid env.FStar_Extraction_ML_Env.tcenv discName)
in (
# 647 "FStar.Extraction.ML.ExtractExp.fst"
let wildcards = (match (fstar_disc_type.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _62_1064) -> begin
(let _143_337 = (FStar_All.pipe_right binders (FStar_List.filter (fun _62_6 -> (match (_62_6) with
| (_62_1069, Some (FStar_Absyn_Syntax.Implicit (_62_1071))) -> begin
true
end
| _62_1076 -> begin
false
end))))
in (FStar_All.pipe_right _143_337 (FStar_List.map (fun _62_1077 -> (let _143_336 = (fresh "_")
in (_143_336, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _62_1080 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 658 "FStar.Extraction.ML.ExtractExp.fst"
let mlid = (fresh "_discr_")
in (
# 659 "FStar.Extraction.ML.ExtractExp.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 662 "FStar.Extraction.ML.ExtractExp.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 663 "FStar.Extraction.ML.ExtractExp.fst"
let discrBody = (let _143_352 = (let _143_351 = (let _143_350 = (let _143_349 = (let _143_348 = (let _143_347 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _143_346 = (let _143_345 = (let _143_341 = (let _143_339 = (let _143_338 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_143_338, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_143_339))
in (let _143_340 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_143_341, None, _143_340)))
in (let _143_344 = (let _143_343 = (let _143_342 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _143_342))
in (_143_343)::[])
in (_143_345)::_143_344))
in (_143_347, _143_346)))
in FStar_Extraction_ML_Syntax.MLE_Match (_143_348))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _143_349))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _143_350))
in FStar_Extraction_ML_Syntax.MLE_Fun (_143_351))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _143_352))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = true})::[])))))))))




