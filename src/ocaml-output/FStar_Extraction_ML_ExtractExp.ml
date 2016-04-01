
open Prims
# 29 "FStar.Extraction.ML.ExtractExp.fst"
let type_leq : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.delta_unfold g) t1 t2))

# 30 "FStar.Extraction.ML.ExtractExp.fst"
let type_leq_c : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.delta_unfold g) t1 t2))

# 31 "FStar.Extraction.ML.ExtractExp.fst"
let erasableType : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.delta_unfold g) t))

# 32 "FStar.Extraction.ML.ExtractExp.fst"
let eraseTypeDeep : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold g) t))

# 34 "FStar.Extraction.ML.ExtractExp.fst"
let fail = (fun r msg -> (
# 35 "FStar.Extraction.ML.ExtractExp.fst"
let _75_19 = (let _164_27 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _164_27))
in (FStar_All.failwith msg)))

# 38 "FStar.Extraction.ML.ExtractExp.fst"
let err_uninst = (fun env e _75_25 -> (match (_75_25) with
| (vars, t) -> begin
(let _164_35 = (let _164_34 = (FStar_Absyn_Print.exp_to_string e)
in (let _164_33 = (let _164_31 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _164_31 (FStar_String.concat ", ")))
in (let _164_32 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_Env.currentModule t)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _164_34 _164_33 _164_32))))
in (fail e.FStar_Absyn_Syntax.pos _164_35))
end))

# 44 "FStar.Extraction.ML.ExtractExp.fst"
let err_ill_typed_application = (fun e args t -> (let _164_41 = (let _164_40 = (FStar_Absyn_Print.exp_to_string e)
in (let _164_39 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _164_40 _164_39)))
in (fail e.FStar_Absyn_Syntax.pos _164_41)))

# 51 "FStar.Extraction.ML.ExtractExp.fst"
let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

# 54 "FStar.Extraction.ML.ExtractExp.fst"
let err_unexpected_eff = (fun e f0 f1 -> (let _164_47 = (let _164_46 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _164_46 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _164_47)))

# 57 "FStar.Extraction.ML.ExtractExp.fst"
let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _164_50 = (FStar_Absyn_Util.compress_exp e)
in _164_50.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _75_49 -> begin
false
end))

# 63 "FStar.Extraction.ML.ExtractExp.fst"
let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _164_53 = (FStar_Absyn_Util.compress_exp e)
in _164_53.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _75_70 -> (match (_75_70) with
| (te, _75_69) -> begin
(match (te) with
| FStar_Util.Inl (_75_72) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _164_55 = (FStar_Absyn_Util.compress_exp head)
in _164_55.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _75_1 -> (match (_75_1) with
| (FStar_Util.Inl (te), _75_86) -> begin
true
end
| _75_89 -> begin
false
end))))
end
| _75_91 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _75_105 -> begin
false
end))

# 82 "FStar.Extraction.ML.ExtractExp.fst"
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_75_126, fields) -> begin
(FStar_Util.for_all (fun _75_133 -> (match (_75_133) with
| (_75_131, e) -> begin
(is_ml_value e)
end)) fields)
end
| _75_135 -> begin
false
end))

# 94 "FStar.Extraction.ML.ExtractExp.fst"
let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _164_64 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (eraseTypeDeep g _164_64)))

# 95 "FStar.Extraction.ML.ExtractExp.fst"
let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _164_69 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (eraseTypeDeep g _164_69)))

# 99 "FStar.Extraction.ML.ExtractExp.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 101 "FStar.Extraction.ML.ExtractExp.fst"
let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))

# 105 "FStar.Extraction.ML.ExtractExp.fst"
let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(
# 107 "FStar.Extraction.ML.ExtractExp.fst"
let _75_150 = (FStar_Extraction_ML_Env.debug g (fun _75_149 -> (match (()) with
| () -> begin
(let _164_90 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_Env.currentModule e)
in (let _164_89 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_Env.currentModule t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _164_90 _164_89)))
end)))
in (
# 108 "FStar.Extraction.ML.ExtractExp.fst"
let e_val = if (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, t))))
end
in (e_val, f, t)))
end else begin
(e, f, t)
end)

# 112 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_coerce : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e tInferred tExpected -> (match ((type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _75_162 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))))
end))

# 121 "FStar.Extraction.ML.ExtractExp.fst"
let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 123 "FStar.Extraction.ML.ExtractExp.fst"
let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_75_171) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 128 "FStar.Extraction.ML.ExtractExp.fst"
let i = FStar_Const.Const_int ((c, None))
in (
# 130 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _164_111 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _164_111))
in (
# 131 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (let _164_120 = (let _164_119 = (let _164_118 = (let _164_117 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _164_116 = (let _164_115 = (let _164_114 = (let _164_113 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p i)
in (FStar_All.pipe_left (fun _164_112 -> FStar_Extraction_ML_Syntax.MLE_Const (_164_112)) _164_113))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _164_114))
in (_164_115)::[])
in (_164_117)::_164_116))
in (FStar_Extraction_ML_Util.prims_op_equality, _164_118))
in FStar_Extraction_ML_Syntax.MLE_App (_164_119))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _164_120))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[]))))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _164_124 = (let _164_123 = (let _164_122 = (let _164_121 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_164_121))
in (_164_122, []))
in Some (_164_123))
in (g, _164_124))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(
# 140 "FStar.Extraction.ML.ExtractExp.fst"
let _75_203 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _75_191; FStar_Extraction_ML_Syntax.loc = _75_189}, ttys, _75_197) -> begin
(n, ttys)
end
| _75_200 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_75_203) with
| (d, tys) -> begin
(
# 143 "FStar.Extraction.ML.ExtractExp.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 144 "FStar.Extraction.ML.ExtractExp.fst"
let _75_207 = (FStar_Util.first_N nTyVars pats)
in (match (_75_207) with
| (tysVarPats, restPats) -> begin
(
# 145 "FStar.Extraction.ML.ExtractExp.fst"
let _75_214 = (FStar_Util.fold_map (fun g _75_211 -> (match (_75_211) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_75_214) with
| (g, tyMLPats) -> begin
(
# 146 "FStar.Extraction.ML.ExtractExp.fst"
let _75_228 = (FStar_Util.fold_map (fun g _75_218 -> (match (_75_218) with
| (p, imp) -> begin
(
# 147 "FStar.Extraction.ML.ExtractExp.fst"
let _75_221 = (extract_one_pat disj false g p)
in (match (_75_221) with
| (env, popt) -> begin
(
# 148 "FStar.Extraction.ML.ExtractExp.fst"
let popt = (match (popt) with
| None -> begin
Some ((FStar_Extraction_ML_Syntax.MLP_Wild, []))
end
| _75_224 -> begin
popt
end)
in (env, popt))
end))
end)) g restPats)
in (match (_75_228) with
| (g, restMLPats) -> begin
(
# 152 "FStar.Extraction.ML.ExtractExp.fst"
let _75_236 = (let _164_130 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _75_2 -> (match (_75_2) with
| Some (x) -> begin
(x)::[]
end
| _75_233 -> begin
[]
end))))
in (FStar_All.pipe_right _164_130 FStar_List.split))
in (match (_75_236) with
| (mlPats, when_clauses) -> begin
(let _164_134 = (let _164_133 = (let _164_132 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _164_131 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_164_132, _164_131)))
in Some (_164_133))
in (g, _164_134))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(
# 156 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (
# 157 "FStar.Extraction.ML.ExtractExp.fst"
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
# 164 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (
# 165 "FStar.Extraction.ML.ExtractExp.fst"
let g = (FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), []))
end)))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(
# 169 "FStar.Extraction.ML.ExtractExp.fst"
let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 170 "FStar.Extraction.ML.ExtractExp.fst"
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
# 178 "FStar.Extraction.ML.ExtractExp.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _75_271 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 183 "FStar.Extraction.ML.ExtractExp.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _164_143 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_164_143))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(
# 192 "FStar.Extraction.ML.ExtractExp.fst"
let _75_286 = (extract_one_pat true g p)
in (match (_75_286) with
| (g, p) -> begin
(
# 193 "FStar.Extraction.ML.ExtractExp.fst"
let ps = (let _164_146 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _164_145 = (extract_one_pat true g x)
in (Prims.snd _164_145)))))
in (p)::_164_146)
in (
# 194 "FStar.Extraction.ML.ExtractExp.fst"
let _75_302 = (FStar_All.pipe_right ps (FStar_List.partition (fun _75_3 -> (match (_75_3) with
| (_75_291, _75_295::_75_293) -> begin
true
end
| _75_299 -> begin
false
end))))
in (match (_75_302) with
| (ps_when, rest) -> begin
(
# 195 "FStar.Extraction.ML.ExtractExp.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _75_305 -> (match (_75_305) with
| (x, whens) -> begin
(let _164_149 = (mk_when_clause whens)
in (x, _164_149))
end))))
in (
# 197 "FStar.Extraction.ML.ExtractExp.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _164_153 = (let _164_152 = (let _164_151 = (let _164_150 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_164_150))
in (_164_151, None))
in (_164_152)::ps)
in (g, _164_153))
end)
in res))
end)))
end))
end
| _75_311 -> begin
(
# 203 "FStar.Extraction.ML.ExtractExp.fst"
let _75_316 = (extract_one_pat false g p)
in (match (_75_316) with
| (g, (p, whens)) -> begin
(
# 204 "FStar.Extraction.ML.ExtractExp.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 207 "FStar.Extraction.ML.ExtractExp.fst"
let normalize_abs : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun e0 -> (
# 208 "FStar.Extraction.ML.ExtractExp.fst"
let rec aux = (fun bs e -> (
# 209 "FStar.Extraction.ML.ExtractExp.fst"
let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _75_328 -> begin
(
# 213 "FStar.Extraction.ML.ExtractExp.fst"
let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))

# 219 "FStar.Extraction.ML.ExtractExp.fst"
let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (
# 220 "FStar.Extraction.ML.ExtractExp.fst"
let name = if ((2 < n) && (n < 6)) then begin
(let _164_162 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _164_162))
end else begin
if (n = 2) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in (("Camlstack")::[], name)))

# 224 "FStar.Extraction.ML.ExtractExp.fst"
let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(
# 228 "FStar.Extraction.ML.ExtractExp.fst"
let args = (FStar_List.map Prims.snd fields)
in (
# 229 "FStar.Extraction.ML.ExtractExp.fst"
let tup = (let _164_169 = (let _164_168 = (let _164_167 = (let _164_166 = (let _164_165 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_164_165))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _164_166))
in (_164_167, args))
in FStar_Extraction_ML_Syntax.MLE_App (_164_168))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _164_169))
in (
# 230 "FStar.Extraction.ML.ExtractExp.fst"
let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _75_347 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

# 244 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 245 "FStar.Extraction.ML.ExtractExp.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _75_357, t1) -> begin
(
# 247 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _164_182 = (FStar_Absyn_Util.gensym ())
in (_164_182, (- (1))))
in (let _164_185 = (let _164_184 = (let _164_183 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _164_183))
in (_164_184)::more_args)
in (eta_args _164_185 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_75_363, _75_365) -> begin
((FStar_List.rev more_args), t)
end
| _75_369 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 252 "FStar.Extraction.ML.ExtractExp.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_75_374, args), Some (FStar_Absyn_Syntax.Record_ctor (_75_379, fields))) -> begin
(
# 255 "FStar.Extraction.ML.ExtractExp.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 256 "FStar.Extraction.ML.ExtractExp.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _75_388 -> begin
e
end))
in (
# 260 "FStar.Extraction.ML.ExtractExp.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 261 "FStar.Extraction.ML.ExtractExp.fst"
let _75_394 = (eta_args [] residualType)
in (match (_75_394) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _164_194 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _164_194))
end
| _75_397 -> begin
(
# 265 "FStar.Extraction.ML.ExtractExp.fst"
let _75_400 = (FStar_List.unzip eargs)
in (match (_75_400) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 268 "FStar.Extraction.ML.ExtractExp.fst"
let body = (let _164_196 = (let _164_195 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _164_195))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _164_196))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _75_407 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _75_411; FStar_Extraction_ML_Syntax.loc = _75_409}, mlarg::[]), _75_420) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(
# 274 "FStar.Extraction.ML.ExtractExp.fst"
let _75_423 = (FStar_Extraction_ML_Env.debug g (fun _75_422 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_75_426, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _75_432; FStar_Extraction_ML_Syntax.loc = _75_430}, mle::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(
# 280 "FStar.Extraction.ML.ExtractExp.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 281 "FStar.Extraction.ML.ExtractExp.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 282 "FStar.Extraction.ML.ExtractExp.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _75_449 -> begin
(let _164_199 = (let _164_198 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_164_198, args))
in FStar_Extraction_ML_Syntax.MLE_App (_164_199))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _164_200 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _164_200))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _164_201 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _164_201))
end
| _75_489 -> begin
mlAppExpr
end)))))

# 298 "FStar.Extraction.ML.ExtractExp.fst"
let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (
# 299 "FStar.Extraction.ML.ExtractExp.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 302 "FStar.Extraction.ML.ExtractExp.fst"
let _75_495 = (FStar_List.hd l)
in (match (_75_495) with
| (p1, w1, e1) -> begin
(
# 303 "FStar.Extraction.ML.ExtractExp.fst"
let _75_499 = (let _164_204 = (FStar_List.tl l)
in (FStar_List.hd _164_204))
in (match (_75_499) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Absyn_Syntax.v, p2.FStar_Absyn_Syntax.v)) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _75_519 -> begin
def
end)
end))
end))
end))

# 310 "FStar.Extraction.ML.ExtractExp.fst"
let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (
# 312 "FStar.Extraction.ML.ExtractExp.fst"
let _75_529 = (let _164_221 = (check_exp' g e f t)
in (erase g _164_221 f t))
in (match (_75_529) with
| (e, _75_526, _75_528) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (
# 316 "FStar.Extraction.ML.ExtractExp.fst"
let _75_537 = (synth_exp g e)
in (match (_75_537) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (
# 322 "FStar.Extraction.ML.ExtractExp.fst"
let _75_543 = (synth_exp' g e)
in (match (_75_543) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (
# 329 "FStar.Extraction.ML.ExtractExp.fst"
let _75_547 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _164_233 = (let _164_232 = (FStar_Absyn_Print.tag_of_exp e)
in (let _164_231 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _164_232 _164_231)))
in (FStar_Util.print_string _164_233))))
in (match ((let _164_234 = (FStar_Absyn_Util.compress_exp e)
in _164_234.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(
# 333 "FStar.Extraction.ML.ExtractExp.fst"
let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (
# 334 "FStar.Extraction.ML.ExtractExp.fst"
let ml_ty = (translate_typ g t)
in (let _164_238 = (let _164_237 = (let _164_236 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _164_235 -> FStar_Extraction_ML_Syntax.MLE_Const (_164_235)) _164_236))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _164_237))
in (_164_238, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e0, t, f) -> begin
(
# 338 "FStar.Extraction.ML.ExtractExp.fst"
let t = (translate_typ g t)
in (
# 339 "FStar.Extraction.ML.ExtractExp.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (
# 342 "FStar.Extraction.ML.ExtractExp.fst"
let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(
# 347 "FStar.Extraction.ML.ExtractExp.fst"
let _75_576 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_75_576) with
| ((x, mltys, _75_573), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _164_239 = (maybe_lalloc_eta_data g qual t x)
in (_164_239, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _75_581 -> begin
(err_uninst g e mltys)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 355 "FStar.Extraction.ML.ExtractExp.fst"
let rec synth_app = (fun is_data _75_590 _75_593 restArgs -> (match ((_75_590, _75_593)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _75_597) -> begin
(
# 363 "FStar.Extraction.ML.ExtractExp.fst"
let _75_608 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _164_248 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _164_248))
end else begin
(FStar_List.fold_left (fun _75_601 _75_604 -> (match ((_75_601, _75_604)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 369 "FStar.Extraction.ML.ExtractExp.fst"
let x = (let _164_251 = (FStar_Absyn_Util.gensym ())
in (_164_251, (- (1))))
in (let _164_253 = (let _164_252 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_164_252)::out_args)
in (((x, arg))::lbs, _164_253)))
end
end)) ([], []) mlargs_f)
end
in (match (_75_608) with
| (lbs, mlargs) -> begin
(
# 372 "FStar.Extraction.ML.ExtractExp.fst"
let app = (let _164_254 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _164_254))
in (
# 373 "FStar.Extraction.ML.ExtractExp.fst"
let l_app = (FStar_List.fold_right (fun _75_612 out -> (match (_75_612) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((FStar_Util.Inl (_75_617), _75_620)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _164_258 = (let _164_257 = (FStar_Extraction_ML_Util.join f f')
in (_164_257, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _164_258 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((FStar_Util.Inr (e0), _75_633)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 387 "FStar.Extraction.ML.ExtractExp.fst"
let _75_645 = (synth_exp g e0)
in (match (_75_645) with
| (e0, f0, tInferred) -> begin
(
# 388 "FStar.Extraction.ML.ExtractExp.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _164_260 = (let _164_259 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_164_259, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _164_260 rest)))
end))
end
| _75_648 -> begin
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
# 397 "FStar.Extraction.ML.ExtractExp.fst"
let synth_app_maybe_projector = (fun is_data mlhead _75_657 args -> (match (_75_657) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Absyn_Syntax.Record_projector (_75_660)) -> begin
(
# 400 "FStar.Extraction.ML.ExtractExp.fst"
let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((FStar_Util.Inr (_75_669), Some (FStar_Absyn_Syntax.Implicit (_75_672)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_75_678, f', t)) -> begin
(let _164_275 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _164_275 t))
end
| _75_685 -> begin
(args, f, t)
end))
in (
# 405 "FStar.Extraction.ML.ExtractExp.fst"
let _75_689 = (remove_implicits args f t)
in (match (_75_689) with
| (args, f, t) -> begin
(synth_app is_data (mlhead, []) (f, t) args)
end)))
end
| _75_691 -> begin
(synth_app is_data (mlhead, []) (f, t) args)
end)
end))
in (
# 410 "FStar.Extraction.ML.ExtractExp.fst"
let head = (FStar_Absyn_Util.compress_exp head)
in (match (head.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(
# 415 "FStar.Extraction.ML.ExtractExp.fst"
let _75_706 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_75_706) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 416 "FStar.Extraction.ML.ExtractExp.fst"
let has_typ_apps = (match (args) with
| (FStar_Util.Inl (_75_710), _75_713)::_75_708 -> begin
true
end
| _75_717 -> begin
false
end)
in (
# 420 "FStar.Extraction.ML.ExtractExp.fst"
let _75_759 = (match (vars) with
| _75_722::_75_720 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _75_725 -> begin
(
# 427 "FStar.Extraction.ML.ExtractExp.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 429 "FStar.Extraction.ML.ExtractExp.fst"
let _75_729 = (FStar_Util.first_N n args)
in (match (_75_729) with
| (prefix, rest) -> begin
(
# 431 "FStar.Extraction.ML.ExtractExp.fst"
let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (
# 433 "FStar.Extraction.ML.ExtractExp.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 434 "FStar.Extraction.ML.ExtractExp.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 436 "FStar.Extraction.ML.ExtractExp.fst"
let _75_738 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _75_738.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _75_738.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _75_744; FStar_Extraction_ML_Syntax.loc = _75_742}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 437 "FStar.Extraction.ML.ExtractExp.fst"
let _75_751 = head
in {FStar_Extraction_ML_Syntax.expr = _75_751.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _75_751.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _75_754 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_75_759) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _164_276 = (maybe_lalloc_eta_data g qual head_t head_ml)
in (_164_276, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _75_762 -> begin
(synth_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _75_764 -> begin
(
# 448 "FStar.Extraction.ML.ExtractExp.fst"
let _75_768 = (synth_exp g head)
in (match (_75_768) with
| (head, f, t) -> begin
(synth_app_maybe_projector None head (f, t) args)
end))
end))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 453 "FStar.Extraction.ML.ExtractExp.fst"
let _75_791 = (FStar_List.fold_left (fun _75_775 _75_779 -> (match ((_75_775, _75_779)) with
| ((ml_bs, env), (b, _75_778)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(
# 455 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 456 "FStar.Extraction.ML.ExtractExp.fst"
let ml_b = (let _164_279 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (_164_279, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| FStar_Util.Inr (x) -> begin
(
# 460 "FStar.Extraction.ML.ExtractExp.fst"
let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (
# 461 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_Extraction_ML_Env.extend_bv env x ([], t) false false false)
in (
# 462 "FStar.Extraction.ML.ExtractExp.fst"
let ml_b = ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v), t)
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_75_791) with
| (ml_bs, env) -> begin
(
# 464 "FStar.Extraction.ML.ExtractExp.fst"
let ml_bs = (FStar_List.rev ml_bs)
in (
# 465 "FStar.Extraction.ML.ExtractExp.fst"
let _75_796 = (synth_exp env body)
in (match (_75_796) with
| (ml_body, f, t) -> begin
(
# 467 "FStar.Extraction.ML.ExtractExp.fst"
let _75_806 = (FStar_List.fold_right (fun _75_800 _75_803 -> (match ((_75_800, _75_803)) with
| ((_75_798, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_75_806) with
| (f, tfun) -> begin
(let _164_282 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_164_282, f, tfun))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(
# 475 "FStar.Extraction.ML.ExtractExp.fst"
let maybe_generalize = (fun _75_818 -> (match (_75_818) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(
# 476 "FStar.Extraction.ML.ExtractExp.fst"
let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (
# 477 "FStar.Extraction.ML.ExtractExp.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(
# 484 "FStar.Extraction.ML.ExtractExp.fst"
let _75_842 = (match ((FStar_Util.prefix_until (fun _75_4 -> (match (_75_4) with
| (FStar_Util.Inr (_75_827), _75_830) -> begin
true
end
| _75_833 -> begin
false
end)) bs)) with
| None -> begin
(bs, (FStar_Absyn_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _164_286 = (FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.FStar_Absyn_Syntax.pos)
in (bs, _164_286))
end)
in (match (_75_842) with
| (tbinders, tbody) -> begin
(
# 489 "FStar.Extraction.ML.ExtractExp.fst"
let n = (FStar_List.length tbinders)
in (
# 490 "FStar.Extraction.ML.ExtractExp.fst"
let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(
# 494 "FStar.Extraction.ML.ExtractExp.fst"
let _75_851 = (FStar_Util.first_N n bs)
in (match (_75_851) with
| (targs, rest_args) -> begin
(
# 498 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (
# 502 "FStar.Extraction.ML.ExtractExp.fst"
let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _75_5 -> (match (_75_5) with
| (FStar_Util.Inl (a), _75_860) -> begin
a
end
| _75_863 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 503 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (
# 504 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (translate_typ env expected_t)
in (
# 505 "FStar.Extraction.ML.ExtractExp.fst"
let polytype = (let _164_290 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_164_290, expected_t))
in (
# 506 "FStar.Extraction.ML.ExtractExp.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _75_872 -> begin
false
end)
in (
# 509 "FStar.Extraction.ML.ExtractExp.fst"
let rest_args = if add_unit then begin
(FStar_Extraction_ML_Util.unit_binder)::rest_args
end else begin
rest_args
end
in (
# 510 "FStar.Extraction.ML.ExtractExp.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _75_877 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _75_880 -> begin
(err_value_restriction e)
end)))
end))
end
| _75_882 -> begin
(
# 539 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 542 "FStar.Extraction.ML.ExtractExp.fst"
let check_lb = (fun env _75_897 -> (match (_75_897) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 543 "FStar.Extraction.ML.ExtractExp.fst"
let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
in (
# 544 "FStar.Extraction.ML.ExtractExp.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 545 "FStar.Extraction.ML.ExtractExp.fst"
let e = (check_exp env e f expected_t)
in (f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true}))))
end))
in (
# 549 "FStar.Extraction.ML.ExtractExp.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 551 "FStar.Extraction.ML.ExtractExp.fst"
let _75_926 = (FStar_List.fold_right (fun lb _75_907 -> (match (_75_907) with
| (env, lbs) -> begin
(
# 552 "FStar.Extraction.ML.ExtractExp.fst"
let _75_920 = lb
in (match (_75_920) with
| (lbname, _75_910, (t, (_75_913, polytype)), add_unit, _75_919) -> begin
(
# 553 "FStar.Extraction.ML.ExtractExp.fst"
let _75_923 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_75_923) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_75_926) with
| (env_body, lbs) -> begin
(
# 556 "FStar.Extraction.ML.ExtractExp.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 558 "FStar.Extraction.ML.ExtractExp.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 560 "FStar.Extraction.ML.ExtractExp.fst"
let _75_932 = (synth_exp env_body e')
in (match (_75_932) with
| (e', f', t') -> begin
(
# 562 "FStar.Extraction.ML.ExtractExp.fst"
let f = (let _164_300 = (let _164_299 = (FStar_List.map Prims.fst lbs)
in (f')::_164_299)
in (FStar_Extraction_ML_Util.join_l _164_300))
in (let _164_306 = (let _164_305 = (let _164_303 = (let _164_302 = (let _164_301 = (FStar_List.map Prims.snd lbs)
in (is_rec, _164_301))
in (_164_302, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_164_303))
in (let _164_304 = (FStar_Extraction_ML_Util.mlloc_of_range e.FStar_Absyn_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _164_305 _164_304)))
in (_164_306, f, t')))
end))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(
# 567 "FStar.Extraction.ML.ExtractExp.fst"
let _75_941 = (synth_exp g scrutinee)
in (match (_75_941) with
| (e, f_e, t_e) -> begin
(
# 568 "FStar.Extraction.ML.ExtractExp.fst"
let _75_945 = (check_pats_for_ite pats)
in (match (_75_945) with
| (b, then_e, else_e) -> begin
(
# 569 "FStar.Extraction.ML.ExtractExp.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 573 "FStar.Extraction.ML.ExtractExp.fst"
let _75_957 = (synth_exp g then_e)
in (match (_75_957) with
| (then_mle, f_then, t_then) -> begin
(
# 574 "FStar.Extraction.ML.ExtractExp.fst"
let _75_961 = (synth_exp g else_e)
in (match (_75_961) with
| (else_mle, f_else, t_else) -> begin
(
# 575 "FStar.Extraction.ML.ExtractExp.fst"
let _75_964 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_75_964) with
| (t_branch, maybe_lift) -> begin
(let _164_337 = (let _164_335 = (let _164_334 = (let _164_333 = (maybe_lift then_mle t_then)
in (let _164_332 = (let _164_331 = (maybe_lift else_mle t_else)
in Some (_164_331))
in (e, _164_333, _164_332)))
in FStar_Extraction_ML_Syntax.MLE_If (_164_334))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _164_335))
in (let _164_336 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_164_337, _164_336, t_branch)))
end))
end))
end))
end
| _75_966 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 586 "FStar.Extraction.ML.ExtractExp.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _75_970 -> (match (_75_970) with
| (pat, when_opt, branch) -> begin
(
# 587 "FStar.Extraction.ML.ExtractExp.fst"
let _75_973 = (extract_pat g pat)
in (match (_75_973) with
| (env, p) -> begin
(
# 588 "FStar.Extraction.ML.ExtractExp.fst"
let _75_984 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 591 "FStar.Extraction.ML.ExtractExp.fst"
let _75_980 = (synth_exp env w)
in (match (_75_980) with
| (w, f_w, t_w) -> begin
(
# 592 "FStar.Extraction.ML.ExtractExp.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_75_984) with
| (when_opt, f_when) -> begin
(
# 594 "FStar.Extraction.ML.ExtractExp.fst"
let _75_988 = (synth_exp env branch)
in (match (_75_988) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _75_991 -> (match (_75_991) with
| (p, wopt) -> begin
(
# 597 "FStar.Extraction.ML.ExtractExp.fst"
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
# 602 "FStar.Extraction.ML.ExtractExp.fst"
let _75_1000 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_75_1000) with
| (fw, _75_997, _75_999) -> begin
(let _164_344 = (let _164_343 = (let _164_342 = (let _164_341 = (let _164_340 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_164_340)::[])
in (fw, _164_341))
in FStar_Extraction_ML_Syntax.MLE_App (_164_342))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _164_343))
in (_164_344, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_75_1003, _75_1005, (_75_1007, f_first, t_first))::rest -> begin
(
# 609 "FStar.Extraction.ML.ExtractExp.fst"
let _75_1033 = (FStar_List.fold_left (fun _75_1015 _75_1025 -> (match ((_75_1015, _75_1025)) with
| ((topt, f), (_75_1017, _75_1019, (_75_1021, f_branch, t_branch))) -> begin
(
# 613 "FStar.Extraction.ML.ExtractExp.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 614 "FStar.Extraction.ML.ExtractExp.fst"
let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
if (type_leq g t t_branch) then begin
Some (t_branch)
end else begin
if (type_leq g t_branch t) then begin
Some (t)
end else begin
None
end
end
end)
in (topt, f)))
end)) (Some (t_first), f_first) rest)
in (match (_75_1033) with
| (topt, f_match) -> begin
(
# 627 "FStar.Extraction.ML.ExtractExp.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _75_1044 -> (match (_75_1044) with
| (p, (wopt, _75_1037), (b, _75_1041, t)) -> begin
(
# 628 "FStar.Extraction.ML.ExtractExp.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_75_1047) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 634 "FStar.Extraction.ML.ExtractExp.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _164_348 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_164_348, f_match, t_match))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _75_1057)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end)))

# 648 "FStar.Extraction.ML.ExtractExp.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 648 "FStar.Extraction.ML.ExtractExp.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 649 "FStar.Extraction.ML.ExtractExp.fst"
let _75_1069 = (FStar_Util.incr c)
in (let _164_351 = (FStar_ST.read c)
in (x, _164_351)))))

# 651 "FStar.Extraction.ML.ExtractExp.fst"
let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 653 "FStar.Extraction.ML.ExtractExp.fst"
let fstar_disc_type = (FStar_Tc_Env.lookup_lid env.FStar_Extraction_ML_Env.tcenv discName)
in (
# 654 "FStar.Extraction.ML.ExtractExp.fst"
let wildcards = (match (fstar_disc_type.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _75_1077) -> begin
(let _164_361 = (FStar_All.pipe_right binders (FStar_List.filter (fun _75_6 -> (match (_75_6) with
| (_75_1082, Some (FStar_Absyn_Syntax.Implicit (_75_1084))) -> begin
true
end
| _75_1089 -> begin
false
end))))
in (FStar_All.pipe_right _164_361 (FStar_List.map (fun _75_1090 -> (let _164_360 = (fresh "_")
in (_164_360, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _75_1093 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 665 "FStar.Extraction.ML.ExtractExp.fst"
let mlid = (fresh "_discr_")
in (
# 666 "FStar.Extraction.ML.ExtractExp.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 669 "FStar.Extraction.ML.ExtractExp.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 670 "FStar.Extraction.ML.ExtractExp.fst"
let discrBody = (let _164_376 = (let _164_375 = (let _164_374 = (let _164_373 = (let _164_372 = (let _164_371 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _164_370 = (let _164_369 = (let _164_365 = (let _164_363 = (let _164_362 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_164_362, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_164_363))
in (let _164_364 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_164_365, None, _164_364)))
in (let _164_368 = (let _164_367 = (let _164_366 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _164_366))
in (_164_367)::[])
in (_164_369)::_164_368))
in (_164_371, _164_370)))
in FStar_Extraction_ML_Syntax.MLE_Match (_164_372))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _164_373))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _164_374))
in FStar_Extraction_ML_Syntax.MLE_Fun (_164_375))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _164_376))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = true})::[])))))))))




