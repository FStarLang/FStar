
open Prims

let type_leq : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_StratifiedExtraction_ML_Util.type_leq (FStar_StratifiedExtraction_ML_Util.delta_unfold g) t1 t2))


let type_leq_c : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_StratifiedExtraction_ML_Util.type_leq_c (FStar_StratifiedExtraction_ML_Util.delta_unfold g) t1 t2))


let erasableType : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_StratifiedExtraction_ML_Util.erasableType (FStar_StratifiedExtraction_ML_Util.delta_unfold g) t))


let eraseTypeDeep : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_StratifiedExtraction_ML_Util.eraseTypeDeep (FStar_StratifiedExtraction_ML_Util.delta_unfold g) t))


let fail = (fun r msg -> (

let _85_13 = (let _186_27 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _186_27))
in (failwith msg)))


let err_uninst = (fun env e _85_19 -> (match (_85_19) with
| (vars, t) -> begin
(let _186_35 = (let _186_34 = (FStar_Absyn_Print.exp_to_string e)
in (let _186_33 = (let _186_31 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _186_31 (FStar_String.concat ", ")))
in (let _186_32 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_StratifiedExtraction_ML_Env.currentModule t)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _186_34 _186_33 _186_32))))
in (fail e.FStar_Absyn_Syntax.pos _186_35))
end))


let err_ill_typed_application = (fun e args t -> (let _186_41 = (let _186_40 = (FStar_Absyn_Print.exp_to_string e)
in (let _186_39 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _186_40 _186_39)))
in (fail e.FStar_Absyn_Syntax.pos _186_41)))


let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))


let err_unexpected_eff = (fun e f0 f1 -> (let _186_47 = (let _186_46 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _186_46 (FStar_StratifiedExtraction_ML_Util.eff_to_string f0) (FStar_StratifiedExtraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _186_47)))


let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _186_50 = (FStar_Absyn_Util.compress_exp e)
in _186_50.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _85_43 -> begin
false
end))


let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _186_53 = (FStar_Absyn_Util.compress_exp e)
in _186_53.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _85_64 -> (match (_85_64) with
| (te, _85_63) -> begin
(match (te) with
| FStar_Util.Inl (_85_66) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _186_55 = (FStar_Absyn_Util.compress_exp head)
in _186_55.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu___555 -> (match (uu___555) with
| (FStar_Util.Inl (te), _85_80) -> begin
true
end
| _85_83 -> begin
false
end))))
end
| _85_85 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _85_99 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_85_120, fields) -> begin
(FStar_Util.for_all (fun _85_127 -> (match (_85_127) with
| (_85_125, e) -> begin
(is_ml_value e)
end)) fields)
end
| _85_129 -> begin
false
end))


let translate_typ : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _186_64 = (FStar_StratifiedExtraction_ML_ExtractTyp.extractTyp g t)
in (eraseTypeDeep g _186_64)))


let translate_typ_of_arg : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _186_69 = (FStar_StratifiedExtraction_ML_ExtractTyp.getTypeFromArg g a)
in (eraseTypeDeep g _186_69)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_StratifiedExtraction_ML_Util.subst s args))


let erasable : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(

let _85_144 = (FStar_StratifiedExtraction_ML_Env.debug g (fun _85_143 -> (match (()) with
| () -> begin
(let _186_90 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_StratifiedExtraction_ML_Env.currentModule e)
in (let _186_89 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_StratifiedExtraction_ML_Env.currentModule t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _186_90 _186_89)))
end)))
in (

let e_val = if (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t)))))
end
in ((e_val), (f), (t))))
end else begin
((e), (f), (t))
end)


let maybe_coerce : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e tInferred tExpected -> (match ((type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _85_156 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (tInferred), (tExpected)))))
end))


let extract_pat : FStar_StratifiedExtraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_StratifiedExtraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (

let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_85_165) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (let _186_111 = (FStar_Absyn_Util.new_bvd None)
in (FStar_StratifiedExtraction_ML_Env.as_mlident _186_111))
in (

let when_clause = (let _186_120 = (let _186_119 = (let _186_118 = (let _186_117 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _186_116 = (let _186_115 = (let _186_114 = (let _186_113 = (FStar_StratifiedExtraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p i)
in (FStar_All.pipe_left (fun _186_112 -> FStar_Extraction_ML_Syntax.MLE_Const (_186_112)) _186_113))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _186_114))
in (_186_115)::[])
in (_186_117)::_186_116))
in ((FStar_StratifiedExtraction_ML_Util.prims_op_equality), (_186_118)))
in FStar_Extraction_ML_Syntax.MLE_App (_186_119))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _186_120))
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[]))))))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _186_124 = (let _186_123 = (let _186_122 = (let _186_121 = (FStar_StratifiedExtraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_186_121))
in ((_186_122), ([])))
in Some (_186_123))
in ((g), (_186_124)))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(

let _85_197 = (match ((FStar_StratifiedExtraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _85_185; FStar_Extraction_ML_Syntax.loc = _85_183}, ttys, _85_191) -> begin
((n), (ttys))
end
| _85_194 -> begin
(failwith "Expected a constructor")
end)
in (match (_85_197) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _85_201 = (FStar_Util.first_N nTyVars pats)
in (match (_85_201) with
| (tysVarPats, restPats) -> begin
(

let _85_208 = (FStar_Util.fold_map (fun g _85_205 -> (match (_85_205) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_85_208) with
| (g, tyMLPats) -> begin
(

let _85_222 = (FStar_Util.fold_map (fun g _85_212 -> (match (_85_212) with
| (p, imp) -> begin
(

let _85_215 = (extract_one_pat disj false g p)
in (match (_85_215) with
| (env, popt) -> begin
(

let popt = (match (popt) with
| None -> begin
Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))
end
| _85_218 -> begin
popt
end)
in ((env), (popt)))
end))
end)) g restPats)
in (match (_85_222) with
| (g, restMLPats) -> begin
(

let _85_230 = (let _186_130 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___556 -> (match (uu___556) with
| Some (x) -> begin
(x)::[]
end
| _85_227 -> begin
[]
end))))
in (FStar_All.pipe_right _186_130 FStar_List.split))
in (match (_85_230) with
| (mlPats, when_clauses) -> begin
(let _186_134 = (let _186_133 = (let _186_132 = (FStar_All.pipe_left (FStar_StratifiedExtraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _186_131 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_186_132), (_186_131))))
in Some (_186_133))
in ((g), (_186_134)))
end))
end))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(

let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (

let g = (FStar_StratifiedExtraction_ML_Env.extend_bv g x (([]), (mlty)) false false imp)
in ((g), (if imp then begin
None
end else begin
Some (((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_StratifiedExtraction_ML_Env.as_mlident x.FStar_Absyn_Syntax.v))), ([])))
end))))
end
| FStar_Absyn_Syntax.Pat_wild (x) when disj -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(

let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (

let g = (FStar_StratifiedExtraction_ML_Env.extend_bv g x (([]), (mlty)) false false imp)
in ((g), (if imp then begin
None
end else begin
Some (((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_StratifiedExtraction_ML_Env.as_mlident x.FStar_Absyn_Syntax.v))), ([])))
end))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(

let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let g = (FStar_StratifiedExtraction_ML_Env.extend_ty g a (Some (mlty)))
in ((g), (if imp then begin
None
end else begin
Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))
end))))
end
| (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) -> begin
((g), (None))
end))
in (

let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
((g), (((x), (v))))
end
| _85_265 -> begin
(failwith "Impossible")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _186_143 = (FStar_List.fold_left FStar_StratifiedExtraction_ML_Util.conjoin hd tl)
in Some (_186_143))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj ((p)::pats) -> begin
(

let _85_280 = (extract_one_pat true g p)
in (match (_85_280) with
| (g, p) -> begin
(

let ps = (let _186_146 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _186_145 = (extract_one_pat true g x)
in (Prims.snd _186_145)))))
in (p)::_186_146)
in (

let _85_296 = (FStar_All.pipe_right ps (FStar_List.partition (fun uu___557 -> (match (uu___557) with
| (_85_285, (_85_289)::_85_287) -> begin
true
end
| _85_293 -> begin
false
end))))
in (match (_85_296) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _85_299 -> (match (_85_299) with
| (x, whens) -> begin
(let _186_149 = (mk_when_clause whens)
in ((x), (_186_149)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps))
end
| rest -> begin
(let _186_153 = (let _186_152 = (let _186_151 = (let _186_150 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_186_150))
in ((_186_151), (None)))
in (_186_152)::ps)
in ((g), (_186_153)))
end)
in res))
end)))
end))
end
| _85_305 -> begin
(

let _85_310 = (extract_one_pat false g p)
in (match (_85_310) with
| (g, (p, whens)) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[])))
end))
end)))))


let normalize_abs : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun e0 -> (

let rec aux = (fun bs e -> (

let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(aux (FStar_List.append bs bs') body)
end
| _85_322 -> begin
(

let e' = (FStar_Absyn_Util.unascribe e)
in if (FStar_Absyn_Util.is_fun e') then begin
(aux bs e')
end else begin
(FStar_Absyn_Syntax.mk_Exp_abs ((bs), (e)) None e0.FStar_Absyn_Syntax.pos)
end)
end)))
in (aux [] e0)))


let ffi_mltuple_mlp : Prims.int  ->  (Prims.string Prims.list * Prims.string) = (fun n -> (

let name = if (((Prims.parse_int "2") < n) && (n < (Prims.parse_int "6"))) then begin
(let _186_162 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _186_162))
end else begin
if (n = (Prims.parse_int "2")) then begin
"mkpair"
end else begin
(failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in ((("Camlstack")::[]), (name))))


let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(

let args = (FStar_List.map Prims.snd fields)
in (

let tup = (let _186_169 = (let _186_168 = (let _186_167 = (let _186_166 = (let _186_165 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_186_165))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _186_166))
in ((_186_167), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_186_168))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _186_169))
in (

let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce (((tup), (dummyTy), (dummyTy))))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(failwith "NYI: lalloc ctor")
end
| _85_341 -> begin
(failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))


let maybe_lalloc_eta_data : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _85_351, t1) -> begin
(

let x = (let _186_182 = (FStar_Absyn_Util.gensym ())
in ((_186_182), ((~- ((Prims.parse_int "1"))))))
in (let _186_185 = (let _186_184 = (let _186_183 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_186_183)))
in (_186_184)::more_args)
in (eta_args _186_185 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_85_357, _85_359) -> begin
(((FStar_List.rev more_args)), (t))
end
| _85_363 -> begin
(failwith "Impossible")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_85_368, args), Some (FStar_Absyn_Syntax.Record_ctor (_85_373, fields))) -> begin
(

let path = (FStar_StratifiedExtraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_StratifiedExtraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _85_382 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _85_388 = (eta_args [] residualType)
in (match (_85_388) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _186_194 = (as_record qual e)
in (FStar_StratifiedExtraction_ML_Util.resugar_exp _186_194))
end
| _85_391 -> begin
(

let _85_394 = (FStar_List.unzip eargs)
in (match (_85_394) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _186_196 = (let _186_195 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _186_195))
in (FStar_All.pipe_left FStar_StratifiedExtraction_ML_Util.resugar_exp _186_196))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _85_401 -> begin
(failwith "Impossible")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _85_405; FStar_Extraction_ML_Syntax.loc = _85_403}, (mlarg)::[]), _85_414) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(

let _85_417 = (FStar_StratifiedExtraction_ML_Env.debug g (fun _85_416 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_85_420, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _85_426; FStar_Extraction_ML_Syntax.loc = _85_424}, (mle)::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_StratifiedExtraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _85_443 -> begin
(let _186_199 = (let _186_198 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_186_198), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_186_199))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _186_200 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _186_200))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _186_201 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _186_201))
end
| _85_483 -> begin
mlAppExpr
end)))))


let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _85_489 = (FStar_List.hd l)
in (match (_85_489) with
| (p1, w1, e1) -> begin
(

let _85_493 = (let _186_204 = (FStar_List.tl l)
in (FStar_List.hd _186_204))
in (match (_85_493) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Absyn_Syntax.v), (p2.FStar_Absyn_Syntax.v))) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _85_513 -> begin
def
end)
end))
end))
end))


let rec check_exp : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (

let _85_523 = (let _186_221 = (check_exp' g e f t)
in (erase g _186_221 f t))
in (match (_85_523) with
| (e, _85_520, _85_522) -> begin
e
end)))
and check_exp' : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (

let _85_531 = (synth_exp g e)
in (match (_85_531) with
| (e0, f0, t0) -> begin
if (FStar_StratifiedExtraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let _85_537 = (synth_exp' g e)
in (match (_85_537) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let _85_541 = (FStar_StratifiedExtraction_ML_Env.debug g (fun u -> (let _186_233 = (let _186_232 = (FStar_Absyn_Print.tag_of_exp e)
in (let _186_231 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _186_232 _186_231)))
in (FStar_Util.print_string _186_233))))
in (

let top = e
in (match ((let _186_234 = (FStar_Absyn_Util.compress_exp e)
in _186_234.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(

let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (

let ml_ty = (translate_typ g t)
in (let _186_238 = (let _186_237 = (let _186_236 = (FStar_StratifiedExtraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _186_235 -> FStar_Extraction_ML_Syntax.MLE_Const (_186_235)) _186_236))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _186_237))
in ((_186_238), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e0, t, f) -> begin
(

let t = (translate_typ g t)
in (

let f = (match (f) with
| None -> begin
(failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(FStar_StratifiedExtraction_ML_ExtractTyp.translate_eff g l)
end)
in (

let e = (check_exp g e0 f t)
in ((e), (f), (t)))))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(

let _85_571 = (FStar_StratifiedExtraction_ML_Env.lookup_var g e)
in (match (_85_571) with
| ((x, mltys, _85_568), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _186_239 = (maybe_lalloc_eta_data g qual t x)
in ((_186_239), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _85_576 -> begin
(err_uninst g e mltys)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let rec synth_app = (fun is_data _85_585 _85_588 restArgs -> (match (((_85_585), (_85_588))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _85_592) -> begin
(

let _85_603 = if ((FStar_Absyn_Util.is_primop head) || (FStar_StratifiedExtraction_ML_Util.codegen_fsharp ())) then begin
(let _186_248 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_186_248)))
end else begin
(FStar_List.fold_left (fun _85_596 _85_599 -> (match (((_85_596), (_85_599))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (let _186_251 = (FStar_Absyn_Util.gensym ())
in ((_186_251), ((~- ((Prims.parse_int "1"))))))
in (let _186_253 = (let _186_252 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_186_252)::out_args)
in (((((x), (arg)))::lbs), (_186_253))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_85_603) with
| (lbs, mlargs) -> begin
(

let app = (let _186_254 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _186_254))
in (

let l_app = (FStar_List.fold_right (fun _85_607 out -> (match (_85_607) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]))), (out)))))
end)) lbs app)
in ((l_app), (f), (t))))
end))
end
| (((FStar_Util.Inl (tt), _85_614))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _186_258 = (let _186_257 = (FStar_StratifiedExtraction_ML_Util.join tt.FStar_Absyn_Syntax.pos f f')
in ((_186_257), (t)))
in (synth_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _186_258 rest))
end else begin
(failwith "Impossible: ill-typed application")
end
end
| (((FStar_Util.Inr (e0), _85_627))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let e0_rng = e0.FStar_Absyn_Syntax.pos
in (

let _85_640 = (synth_exp g e0)
in (match (_85_640) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _186_260 = (let _186_259 = (FStar_StratifiedExtraction_ML_Util.join_l e0_rng ((f)::(f')::(f0)::[]))
in ((_186_259), (t)))
in (synth_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _186_260 rest)))
end)))
end
| _85_643 -> begin
(match ((FStar_StratifiedExtraction_ML_Util.delta_unfold g t)) with
| Some (t) -> begin
(synth_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application e restArgs t)
end)
end)
end))
in (

let synth_app_maybe_projector = (fun is_data mlhead _85_652 args -> (match (_85_652) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Absyn_Syntax.Record_projector (_85_655)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((FStar_Util.Inr (ee), Some (FStar_Absyn_Syntax.Implicit (_85_666))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_85_672, f', t)) -> begin
(let _186_275 = (FStar_StratifiedExtraction_ML_Util.join ee.FStar_Absyn_Syntax.pos f f')
in (remove_implicits args _186_275 t))
end
| _85_679 -> begin
((args), (f), (t))
end))
in (

let _85_683 = (remove_implicits args f t)
in (match (_85_683) with
| (args, f, t) -> begin
(synth_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _85_685 -> begin
(synth_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in (

let head = (FStar_Absyn_Util.compress_exp head)
in (match (head.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(

let _85_700 = (FStar_StratifiedExtraction_ML_Env.lookup_var g head)
in (match (_85_700) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((FStar_Util.Inl (_85_704), _85_707))::_85_702 -> begin
true
end
| _85_711 -> begin
false
end)
in (

let _85_753 = (match (vars) with
| (_85_716)::_85_714 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _85_719 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _85_723 = (FStar_Util.first_N n args)
in (match (_85_723) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _85_732 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _85_732.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _85_732.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _85_738; FStar_Extraction_ML_Syntax.loc = _85_736})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _85_745 = head
in {FStar_Extraction_ML_Syntax.expr = _85_745.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _85_745.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _85_748 -> begin
(failwith "Impossible")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_85_753) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _186_276 = (maybe_lalloc_eta_data g qual head_t head_ml)
in ((_186_276), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _85_756 -> begin
(synth_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _85_758 -> begin
(

let _85_762 = (synth_exp g head)
in (match (_85_762) with
| (head, f, t) -> begin
(synth_app_maybe_projector None head ((f), (t)) args)
end))
end))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let _85_785 = (FStar_List.fold_left (fun _85_769 _85_773 -> (match (((_85_769), (_85_773))) with
| ((ml_bs, env), (b, _85_772)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(

let env = (FStar_StratifiedExtraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _186_279 = (FStar_StratifiedExtraction_ML_Env.btvar_as_mlTermVar a)
in ((_186_279), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env))))
end
| FStar_Util.Inr (x) -> begin
(

let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (

let env = (FStar_StratifiedExtraction_ML_Env.extend_bv env x (([]), (t)) false false false)
in (

let ml_b = (((FStar_StratifiedExtraction_ML_Env.as_mlident x.FStar_Absyn_Syntax.v)), (t))
in (((ml_b)::ml_bs), (env)))))
end)
end)) (([]), (g)) bs)
in (match (_85_785) with
| (ml_bs, env) -> begin
(

let ml_bs = (FStar_List.rev ml_bs)
in (

let _85_790 = (synth_exp env body)
in (match (_85_790) with
| (ml_body, f, t) -> begin
(

let _85_800 = (FStar_List.fold_right (fun _85_794 _85_797 -> (match (((_85_794), (_85_797))) with
| ((_85_792, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_85_800) with
| (f, tfun) -> begin
(let _186_282 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_186_282), (f), (tfun)))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(

let maybe_generalize = (fun _85_812 -> (match (_85_812) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(

let f_e = (FStar_StratifiedExtraction_ML_ExtractTyp.translate_eff g lbeff)
in (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_StratifiedExtraction_ML_Util.is_type_abstraction bs) -> begin
(

let _85_836 = (match ((FStar_Util.prefix_until (fun uu___558 -> (match (uu___558) with
| (FStar_Util.Inr (_85_821), _85_824) -> begin
true
end
| _85_827 -> begin
false
end)) bs)) with
| None -> begin
((bs), ((FStar_Absyn_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _186_286 = (FStar_Absyn_Syntax.mk_Typ_fun (((b)::rest), (c)) None c.FStar_Absyn_Syntax.pos)
in ((bs), (_186_286)))
end)
in (match (_85_836) with
| (tbinders, tbody) -> begin
(

let n = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(

let _85_845 = (FStar_Util.first_N n bs)
in (match (_85_845) with
| (targs, rest_args) -> begin
(

let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (

let targs = (FStar_All.pipe_right targs (FStar_List.map (fun uu___559 -> (match (uu___559) with
| (FStar_Util.Inl (a), _85_854) -> begin
a
end
| _85_857 -> begin
(failwith "Impossible")
end))))
in (

let env = (FStar_List.fold_left (fun env a -> (FStar_StratifiedExtraction_ML_Env.extend_ty env a None)) g targs)
in (

let expected_t = (translate_typ env expected_t)
in (

let polytype = (let _186_290 = (FStar_All.pipe_right targs (FStar_List.map FStar_StratifiedExtraction_ML_Env.btvar_as_mltyvar))
in ((_186_290), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _85_866 -> begin
false
end)
in (

let rest_args = if add_unit then begin
(FStar_StratifiedExtraction_ML_Util.unit_binder)::rest_args
end else begin
rest_args
end
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| _85_871 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs ((rest_args), (body)) None e.FStar_Absyn_Syntax.pos)
end)
in ((lbname), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body))))))))))
end))
end else begin
(failwith "Not enough type binders")
end
end
| _85_874 -> begin
(err_value_restriction e)
end)))
end))
end
| _85_876 -> begin
(

let expected_t = (translate_typ g t)
in ((lbname), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _85_891 -> (match (_85_891) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env a -> (FStar_StratifiedExtraction_ML_Env.extend_ty env a None)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let e = (check_exp env e f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _85_920 = (FStar_List.fold_right (fun lb _85_901 -> (match (_85_901) with
| (env, lbs) -> begin
(

let _85_914 = lb
in (match (_85_914) with
| (lbname, _85_904, (t, (_85_907, polytype)), add_unit, _85_913) -> begin
(

let _85_917 = (FStar_StratifiedExtraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_85_917) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_85_920) with
| (env_body, lbs) -> begin
(

let env_def = if is_rec then begin
env_body
end else begin
g
end
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'.FStar_Absyn_Syntax.pos
in (

let _85_927 = (synth_exp env_body e')
in (match (_85_927) with
| (e', f', t') -> begin
(

let f = (let _186_300 = (let _186_299 = (FStar_List.map Prims.fst lbs)
in (f')::_186_299)
in (FStar_StratifiedExtraction_ML_Util.join_l e'_rng _186_300))
in (

let is_rec = if is_rec then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NonRec
end
in (let _186_306 = (let _186_305 = (let _186_303 = (let _186_302 = (let _186_301 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_186_301)))
in ((_186_302), (e')))
in FStar_Extraction_ML_Syntax.MLE_Let (_186_303))
in (let _186_304 = (FStar_StratifiedExtraction_ML_Util.mlloc_of_range e.FStar_Absyn_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _186_305 _186_304)))
in ((_186_306), (f), (t')))))
end)))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(

let _85_937 = (synth_exp g scrutinee)
in (match (_85_937) with
| (e, f_e, t_e) -> begin
(

let _85_941 = (check_pats_for_ite pats)
in (match (_85_941) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _85_953 = (synth_exp g then_e)
in (match (_85_953) with
| (then_mle, f_then, t_then) -> begin
(

let _85_957 = (synth_exp g else_e)
in (match (_85_957) with
| (else_mle, f_else, t_else) -> begin
(

let _85_960 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_85_960) with
| (t_branch, maybe_lift) -> begin
(let _186_337 = (let _186_335 = (let _186_334 = (let _186_333 = (maybe_lift then_mle t_then)
in (let _186_332 = (let _186_331 = (maybe_lift else_mle t_else)
in Some (_186_331))
in ((e), (_186_333), (_186_332))))
in FStar_Extraction_ML_Syntax.MLE_If (_186_334))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _186_335))
in (let _186_336 = (FStar_StratifiedExtraction_ML_Util.join top.FStar_Absyn_Syntax.pos f_then f_else)
in ((_186_337), (_186_336), (t_branch))))
end))
end))
end))
end
| _85_962 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _85_966 -> (match (_85_966) with
| (pat, when_opt, branch) -> begin
(

let _85_969 = (extract_pat g pat)
in (match (_85_969) with
| (env, p) -> begin
(

let _85_980 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _85_976 = (synth_exp env w)
in (match (_85_976) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_85_980) with
| (when_opt, f_when) -> begin
(

let _85_984 = (synth_exp env branch)
in (match (_85_984) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _85_987 -> (match (_85_987) with
| (p, wopt) -> begin
(

let when_clause = (FStar_StratifiedExtraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
end))
end))
end))
end))))
in (match (mlbranches) with
| [] -> begin
(

let _85_996 = (FStar_StratifiedExtraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_85_996) with
| (fw, _85_993, _85_995) -> begin
(let _186_344 = (let _186_343 = (let _186_342 = (let _186_341 = (let _186_340 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_186_340)::[])
in ((fw), (_186_341)))
in FStar_Extraction_ML_Syntax.MLE_App (_186_342))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _186_343))
in ((_186_344), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_85_999, _85_1001, (_85_1003, f_first, t_first)))::rest -> begin
(

let _85_1029 = (FStar_List.fold_left (fun _85_1011 _85_1021 -> (match (((_85_1011), (_85_1021))) with
| ((topt, f), (_85_1013, _85_1015, (_85_1017, f_branch, t_branch))) -> begin
(

let f = (FStar_StratifiedExtraction_ML_Util.join top.FStar_Absyn_Syntax.pos f f_branch)
in (

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
in ((topt), (f))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (_85_1029) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _85_1040 -> (match (_85_1040) with
| (p, (wopt, _85_1033), (b, _85_1037, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_85_1043) -> begin
b
end)
in ((p), (wopt), (b)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _186_348 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_186_348), (f_match), (t_match)))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _85_1053)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> (

let _85_1065 = (FStar_Util.incr c)
in (let _186_351 = (FStar_ST.read c)
in ((x), (_186_351))))))


let ind_discriminator_body : FStar_StratifiedExtraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let fstar_disc_type = (FStar_Tc_Env.lookup_lid env.FStar_StratifiedExtraction_ML_Env.tcenv discName)
in (

let wildcards = (match (fstar_disc_type.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _85_1073) -> begin
(let _186_361 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___560 -> (match (uu___560) with
| (_85_1078, Some (FStar_Absyn_Syntax.Implicit (_85_1080))) -> begin
true
end
| _85_1085 -> begin
false
end))))
in (FStar_All.pipe_right _186_361 (FStar_List.map (fun _85_1086 -> (let _186_360 = (fresh "_")
in ((_186_360), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _85_1089 -> begin
(failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _186_376 = (let _186_375 = (let _186_374 = (let _186_373 = (let _186_372 = (let _186_371 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _186_370 = (let _186_369 = (let _186_365 = (let _186_363 = (let _186_362 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_186_362), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_186_363))
in (let _186_364 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_186_365), (None), (_186_364))))
in (let _186_368 = (let _186_367 = (let _186_366 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_186_366)))
in (_186_367)::[])
in (_186_369)::_186_368))
in ((_186_371), (_186_370))))
in FStar_Extraction_ML_Syntax.MLE_Match (_186_372))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _186_373))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_186_374)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_186_375))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _186_376))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_StratifiedExtraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = true})::[]))))))))))




