
open Prims

let type_leq : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.delta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.delta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.delta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold g) t))


let fail = (fun r msg -> (

let _79_19 = (let _176_27 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _176_27))
in (FStar_All.failwith msg)))


let err_uninst = (fun env e _79_25 -> (match (_79_25) with
| (vars, t) -> begin
(let _176_35 = (let _176_34 = (FStar_Absyn_Print.exp_to_string e)
in (let _176_33 = (let _176_31 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _176_31 (FStar_String.concat ", ")))
in (let _176_32 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_Env.currentModule t)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _176_34 _176_33 _176_32))))
in (fail e.FStar_Absyn_Syntax.pos _176_35))
end))


let err_ill_typed_application = (fun e args t -> (let _176_41 = (let _176_40 = (FStar_Absyn_Print.exp_to_string e)
in (let _176_39 = (FStar_Absyn_Print.args_to_string args)
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _176_40 _176_39)))
in (fail e.FStar_Absyn_Syntax.pos _176_41)))


let err_value_restriction = (fun e -> (fail e.FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))


let err_unexpected_eff = (fun e f0 f1 -> (let _176_47 = (let _176_46 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _176_46 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail e.FStar_Absyn_Syntax.pos _176_47)))


let is_constructor : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _176_50 = (FStar_Absyn_Util.compress_exp e)
in _176_50.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Data_ctor))) | (FStar_Absyn_Syntax.Exp_fvar (_, Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
true
end
| _79_49 -> begin
false
end))


let rec is_value_or_type_app : FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e -> (match ((let _176_53 = (FStar_Absyn_Util.compress_exp e)
in _176_53.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_70 -> (match (_79_70) with
| (te, _79_69) -> begin
(match (te) with
| FStar_Util.Inl (_79_72) -> begin
true
end
| FStar_Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end else begin
(match ((let _176_55 = (FStar_Absyn_Util.compress_exp head)
in _176_55.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_1 -> (match (_79_1) with
| (FStar_Util.Inl (te), _79_86) -> begin
true
end
| _79_89 -> begin
false
end))))
end
| _79_91 -> begin
false
end)
end
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _))) | (FStar_Absyn_Syntax.Exp_ascribed (e, _, _)) -> begin
(is_value_or_type_app e)
end
| _79_105 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_126, fields) -> begin
(FStar_Util.for_all (fun _79_133 -> (match (_79_133) with
| (_79_131, e) -> begin
(is_ml_value e)
end)) fields)
end
| _79_135 -> begin
false
end))


let translate_typ : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (let _176_64 = (FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (eraseTypeDeep g _176_64)))


let translate_typ_of_arg : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun g a -> (let _176_69 = (FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (eraseTypeDeep g _176_69)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e f t -> if (erasable g f t) then begin
(

let _79_150 = (FStar_Extraction_ML_Env.debug g (fun _79_149 -> (match (()) with
| () -> begin
(let _176_90 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_Env.currentModule e)
in (let _176_89 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_Env.currentModule t)
in (FStar_Util.print2 "Erasing %s at type %s\n" _176_90 _176_89)))
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


let maybe_coerce : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e tInferred tExpected -> (match ((type_leq_c g (Some (e)) tInferred tExpected)) with
| (true, Some (e')) -> begin
e'
end
| _79_162 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tExpected) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (tInferred), (tExpected)))))
end))


let extract_pat : FStar_Extraction_ML_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Extraction_ML_Env.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (

let rec extract_one_pat = (fun disj imp g p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_79_171) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (let _176_111 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Extraction_ML_Syntax.as_mlident _176_111))
in (

let when_clause = (let _176_120 = (let _176_119 = (let _176_118 = (let _176_117 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _176_116 = (let _176_115 = (let _176_114 = (let _176_113 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p i)
in (FStar_All.pipe_left (fun _176_112 -> FStar_Extraction_ML_Syntax.MLE_Const (_176_112)) _176_113))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _176_114))
in (_176_115)::[])
in (_176_117)::_176_116))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_176_118)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_119))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _176_120))
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[]))))))))
end
| FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _176_124 = (let _176_123 = (let _176_122 = (let _176_121 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Absyn_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_176_121))
in ((_176_122), ([])))
in Some (_176_123))
in ((g), (_176_124)))
end
| FStar_Absyn_Syntax.Pat_cons (f, q, pats) -> begin
(

let _79_203 = (match ((FStar_Extraction_ML_Env.lookup_fv g f)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _79_191; FStar_Extraction_ML_Syntax.loc = _79_189}, ttys, _79_197) -> begin
((n), (ttys))
end
| _79_200 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_79_203) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _79_207 = (FStar_Util.first_N nTyVars pats)
in (match (_79_207) with
| (tysVarPats, restPats) -> begin
(

let _79_214 = (FStar_Util.fold_map (fun g _79_211 -> (match (_79_211) with
| (p, imp) -> begin
(extract_one_pat disj true g p)
end)) g tysVarPats)
in (match (_79_214) with
| (g, tyMLPats) -> begin
(

let _79_228 = (FStar_Util.fold_map (fun g _79_218 -> (match (_79_218) with
| (p, imp) -> begin
(

let _79_221 = (extract_one_pat disj false g p)
in (match (_79_221) with
| (env, popt) -> begin
(

let popt = (match (popt) with
| None -> begin
Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))
end
| _79_224 -> begin
popt
end)
in ((env), (popt)))
end))
end)) g restPats)
in (match (_79_228) with
| (g, restMLPats) -> begin
(

let _79_236 = (let _176_130 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| Some (x) -> begin
(x)::[]
end
| _79_233 -> begin
[]
end))))
in (FStar_All.pipe_right _176_130 FStar_List.split))
in (match (_79_236) with
| (mlPats, when_clauses) -> begin
(let _176_134 = (let _176_133 = (let _176_132 = (FStar_All.pipe_left (FStar_Extraction_ML_Util.resugar_pat q) (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _176_131 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_176_132), (_176_131))))
in Some (_176_133))
in ((g), (_176_134)))
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

let g = (FStar_Extraction_ML_Env.extend_bv g x (([]), (mlty)) false false imp)
in ((g), (if imp then begin
None
end else begin
Some (((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))), ([])))
end))))
end
| FStar_Absyn_Syntax.Pat_wild (x) when disj -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(

let mlty = (translate_typ g x.FStar_Absyn_Syntax.sort)
in (

let g = (FStar_Extraction_ML_Env.extend_bv g x (([]), (mlty)) false false imp)
in ((g), (if imp then begin
None
end else begin
Some (((FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))), ([])))
end))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(

let mlty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let g = (FStar_Extraction_ML_Env.extend_ty g a (Some (mlty)))
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
| _79_271 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _176_143 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_176_143))
end))
in (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_disj ((p)::pats) -> begin
(

let _79_286 = (extract_one_pat true g p)
in (match (_79_286) with
| (g, p) -> begin
(

let ps = (let _176_146 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _176_145 = (extract_one_pat true g x)
in (Prims.snd _176_145)))))
in (p)::_176_146)
in (

let _79_302 = (FStar_All.pipe_right ps (FStar_List.partition (fun _79_3 -> (match (_79_3) with
| (_79_291, (_79_295)::_79_293) -> begin
true
end
| _79_299 -> begin
false
end))))
in (match (_79_302) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _79_305 -> (match (_79_305) with
| (x, whens) -> begin
(let _176_149 = (mk_when_clause whens)
in ((x), (_176_149)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps))
end
| rest -> begin
(let _176_153 = (let _176_152 = (let _176_151 = (let _176_150 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_176_150))
in ((_176_151), (None)))
in (_176_152)::ps)
in ((g), (_176_153)))
end)
in res))
end)))
end))
end
| _79_311 -> begin
(

let _79_316 = (extract_one_pat false g p)
in (match (_79_316) with
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
| _79_328 -> begin
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
(let _176_162 = (FStar_Util.string_of_int n)
in (Prims.strcat "mktuple" _176_162))
end else begin
if (n = (Prims.parse_int "2")) then begin
"mkpair"
end else begin
(FStar_All.failwith "NYI in runtime/allocator/camlstack.mli")
end
end
in ((("Camlstack")::[]), (name))))


let fix_lalloc : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun arg -> (match (arg.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(FStar_All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| FStar_Extraction_ML_Syntax.MLE_Record (mlns, fields) -> begin
(

let args = (FStar_List.map Prims.snd fields)
in (

let tup = (let _176_169 = (let _176_168 = (let _176_167 = (let _176_166 = (let _176_165 = (ffi_mltuple_mlp (FStar_List.length args))
in FStar_Extraction_ML_Syntax.MLE_Name (_176_165))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _176_166))
in ((_176_167), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_168))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _176_169))
in (

let dummyTy = FStar_Extraction_ML_Syntax.ml_unit_ty
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty dummyTy) (FStar_Extraction_ML_Syntax.MLE_Coerce (((tup), (dummyTy), (dummyTy))))))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(FStar_All.failwith "NYI: lalloc ctor")
end
| _79_347 -> begin
(FStar_All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))


let maybe_lalloc_eta_data : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _79_357, t1) -> begin
(

let x = (let _176_182 = (FStar_Absyn_Util.gensym ())
in ((_176_182), ((~- ((Prims.parse_int "1"))))))
in (let _176_185 = (let _176_184 = (let _176_183 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_176_183)))
in (_176_184)::more_args)
in (eta_args _176_185 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_363, _79_365) -> begin
(((FStar_List.rev more_args)), (t))
end
| _79_369 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_79_374, args), Some (FStar_Absyn_Syntax.Record_ctor (_79_379, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _79_388 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _79_394 = (eta_args [] residualType)
in (match (_79_394) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _176_194 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _176_194))
end
| _79_397 -> begin
(

let _79_400 = (FStar_List.unzip eargs)
in (match (_79_400) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _176_196 = (let _176_195 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _176_195))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _176_196))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _79_407 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _79_411; FStar_Extraction_ML_Syntax.loc = _79_409}, (mlarg)::[]), _79_420) when (mlp = FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(

let _79_423 = (FStar_Extraction_ML_Env.debug g (fun _79_422 -> (match (()) with
| () -> begin
(FStar_Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_79_426, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _79_432; FStar_Extraction_ML_Syntax.loc = _79_430}, (mle)::args), Some (FStar_Absyn_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _79_449 -> begin
(let _176_199 = (let _176_198 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_176_198), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_199))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _176_200 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _176_200))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(let _176_201 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _176_201))
end
| _79_489 -> begin
mlAppExpr
end)))))


let check_pats_for_ite : (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) Prims.list  ->  (Prims.bool * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _79_495 = (FStar_List.hd l)
in (match (_79_495) with
| (p1, w1, e1) -> begin
(

let _79_499 = (let _176_204 = (FStar_List.tl l)
in (FStar_List.hd _176_204))
in (match (_79_499) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Absyn_Syntax.v), (p2.FStar_Absyn_Syntax.v))) with
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _79_519 -> begin
def
end)
end))
end))
end))


let rec check_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (

let _79_529 = (let _176_221 = (check_exp' g e f t)
in (erase g _176_221 f t))
in (match (_79_529) with
| (e, _79_526, _79_528) -> begin
e
end)))
and check_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e f t -> (

let _79_537 = (synth_exp g e)
in (match (_79_537) with
| (e0, f0, t0) -> begin
if (FStar_Extraction_ML_Util.eff_leq f0 f) then begin
(maybe_coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end)))
and synth_exp : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let _79_543 = (synth_exp' g e)
in (match (_79_543) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' : FStar_Extraction_ML_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let _79_547 = (FStar_Extraction_ML_Env.debug g (fun u -> (let _176_233 = (let _176_232 = (FStar_Absyn_Print.tag_of_exp e)
in (let _176_231 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "now synthesizing expression (%s) :  %s \n" _176_232 _176_231)))
in (FStar_Util.print_string _176_233))))
in (

let top = e
in (match ((let _176_234 = (FStar_Absyn_Util.compress_exp e)
in _176_234.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(

let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (

let ml_ty = (translate_typ g t)
in (let _176_238 = (let _176_237 = (let _176_236 = (FStar_Extraction_ML_Util.mlconst_of_const' e.FStar_Absyn_Syntax.pos c)
in (FStar_All.pipe_left (fun _176_235 -> FStar_Extraction_ML_Syntax.MLE_Const (_176_235)) _176_236))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _176_237))
in ((_176_238), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty)))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e0, t, f) -> begin
(

let t = (translate_typ g t)
in (

let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (

let e = (check_exp g e0 f t)
in ((e), (f), (t)))))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(

let _79_577 = (FStar_Extraction_ML_Env.lookup_var g e)
in (match (_79_577) with
| ((x, mltys, _79_574), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _176_239 = (maybe_lalloc_eta_data g qual t x)
in ((_176_239), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _79_582 -> begin
(err_uninst g e mltys)
end)
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let rec synth_app = (fun is_data _79_591 _79_594 restArgs -> (match (((_79_591), (_79_594))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _79_598) -> begin
(

let _79_609 = if ((FStar_Absyn_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _176_248 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_176_248)))
end else begin
(FStar_List.fold_left (fun _79_602 _79_605 -> (match (((_79_602), (_79_605))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (let _176_251 = (FStar_Absyn_Util.gensym ())
in ((_176_251), ((~- ((Prims.parse_int "1"))))))
in (let _176_253 = (let _176_252 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_176_252)::out_args)
in (((((x), (arg)))::lbs), (_176_253))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_79_609) with
| (lbs, mlargs) -> begin
(

let app = (let _176_254 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_lalloc_eta_data g is_data t) _176_254))
in (

let l_app = (FStar_List.fold_right (fun _79_613 out -> (match (_79_613) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]))), (out)))))
end)) lbs app)
in ((l_app), (f), (t))))
end))
end
| (((FStar_Util.Inl (tt), _79_620))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) -> begin
if (type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _176_258 = (let _176_257 = (FStar_Extraction_ML_Util.join tt.FStar_Absyn_Syntax.pos f f')
in ((_176_257), (t)))
in (synth_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _176_258 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| (((FStar_Util.Inr (e0), _79_633))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let e0_rng = e0.FStar_Absyn_Syntax.pos
in (

let _79_646 = (synth_exp g e0)
in (match (_79_646) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _176_260 = (let _176_259 = (FStar_Extraction_ML_Util.join_l e0_rng ((f)::(f')::(f0)::[]))
in ((_176_259), (t)))
in (synth_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _176_260 rest)))
end)))
end
| _79_649 -> begin
(match ((FStar_Extraction_ML_Util.delta_unfold g t)) with
| Some (t) -> begin
(synth_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application e restArgs t)
end)
end)
end))
in (

let synth_app_maybe_projector = (fun is_data mlhead _79_658 args -> (match (_79_658) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Absyn_Syntax.Record_projector (_79_661)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((FStar_Util.Inr (ee), Some (FStar_Absyn_Syntax.Implicit (_79_672))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_79_678, f', t)) -> begin
(let _176_275 = (FStar_Extraction_ML_Util.join ee.FStar_Absyn_Syntax.pos f f')
in (remove_implicits args _176_275 t))
end
| _79_685 -> begin
((args), (f), (t))
end))
in (

let _79_689 = (remove_implicits args f t)
in (match (_79_689) with
| (args, f, t) -> begin
(synth_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _79_691 -> begin
(synth_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in (

let head = (FStar_Absyn_Util.compress_exp head)
in (match (head.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(

let _79_706 = (FStar_Extraction_ML_Env.lookup_var g head)
in (match (_79_706) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((FStar_Util.Inl (_79_710), _79_713))::_79_708 -> begin
true
end
| _79_717 -> begin
false
end)
in (

let _79_759 = (match (vars) with
| (_79_722)::_79_720 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _79_725 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _79_729 = (FStar_Util.first_N n args)
in (match (_79_729) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (translate_typ_of_arg g) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _79_738 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _79_738.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _79_738.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _79_744; FStar_Extraction_ML_Syntax.loc = _79_742})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _79_751 = head
in {FStar_Extraction_ML_Syntax.expr = _79_751.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _79_751.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _79_754 -> begin
(FStar_All.failwith "Impossible")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_79_759) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _176_276 = (maybe_lalloc_eta_data g qual head_t head_ml)
in ((_176_276), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _79_762 -> begin
(synth_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _79_764 -> begin
(

let _79_768 = (synth_exp g head)
in (match (_79_768) with
| (head, f, t) -> begin
(synth_app_maybe_projector None head ((f), (t)) args)
end))
end))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let _79_791 = (FStar_List.fold_left (fun _79_775 _79_779 -> (match (((_79_775), (_79_779))) with
| ((ml_bs, env), (b, _79_778)) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(

let env = (FStar_Extraction_ML_Env.extend_ty env a (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _176_279 = (FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in ((_176_279), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env))))
end
| FStar_Util.Inr (x) -> begin
(

let t = (translate_typ env x.FStar_Absyn_Syntax.sort)
in (

let env = (FStar_Extraction_ML_Env.extend_bv env x (([]), (t)) false false false)
in (

let ml_b = (((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v)), (t))
in (((ml_b)::ml_bs), (env)))))
end)
end)) (([]), (g)) bs)
in (match (_79_791) with
| (ml_bs, env) -> begin
(

let ml_bs = (FStar_List.rev ml_bs)
in (

let _79_796 = (synth_exp env body)
in (match (_79_796) with
| (ml_body, f, t) -> begin
(

let _79_806 = (FStar_List.fold_right (fun _79_800 _79_803 -> (match (((_79_800), (_79_803))) with
| ((_79_798, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_79_806) with
| (f, tfun) -> begin
(let _176_282 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_176_282), (f), (tfun)))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), e') -> begin
(

let maybe_generalize = (fun _79_818 -> (match (_79_818) with
| {FStar_Absyn_Syntax.lbname = lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = lbeff; FStar_Absyn_Syntax.lbdef = e} -> begin
(

let f_e = (FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) when (FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(

let _79_842 = (match ((FStar_Util.prefix_until (fun _79_4 -> (match (_79_4) with
| (FStar_Util.Inr (_79_827), _79_830) -> begin
true
end
| _79_833 -> begin
false
end)) bs)) with
| None -> begin
((bs), ((FStar_Absyn_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _176_286 = (FStar_Absyn_Syntax.mk_Typ_fun (((b)::rest), (c)) None c.FStar_Absyn_Syntax.pos)
in ((bs), (_176_286)))
end)
in (match (_79_842) with
| (tbinders, tbody) -> begin
(

let n = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
if (n <= (FStar_List.length bs)) then begin
(

let _79_851 = (FStar_Util.first_N n bs)
in (match (_79_851) with
| (targs, rest_args) -> begin
(

let expected_t = (match ((FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(FStar_All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tbody)
end)
in (

let targs = (FStar_All.pipe_right targs (FStar_List.map (fun _79_5 -> (match (_79_5) with
| (FStar_Util.Inl (a), _79_860) -> begin
a
end
| _79_863 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (

let expected_t = (translate_typ env expected_t)
in (

let polytype = (let _176_290 = (FStar_All.pipe_right targs (FStar_List.map FStar_Extraction_ML_Env.btvar_as_mltyvar))
in ((_176_290), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _79_872 -> begin
false
end)
in (

let rest_args = if add_unit then begin
(FStar_Extraction_ML_Util.unit_binder)::rest_args
end else begin
rest_args
end
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| _79_877 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs ((rest_args), (body)) None e.FStar_Absyn_Syntax.pos)
end)
in ((lbname), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body))))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _79_880 -> begin
(err_value_restriction e)
end)))
end))
end
| _79_882 -> begin
(

let expected_t = (translate_typ g t)
in ((lbname), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _79_897 -> (match (_79_897) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env a -> (FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
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

let _79_926 = (FStar_List.fold_right (fun lb _79_907 -> (match (_79_907) with
| (env, lbs) -> begin
(

let _79_920 = lb
in (match (_79_920) with
| (lbname, _79_910, (t, (_79_913, polytype)), add_unit, _79_919) -> begin
(

let _79_923 = (FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit true)
in (match (_79_923) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_79_926) with
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

let _79_933 = (synth_exp env_body e')
in (match (_79_933) with
| (e', f', t') -> begin
(

let f = (let _176_300 = (let _176_299 = (FStar_List.map Prims.fst lbs)
in (f')::_176_299)
in (FStar_Extraction_ML_Util.join_l e'_rng _176_300))
in (

let is_rec = if is_rec then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NonRec
end
in (let _176_306 = (let _176_305 = (let _176_303 = (let _176_302 = (let _176_301 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_176_301)))
in ((_176_302), (e')))
in FStar_Extraction_ML_Syntax.MLE_Let (_176_303))
in (let _176_304 = (FStar_Extraction_ML_Util.mlloc_of_range e.FStar_Absyn_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _176_305 _176_304)))
in ((_176_306), (f), (t')))))
end)))))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (scrutinee, pats) -> begin
(

let _79_943 = (synth_exp g scrutinee)
in (match (_79_943) with
| (e, f_e, t_e) -> begin
(

let _79_947 = (check_pats_for_ite pats)
in (match (_79_947) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _79_959 = (synth_exp g then_e)
in (match (_79_959) with
| (then_mle, f_then, t_then) -> begin
(

let _79_963 = (synth_exp g else_e)
in (match (_79_963) with
| (else_mle, f_else, t_else) -> begin
(

let _79_966 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_79_966) with
| (t_branch, maybe_lift) -> begin
(let _176_337 = (let _176_335 = (let _176_334 = (let _176_333 = (maybe_lift then_mle t_then)
in (let _176_332 = (let _176_331 = (maybe_lift else_mle t_else)
in Some (_176_331))
in ((e), (_176_333), (_176_332))))
in FStar_Extraction_ML_Syntax.MLE_If (_176_334))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _176_335))
in (let _176_336 = (FStar_Extraction_ML_Util.join top.FStar_Absyn_Syntax.pos f_then f_else)
in ((_176_337), (_176_336), (t_branch))))
end))
end))
end))
end
| _79_968 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _79_972 -> (match (_79_972) with
| (pat, when_opt, branch) -> begin
(

let _79_975 = (extract_pat g pat)
in (match (_79_975) with
| (env, p) -> begin
(

let _79_986 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _79_982 = (synth_exp env w)
in (match (_79_982) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_79_986) with
| (when_opt, f_when) -> begin
(

let _79_990 = (synth_exp env branch)
in (match (_79_990) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _79_993 -> (match (_79_993) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
end))
end))
end))
end))))
in (match (mlbranches) with
| [] -> begin
(

let _79_1002 = (FStar_Extraction_ML_Env.lookup_fv g (FStar_Absyn_Util.fv FStar_Absyn_Const.failwith_lid))
in (match (_79_1002) with
| (fw, _79_999, _79_1001) -> begin
(let _176_344 = (let _176_343 = (let _176_342 = (let _176_341 = (let _176_340 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_176_340)::[])
in ((fw), (_176_341)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_342))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _176_343))
in ((_176_344), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_79_1005, _79_1007, (_79_1009, f_first, t_first)))::rest -> begin
(

let _79_1035 = (FStar_List.fold_left (fun _79_1017 _79_1027 -> (match (((_79_1017), (_79_1027))) with
| ((topt, f), (_79_1019, _79_1021, (_79_1023, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join top.FStar_Absyn_Syntax.pos f f_branch)
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
in (match (_79_1035) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _79_1046 -> (match (_79_1046) with
| (p, (wopt, _79_1039), (b, _79_1043, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_79_1049) -> begin
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
in (let _176_348 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_176_348), (f_match), (t_match)))))
end))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _79_1059)) -> begin
(synth_exp g e)
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(fail e.FStar_Absyn_Syntax.pos "Unexpected expression")
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> (

let _79_1071 = (FStar_Util.incr c)
in (let _176_351 = (FStar_ST.read c)
in ((x), (_176_351))))))


let ind_discriminator_body : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let fstar_disc_type = (FStar_Tc_Env.lookup_lid env.FStar_Extraction_ML_Env.tcenv discName)
in (

let wildcards = (match (fstar_disc_type.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _79_1079) -> begin
(let _176_361 = (FStar_All.pipe_right binders (FStar_List.filter (fun _79_6 -> (match (_79_6) with
| (_79_1084, Some (FStar_Absyn_Syntax.Implicit (_79_1086))) -> begin
true
end
| _79_1091 -> begin
false
end))))
in (FStar_All.pipe_right _176_361 (FStar_List.map (fun _79_1092 -> (let _176_360 = (fresh "_")
in ((_176_360), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _79_1095 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _176_376 = (let _176_375 = (let _176_374 = (let _176_373 = (let _176_372 = (let _176_371 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _176_370 = (let _176_369 = (let _176_365 = (let _176_363 = (let _176_362 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_176_362), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_176_363))
in (let _176_364 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_176_365), (None), (_176_364))))
in (let _176_368 = (let _176_367 = (let _176_366 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_176_366)))
in (_176_367)::[])
in (_176_369)::_176_368))
in ((_176_371), (_176_370))))
in FStar_Extraction_ML_Syntax.MLE_Match (_176_372))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _176_373))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_176_374)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_176_375))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _176_376))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_Env.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = true})::[]))))))))))




