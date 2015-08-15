
let eff_to_string = (fun ( _61_1 ) -> (match (_61_1) with
| Microsoft_FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

let fail = (fun ( r ) ( msg ) -> (let _61_10 = (let _132_5 = (Microsoft_FStar_Absyn_Print.format_error r msg)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _132_5))
in (Support.All.exit 1)))

let err_uninst = (fun ( e ) -> (let _132_8 = (let _132_7 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _132_7))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _132_8)))

let err_ill_typed_application = (fun ( e ) ( args ) ( t ) -> (let _132_14 = (let _132_13 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _132_12 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _132_13 _132_12)))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _132_14)))

let err_value_restriction = (fun ( e ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun ( e ) ( f0 ) ( f1 ) -> (let _132_20 = (let _132_19 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "for expression %s, Expected effect %s; got effect %s" _132_19 (eff_to_string f0) (eff_to_string f1)))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _132_20)))

let is_constructor = (fun ( e ) -> (match ((let _132_23 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _132_23.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_))))) -> begin
true
end
| _61_36 -> begin
false
end))

let rec is_value_or_type_app = (fun ( e ) -> (match ((let _132_26 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _132_26.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(match ((is_constructor head)) with
| true -> begin
(Support.All.pipe_right args (Support.List.for_all (fun ( _61_57 ) -> (match (_61_57) with
| (te, _61_56) -> begin
(match (te) with
| Support.Microsoft.FStar.Util.Inl (_61_59) -> begin
true
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end
| false -> begin
(match ((let _132_28 = (Microsoft_FStar_Absyn_Util.compress_exp head)
in _132_28.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(Support.All.pipe_right args (Support.List.for_all (fun ( _61_2 ) -> (match (_61_2) with
| (Support.Microsoft.FStar.Util.Inl (te), _61_73) -> begin
true
end
| _61_76 -> begin
false
end))))
end
| _61_78 -> begin
false
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _)))) | (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _))) -> begin
(is_value_or_type_app e)
end
| _61_92 -> begin
false
end))

let rec is_ml_value = (fun ( e ) -> (match (e) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (_)) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (_)) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (_)) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((_, exps))) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(Support.Microsoft.FStar.Util.for_all is_ml_value exps)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((_61_113, fields)) -> begin
(Support.Microsoft.FStar.Util.for_all (fun ( _61_120 ) -> (match (_61_120) with
| (_61_118, e) -> begin
(is_ml_value e)
end)) fields)
end
| _61_122 -> begin
false
end))

let translate_typ = (fun ( g ) ( t ) -> (let _132_37 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep g _132_37)))

let translate_typ_of_arg = (fun ( g ) ( a ) -> (let _132_42 = (Microsoft_FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep g _132_42)))

let instantiate = (fun ( s ) ( args ) -> (Microsoft_FStar_Extraction_ML_Util.subst s args))

let erasable = (fun ( g ) ( f ) ( t ) -> ((f = Microsoft_FStar_Extraction_ML_Syntax.E_PURE) && (Microsoft_FStar_Extraction_ML_Util.erasableType g t)))

let erase = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((erasable g f t)) with
| true -> begin
(let _61_137 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( _61_136 ) -> (match (()) with
| () -> begin
(let _132_63 = (Microsoft_FStar_Extraction_OCaml_Code.string_of_mlexpr g e)
in (let _132_62 = (Microsoft_FStar_Extraction_OCaml_Code.string_of_mlty g t)
in (Support.Microsoft.FStar.Util.fprint2 "Erasing %s at type %s\n" _132_63 _132_62)))
end)))
in (Microsoft_FStar_Extraction_ML_Syntax.ml_unit, f, Microsoft_FStar_Extraction_ML_Env.erasedContent))
end
| false -> begin
(e, f, t)
end))

let maybe_coerce = (fun ( g ) ( e ) ( tInferred ) ( etag ) ( tExpected ) -> (match ((Microsoft_FStar_Extraction_ML_Util.equiv g tInferred tExpected)) with
| true -> begin
e
end
| false -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, tInferred, tExpected))
end))

let eff_leq = (fun ( f ) ( f' ) -> (match ((f, f')) with
| ((Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _)) | ((_, Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE)) -> begin
true
end
| _61_155 -> begin
false
end))

let join = (fun ( f ) ( f' ) -> (match ((f, f')) with
| ((Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE, _)) | ((_, Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE)) -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE
end
| _61_167 -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_PURE
end))

let join_l = (fun ( fs ) -> (Support.List.fold_left join Microsoft_FStar_Extraction_ML_Syntax.E_PURE fs))

let extract_pat = (fun ( g ) ( p ) -> (let rec extract_pat = (fun ( disj ) ( imp ) ( g ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _61_184 = (extract_pat true false g p)
in (match (_61_184) with
| (g, p) -> begin
(let _132_101 = (let _132_100 = (let _132_99 = (let _132_98 = (Support.List.collect (fun ( x ) -> (let _132_97 = (extract_pat true false g x)
in (Support.Prims.snd _132_97))) pats)
in (Support.List.append p _132_98))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (_132_99))
in (_132_100)::[])
in (g, _132_101))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _132_104 = (let _132_103 = (let _132_102 = (Microsoft_FStar_Extraction_ML_Util.mlconst_of_const s)
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (_132_102))
in (_132_103)::[])
in (g, _132_104))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, q, pats)) -> begin
(let _61_201 = (match ((Microsoft_FStar_Extraction_ML_Env.lookup_fv g f)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (n), ttys) -> begin
(n, ttys)
end
| _61_198 -> begin
(Support.All.failwith "Expected a constructor")
end)
in (match (_61_201) with
| (d, tys) -> begin
(let nTyVars = (Support.List.length (Support.Prims.fst tys))
in (let _61_205 = (Support.Microsoft.FStar.Util.first_N nTyVars pats)
in (match (_61_205) with
| (tysVarPats, restPats) -> begin
(let _61_212 = (Support.Microsoft.FStar.Util.fold_map (fun ( g ) ( _61_209 ) -> (match (_61_209) with
| (p, imp) -> begin
(extract_pat disj true g p)
end)) g tysVarPats)
in (match (_61_212) with
| (g, tyMLPats) -> begin
(let _61_219 = (Support.Microsoft.FStar.Util.fold_map (fun ( g ) ( _61_216 ) -> (match (_61_216) with
| (p, imp) -> begin
(extract_pat disj false g p)
end)) g restPats)
in (match (_61_219) with
| (g, restMLPats) -> begin
(let mlPats = (Support.List.append tyMLPats restMLPats)
in (let _132_110 = (let _132_109 = (Support.All.pipe_left (Microsoft_FStar_Extraction_ML_Util.resugar_pat q) (Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((d, (Support.List.flatten mlPats)))))
in (_132_109)::[])
in (g, _132_110)))
end))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let mlty = (translate_typ g x.Microsoft_FStar_Absyn_Syntax.sort)
in (let g = (Microsoft_FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false imp)
in (g, (match (imp) with
| true -> begin
[]
end
| false -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLP_Var ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v)))::[]
end))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) when disj -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let mlty = (translate_typ g x.Microsoft_FStar_Absyn_Syntax.sort)
in (let g = (Microsoft_FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false imp)
in (g, (match (imp) with
| true -> begin
[]
end
| false -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLP_Var ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v)))::[]
end))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_61_232) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let mlty = Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top
in (let g = (Microsoft_FStar_Extraction_ML_Env.extend_ty g a (Some (mlty)))
in (g, (match (imp) with
| true -> begin
[]
end
| false -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[]
end))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) -> begin
(g, [])
end))
in (extract_pat false false g p)))

let normalize_abs = (fun ( e0 ) -> (let rec aux = (fun ( bs ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs', body)) -> begin
(aux (Support.List.append bs bs') body)
end
| _61_254 -> begin
(let e' = (Microsoft_FStar_Absyn_Util.unascribe e)
in (match ((Microsoft_FStar_Absyn_Util.is_fun e')) with
| true -> begin
(aux bs e')
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, e) None e0.Microsoft_FStar_Absyn_Syntax.pos)
end))
end)))
in (aux [] e0)))

let maybe_eta_data = (fun ( qual ) ( residualType ) ( mlAppExpr ) -> (let rec eta_args = (fun ( more_args ) ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t0, _61_264, t1)) -> begin
(let x = (let _132_127 = (Microsoft_FStar_Absyn_Util.gensym ())
in (_132_127, (- (1))))
in (eta_args ((((x, Some (t0)), Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x)))::more_args) t1))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((_61_270, _61_272)) -> begin
(Support.List.rev more_args)
end
| _61_276 -> begin
(Support.All.failwith "Impossible")
end))
in (let as_record = (fun ( qual ) ( e ) -> (match ((e, qual)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((_61_281, args)), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((_61_286, fields)))) -> begin
(let path = (Microsoft_FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (Microsoft_FStar_Extraction_ML_Util.record_fields fields args)
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))
end
| _61_295 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun ( qual ) ( e ) -> (let eargs = (eta_args [] residualType)
in (match (eargs) with
| [] -> begin
(let _132_136 = (as_record qual e)
in (Microsoft_FStar_Extraction_ML_Util.resugar_exp _132_136))
end
| _61_302 -> begin
(let _61_305 = (Support.List.unzip eargs)
in (match (_61_305) with
| (binders, eargs) -> begin
(match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((head, args)) -> begin
(let body = (let _132_137 = (Support.All.pipe_left (as_record qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((head, (Support.List.append args eargs)))))
in (Support.All.pipe_left Microsoft_FStar_Extraction_ML_Util.resugar_exp _132_137))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))
end
| _61_312 -> begin
(Support.All.failwith "Impossible")
end)
end))
end)))
in (match ((mlAppExpr, qual)) with
| (_61_314, None) -> begin
mlAppExpr
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mle::args)), Some (Microsoft_FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (Microsoft_FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (match (args) with
| [] -> begin
proj
end
| _61_332 -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((proj, args))
end)))
end
| ((Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs)), Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) | ((Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs)), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(Support.All.pipe_left (resugar_and_maybe_eta qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
end
| ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) | ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(Support.All.pipe_left (resugar_and_maybe_eta qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
end
| _61_361 -> begin
mlAppExpr
end)))))

let rec check_exp = (fun ( g ) ( e ) ( f ) ( t ) -> (let _61_371 = (let _132_154 = (check_exp' g e f t)
in (erase g _132_154 f t))
in (match (_61_371) with
| (e, _61_368, _61_370) -> begin
e
end)))
and check_exp' = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((let _132_159 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _132_159.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_match ((scrutinee, pats)) -> begin
(let _61_383 = (synth_exp g scrutinee)
in (match (_61_383) with
| (e, f_e, t_e) -> begin
(let mlbranches = (Support.All.pipe_right pats (Support.List.map (fun ( _61_387 ) -> (match (_61_387) with
| (pat, when_opt, branch) -> begin
(let _61_390 = (extract_pat g pat)
in (match (_61_390) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _132_161 = (check_exp env w Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE Microsoft_FStar_Extraction_ML_Syntax.ml_bool_ty)
in Some (_132_161))
end)
in (let branch = (check_exp env branch f t)
in (let _132_162 = (Support.List.hd p)
in (_132_162, when_opt, branch))))
end))
end))))
in (match ((eff_leq f_e f)) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))
end
| false -> begin
(err_unexpected_eff scrutinee f f_e)
end))
end))
end
| _61_398 -> begin
(let _61_402 = (synth_exp g e)
in (match (_61_402) with
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
and synth_exp = (fun ( g ) ( e ) -> (let _61_408 = (synth_exp' g e)
in (match (_61_408) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun ( g ) ( e ) -> (let _61_412 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( u ) -> (let _132_169 = (let _132_168 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "now synthesizing expression :  %s \n" _132_168))
in (Support.Microsoft.FStar.Util.print_string _132_169))))
in (match ((let _132_170 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _132_170.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (let _132_174 = (let _132_172 = (Microsoft_FStar_Extraction_ML_Util.mlconst_of_const c)
in (Support.All.pipe_left (fun ( _132_171 ) -> Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (_132_171)) _132_172))
in (let _132_173 = (translate_typ g t)
in (_132_174, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _132_173))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e0, t, f)) -> begin
(let t = (translate_typ g t)
in (let f = (match (f) with
| None -> begin
(Support.All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(Microsoft_FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _61_438 = (Microsoft_FStar_Extraction_ML_Env.lookup_var g e)
in (match (_61_438) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _132_175 = (maybe_eta_data qual t x)
in (_132_175, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _61_443 -> begin
(err_uninst e)
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let rec synth_app = (fun ( is_data ) ( _61_452 ) ( _61_455 ) ( restArgs ) -> (match ((_61_452, _61_455)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _61_459) -> begin
(let _61_470 = (match ((Microsoft_FStar_Absyn_Util.is_primop head)) with
| true -> begin
(let _132_184 = (Support.All.pipe_right (Support.List.rev mlargs_f) (Support.List.map Support.Prims.fst))
in ([], _132_184))
end
| false -> begin
(Support.List.fold_left (fun ( _61_463 ) ( _61_466 ) -> (match ((_61_463, _61_466)) with
| ((lbs, out_args), (arg, f)) -> begin
(match ((f = Microsoft_FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(lbs, (arg)::out_args)
end
| false -> begin
(let x = (let _132_187 = (Microsoft_FStar_Absyn_Util.gensym ())
in (_132_187, (- (1))))
in (((x, arg))::lbs, (Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x))::out_args))
end)
end)) ([], []) mlargs_f)
end)
in (match (_61_470) with
| (lbs, mlargs) -> begin
(let app = (Support.All.pipe_left (maybe_eta_data is_data t) (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (let l_app = (Support.List.fold_right (fun ( _61_474 ) ( out ) -> (match (_61_474) with
| (x, arg) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = x; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((Support.Microsoft.FStar.Util.Inl (_61_479), _61_482)::rest, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tunit, f', t))) -> begin
(match ((Microsoft_FStar_Extraction_ML_Util.equiv g tunit Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
(synth_app is_data (mlhead, ((Microsoft_FStar_Extraction_ML_Syntax.ml_unit, Microsoft_FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) ((join f f'), t) rest)
end
| false -> begin
(Support.All.failwith "Impossible: ill-typed application")
end)
end
| ((Support.Microsoft.FStar.Util.Inr (e0), _61_495)::rest, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tExpected, f', t))) -> begin
(let _61_507 = (synth_exp g e0)
in (match (_61_507) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred f' tExpected)
in (let _132_191 = (let _132_190 = (join_l ((f)::(f')::(f0)::[]))
in (_132_190, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _132_191 rest)))
end))
end
| _61_510 -> begin
(match ((Microsoft_FStar_Extraction_ML_Util.delta_unfold g t)) with
| Some (t) -> begin
(synth_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application e restArgs t)
end)
end)
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _61_527 = (Microsoft_FStar_Extraction_ML_Env.lookup_var g head)
in (match (_61_527) with
| ((head, (vars, t)), qual) -> begin
(let n = (Support.List.length vars)
in (match ((n <= (Support.List.length args))) with
| true -> begin
(let _61_531 = (Support.Microsoft.FStar.Util.first_N n args)
in (match (_61_531) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (Support.List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (match (rest) with
| [] -> begin
(let _132_192 = (maybe_eta_data qual t head)
in (_132_192, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _61_537 -> begin
(synth_app qual (head, []) (Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end))))
end))
end
| false -> begin
(err_uninst e)
end))
end))
end
| _61_539 -> begin
(let _61_543 = (synth_exp g head)
in (match (_61_543) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _61_566 = (Support.List.fold_left (fun ( _61_550 ) ( _61_554 ) -> (match ((_61_550, _61_554)) with
| ((ml_bs, env), (b, _61_553)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let env = (Microsoft_FStar_Extraction_ML_Env.extend_ty env a (Some (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _132_197 = (Microsoft_FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (let _132_196 = (Support.All.pipe_left (fun ( _132_195 ) -> Some (_132_195)) Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)
in (_132_197, _132_196)))
in ((ml_b)::ml_bs, env)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (translate_typ env x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env = (Microsoft_FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v), Some (t))
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_61_566) with
| (ml_bs, env) -> begin
(let ml_bs = (Support.List.rev ml_bs)
in (let _61_571 = (synth_exp env body)
in (match (_61_571) with
| (ml_body, f, t) -> begin
(let _61_581 = (Support.List.fold_right (fun ( _61_575 ) ( _61_578 ) -> (match ((_61_575, _61_578)) with
| ((_61_573, targ), (f, t)) -> begin
(let _132_202 = (let _132_201 = (let _132_200 = (Support.Microsoft.FStar.Util.must targ)
in (_132_200, f, t))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_132_201))
in (Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _132_202))
end)) ml_bs (f, t))
in (match (_61_581) with
| (f, tfun) -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body)), f, tfun)
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), e')) -> begin
(let maybe_generalize = (fun ( _61_593 ) -> (match (_61_593) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = lbeff; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (Microsoft_FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) when (Microsoft_FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _61_617 = (match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _61_3 ) -> (match (_61_3) with
| (Support.Microsoft.FStar.Util.Inr (_61_602), _61_605) -> begin
true
end
| _61_608 -> begin
false
end)) bs)) with
| None -> begin
(bs, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| Some ((bs, b, rest)) -> begin
(let _132_206 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _132_206))
end)
in (match (_61_617) with
| (tbinders, tbody) -> begin
(let n = (Support.List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(match ((n <= (Support.List.length bs))) with
| true -> begin
(let _61_626 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_61_626) with
| (targs, rest_args) -> begin
(let expected_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(Support.All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (Support.All.pipe_right targs (Support.List.map (fun ( _61_4 ) -> (match (_61_4) with
| (Support.Microsoft.FStar.Util.Inl (a), _61_635) -> begin
a
end
| _61_638 -> begin
(Support.All.failwith "Impossible")
end))))
in (let env = (Support.List.fold_left (fun ( env ) ( a ) -> (Microsoft_FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _132_210 = (Support.All.pipe_right targs (Support.List.map Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_132_210, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _61_647 -> begin
false
end)
in (let rest_args = (match (add_unit) with
| true -> begin
(Microsoft_FStar_Extraction_ML_Util.unit_binder)::rest_args
end
| false -> begin
rest_args
end)
in (let body = (match (rest_args) with
| [] -> begin
body
end
| _61_652 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end
| false -> begin
(Support.All.failwith "Not enough type binders")
end)
end
| _61_655 -> begin
(err_value_restriction e)
end)))
end))
end
| _61_657 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun ( env ) ( _61_672 ) -> (match (_61_672) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(let env = (Support.List.fold_left (fun ( env ) ( a ) -> (Microsoft_FStar_Extraction_ML_Env.extend_ty env a None)) env targs)
in (let expected_t = (match (add_unit) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, (Support.Prims.snd polytype)))
end
| false -> begin
(Support.Prims.snd polytype)
end)
in (let e = (check_exp env e f expected_t)
in (f, {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = nm; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e}))))
end))
in (let lbs = (Support.All.pipe_right lbs (Support.List.map maybe_generalize))
in (let _61_701 = (Support.List.fold_right (fun ( lb ) ( _61_682 ) -> (match (_61_682) with
| (env, lbs) -> begin
(let _61_695 = lb
in (match (_61_695) with
| (lbname, _61_685, (t, (_61_688, polytype)), add_unit, _61_694) -> begin
(let _61_698 = (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_61_698) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_61_701) with
| (env_body, lbs) -> begin
(let env_def = (match (is_rec) with
| true -> begin
env_body
end
| false -> begin
g
end)
in (let lbs = (Support.All.pipe_right lbs (Support.List.map (check_lb env_def)))
in (let _61_707 = (synth_exp env_body e')
in (match (_61_707) with
| (e', f', t') -> begin
(let f = (let _132_220 = (let _132_219 = (Support.List.map Support.Prims.fst lbs)
in (f')::_132_219)
in (join_l _132_220))
in (let _132_224 = (let _132_223 = (let _132_222 = (let _132_221 = (Support.List.map Support.Prims.snd lbs)
in (is_rec, _132_221))
in (_132_222, e'))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (_132_223))
in (_132_224, f, t')))
end))))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(Support.All.failwith "Matches must be checked; missing a compiler-provided annotation")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _61_715))) -> begin
(synth_exp g e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(Support.All.failwith "Unexpected expression")
end)))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( x ) -> (let _61_727 = (Support.Microsoft.FStar.Util.incr c)
in (let _132_227 = (Support.ST.read c)
in (x, _132_227)))))

let ind_discriminator_body = (fun ( env ) ( discName ) ( constrName ) -> (let mlid = (fresh "_discr_")
in (let _61_736 = (let _132_234 = (Microsoft_FStar_Absyn_Util.fv constrName)
in (Microsoft_FStar_Extraction_ML_Env.lookup_fv env _132_234))
in (match (_61_736) with
| (_61_734, ts) -> begin
(let arg_pat = (match ((Support.Prims.snd ts)) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_61_738) -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[]
end
| _61_741 -> begin
[]
end)
in (let rid = constrName
in (let discrBody = (let _132_242 = (let _132_241 = (let _132_240 = (let _132_239 = (let _132_238 = (let _132_237 = (let _132_236 = (let _132_235 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_132_235, arg_pat))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor (_132_236))
in (_132_237, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_132_238)::((Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (false))))::[])
in (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Extraction_ML_Syntax.idsym mlid))), _132_239))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Match (_132_240))
in (((mlid, None))::[], _132_241))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (_132_242))
in Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = (Microsoft_FStar_Extraction_ML_Env.convIdent discName.Microsoft_FStar_Absyn_Syntax.ident); Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[])))))
end))))

let dummyPatIdent = (fun ( n ) -> (let _132_246 = (let _132_245 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat "dummyPat" _132_245))
in (_132_246, 0)))

let dummyPatIdents = (fun ( n ) -> (let _132_249 = (Microsoft_FStar_Extraction_ML_ExtractTyp.firstNNats n)
in (Support.List.map dummyPatIdent _132_249)))




