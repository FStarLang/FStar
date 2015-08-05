
let eff_to_string = (fun ( _59_1 ) -> (match (_59_1) with
| Microsoft_FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

let fail = (fun ( r ) ( msg ) -> (let _59_10 = (let _68_25156 = (Microsoft_FStar_Absyn_Print.format_error r msg)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_25156))
in (exit (1))))

let err_uninst = (fun ( e ) -> (let _68_25159 = (let _68_25158 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _68_25158))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _68_25159)))

let err_ill_typed_application = (fun ( e ) ( args ) ( t ) -> (let _68_25165 = (let _68_25164 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _68_25163 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _68_25164 _68_25163)))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _68_25165)))

let err_value_restriction = (fun ( e ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun ( e ) ( f0 ) ( f1 ) -> (let _68_25171 = (let _68_25170 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "for expression %s, Expected effect %s; got effect %s" _68_25170 (eff_to_string f0) (eff_to_string f1)))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _68_25171)))

let is_constructor = (fun ( e ) -> (match ((let _68_25174 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_25174.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_))))) -> begin
true
end
| _59_36 -> begin
false
end))

let rec is_value_or_type_app = (fun ( e ) -> (match ((let _68_25177 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_25177.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(match ((is_constructor head)) with
| true -> begin
(Support.Prims.pipe_right args (Support.List.for_all (fun ( _59_57 ) -> (match (_59_57) with
| (te, _59_56) -> begin
(match (te) with
| Support.Microsoft.FStar.Util.Inl (_59_59) -> begin
true
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(is_value_or_type_app e)
end)
end))))
end
| false -> begin
(match ((let _68_25179 = (Microsoft_FStar_Absyn_Util.compress_exp head)
in _68_25179.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(Support.Prims.pipe_right args (Support.List.for_all (fun ( _59_2 ) -> (match (_59_2) with
| (Support.Microsoft.FStar.Util.Inl (te), _59_73) -> begin
true
end
| _59_76 -> begin
false
end))))
end
| _59_78 -> begin
false
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _)))) | (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _))) -> begin
(is_value_or_type_app e)
end
| _59_92 -> begin
false
end))

let rec is_ml_value = (fun ( e ) -> (match (e) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (_)) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (_)) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (_)) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((_, exps))) | (Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(Support.Microsoft.FStar.Util.for_all is_ml_value exps)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((_59_113, fields)) -> begin
(Support.Microsoft.FStar.Util.for_all (fun ( _59_120 ) -> (match (_59_120) with
| (_59_118, e) -> begin
(is_ml_value e)
end)) fields)
end
| _59_122 -> begin
false
end))

let translate_typ = (fun ( g ) ( t ) -> (let _68_25188 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep g _68_25188)))

let instantiate = (fun ( s ) ( args ) -> (Microsoft_FStar_Extraction_ML_Util.subst s args))

let erasable = (fun ( g ) ( f ) ( t ) -> ((f = Microsoft_FStar_Extraction_ML_Syntax.E_PURE) && (Microsoft_FStar_Extraction_ML_Util.erasableType g t)))

let erase = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((erasable g f t)) with
| true -> begin
(let _59_135 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( _59_134 ) -> (match (()) with
| () -> begin
(let _68_25209 = (Microsoft_FStar_Extraction_OCaml_Code.string_of_mlexpr g e)
in (let _68_25208 = (Microsoft_FStar_Extraction_OCaml_Code.string_of_mlty g t)
in (Support.Microsoft.FStar.Util.fprint2 "Erasing %s at type %s\n" _68_25209 _68_25208)))
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
| _59_153 -> begin
false
end))

let join = (fun ( f ) ( f' ) -> (match ((f, f')) with
| ((Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE, _)) | ((_, Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE)) -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE
end
| _59_165 -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_PURE
end))

let join_l = (fun ( fs ) -> (Support.List.fold_left join Microsoft_FStar_Extraction_ML_Syntax.E_PURE fs))

let extract_pat = (fun ( g ) ( p ) -> (let rec extract_pat = (fun ( disj ) ( g ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _59_181 = (extract_pat true g p)
in (match (_59_181) with
| (g, p) -> begin
(let _68_25245 = (let _68_25244 = (let _68_25243 = (let _68_25242 = (Support.List.collect (fun ( x ) -> (let _68_25241 = (extract_pat true g x)
in (Support.Prims.snd _68_25241))) pats)
in (Support.List.append p _68_25242))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (_68_25243))
in (_68_25244)::[])
in (g, _68_25245))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _68_25248 = (let _68_25247 = (let _68_25246 = (Microsoft_FStar_Extraction_ML_Util.mlconst_of_const s)
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (_68_25246))
in (_68_25247)::[])
in (g, _68_25248))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, q, pats)) -> begin
(let d = (match ((Microsoft_FStar_Extraction_ML_Env.lookup_fv g f)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (n), _59_193) -> begin
n
end
| _59_196 -> begin
(failwith ("Expected a constructor"))
end)
in (let _59_200 = (Support.Microsoft.FStar.Util.fold_map (extract_pat disj) g pats)
in (match (_59_200) with
| (g, pats) -> begin
(let _68_25250 = (let _68_25249 = (Support.Prims.pipe_left (Microsoft_FStar_Extraction_ML_Util.resugar_pat q) (Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((d, (Support.List.flatten pats)))))
in (_68_25249)::[])
in (g, _68_25250))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _59_203)) -> begin
(let mlty = (translate_typ g x.Microsoft_FStar_Absyn_Syntax.sort)
in (let g = (Microsoft_FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false)
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLP_Var ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v)))::[])))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) when disj -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let mlty = (translate_typ g x.Microsoft_FStar_Absyn_Syntax.sort)
in (let g = (Microsoft_FStar_Extraction_ML_Env.extend_bv g x ([], mlty) false)
in (g, (Microsoft_FStar_Extraction_ML_Syntax.MLP_Var ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v)))::[])))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_59_215) -> begin
(g, (Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[])
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) -> begin
(g, [])
end))
in (extract_pat false g p)))

let normalize_abs = (fun ( e0 ) -> (let rec aux = (fun ( bs ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs', body)) -> begin
(aux (Support.List.append bs bs') body)
end
| _59_236 -> begin
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
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t0, _59_246, t1)) -> begin
(let x = (let _68_25267 = (Microsoft_FStar_Absyn_Util.gensym ())
in (_68_25267, (- (1))))
in (eta_args ((((x, Some (t0)), Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x)))::more_args) t1))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((_59_252, _59_254)) -> begin
(Support.List.rev more_args)
end
| _59_258 -> begin
(failwith ("Impossible"))
end))
in (let as_record = (fun ( qual ) ( e ) -> (match ((e, qual)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((_59_263, args)), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((_59_268, fields)))) -> begin
(let path = (Microsoft_FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (Microsoft_FStar_Extraction_ML_Util.record_fields fields args)
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))
end
| _59_277 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun ( qual ) ( e ) -> (let eargs = (eta_args [] residualType)
in (match (eargs) with
| [] -> begin
(let _68_25276 = (as_record qual e)
in (Microsoft_FStar_Extraction_ML_Util.resugar_exp _68_25276))
end
| _59_284 -> begin
(let _59_287 = (Support.List.unzip eargs)
in (match (_59_287) with
| (binders, eargs) -> begin
(match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((head, args)) -> begin
(let body = (let _68_25277 = (Support.Prims.pipe_left (as_record qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((head, (Support.List.append args eargs)))))
in (Support.Prims.pipe_left Microsoft_FStar_Extraction_ML_Util.resugar_exp _68_25277))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))
end
| _59_294 -> begin
(failwith ("Impossible"))
end)
end))
end)))
in (match ((mlAppExpr, qual)) with
| (_59_296, None) -> begin
mlAppExpr
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mle::args)), Some (Microsoft_FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (Microsoft_FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (match (args) with
| [] -> begin
proj
end
| _59_314 -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((proj, args))
end)))
end
| ((Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs)), Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) | ((Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs)), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(Support.Prims.pipe_left (resugar_and_maybe_eta qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
end
| ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) | ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(Support.Prims.pipe_left (resugar_and_maybe_eta qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
end
| _59_343 -> begin
mlAppExpr
end)))))

let rec check_exp = (fun ( g ) ( e ) ( f ) ( t ) -> (let _59_353 = (let _68_25294 = (check_exp' g e f t)
in (erase g _68_25294 f t))
in (match (_59_353) with
| (e, _59_350, _59_352) -> begin
e
end)))
and check_exp' = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((let _68_25299 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_25299.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_match ((scrutinee, pats)) -> begin
(let _59_365 = (synth_exp g scrutinee)
in (match (_59_365) with
| (e, f_e, t_e) -> begin
(let mlbranches = (Support.Prims.pipe_right pats (Support.List.map (fun ( _59_369 ) -> (match (_59_369) with
| (pat, when_opt, branch) -> begin
(let _59_372 = (extract_pat g pat)
in (match (_59_372) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _68_25301 = (check_exp env w Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE Microsoft_FStar_Extraction_ML_Syntax.ml_bool_ty)
in Some (_68_25301))
end)
in (let branch = (check_exp env branch f t)
in (let _68_25302 = (Support.List.hd p)
in (_68_25302, when_opt, branch))))
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
| _59_380 -> begin
(let _59_384 = (synth_exp g e)
in (match (_59_384) with
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
and synth_exp = (fun ( g ) ( e ) -> (let _59_390 = (synth_exp' g e)
in (match (_59_390) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun ( g ) ( e ) -> (let _59_394 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( u ) -> (let _68_25309 = (let _68_25308 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "now synthesizing expression :  %s \n" _68_25308))
in (Support.Microsoft.FStar.Util.print_string _68_25309))))
in (match ((let _68_25310 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_25310.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (let _68_25314 = (let _68_25312 = (Microsoft_FStar_Extraction_ML_Util.mlconst_of_const c)
in (Support.Prims.pipe_left (fun ( _68_25311 ) -> Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (_68_25311)) _68_25312))
in (let _68_25313 = (translate_typ g t)
in (_68_25314, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _68_25313))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e0, t, f)) -> begin
(let t = (translate_typ g t)
in (let f = (match (f) with
| None -> begin
(failwith ("Ascription node with an empty effect label"))
end
| Some (l) -> begin
(Microsoft_FStar_Extraction_ML_ExtractTyp.translate_eff g l)
end)
in (let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _59_420 = (Microsoft_FStar_Extraction_ML_Env.lookup_var g e)
in (match (_59_420) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _68_25315 = (maybe_eta_data qual t x)
in (_68_25315, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _59_425 -> begin
(err_uninst e)
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let rec synth_app = (fun ( is_data ) ( _59_434 ) ( _59_437 ) ( restArgs ) -> (match ((_59_434, _59_437)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _59_441) -> begin
(let _59_452 = (match ((Microsoft_FStar_Absyn_Util.is_primop head)) with
| true -> begin
(let _68_25324 = (Support.Prims.pipe_right (Support.List.rev mlargs_f) (Support.List.map Support.Prims.fst))
in ([], _68_25324))
end
| false -> begin
(Support.List.fold_left (fun ( _59_445 ) ( _59_448 ) -> (match ((_59_445, _59_448)) with
| ((lbs, out_args), (arg, f)) -> begin
(match ((f = Microsoft_FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(lbs, (arg)::out_args)
end
| false -> begin
(let x = (let _68_25327 = (Microsoft_FStar_Absyn_Util.gensym ())
in (_68_25327, (- (1))))
in (((x, arg))::lbs, (Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x))::out_args))
end)
end)) ([], []) mlargs_f)
end)
in (match (_59_452) with
| (lbs, mlargs) -> begin
(let app = (Support.Prims.pipe_left (maybe_eta_data is_data t) (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (let l_app = (Support.List.fold_right (fun ( _59_456 ) ( out ) -> (match (_59_456) with
| (x, arg) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = x; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((Support.Microsoft.FStar.Util.Inl (_59_461), _59_464)::rest, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tunit, f', t))) -> begin
(match ((Microsoft_FStar_Extraction_ML_Util.equiv g tunit Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
(synth_app is_data (mlhead, ((Microsoft_FStar_Extraction_ML_Syntax.ml_unit, Microsoft_FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) ((join f f'), t) rest)
end
| false -> begin
(failwith ("Impossible: ill-typed application"))
end)
end
| ((Support.Microsoft.FStar.Util.Inr (e0), _59_477)::rest, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tExpected, f', t))) -> begin
(let _59_489 = (synth_exp g e0)
in (match (_59_489) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred f' tExpected)
in (let _68_25331 = (let _68_25330 = (join_l ((f)::(f')::(f0)::[]))
in (_68_25330, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _68_25331 rest)))
end))
end
| _59_492 -> begin
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
(let _59_509 = (Microsoft_FStar_Extraction_ML_Env.lookup_var g head)
in (match (_59_509) with
| ((head, (vars, t)), qual) -> begin
(let n = (Support.List.length vars)
in (match ((n <= (Support.List.length args))) with
| true -> begin
(let _59_513 = (Support.Microsoft.FStar.Util.first_N n args)
in (match (_59_513) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (Support.List.map (Microsoft_FStar_Extraction_ML_ExtractTyp.getTypeFromArg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (match (rest) with
| [] -> begin
(let _68_25332 = (maybe_eta_data qual t head)
in (_68_25332, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _59_519 -> begin
(synth_app qual (head, []) (Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end))))
end))
end
| false -> begin
(err_uninst e)
end))
end))
end
| _59_521 -> begin
(let _59_525 = (synth_exp g head)
in (match (_59_525) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _59_548 = (Support.List.fold_left (fun ( _59_532 ) ( _59_536 ) -> (match ((_59_532, _59_536)) with
| ((ml_bs, env), (b, _59_535)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let env = (Microsoft_FStar_Extraction_ML_Env.extend_ty env a (Some (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _68_25337 = (Microsoft_FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (let _68_25336 = (Support.Prims.pipe_left (fun ( _68_25335 ) -> Some (_68_25335)) Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)
in (_68_25337, _68_25336)))
in ((ml_b)::ml_bs, env)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (translate_typ env x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env = (Microsoft_FStar_Extraction_ML_Env.extend_bv env x ([], t) false)
in (let ml_b = ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v), Some (t))
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_59_548) with
| (ml_bs, env) -> begin
(let ml_bs = (Support.List.rev ml_bs)
in (let _59_553 = (synth_exp env body)
in (match (_59_553) with
| (ml_body, f, t) -> begin
(let _59_563 = (Support.List.fold_right (fun ( _59_557 ) ( _59_560 ) -> (match ((_59_557, _59_560)) with
| ((_59_555, targ), (f, t)) -> begin
(let _68_25342 = (let _68_25341 = (let _68_25340 = (Support.Microsoft.FStar.Util.must targ)
in (_68_25340, f, t))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_68_25341))
in (Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _68_25342))
end)) ml_bs (f, t))
in (match (_59_563) with
| (f, tfun) -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body)), f, tfun)
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), e')) -> begin
(let maybe_generalize = (fun ( _59_575 ) -> (match (_59_575) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = lbeff; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (Microsoft_FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) when (Microsoft_FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _59_599 = (match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _59_3 ) -> (match (_59_3) with
| (Support.Microsoft.FStar.Util.Inr (_59_584), _59_587) -> begin
true
end
| _59_590 -> begin
false
end)) bs)) with
| None -> begin
(bs, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| Some ((bs, b, rest)) -> begin
(let _68_25346 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _68_25346))
end)
in (match (_59_599) with
| (tbinders, tbody) -> begin
(let n = (Support.List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(match ((n <= (Support.List.length bs))) with
| true -> begin
(let _59_608 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_59_608) with
| (targs, rest_args) -> begin
(let expected_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(failwith ("Not enough type binders in the body of the let expression"))
end
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (Support.Prims.pipe_right targs (Support.List.map (fun ( _59_4 ) -> (match (_59_4) with
| (Support.Microsoft.FStar.Util.Inl (a), _59_617) -> begin
a
end
| _59_620 -> begin
(failwith ("Impossible"))
end))))
in (let env = (Support.List.fold_left (fun ( env ) ( a ) -> (Microsoft_FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _68_25350 = (Support.Prims.pipe_right targs (Support.List.map Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_68_25350, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _59_629 -> begin
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
| _59_634 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end
| false -> begin
(failwith ("Not enough type binders"))
end)
end
| _59_637 -> begin
(err_value_restriction e)
end)))
end))
end
| _59_639 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun ( env ) ( _59_654 ) -> (match (_59_654) with
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
in (let lbs = (Support.Prims.pipe_right lbs (Support.List.map maybe_generalize))
in (let _59_683 = (Support.List.fold_right (fun ( lb ) ( _59_664 ) -> (match (_59_664) with
| (env, lbs) -> begin
(let _59_677 = lb
in (match (_59_677) with
| (lbname, _59_667, (t, (_59_670, polytype)), add_unit, _59_676) -> begin
(let _59_680 = (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_59_680) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_59_683) with
| (env_body, lbs) -> begin
(let env_def = (match (is_rec) with
| true -> begin
env_body
end
| false -> begin
g
end)
in (let lbs = (Support.Prims.pipe_right lbs (Support.List.map (check_lb env_def)))
in (let _59_689 = (synth_exp env_body e')
in (match (_59_689) with
| (e', f', t') -> begin
(let f = (let _68_25360 = (let _68_25359 = (Support.List.map Support.Prims.fst lbs)
in (f')::_68_25359)
in (join_l _68_25360))
in (let _68_25364 = (let _68_25363 = (let _68_25362 = (let _68_25361 = (Support.List.map Support.Prims.snd lbs)
in (is_rec, _68_25361))
in (_68_25362, e'))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (_68_25363))
in (_68_25364, f, t')))
end))))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(failwith ("Matches must be checked; missing a compiler-provided annotation"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _59_697))) -> begin
(synth_exp g e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(failwith ("Unexpected expression"))
end)))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( x ) -> (let _59_709 = (Support.Microsoft.FStar.Util.incr c)
in (let _68_25367 = (Support.ST.read c)
in (x, _68_25367)))))

let ind_discriminator_body = (fun ( env ) ( discName ) ( constrName ) -> (let mlid = (fresh "_discr_")
in (let _59_718 = (let _68_25374 = (Microsoft_FStar_Absyn_Util.fv constrName)
in (Microsoft_FStar_Extraction_ML_Env.lookup_fv env _68_25374))
in (match (_59_718) with
| (_59_716, ts) -> begin
(let arg_pat = (match ((Support.Prims.snd ts)) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_59_720) -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[]
end
| _59_723 -> begin
[]
end)
in (let rid = constrName
in (let discrBody = (let _68_25382 = (let _68_25381 = (let _68_25380 = (let _68_25379 = (let _68_25378 = (let _68_25377 = (let _68_25376 = (let _68_25375 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_68_25375, arg_pat))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor (_68_25376))
in (_68_25377, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_68_25378)::((Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (false))))::[])
in (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Extraction_ML_Syntax.idsym mlid))), _68_25379))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Match (_68_25380))
in (((mlid, None))::[], _68_25381))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (_68_25382))
in Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = (Microsoft_FStar_Extraction_ML_Env.convIdent discName.Microsoft_FStar_Absyn_Syntax.ident); Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[])))))
end))))

let dummyPatIdent = (fun ( n ) -> (let _68_25386 = (let _68_25385 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat "dummyPat" _68_25385))
in (_68_25386, 0)))

let dummyPatIdents = (fun ( n ) -> (let _68_25389 = (Microsoft_FStar_Extraction_ML_ExtractTyp.firstNNats n)
in (Support.List.map dummyPatIdent _68_25389)))

let ind_projector_body = (fun ( c ) ( discName ) ( constrName ) -> (let mlid = (fresh "_proj_")
in (let _59_739 = (Microsoft_FStar_Extraction_ML_Env.lookup_fv_by_lid c constrName)
in (match (_59_739) with
| (_59_734, (_59_736, ctype)) -> begin
(let cargs = (Microsoft_FStar_Extraction_ML_ExtractTyp.argTypes ctype)
in (let projs = (dummyPatIdents (Support.List.length cargs))
in (let cargs = (Support.List.map (fun ( x ) -> Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x)) projs)
in (let _59_746 = (Support.List.rev discName.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_59_746) with
| cn::cr -> begin
(let crstr = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) cr)
in (let rid = {Microsoft_FStar_Absyn_Syntax.ns = cr; Microsoft_FStar_Absyn_Syntax.ident = (let _59_749 = discName.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = cn.Microsoft_FStar_Absyn_Syntax.idText; Microsoft_FStar_Absyn_Syntax.idRange = _59_749.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = (Support.String.concat "." crstr); Microsoft_FStar_Absyn_Syntax.str = discName.Microsoft_FStar_Absyn_Syntax.nsstr}
in (let cn = cn.Microsoft_FStar_Absyn_Syntax.idText
in (let discrBody = (let _68_25405 = (let _68_25404 = (let _68_25403 = (let _68_25402 = (let _68_25401 = (let _68_25400 = (let _68_25399 = (let _68_25398 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_68_25398, cargs))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor (_68_25399))
in (_68_25400, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (([], discName.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))))
in (_68_25401)::[])
in (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Extraction_ML_Syntax.idsym mlid))), _68_25402))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Match (_68_25403))
in (((mlid, None))::[], _68_25404))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (_68_25405))
in Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = (Microsoft_FStar_Extraction_ML_Env.convIdent discName.Microsoft_FStar_Absyn_Syntax.ident); Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[]))))))
end)))))
end))))




