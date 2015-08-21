
let eff_to_string = (fun ( _61_1 ) -> (match (_61_1) with
| Microsoft_FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))

let fail = (fun ( r ) ( msg ) -> (let _61_10 = (let _125_5 = (Microsoft_FStar_Absyn_Print.format_error r msg)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _125_5))
in (Support.All.exit 1)))

let err_uninst = (fun ( e ) -> (let _125_8 = (let _125_7 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" _125_7))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _125_8)))

let err_ill_typed_application = (fun ( e ) ( args ) ( t ) -> (let _125_14 = (let _125_13 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _125_12 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _125_13 _125_12)))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _125_14)))

let err_value_restriction = (fun ( e ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun ( e ) ( f0 ) ( f1 ) -> (let _125_20 = (let _125_19 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "for expression %s, Expected effect %s; got effect %s" _125_19 (eff_to_string f0) (eff_to_string f1)))
in (fail e.Microsoft_FStar_Absyn_Syntax.pos _125_20)))

let is_constructor = (fun ( e ) -> (match ((let _125_23 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _125_23.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)))) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_))))) -> begin
true
end
| _61_36 -> begin
false
end))

let rec is_value_or_type_app = (fun ( e ) -> (match ((let _125_26 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _125_26.Microsoft_FStar_Absyn_Syntax.n)) with
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
(match ((let _125_28 = (Microsoft_FStar_Absyn_Util.compress_exp head)
in _125_28.Microsoft_FStar_Absyn_Syntax.n)) with
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

let translate_typ = (fun ( g ) ( t ) -> (let _125_37 = (Microsoft_FStar_Extraction_ML_ExtractTyp.extractTyp g t)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep g _125_37)))

let translate_typ_of_arg = (fun ( g ) ( a ) -> (let _125_42 = (Microsoft_FStar_Extraction_ML_ExtractTyp.getTypeFromArg g a)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep g _125_42)))

let instantiate = (fun ( s ) ( args ) -> (Microsoft_FStar_Extraction_ML_Util.subst s args))

let erasable = (fun ( g ) ( f ) ( t ) -> ((f = Microsoft_FStar_Extraction_ML_Syntax.E_PURE) && (Microsoft_FStar_Extraction_ML_Util.erasableType g t)))

let erase = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((erasable g f t)) with
| true -> begin
(let _61_137 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( _61_136 ) -> (match (()) with
| () -> begin
(let _125_63 = (Microsoft_FStar_Extraction_OCaml_Code.string_of_mlexpr g e)
in (let _125_62 = (Microsoft_FStar_Extraction_OCaml_Code.string_of_mlty g t)
in (Support.Microsoft.FStar.Util.fprint2 "Erasing %s at type %s\n" _125_63 _125_62)))
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
(let _125_101 = (let _125_100 = (let _125_99 = (let _125_98 = (Support.List.collect (fun ( x ) -> (let _125_97 = (extract_pat true false g x)
in (Support.Prims.snd _125_97))) pats)
in (Support.List.append p _125_98))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (_125_99))
in (_125_100)::[])
in (g, _125_101))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (s) -> begin
(let _125_104 = (let _125_103 = (let _125_102 = (Microsoft_FStar_Extraction_ML_Util.mlconst_of_const s)
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (_125_102))
in (_125_103)::[])
in (g, _125_104))
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
in (let _125_110 = (let _125_109 = (Support.All.pipe_left (Microsoft_FStar_Extraction_ML_Util.resugar_pat q) (Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((d, (Support.List.flatten mlPats)))))
in (_125_109)::[])
in (g, _125_110)))
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

let ffi_mltuple_mlp = (fun ( n ) -> (let name = (match (((2 < n) && (n < 6))) with
| true -> begin
(let _125_119 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat "mktuple" _125_119))
end
| false -> begin
(match ((n = 2)) with
| true -> begin
"mkpair"
end
| false -> begin
(Support.All.failwith "NYI in runtime/allocator/camlstack.mli")
end)
end)
in (("Camlstack")::[], name)))

let fix_lalloc = (fun ( arg ) -> (match (arg) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (args) -> begin
(Support.All.failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((mlns, fields)) -> begin
(let args = (Support.List.map Support.Prims.snd fields)
in (let tup = (let _125_124 = (let _125_123 = (let _125_122 = (ffi_mltuple_mlp (Support.List.length args))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (_125_122))
in (_125_123, args))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_App (_125_124))
in (let dummyTy = Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((tup, dummyTy, dummyTy)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, args)) -> begin
(Support.All.failwith "NYI: lalloc ctor")
end
| _61_273 -> begin
(Support.All.failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap.")
end))

let maybe_lalloc_eta_data = (fun ( g ) ( qual ) ( residualType ) ( mlAppExpr ) -> (let rec eta_args = (fun ( more_args ) ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t0, _61_283, t1)) -> begin
(let x = (let _125_137 = (Microsoft_FStar_Absyn_Util.gensym ())
in (_125_137, (- (1))))
in (eta_args ((((x, Some (t0)), Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x)))::more_args) t1))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((_61_289, _61_291)) -> begin
(Support.List.rev more_args)
end
| _61_295 -> begin
(Support.All.failwith "Impossible")
end))
in (let as_record = (fun ( qual ) ( e ) -> (match ((e, qual)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((_61_300, args)), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((_61_305, fields)))) -> begin
(let path = (Microsoft_FStar_Extraction_ML_Util.record_field_path fields)
in (let fields = (Microsoft_FStar_Extraction_ML_Util.record_fields fields args)
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))
end
| _61_314 -> begin
e
end))
in (let resugar_and_maybe_eta = (fun ( qual ) ( e ) -> (let eargs = (eta_args [] residualType)
in (match (eargs) with
| [] -> begin
(let _125_146 = (as_record qual e)
in (Microsoft_FStar_Extraction_ML_Util.resugar_exp _125_146))
end
| _61_321 -> begin
(let _61_324 = (Support.List.unzip eargs)
in (match (_61_324) with
| (binders, eargs) -> begin
(match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((head, args)) -> begin
(let body = (let _125_147 = (Support.All.pipe_left (as_record qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((head, (Support.List.append args eargs)))))
in (Support.All.pipe_left Microsoft_FStar_Extraction_ML_Util.resugar_exp _125_147))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))
end
| _61_331 -> begin
(Support.All.failwith "Impossible")
end)
end))
end)))
in (match ((mlAppExpr, qual)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlarg::[])), _61_339) when (mlp = Microsoft_FStar_Extraction_ML_Syntax.mlp_lalloc) -> begin
(let _61_342 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( _61_341 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.print_string "need to do lalloc surgery here\n")
end)))
in (fix_lalloc mlarg))
end
| (_61_345, None) -> begin
mlAppExpr
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mle::args)), Some (Microsoft_FStar_Absyn_Syntax.Record_projector (f))) -> begin
(let fn = (Microsoft_FStar_Extraction_ML_Util.mlpath_of_lid f)
in (let proj = Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (match (args) with
| [] -> begin
proj
end
| _61_363 -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((proj, args))
end)))
end
| ((Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs)), Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) | ((Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), mlargs)), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(Support.All.pipe_left (resugar_and_maybe_eta qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
end
| ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) | ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))) -> begin
(Support.All.pipe_left (resugar_and_maybe_eta qual) (Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
end
| _61_392 -> begin
mlAppExpr
end)))))

let rec check_exp = (fun ( g ) ( e ) ( f ) ( t ) -> (let _61_402 = (let _125_165 = (check_exp' g e f t)
in (erase g _125_165 f t))
in (match (_61_402) with
| (e, _61_399, _61_401) -> begin
e
end)))
and check_exp' = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((let _125_170 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _125_170.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_match ((scrutinee, pats)) -> begin
(let _61_414 = (synth_exp g scrutinee)
in (match (_61_414) with
| (e, f_e, t_e) -> begin
(let mlbranches = (Support.All.pipe_right pats (Support.List.map (fun ( _61_418 ) -> (match (_61_418) with
| (pat, when_opt, branch) -> begin
(let _61_421 = (extract_pat g pat)
in (match (_61_421) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _125_172 = (check_exp env w Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE Microsoft_FStar_Extraction_ML_Syntax.ml_bool_ty)
in Some (_125_172))
end)
in (let branch = (check_exp env branch f t)
in (let _125_173 = (Support.List.hd p)
in (_125_173, when_opt, branch))))
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
| _61_429 -> begin
(let _61_433 = (synth_exp g e)
in (match (_61_433) with
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
and synth_exp = (fun ( g ) ( e ) -> (let _61_439 = (synth_exp' g e)
in (match (_61_439) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun ( g ) ( e ) -> (let _61_443 = (Microsoft_FStar_Extraction_ML_Env.debug g (fun ( u ) -> (let _125_180 = (let _125_179 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "now synthesizing expression :  %s \n" _125_179))
in (Support.Microsoft.FStar.Util.print_string _125_180))))
in (match ((let _125_181 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _125_181.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (let _125_185 = (let _125_183 = (Microsoft_FStar_Extraction_ML_Util.mlconst_of_const c)
in (Support.All.pipe_left (fun ( _125_182 ) -> Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (_125_182)) _125_183))
in (let _125_184 = (translate_typ g t)
in (_125_185, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _125_184))))
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
(let _61_469 = (Microsoft_FStar_Extraction_ML_Env.lookup_var g e)
in (match (_61_469) with
| ((x, mltys), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _125_186 = (maybe_lalloc_eta_data g qual t x)
in (_125_186, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _61_474 -> begin
(err_uninst e)
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let rec synth_app = (fun ( is_data ) ( _61_483 ) ( _61_486 ) ( restArgs ) -> (match ((_61_483, _61_486)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _61_490) -> begin
(let _61_501 = (match ((Microsoft_FStar_Absyn_Util.is_primop head)) with
| true -> begin
(let _125_195 = (Support.All.pipe_right (Support.List.rev mlargs_f) (Support.List.map Support.Prims.fst))
in ([], _125_195))
end
| false -> begin
(Support.List.fold_left (fun ( _61_494 ) ( _61_497 ) -> (match ((_61_494, _61_497)) with
| ((lbs, out_args), (arg, f)) -> begin
(match ((f = Microsoft_FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(lbs, (arg)::out_args)
end
| false -> begin
(let x = (let _125_198 = (Microsoft_FStar_Absyn_Util.gensym ())
in (_125_198, (- (1))))
in (((x, arg))::lbs, (Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x))::out_args))
end)
end)) ([], []) mlargs_f)
end)
in (match (_61_501) with
| (lbs, mlargs) -> begin
(let app = (Support.All.pipe_left (maybe_lalloc_eta_data g is_data t) (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (let l_app = (Support.List.fold_right (fun ( _61_505 ) ( out ) -> (match (_61_505) with
| (x, arg) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = x; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = arg})::[]), out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((Support.Microsoft.FStar.Util.Inl (_61_510), _61_513)::rest, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tunit, f', t))) -> begin
(match ((Microsoft_FStar_Extraction_ML_Util.equiv g tunit Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
(synth_app is_data (mlhead, ((Microsoft_FStar_Extraction_ML_Syntax.ml_unit, Microsoft_FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) ((join f f'), t) rest)
end
| false -> begin
(Support.All.failwith "Impossible: ill-typed application")
end)
end
| ((Support.Microsoft.FStar.Util.Inr (e0), _61_526)::rest, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tExpected, f', t))) -> begin
(let _61_538 = (synth_exp g e0)
in (match (_61_538) with
| (e0, f0, tInferred) -> begin
(let e0 = (maybe_coerce g e0 tInferred f' tExpected)
in (let _125_202 = (let _125_201 = (join_l ((f)::(f')::(f0)::[]))
in (_125_201, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _125_202 rest)))
end))
end
| _61_541 -> begin
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
(let _61_558 = (Microsoft_FStar_Extraction_ML_Env.lookup_var g head)
in (match (_61_558) with
| ((head, (vars, t)), qual) -> begin
(let n = (Support.List.length vars)
in (match ((n <= (Support.List.length args))) with
| true -> begin
(let _61_562 = (Support.Microsoft.FStar.Util.first_N n args)
in (match (_61_562) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (Support.List.map (translate_typ_of_arg g) prefix)
in (let t0 = t
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (match (rest) with
| [] -> begin
(let _125_203 = (maybe_lalloc_eta_data g qual t head)
in (_125_203, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _61_568 -> begin
(synth_app qual (head, []) (Microsoft_FStar_Extraction_ML_Syntax.E_PURE, t) rest)
end))))
end))
end
| false -> begin
(err_uninst e)
end))
end))
end
| _61_570 -> begin
(let _61_574 = (synth_exp g head)
in (match (_61_574) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _61_597 = (Support.List.fold_left (fun ( _61_581 ) ( _61_585 ) -> (match ((_61_581, _61_585)) with
| ((ml_bs, env), (b, _61_584)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let env = (Microsoft_FStar_Extraction_ML_Env.extend_ty env a (Some (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top)))
in (let ml_b = (let _125_208 = (Microsoft_FStar_Extraction_ML_Env.btvar_as_mlTermVar a)
in (let _125_207 = (Support.All.pipe_left (fun ( _125_206 ) -> Some (_125_206)) Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)
in (_125_208, _125_207)))
in ((ml_b)::ml_bs, env)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (translate_typ env x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env = (Microsoft_FStar_Extraction_ML_Env.extend_bv env x ([], t) false false)
in (let ml_b = ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v), Some (t))
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_61_597) with
| (ml_bs, env) -> begin
(let ml_bs = (Support.List.rev ml_bs)
in (let _61_602 = (synth_exp env body)
in (match (_61_602) with
| (ml_body, f, t) -> begin
(let _61_612 = (Support.List.fold_right (fun ( _61_606 ) ( _61_609 ) -> (match ((_61_606, _61_609)) with
| ((_61_604, targ), (f, t)) -> begin
(let _125_213 = (let _125_212 = (let _125_211 = (Support.Microsoft.FStar.Util.must targ)
in (_125_211, f, t))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_125_212))
in (Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _125_213))
end)) ml_bs (f, t))
in (match (_61_612) with
| (f, tfun) -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body)), f, tfun)
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), e')) -> begin
(let maybe_generalize = (fun ( _61_624 ) -> (match (_61_624) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = lbeff; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (Microsoft_FStar_Extraction_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) when (Microsoft_FStar_Extraction_ML_Util.is_type_abstraction bs) -> begin
(let _61_648 = (match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _61_3 ) -> (match (_61_3) with
| (Support.Microsoft.FStar.Util.Inr (_61_633), _61_636) -> begin
true
end
| _61_639 -> begin
false
end)) bs)) with
| None -> begin
(bs, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| Some ((bs, b, rest)) -> begin
(let _125_217 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((b)::rest, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _125_217))
end)
in (match (_61_648) with
| (tbinders, tbody) -> begin
(let n = (Support.List.length tbinders)
in (let e = (normalize_abs e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(match ((n <= (Support.List.length bs))) with
| true -> begin
(let _61_657 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_61_657) with
| (targs, rest_args) -> begin
(let expected_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(Support.All.failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = (Support.All.pipe_right targs (Support.List.map (fun ( _61_4 ) -> (match (_61_4) with
| (Support.Microsoft.FStar.Util.Inl (a), _61_666) -> begin
a
end
| _61_669 -> begin
(Support.All.failwith "Impossible")
end))))
in (let env = (Support.List.fold_left (fun ( env ) ( a ) -> (Microsoft_FStar_Extraction_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (let _125_221 = (Support.All.pipe_right targs (Support.List.map Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar))
in (_125_221, expected_t))
in (let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_value_or_type_app body)))
end
| _61_678 -> begin
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
| _61_683 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest_args, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body)))))))))
end))
end
| false -> begin
(Support.All.failwith "Not enough type binders")
end)
end
| _61_686 -> begin
(err_value_restriction e)
end)))
end))
end
| _61_688 -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (let check_lb = (fun ( env ) ( _61_703 ) -> (match (_61_703) with
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
in (let _61_732 = (Support.List.fold_right (fun ( lb ) ( _61_713 ) -> (match (_61_713) with
| (env, lbs) -> begin
(let _61_726 = lb
in (match (_61_726) with
| (lbname, _61_716, (t, (_61_719, polytype)), add_unit, _61_725) -> begin
(let _61_729 = (Microsoft_FStar_Extraction_ML_Env.extend_lb env lbname t polytype add_unit)
in (match (_61_729) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_61_732) with
| (env_body, lbs) -> begin
(let env_def = (match (is_rec) with
| true -> begin
env_body
end
| false -> begin
g
end)
in (let lbs = (Support.All.pipe_right lbs (Support.List.map (check_lb env_def)))
in (let _61_738 = (synth_exp env_body e')
in (match (_61_738) with
| (e', f', t') -> begin
(let f = (let _125_231 = (let _125_230 = (Support.List.map Support.Prims.fst lbs)
in (f')::_125_230)
in (join_l _125_231))
in (let _125_235 = (let _125_234 = (let _125_233 = (let _125_232 = (Support.List.map Support.Prims.snd lbs)
in (is_rec, _125_232))
in (_125_233, e'))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (_125_234))
in (_125_235, f, t')))
end))))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(Support.All.failwith "Matches must be checked; missing a compiler-provided annotation")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _61_746))) -> begin
(synth_exp g e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(Support.All.failwith "Unexpected expression")
end)))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( x ) -> (let _61_758 = (Support.Microsoft.FStar.Util.incr c)
in (let _125_238 = (Support.ST.read c)
in (x, _125_238)))))

let ind_discriminator_body = (fun ( env ) ( discName ) ( constrName ) -> (let mlid = (fresh "_discr_")
in (let _61_767 = (let _125_245 = (Microsoft_FStar_Absyn_Util.fv constrName)
in (Microsoft_FStar_Extraction_ML_Env.lookup_fv env _125_245))
in (match (_61_767) with
| (_61_765, ts) -> begin
(let arg_pat = (match ((Support.Prims.snd ts)) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_61_769) -> begin
(Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild)::[]
end
| _61_772 -> begin
[]
end)
in (let rid = constrName
in (let discrBody = (let _125_253 = (let _125_252 = (let _125_251 = (let _125_250 = (let _125_249 = (let _125_248 = (let _125_247 = (let _125_246 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident rid)
in (_125_246, arg_pat))
in Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor (_125_247))
in (_125_248, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_125_249)::((Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild, None, Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (false))))::[])
in (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Extraction_ML_Syntax.idsym mlid))), _125_250))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Match (_125_251))
in (((mlid, None))::[], _125_252))
in Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (_125_253))
in Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((false, ({Microsoft_FStar_Extraction_ML_Syntax.mllb_name = (Microsoft_FStar_Extraction_ML_Env.convIdent discName.Microsoft_FStar_Absyn_Syntax.ident); Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = discrBody})::[])))))
end))))

let dummyPatIdent = (fun ( n ) -> (let _125_257 = (let _125_256 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat "dummyPat" _125_256))
in (_125_257, 0)))

let dummyPatIdents = (fun ( n ) -> (let _125_260 = (Microsoft_FStar_Extraction_ML_ExtractTyp.firstNNats n)
in (Support.List.map dummyPatIdent _125_260)))




