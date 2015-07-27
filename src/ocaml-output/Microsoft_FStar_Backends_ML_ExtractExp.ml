
let eff_to_string = (fun ( _54_1 ) -> (match (_54_1) with
| Microsoft_FStar_Backends_ML_Syntax.MayErase -> begin
"MayErase"
end
| Microsoft_FStar_Backends_ML_Syntax.Keep -> begin
"Keep"
end))

let fail = (fun ( r ) ( msg ) -> (let _54_9 = (Support.Microsoft.FStar.Util.print_string (Microsoft_FStar_Absyn_Print.format_error r msg))
in (exit (1))))

let err_uninst = (fun ( e ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos (Support.Microsoft.FStar.Util.format1 "Variable %s has a polymorphic type; expected it to be fully instantiated" (Microsoft_FStar_Absyn_Print.exp_to_string e))))

let err_ill_typed_application = (fun ( e ) ( args ) ( t ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos "Ill-typed application"))

let err_value_restriction = (fun ( e ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos "Refusing to generalize because of the value restriction"))

let err_unexpected_eff = (fun ( e ) ( f0 ) ( f1 ) -> (fail e.Microsoft_FStar_Absyn_Syntax.pos (Support.Microsoft.FStar.Util.format2 "Expected effect %s; got effect %s" (eff_to_string f0) (eff_to_string f1))))

let is_constructor = (fun ( e ) -> (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((_, b)) -> begin
b
end
| _ -> begin
false
end))

let rec is_value = (fun ( e ) -> (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
((is_constructor head) && ((Support.List.for_all (fun ( _54_44 ) -> (match (_54_44) with
| (te, _) -> begin
(match (te) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
true
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(is_value e)
end)
end))) args))
end
| _ -> begin
false
end))

let translate_typ = (fun ( g ) ( t ) -> (Microsoft_FStar_Backends_ML_ExtractTyp.extractTyp g t))

let instantiate = (fun ( s ) ( args ) -> (Microsoft_FStar_Backends_ML_Util.subst s args))

let ml_unit = Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Unit)

let ml_bool_ty = Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (([], ([], "bool")))

let erasable = (fun ( g ) ( f ) ( t ) -> ((f = Microsoft_FStar_Backends_ML_Syntax.MayErase) && (Microsoft_FStar_Backends_ML_Env.erasableType g t)))

let erase = (fun ( g ) ( e ) ( f ) ( t ) -> if (erasable g f t) then begin
(ml_unit, f, Microsoft_FStar_Backends_ML_Env.ml_unit_ty)
end else begin
(e, f, t)
end)

let coerce = (fun ( g ) ( e ) ( t ) ( t' ) -> if (Microsoft_FStar_Backends_ML_Util.equiv g t t') then begin
e
end else begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t'))
end)

let eff_leq = (fun ( f ) ( f' ) -> (match ((f, f')) with
| ((Microsoft_FStar_Backends_ML_Syntax.MayErase, _)) | ((_, Microsoft_FStar_Backends_ML_Syntax.Keep)) -> begin
true
end
| _ -> begin
false
end))

let join = (fun ( f ) ( f' ) -> (match ((f, f')) with
| ((Microsoft_FStar_Backends_ML_Syntax.Keep, _)) | ((_, Microsoft_FStar_Backends_ML_Syntax.Keep)) -> begin
Microsoft_FStar_Backends_ML_Syntax.Keep
end
| _ -> begin
Microsoft_FStar_Backends_ML_Syntax.MayErase
end))

let join_l = (fun ( fs ) -> (Support.List.fold_left join Microsoft_FStar_Backends_ML_Syntax.MayErase fs))

let rec extract_pat = (fun ( g ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::pats) -> begin
(let _54_102 = (extract_pat g p)
in (match (_54_102) with
| (g, p) -> begin
(g, (Microsoft_FStar_Backends_ML_Syntax.MLP_Branch ((Support.List.collect (fun ( x ) -> (Support.Prims.snd (extract_pat g x))) pats)))::[])
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (s) -> begin
(g, (Microsoft_FStar_Backends_ML_Syntax.MLP_Const ((Microsoft_FStar_Backends_ML_Util.mlconst_of_const s)))::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, pats)) -> begin
(let _54_113 = (Microsoft_FStar_Backends_ML_Env.lookup_fv g f)
in (match (_54_113) with
| (d, _) -> begin
(let _54_116 = (Support.Microsoft.FStar.Util.fold_map extract_pat g pats)
in (match (_54_116) with
| (g, pats) -> begin
(g, (Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((d, (Support.List.flatten pats))))::[])
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
(let mlty = (translate_typ g x.Microsoft_FStar_Absyn_Syntax.sort)
in (let g = (Microsoft_FStar_Backends_ML_Env.extend_bv g x ([], mlty))
in (g, (Microsoft_FStar_Backends_ML_Syntax.MLP_Var ((Microsoft_FStar_Backends_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v)))::[])))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) -> begin
(g, (Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)::[])
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) -> begin
(g, [])
end))

let maybe_eta_data = (fun ( isDataCons ) ( residualType ) ( mlAppExpr ) -> (let rec eta_args = (fun ( more_args ) ( t ) -> (match (t) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t0, _, t1)) -> begin
(let x = ((Microsoft_FStar_Absyn_Util.gensym ()), (- (1)))
in (eta_args ((((x, Some (t0)), Microsoft_FStar_Backends_ML_Syntax.MLE_Var (x)))::more_args) t1))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((_, _)) -> begin
(Support.List.rev more_args)
end
| _ -> begin
(failwith "Impossible")
end))
in (let maybe_eta = (fun ( e ) -> (let eargs = (eta_args [] residualType)
in (match (eargs) with
| [] -> begin
e
end
| _ -> begin
(let _54_168 = (Support.List.unzip eargs)
in (match (_54_168) with
| (binders, eargs) -> begin
(match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((head, args)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((binders, Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((head, (Support.List.append args eargs)))))
end
| _ -> begin
(failwith "Impossible")
end)
end))
end)))
in (match ((mlAppExpr, isDataCons)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_App ((Microsoft_FStar_Backends_ML_Syntax.MLE_Name (mlp), mlargs)), true) -> begin
(maybe_eta (Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((mlp, mlargs))))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (mlp), true) -> begin
(maybe_eta (Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((mlp, []))))
end
| _ -> begin
mlAppExpr
end))))

let rec check_exp = (fun ( g ) ( e ) ( f ) ( t ) -> (let _54_197 = (erase g (check_exp' g e f t) f t)
in (match (_54_197) with
| (e, _, _) -> begin
e
end)))
and check_exp' = (fun ( g ) ( e ) ( f ) ( t ) -> (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_match ((scrutinee, pats)) -> begin
(let _54_209 = (synth_exp g scrutinee)
in (match (_54_209) with
| (e, f_e, t_e) -> begin
(let mlbranches = ((Support.List.map (fun ( _54_213 ) -> (match (_54_213) with
| (pat, when_opt, branch) -> begin
(let _54_216 = (extract_pat g pat)
in (match (_54_216) with
| (env, p) -> begin
(let when_opt = (match (when_opt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((check_exp env w Microsoft_FStar_Backends_ML_Syntax.MayErase ml_bool_ty))
end)
in (let branch = (check_exp env branch f t)
in ((Support.List.hd p), when_opt, branch)))
end))
end))) pats)
in if (eff_leq f_e f) then begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((e, mlbranches))
end else begin
(err_unexpected_eff scrutinee f f_e)
end)
end))
end
| _ -> begin
(let _54_228 = (synth_exp g e)
in (match (_54_228) with
| (e0, f0, t0) -> begin
if (eff_leq f0 f) then begin
(coerce g e0 t0 t)
end else begin
(err_unexpected_eff e f f0)
end
end))
end))
and synth_exp = (fun ( g ) ( e ) -> (let _54_234 = (synth_exp' g e)
in (match (_54_234) with
| (e, f, t) -> begin
(erase g e f t)
end)))
and synth_exp' = (fun ( g ) ( e ) -> (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Const ((Microsoft_FStar_Backends_ML_Util.mlconst_of_const c)), Microsoft_FStar_Backends_ML_Syntax.MayErase, (translate_typ g t)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e0, t, f)) -> begin
(let t = (translate_typ g t)
in (let f = (match (f) with
| None -> begin
(failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(Microsoft_FStar_Backends_ML_ExtractTyp.translate_eff g l)
end)
in (let e = (check_exp g e0 f t)
in (e, f, t))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _54_261 = (Microsoft_FStar_Backends_ML_Env.lookup_var g e)
in (match (_54_261) with
| ((x, mltys), is_data) -> begin
(match (mltys) with
| ([], t) -> begin
((maybe_eta_data is_data t x), Microsoft_FStar_Backends_ML_Syntax.MayErase, t)
end
| _ -> begin
(err_uninst e)
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let rec synth_app = (fun ( is_data ) ( _54_275 ) ( _54_278 ) ( restArgs ) -> (match ((_54_275, _54_278)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _) -> begin
(let _54_293 = (Support.List.fold_left (fun ( _54_286 ) ( _54_289 ) -> (match ((_54_286, _54_289)) with
| ((lbs, out_args), (arg, f)) -> begin
if (f = Microsoft_FStar_Backends_ML_Syntax.MayErase) then begin
(lbs, (arg)::out_args)
end else begin
(let x = ((Microsoft_FStar_Absyn_Util.gensym ()), (- (1)))
in (((x, arg))::lbs, (Microsoft_FStar_Backends_ML_Syntax.MLE_Var (x))::out_args))
end
end)) ([], []) mlargs_f)
in (match (_54_293) with
| (lbs, mlargs) -> begin
(let app = ((maybe_eta_data is_data t) (Microsoft_FStar_Backends_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (let l_app = (Support.List.fold_right (fun ( _54_297 ) ( out ) -> (match (_54_297) with
| (x, arg) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((false, ((x, None, [], arg))::[]), out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((Support.Microsoft.FStar.Util.Inl (_), _)::rest, Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((tunit, f', t))) -> begin
if (Microsoft_FStar_Backends_ML_Util.equiv g tunit Microsoft_FStar_Backends_ML_Env.ml_unit_ty) then begin
(synth_app is_data (mlhead, ((ml_unit, Microsoft_FStar_Backends_ML_Syntax.MayErase))::mlargs_f) ((join f f'), t) rest)
end else begin
(failwith "Impossible: ill-typed application")
end
end
| ((Support.Microsoft.FStar.Util.Inr (e0), _)::rest, Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t0, f', t))) -> begin
(let _54_330 = (synth_exp g e0)
in (match (_54_330) with
| (e0, f0, t0') -> begin
(let e0 = (coerce g e0 t0' t0)
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) ((join_l ((f)::(f')::(f0)::[])), t) rest))
end))
end
| _ -> begin
(err_ill_typed_application e restArgs t)
end)
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
(let _54_347 = (Microsoft_FStar_Backends_ML_Env.lookup_var g head)
in (match (_54_347) with
| ((head, (vars, t)), is_data) -> begin
(let n = (Support.List.length vars)
in if (n <= (Support.List.length args)) then begin
(let _54_351 = (Support.Microsoft.FStar.Util.first_N n args)
in (match (_54_351) with
| (prefix, rest) -> begin
(let prefixAsMLTypes = (Support.List.map (Microsoft_FStar_Backends_ML_ExtractTyp.getTypeFromArg g) prefix)
in (let t = (instantiate (vars, t) prefixAsMLTypes)
in (match (rest) with
| [] -> begin
(head, Microsoft_FStar_Backends_ML_Syntax.MayErase, t)
end
| _ -> begin
(synth_app is_data (head, []) (Microsoft_FStar_Backends_ML_Syntax.MayErase, t) rest)
end)))
end))
end else begin
(err_uninst e)
end)
end))
end
| _ -> begin
(let _54_362 = (synth_exp g head)
in (match (_54_362) with
| (head, f, t) -> begin
(synth_app false (head, []) (f, t) args)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _54_385 = (Support.List.fold_left (fun ( _54_369 ) ( _54_373 ) -> (match ((_54_369, _54_373)) with
| ((ml_bs, env), (b, _)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let env = (Microsoft_FStar_Backends_ML_Env.extend_ty env a (Some (Microsoft_FStar_Backends_ML_Syntax.MLTY_Top)))
in (let ml_b = ((Microsoft_FStar_Backends_ML_Env.btvar_as_mlident a), ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) Microsoft_FStar_Backends_ML_Env.ml_unit_ty))
in ((ml_b)::ml_bs, env)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (translate_typ env x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env = (Microsoft_FStar_Backends_ML_Env.extend_bv env x ([], t))
in (let ml_b = ((Microsoft_FStar_Backends_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v), Some (t))
in ((ml_b)::ml_bs, env))))
end)
end)) ([], g) bs)
in (match (_54_385) with
| (ml_bs, env) -> begin
(let ml_bs = (Support.List.rev ml_bs)
in (let _54_390 = (synth_exp env body)
in (match (_54_390) with
| (ml_body, f, t) -> begin
(let _54_400 = (Support.List.fold_right (fun ( _54_394 ) ( _54_397 ) -> (match ((_54_394, _54_397)) with
| ((_, targ), (f, t)) -> begin
(Microsoft_FStar_Backends_ML_Syntax.MayErase, Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun (((Support.Microsoft.FStar.Util.must targ), f, t)))
end)) ml_bs (f, t))
in (match (_54_400) with
| (f, tfun) -> begin
(Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ml_bs, ml_body)), f, tfun)
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), e')) -> begin
(let maybe_generalize = (fun ( _54_412 ) -> (match (_54_412) with
| {Microsoft_FStar_Absyn_Syntax.lbname = lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = lbeff; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let f_e = (Microsoft_FStar_Backends_ML_ExtractTyp.translate_eff g lbeff)
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) when (Microsoft_FStar_Backends_ML_Util.is_type_abstraction bs) -> begin
(let _54_436 = (match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _54_2 ) -> (match (_54_2) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| _ -> begin
false
end)) bs)) with
| None -> begin
(bs, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| Some ((bs, b, rest)) -> begin
(bs, (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Microsoft_FStar_Backends_ML_Util.unit_binder)::(b)::rest, c) None c.Microsoft_FStar_Absyn_Syntax.pos))
end)
in (match (_54_436) with
| (tbinders, tbody) -> begin
(let n = (Support.List.length tbinders)
in (let e = (Microsoft_FStar_Absyn_Util.unascribe e)
in (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
if (n <= (Support.List.length bs)) then begin
(let _54_445 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_54_445) with
| (targs, rest_args) -> begin
(let expected_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder targs tbinders)) with
| None -> begin
(failwith "Not enough type binders in the body of the let expression")
end
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tbody)
end)
in (let targs = ((Support.List.map (fun ( _54_3 ) -> (match (_54_3) with
| (Support.Microsoft.FStar.Util.Inl (a), _) -> begin
a
end
| _ -> begin
(failwith "Impossible")
end))) targs)
in (let env = (Support.List.fold_left (fun ( env ) ( a ) -> (Microsoft_FStar_Backends_ML_Env.extend_ty env a None)) g targs)
in (let expected_t = (translate_typ env expected_t)
in (let polytype = (((Support.List.map Microsoft_FStar_Backends_ML_Env.btvar_as_mlident) targs), expected_t)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs ((Microsoft_FStar_Backends_ML_Util.unit_binder)::rest_args, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (lbname, f_e, (t, (targs, polytype)), body)))))))
end))
end else begin
(failwith "Not enough type binders")
end
end
| _ -> begin
(err_value_restriction e)
end)))
end))
end
| _ -> begin
(let expected_t = (translate_typ g t)
in (lbname, f_e, (t, ([], ([], expected_t))), e))
end)))
end))
in (let check_lb = (fun ( env ) ( _54_482 ) -> (match (_54_482) with
| (nm, (lbname, f, (t, (targs, polytype)), e)) -> begin
(let env = (Support.List.fold_left (fun ( env ) ( a ) -> (Microsoft_FStar_Backends_ML_Env.extend_ty env a None)) env targs)
in (let e = (check_exp env e f (Support.Prims.snd polytype))
in (f, (nm, Some (polytype), [], e))))
end))
in (let lbs = ((Support.List.map maybe_generalize) lbs)
in (let _54_509 = (Support.List.fold_right (fun ( lb ) ( _54_491 ) -> (match (_54_491) with
| (env, lbs) -> begin
(let _54_503 = lb
in (match (_54_503) with
| (lbname, _, (t, (_, polytype)), _) -> begin
(let _54_506 = (Microsoft_FStar_Backends_ML_Env.extend_lb env lbname t polytype)
in (match (_54_506) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_54_509) with
| (env_body, lbs) -> begin
(let env_def = if is_rec then begin
env_body
end else begin
g
end
in (let lbs = ((Support.List.map (check_lb env_def)) lbs)
in (let _54_515 = (synth_exp env_body e')
in (match (_54_515) with
| (e', f', t') -> begin
(let f = (join_l ((f')::(Support.List.map (Support.Prims.fst) lbs)))
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((is_rec, (Support.List.map (Support.Prims.snd) lbs)), e')), f', t'))
end))))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(failwith "Matches must be checked; missing a compiler-provided annotation")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(synth_exp g e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_delayed (_)) -> begin
(failwith "Unexpected expression")
end))




