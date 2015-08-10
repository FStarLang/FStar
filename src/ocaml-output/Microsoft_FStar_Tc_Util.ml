
let try_solve = (fun ( env ) ( f ) -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun ( env ) ( errs ) -> (let _70_16418 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16417 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _70_16418 _70_16417))))

let discharge_guard = (fun ( env ) ( g ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env ) ( g ) -> (discharge_guard env g))

let syn' = (fun ( env ) ( k ) -> (let _70_16437 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _70_16437 k)))

let is_xvar_free = (fun ( x ) ( t ) -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) f.Microsoft_FStar_Absyn_Syntax.fxvs)))

let is_tvar_free = (fun ( a ) ( t ) -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun) f.Microsoft_FStar_Absyn_Syntax.ftvs)))

let check_and_ascribe = (fun ( env ) ( e ) ( t1 ) ( t2 ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let check = (fun ( env ) ( t1 ) ( t2 ) -> (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(Microsoft_FStar_Tc_Rel.try_teq env t1 t2)
end
| false -> begin
(match ((Microsoft_FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _70_16461 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.All.pipe_left (fun ( _70_16460 ) -> Some (_70_16460)) _70_16461))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _70_16465 = (let _70_16464 = (let _70_16463 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _70_16462 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_16463, _70_16462)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16464))
in (raise (_70_16465)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _70_16469 = (let _70_16468 = (let _70_16467 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _70_16466 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_16467, _70_16466)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16468))
in (raise (_70_16469)))
end
| Some (g) -> begin
(let _37_51 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16470 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _70_16470))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t2) (Some (t2)) e.Microsoft_FStar_Absyn_Syntax.pos)
end
| _37_57 -> begin
(let _37_58 = e
in (let _70_16471 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _37_58.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _70_16471; Microsoft_FStar_Absyn_Syntax.pos = _37_58.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _37_58.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _37_58.Microsoft_FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end))))

let env_binders = (fun ( env ) -> (match ((Support.ST.read Microsoft_FStar_Options.full_context_dependency)) with
| true -> begin
(Microsoft_FStar_Tc_Env.binders env)
end
| false -> begin
(Microsoft_FStar_Tc_Env.t_binders env)
end))

let as_uvar_e = (fun ( _37_1 ) -> (match (_37_1) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _37_73)); Microsoft_FStar_Absyn_Syntax.tk = _37_70; Microsoft_FStar_Absyn_Syntax.pos = _37_68; Microsoft_FStar_Absyn_Syntax.fvs = _37_66; Microsoft_FStar_Absyn_Syntax.uvs = _37_64} -> begin
uv
end
| _37_78 -> begin
(Support.All.failwith "Impossible")
end))

let as_uvar_t = (fun ( t ) -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _37_90)); Microsoft_FStar_Absyn_Syntax.tk = _37_87; Microsoft_FStar_Absyn_Syntax.pos = _37_85; Microsoft_FStar_Absyn_Syntax.fvs = _37_83; Microsoft_FStar_Absyn_Syntax.uvs = _37_81} -> begin
uv
end
| _37_95 -> begin
(Support.All.failwith "Impossible")
end))

let new_kvar = (fun ( env ) -> (let _70_16481 = (let _70_16480 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16479 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _70_16480 _70_16479)))
in (Support.All.pipe_right _70_16481 Support.Prims.fst)))

let new_tvar = (fun ( env ) ( k ) -> (let _70_16488 = (let _70_16487 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16486 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _70_16487 _70_16486 k)))
in (Support.All.pipe_right _70_16488 Support.Prims.fst)))

let new_evar = (fun ( env ) ( t ) -> (let _70_16495 = (let _70_16494 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16493 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _70_16494 _70_16493 t)))
in (Support.All.pipe_right _70_16495 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env ) ( k ) -> (let _37_105 = (let _70_16501 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16500 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _70_16501 _70_16500 k)))
in (match (_37_105) with
| (t, u) -> begin
(let _70_16503 = (let _70_16502 = (as_uvar_t u)
in (_70_16502, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _70_16503))
end)))

let new_implicit_evar = (fun ( env ) ( t ) -> (let _37_110 = (let _70_16509 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16508 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _70_16509 _70_16508 t)))
in (match (_37_110) with
| (e, u) -> begin
(let _70_16511 = (let _70_16510 = (as_uvar_e u)
in (_70_16510, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _70_16511))
end)))

let force_tk = (fun ( s ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _70_16514 = (let _70_16513 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _70_16513))
in (Support.All.failwith _70_16514))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args ) -> (Support.All.pipe_right args (Support.List.map (fun ( _37_2 ) -> (match (_37_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _70_16519 = (let _70_16518 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_70_16518))
in (_70_16519, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _70_16521 = (let _70_16520 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_70_16520))
in (_70_16521, imp))
end)))))

let is_implicit = (fun ( _37_3 ) -> (match (_37_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _37_129 -> begin
false
end))

let destruct_arrow_kind = (fun ( env ) ( tt ) ( k ) ( args ) -> (let ktop = (let _70_16532 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.All.pipe_right _70_16532 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_37_145, qual)::_37_143 -> begin
(is_implicit qual)
end
| _37_150 -> begin
false
end)
in (let rec mk_implicits = (fun ( vars ) ( subst ) ( bs ) -> (match (bs) with
| b::brest -> begin
(match ((Support.All.pipe_right (Support.Prims.snd b) is_implicit)) with
| true -> begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_16545 = (let _70_16542 = (let _70_16541 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _70_16541))
in (Support.All.pipe_right _70_16542 Support.Prims.fst))
in (Support.All.pipe_right _70_16545 (fun ( x ) -> (let _70_16544 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _70_16544)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_16550 = (let _70_16547 = (let _70_16546 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _70_16546))
in (Support.All.pipe_right _70_16547 Support.Prims.fst))
in (Support.All.pipe_right _70_16550 (fun ( x ) -> (let _70_16549 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _70_16549)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _70_16551 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_70_16551)::subst)
end)
in (let _37_169 = (mk_implicits vars subst brest)
in (match (_37_169) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _70_16552 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _70_16552))
end)
end
| _37_171 -> begin
(let _70_16553 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _70_16553))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _37_174 = (let _70_16554 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _70_16554 [] bs))
in (match (_37_174) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_37_176, k)) -> begin
(aux k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_37_181) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _70_16555 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.All.pipe_right _70_16555 Support.Prims.fst))
in (let bs = (let _70_16556 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _70_16556))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _37_188 = (let _70_16557 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.All.pipe_left (force_trivial env) _70_16557))
in ([], bs, kres)))))))
end
| _37_191 -> begin
(let _70_16560 = (let _70_16559 = (let _70_16558 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_70_16558, r))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16559))
in (raise (_70_16560)))
end))
in (aux ktop)))))

let as_imp = (fun ( _37_4 ) -> (match (_37_4) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _37_196 -> begin
false
end))

let pat_as_exps = (fun ( allow_implicits ) ( env ) ( p ) -> (let pvar_eq = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_205)), Microsoft_FStar_Tc_Env.Binding_var ((y, _37_210))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_216)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _37_221))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _37_226 -> begin
false
end))
in (let vars_of_bindings = (fun ( bs ) -> (Support.All.pipe_right bs (Support.List.map (fun ( _37_5 ) -> (match (_37_5) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _37_232)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_237)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _37_241 -> begin
(Support.All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _37_248)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _37_254 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_37_254) with
| (e, u) -> begin
(let p = (let _37_255 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _37_255.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_255.Microsoft_FStar_Absyn_Syntax.p})
in ([], [], [], env, Support.Microsoft.FStar.Util.Inr (e), p))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _37_260)) -> begin
(let k = (new_kvar env)
in (let _37_266 = (let _70_16582 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _70_16582 k))
in (match (_37_266) with
| (t, u) -> begin
(let p = (let _37_267 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _37_267.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_267.Microsoft_FStar_Absyn_Syntax.p})
in ([], [], [], env, Support.Microsoft.FStar.Util.Inl (t), p))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in ([], [], [], env, Support.Microsoft.FStar.Util.Inr (e), p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _70_16584 = (let _70_16583 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_16583))
in Microsoft_FStar_Tc_Env.Binding_var (_70_16584))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, Support.Microsoft.FStar.Util.Inr (e), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let b = (let _70_16586 = (let _70_16585 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_16585))
in Microsoft_FStar_Tc_Env.Binding_var (_70_16586))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, Support.Microsoft.FStar.Util.Inr (e), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _70_16588 = (let _70_16587 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_16587))
in Microsoft_FStar_Tc_Env.Binding_typ (_70_16588))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, Support.Microsoft.FStar.Util.Inl (t), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _70_16590 = (let _70_16589 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_16589))
in Microsoft_FStar_Tc_Env.Binding_typ (_70_16590))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, Support.Microsoft.FStar.Util.Inl (t), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _37_326 = (Support.All.pipe_right pats (Support.List.fold_left (fun ( _37_304 ) ( _37_307 ) -> (match ((_37_304, _37_307)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _37_314 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_37_314) with
| (b', a', w', env, te, pat) -> begin
(let arg = (match (te) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(match (imp) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.itarg t)
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(match (imp) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.ivarg e)
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end)
end)
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_37_326) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _70_16598 = (let _70_16597 = (let _70_16596 = (let _70_16595 = (let _70_16594 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_16593 = (Support.All.pipe_right args Support.List.rev)
in (_70_16594, _70_16593)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _70_16595 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_70_16596, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_16597))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _70_16598))
in (let _70_16601 = (Support.All.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _70_16600 = (Support.All.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _70_16599 = (Support.All.pipe_right (Support.List.rev w) Support.List.flatten)
in (_70_16601, _70_16600, _70_16599, env, Support.Microsoft.FStar.Util.Inr (e), (let _37_328 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _37_328.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_328.Microsoft_FStar_Absyn_Syntax.p}))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_37_331) -> begin
(Support.All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let pats = (Support.List.map (fun ( _37_343 ) -> (match (_37_343) with
| (p, imp) -> begin
(let _70_16607 = (elaborate_pat env p)
in (_70_16607, imp))
end)) pats)
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env fv.Microsoft_FStar_Absyn_Syntax.v)
in (let pats = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _37_349 -> begin
(let _70_16610 = (let _70_16609 = (let _70_16608 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _70_16608))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16609))
in (raise (_70_16610)))
end)
end
| Some ((f, _37_352)) -> begin
(let rec aux = (fun ( formals ) ( pats ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _37_365::_37_363) -> begin
(let _70_16617 = (let _70_16616 = (let _70_16615 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _70_16615))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16616))
in (raise (_70_16617)))
end
| (_37_371::_37_369, []) -> begin
(Support.All.pipe_right formals (Support.List.map (fun ( f ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let a = (let _70_16619 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_16619 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _70_16621 = (let _70_16620 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _70_16620))
in (_70_16621, (as_imp imp)))
end
| false -> begin
(let _70_16623 = (let _70_16622 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _70_16622))
in (_70_16623, (as_imp imp)))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_37_382), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _70_16625 = (let _70_16624 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var (a)) None _70_16624))
in (_70_16625, true)))
end
| _37_389 -> begin
(let _70_16630 = (let _70_16629 = (let _70_16628 = (let _70_16626 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _70_16626))
in (let _70_16627 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_70_16628, _70_16627)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16629))
in (raise (_70_16630)))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), imp), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), imp), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _70_16631 = (aux formals' pats')
in ((p, (as_imp imp)))::_70_16631)
end
| ((Support.Microsoft.FStar.Util.Inl (_37_417), imp), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_422)) when allow_implicits -> begin
(let _70_16632 = (aux formals' pats')
in ((p, (as_imp imp)))::_70_16632)
end
| ((Support.Microsoft.FStar.Util.Inl (_37_426), imp), _37_431) -> begin
(let a = (let _70_16633 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_16633 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _70_16634 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _70_16634))
end
| false -> begin
(let _70_16635 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _70_16635))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_436) -> begin
pats'
end
| _37_439 -> begin
pats
end)
in (let _70_16636 = (aux formals' pats')
in ((p1, (as_imp imp)))::_70_16636))))
end
| ((Support.Microsoft.FStar.Util.Inr (_37_442), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _37_448) when p_imp -> begin
(let _70_16637 = (aux formals' pats')
in ((p, true))::_70_16637)
end
| ((Support.Microsoft.FStar.Util.Inr (_37_451), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _37_457) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _70_16638 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var (a)) None _70_16638))
in (let _70_16639 = (aux formals' pats)
in ((p, true))::_70_16639)))
end
| ((Support.Microsoft.FStar.Util.Inr (_37_462), imp), _37_467) -> begin
(let _70_16640 = (aux formals' pats')
in ((p, (as_imp imp)))::_70_16640)
end)
end))
in (aux f pats))
end)
in (let _37_470 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); Microsoft_FStar_Absyn_Syntax.sort = _37_470.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_470.Microsoft_FStar_Absyn_Syntax.p}))))
end
| _37_473 -> begin
p
end))
in (let one_pat = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (let p = (elaborate_pat env p)
in (let _37_485 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_37_485) with
| (b, a, w, env, arg, p) -> begin
(match ((Support.All.pipe_right b (Support.Microsoft.FStar.Util.find_dup pvar_eq))) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_488))) -> begin
(let _70_16649 = (let _70_16648 = (let _70_16647 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_70_16647, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16648))
in (raise (_70_16649)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_494))) -> begin
(let _70_16652 = (let _70_16651 = (let _70_16650 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_70_16650, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16651))
in (raise (_70_16652)))
end
| _37_499 -> begin
(b, a, w, arg, p)
end)
end))))
in (let as_arg = (fun ( _37_6 ) -> (match (_37_6) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Support.All.failwith "Impossible")
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end))
in (let top_level_pat_as_args = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _37_521 = (one_pat false env q)
in (match (_37_521) with
| (b, a, _37_518, te, q) -> begin
(let _37_536 = (Support.List.fold_right (fun ( p ) ( _37_526 ) -> (match (_37_526) with
| (w, args, pats) -> begin
(let _37_532 = (one_pat false env p)
in (match (_37_532) with
| (b', a', w', arg, p) -> begin
(match ((not ((Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a')))) with
| true -> begin
(let _70_16666 = (let _70_16665 = (let _70_16664 = (let _70_16662 = (vars_of_bindings a)
in (let _70_16661 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _70_16662 _70_16661)))
in (let _70_16663 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_16664, _70_16663)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16665))
in (raise (_70_16666)))
end
| false -> begin
(let _70_16668 = (let _70_16667 = (as_arg arg)
in (_70_16667)::args)
in ((Support.List.append w' w), _70_16668, (p)::pats))
end)
end))
end)) pats ([], [], []))
in (match (_37_536) with
| (w, args, pats) -> begin
(let _70_16670 = (let _70_16669 = (as_arg te)
in (_70_16669)::args)
in ((Support.List.append b w), _70_16670, (let _37_537 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_disj ((q)::pats); Microsoft_FStar_Absyn_Syntax.sort = _37_537.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_537.Microsoft_FStar_Absyn_Syntax.p})))
end))
end))
end
| _37_540 -> begin
(let _37_548 = (one_pat true env p)
in (match (_37_548) with
| (b, _37_543, _37_545, arg, p) -> begin
(let _70_16672 = (let _70_16671 = (as_arg arg)
in (_70_16671)::[])
in (b, _70_16672, p))
end))
end))
in (let _37_552 = (top_level_pat_as_args env p)
in (match (_37_552) with
| (b, args, p) -> begin
(let exps = (Support.All.pipe_right args (Support.List.map (fun ( _37_7 ) -> (match (_37_7) with
| (Support.Microsoft.FStar.Util.Inl (_37_555), _37_558) -> begin
(Support.All.failwith "Impossible: top-level pattern must be an expression")
end
| (Support.Microsoft.FStar.Util.Inr (e), _37_563) -> begin
e
end))))
in (b, exps, p))
end))))))))))

let decorate_pattern = (fun ( env ) ( p ) ( exps ) -> (let qq = p
in (let rec aux = (fun ( p ) ( e ) -> (let pkg = (fun ( q ) ( t ) -> (let _70_16691 = (Support.All.pipe_left (fun ( _70_16690 ) -> Some (_70_16690)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _70_16691 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_37_579), Microsoft_FStar_Absyn_Syntax.Exp_constant (_37_582)) -> begin
(let _70_16692 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _70_16692))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _37_590 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _70_16695 = (let _70_16694 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_16693 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_16694 _70_16693)))
in (Support.All.failwith _70_16695))
end
| false -> begin
()
end)
in (let _37_592 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _70_16697 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_16696 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _70_16697 _70_16696)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _37_595 = x
in {Microsoft_FStar_Absyn_Syntax.v = _37_595.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _37_595.Microsoft_FStar_Absyn_Syntax.p})
in (let _70_16698 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) _70_16698))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _37_603 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _70_16701 = (let _70_16700 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_16699 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_16700 _70_16699)))
in (Support.All.failwith _70_16701))
end
| false -> begin
()
end)
in (let x = (let _37_605 = x
in (let _70_16702 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _37_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_16702; Microsoft_FStar_Absyn_Syntax.p = _37_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _37_610)), _37_614) -> begin
(let x = (let _37_616 = x
in (let _70_16703 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _37_616.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_16703; Microsoft_FStar_Absyn_Syntax.p = _37_616.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _37_626))) -> begin
(let _37_630 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _70_16704 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _70_16704))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _37_647)); Microsoft_FStar_Absyn_Syntax.tk = _37_644; Microsoft_FStar_Absyn_Syntax.pos = _37_642; Microsoft_FStar_Absyn_Syntax.fvs = _37_640; Microsoft_FStar_Absyn_Syntax.uvs = _37_638}, args))) -> begin
(let _37_655 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _70_16705 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _70_16705))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats ) ( args ) ( argpats ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _70_16712 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _70_16712))
end
| (arg::args, (argpat, _37_671)::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_681)) -> begin
(let x = (let _70_16713 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _70_16713))
in (let q = (let _70_16715 = (Support.All.pipe_left (fun ( _70_16714 ) -> Some (_70_16714)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _70_16715 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_37_692)) -> begin
(let x = (let _70_16716 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _70_16716))
in (let q = (let _70_16718 = (Support.All.pipe_left (fun ( _70_16717 ) -> Some (_70_16717)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _70_16718 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inl (t), imp), _37_702) -> begin
(let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((Support.Microsoft.FStar.Util.Inr (e), imp), _37_710) -> begin
(let pat = (let _70_16719 = (aux argpat e)
in (_70_16719, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _37_714 -> begin
(let _70_16722 = (let _70_16721 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _70_16720 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _70_16721 _70_16720)))
in (Support.All.failwith _70_16722))
end))
in (match_args [] args argpats))))
end
| _37_716 -> begin
(let _70_16727 = (let _70_16726 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_16725 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _70_16724 = (let _70_16723 = (Support.All.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.All.pipe_right _70_16723 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _70_16726 _70_16725 _70_16724))))
in (Support.All.failwith _70_16727))
end))))
and aux_t = (fun ( p ) ( t0 ) -> (let pkg = (fun ( q ) ( k ) -> (let _70_16735 = (Support.All.pipe_left (fun ( _70_16734 ) -> Some (_70_16734)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _70_16735 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _37_728 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _70_16738 = (let _70_16737 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_16736 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_16737 _70_16736)))
in (Support.All.failwith _70_16738))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _37_735 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _70_16741 = (let _70_16740 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_16739 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_16740 _70_16739)))
in (Support.All.failwith _70_16741))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_tvar (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _37_739)), _37_743) -> begin
(let k0 = (force_tk t0)
in (let a = (let _37_746 = a
in {Microsoft_FStar_Absyn_Syntax.v = _37_746.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k0; Microsoft_FStar_Absyn_Syntax.p = _37_746.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.Microsoft_FStar_Absyn_Syntax.sort)))
end
| _37_750 -> begin
(let _70_16745 = (let _70_16744 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_16743 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _70_16742 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _70_16744 _70_16743 _70_16742))))
in (Support.All.failwith _70_16745))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _37_754) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _70_16747 = (Support.All.pipe_left (fun ( _70_16746 ) -> Some (_70_16746)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _70_16747 p.Microsoft_FStar_Absyn_Syntax.p)))
end
| (_37_758, e::[]) -> begin
(aux p e)
end
| _37_763 -> begin
(Support.All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp = (fun ( pat ) -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _37_770 -> begin
(Support.All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun ( f ) -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun ( _37_777 ) -> (match (_37_777) with
| (p, i) -> begin
(let _37_780 = (decorated_pattern_as_either p)
in (match (_37_780) with
| (vars, te) -> begin
(let _70_16767 = (let _70_16766 = (Microsoft_FStar_Absyn_Syntax.as_implicit i)
in (te, _70_16766))
in (vars, _70_16767))
end))
end))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_37_782) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _70_16770 = (Support.All.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _70_16770))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _70_16773 = (Support.All.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _70_16773))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _37_796 = (let _70_16774 = (Support.All.pipe_right pats (Support.List.map pat_as_arg))
in (Support.All.pipe_right _70_16774 Support.List.unzip))
in (match (_37_796) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _70_16780 = (let _70_16779 = (let _70_16778 = (let _70_16777 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_70_16777, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _70_16778))
in (Support.All.pipe_right _70_16779 pkg))
in (vars, _70_16780)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
([], e)
end
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(Support.All.failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _70_16782 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _70_16782))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _37_820 -> begin
(Support.All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _37_833 = (decorated_pattern_as_typ p)
in (match (_37_833) with
| (vars, t) -> begin
(vars, Support.Microsoft.FStar.Util.Inl (t))
end))
end
| _37_835 -> begin
(let _37_838 = (decorated_pattern_as_exp p)
in (match (_37_838) with
| (vars, e) -> begin
(vars, Support.Microsoft.FStar.Util.Inr (e))
end))
end))

let mk_basic_dtuple_type = (fun ( env ) ( n ) -> (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let l = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (Microsoft_FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (Microsoft_FStar_Absyn_Util.ftv l k)
in (let vars = (Microsoft_FStar_Tc_Env.binders env)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _37_854; Microsoft_FStar_Absyn_Syntax.pos = _37_852; Microsoft_FStar_Absyn_Syntax.fvs = _37_850; Microsoft_FStar_Absyn_Syntax.uvs = _37_848})) -> begin
(let _37_884 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _37_861 ) ( _37_865 ) -> (match ((_37_861, _37_865)) with
| ((out, subst), (b, _37_864)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_37_867) -> begin
(Support.All.failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let _70_16790 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_16790 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _70_16793 = (let _70_16792 = (let _70_16791 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_16791 Support.Prims.fst))
in (bs, _70_16792))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_16793 (Some (k)) r))
end
| _37_878 -> begin
(Support.All.failwith "Impossible")
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _70_16795 = (let _70_16794 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_70_16794)::out)
in (_70_16795, subst)))))
end)
end)) ([], [])))
in (match (_37_884) with
| (args, _37_883) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, (Support.List.rev args)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
end))
end
| _37_886 -> begin
(Support.All.failwith "Impossible")
end)))))))

let extract_lb_annotation = (fun ( env ) ( t ) ( e ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun ( scope ) ( a ) -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _70_16806 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.All.pipe_right _70_16806 Support.Prims.fst))
in ((let _37_897 = a
in {Microsoft_FStar_Absyn_Syntax.v = _37_897.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _37_897.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _37_900 -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _70_16811 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_16811 Support.Prims.fst))
in (match ((Microsoft_FStar_Absyn_Syntax.null_v_binder t)) with
| (Support.Microsoft.FStar.Util.Inr (x), _37_909) -> begin
(x, false)
end
| _37_912 -> begin
(Support.All.failwith "impos")
end))
end
| _37_914 -> begin
(match ((Microsoft_FStar_Absyn_Syntax.null_v_binder x.Microsoft_FStar_Absyn_Syntax.sort)) with
| (Support.Microsoft.FStar.Util.Inr (x), _37_918) -> begin
(x, true)
end
| _37_921 -> begin
(Support.All.failwith "impos")
end)
end))
in (let rec aux = (fun ( vars ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _37_927))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _37_934)) -> begin
(e, t, true)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _37_963 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _37_944 ) ( b ) -> (match (_37_944) with
| (scope, bs, check) -> begin
(match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _37_950 = (mk_t_binder scope a)
in (match (_37_950) with
| (tb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl (tb), (Support.Prims.snd b))
in (let bs = (Support.List.append bs ((b)::[]))
in (let scope = (Support.List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _37_958 = (mk_v_binder scope x)
in (match (_37_958) with
| (vb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (vb), (Support.Prims.snd b))
in (scope, (Support.List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_37_963) with
| (scope, bs, check) -> begin
(let _37_967 = (aux scope body)
in (match (_37_967) with
| (body, res, check_res) -> begin
(let c = (Microsoft_FStar_Absyn_Util.ml_comp res r)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _37_970 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _70_16819 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _70_16818 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _70_16819 _70_16818)))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _37_974 -> begin
(let _70_16821 = (let _70_16820 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_16820 Support.Prims.fst))
in (e, _70_16821, false))
end))
in (let _70_16822 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _70_16822 e))))))
end
| _37_976 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun ( c ) -> (let _37_993 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _37_986)::(Support.Microsoft.FStar.Util.Inl (wlp), _37_981)::[] -> begin
(wp, wlp)
end
| _37_990 -> begin
(let _70_16827 = (let _70_16826 = (let _70_16825 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.All.pipe_right _70_16825 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _70_16826))
in (Support.All.failwith _70_16827))
end)
in (match (_37_993) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c ) ( m ) ( lift ) -> (let _37_1001 = (destruct_comp c)
in (match (_37_1001) with
| (_37_998, wp, wlp) -> begin
(let _70_16849 = (let _70_16848 = (let _70_16844 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_16844))
in (let _70_16847 = (let _70_16846 = (let _70_16845 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_16845))
in (_70_16846)::[])
in (_70_16848)::_70_16847))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _70_16849; Microsoft_FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun ( env ) ( l ) -> (let rec find = (fun ( l ) -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some ((_37_1009, c)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c).Microsoft_FStar_Absyn_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (let res = (match ((Support.Microsoft.FStar.Util.smap_try_find cache l.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(let _37_1023 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str m)
in m)
end)
end)
in res))))

let join_effects = (fun ( env ) ( l1 ) ( l2 ) -> (let _37_1034 = (let _70_16863 = (norm_eff_name env l1)
in (let _70_16862 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _70_16863 _70_16862)))
in (match (_37_1034) with
| (m, _37_1031, _37_1033) -> begin
m
end)))

let join_lcomp = (fun ( env ) ( c1 ) ( c2 ) -> (match (((Microsoft_FStar_Absyn_Syntax.lid_equals c1.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) && (Microsoft_FStar_Absyn_Syntax.lid_equals c2.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid))) with
| true -> begin
Microsoft_FStar_Absyn_Const.effect_Tot_lid
end
| false -> begin
(join_effects env c1.Microsoft_FStar_Absyn_Syntax.eff_name c2.Microsoft_FStar_Absyn_Syntax.eff_name)
end))

let lift_and_destruct = (fun ( env ) ( c1 ) ( c2 ) -> (let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _37_1046 = (Microsoft_FStar_Tc_Env.join env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (match (_37_1046) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env m)
in (let _37_1052 = (Microsoft_FStar_Tc_Env.wp_signature env md.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_37_1052) with
| (a, kwp) -> begin
(let _70_16877 = (destruct_comp m1)
in (let _70_16876 = (destruct_comp m2)
in ((md, a, kwp), _70_16877, _70_16876)))
end)))))
end)))))

let is_pure_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md ) ( result ) ( wp ) ( wlp ) ( flags ) -> (let _70_16900 = (let _70_16899 = (let _70_16898 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _70_16897 = (let _70_16896 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_16896)::[])
in (_70_16898)::_70_16897))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _70_16899; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _70_16900)))

let lcomp_of_comp = (fun ( c0 ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _37_1066 ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst ) ( lc ) -> (let _37_1069 = lc
in (let _70_16910 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1069.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _70_16910; Microsoft_FStar_Absyn_Syntax.cflags = _37_1069.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _37_1071 ) -> (match (()) with
| () -> begin
(let _70_16909 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _70_16909))
end))})))

let is_function = (fun ( t ) -> (match ((let _70_16913 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_16913.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_37_1074) -> begin
true
end
| _37_1077 -> begin
false
end))

let return_value = (fun ( env ) ( t ) ( v ) -> (let c = (match ((Microsoft_FStar_Tc_Env.effect_decl_opt env Microsoft_FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _37_1086 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_37_1086) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _70_16925 = (let _70_16924 = (let _70_16923 = (let _70_16922 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_16921 = (let _70_16920 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_70_16920)::[])
in (_70_16922)::_70_16921))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _70_16923))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16924 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _70_16925))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _37_1091 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _70_16928 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_16927 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _70_16926 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _70_16928 _70_16927 _70_16926))))
end
| false -> begin
()
end)
in c)))

let bind = (fun ( env ) ( e1opt ) ( lc1 ) ( _37_1098 ) -> (match (_37_1098) with
| (b, lc2) -> begin
(let _37_1109 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1102))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| _37_1107 -> begin
"??"
end)
in (let _70_16938 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _70_16937 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _70_16938 bstr _70_16937))))
end
| false -> begin
()
end)
in (let bind_it = (fun ( _37_1112 ) -> (match (()) with
| () -> begin
(let c1 = (lc1.Microsoft_FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.Microsoft_FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun ( _37_1116 ) -> (match (()) with
| () -> begin
(let aux = (fun ( _37_1118 ) -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Absyn_Util.is_trivial_wp c1)) with
| true -> begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid (_37_1121)) -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_var (_37_1125)) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c2)) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end
| _37_1129 -> begin
None
end)
end
| false -> begin
(match (((Microsoft_FStar_Absyn_Util.is_ml_comp c1) && (Microsoft_FStar_Absyn_Util.is_ml_comp c2))) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end)
end))
in (match ((e1opt, b)) with
| (Some (e), Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1134)))) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((Microsoft_FStar_Absyn_Syntax.is_null_bvd x))))) with
| true -> begin
(let _70_16946 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.All.pipe_left (fun ( _70_16945 ) -> Some (_70_16945)) _70_16946))
end
| false -> begin
(aux ())
end)
end
| _37_1140 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _37_1158 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("bind")))) with
| true -> begin
(let _70_16950 = (match (b) with
| None -> begin
"None"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1146))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, _37_1152))) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| _37_1157 -> begin
"Something else"
end)
in (let _70_16949 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _70_16948 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _70_16947 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _70_16950 _70_16949 _70_16948 _70_16947)))))
end
| false -> begin
()
end)
in c)
end
| None -> begin
(let _37_1173 = (lift_and_destruct env c1 c2)
in (match (_37_1173) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _70_16951 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_70_16951)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _70_16952 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_70_16952)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _70_16953 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_70_16953)::[])
end
| _37_1186 -> begin
(Support.All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun ( wp ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _70_16968 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _70_16967 = (let _70_16966 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _70_16965 = (let _70_16964 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _70_16963 = (let _70_16962 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _70_16961 = (let _70_16960 = (let _70_16956 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _70_16956))
in (let _70_16959 = (let _70_16958 = (let _70_16957 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _70_16957))
in (_70_16958)::[])
in (_70_16960)::_70_16959))
in (_70_16962)::_70_16961))
in (_70_16964)::_70_16963))
in (_70_16966)::_70_16965))
in (_70_16968)::_70_16967))
in (let wlp_args = (let _70_16976 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _70_16975 = (let _70_16974 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _70_16973 = (let _70_16972 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _70_16971 = (let _70_16970 = (let _70_16969 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _70_16969))
in (_70_16970)::[])
in (_70_16972)::_70_16971))
in (_70_16974)::_70_16973))
in (_70_16976)::_70_16975))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _70_16977 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_16977; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env ) ( t ) ( mk_wp ) ( mk_wlp ) ( f ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _37_1204 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_37_1204) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _70_16992 = (let _70_16991 = (let _70_16990 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_16989 = (let _70_16988 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_70_16988)::[])
in (_70_16990)::_70_16989))
in (mk_wp, _70_16991))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16992 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_16997 = (let _70_16996 = (let _70_16995 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_16994 = (let _70_16993 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_70_16993)::[])
in (_70_16995)::_70_16994))
in (mk_wlp, _70_16996))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16997 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md_pure Microsoft_FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.Microsoft_FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun ( env ) ( b ) ( lc ) -> (let refresh = (fun ( _37_1213 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1216) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _37_1220 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_17009 = (let _70_17008 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_17008))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _70_17009))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1223 = (match (((Support.All.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name)) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low))) with
| true -> begin
(let _70_17012 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _70_17011 = (let _70_17010 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.All.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _70_17010))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _70_17012 _70_17011)))
end
| false -> begin
()
end)
in (let _37_1228 = (destruct_comp c')
in (match (_37_1228) with
| (t, wp, wlp) -> begin
(let wp = (let _70_17015 = (let _70_17014 = (let _70_17013 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _70_17013))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_70_17014))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_17015))
in (let wlp = (let _70_17018 = (let _70_17017 = (let _70_17016 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _70_17016))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_70_17017))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_17018))
in (let _70_17023 = (let _37_1231 = c'
in (let _70_17022 = (let _70_17021 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _70_17020 = (let _70_17019 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_17019)::[])
in (_70_17021)::_70_17020))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _37_1231.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _37_1231.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _70_17022; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _70_17023))))
end)))))
end)
end))
end))
in (let _37_1233 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1233.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1233.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1233.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = refresh})))

let label = (fun ( reason ) ( r ) ( f ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun ( env ) ( reason ) ( r ) ( f ) -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(match ((let _70_17047 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.pipe_left Support.Prims.op_Negation _70_17047))) with
| true -> begin
f
end
| false -> begin
(let _70_17048 = (reason ())
in (label _70_17048 r f))
end)
end))

let label_guard = (fun ( reason ) ( r ) ( g ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _70_17055 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_70_17055))
end))

let weaken_guard = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _37_1260 -> begin
g2
end))

let weaken_precondition = (fun ( env ) ( lc ) ( f ) -> (let weaken = (fun ( _37_1265 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match (f) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1274 = (destruct_comp c)
in (match (_37_1274) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _70_17074 = (let _70_17073 = (let _70_17072 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17071 = (let _70_17070 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _70_17069 = (let _70_17068 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17068)::[])
in (_70_17070)::_70_17069))
in (_70_17072)::_70_17071))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _70_17073))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17074 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_17081 = (let _70_17080 = (let _70_17079 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17078 = (let _70_17077 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _70_17076 = (let _70_17075 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_17075)::[])
in (_70_17077)::_70_17076))
in (_70_17079)::_70_17078))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _70_17080))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17081 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end)))
end)
end))
end))
in (let _37_1278 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1278.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1278.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1278.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun ( reason ) ( env ) ( e ) ( lc ) ( g0 ) -> (match ((Microsoft_FStar_Tc_Rel.is_trivial g0)) with
| true -> begin
(lc, g0)
end
| false -> begin
(let flags = (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _37_8 ) -> (match (_37_8) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _37_1289 -> begin
[]
end))))
in (let strengthen = (fun ( _37_1292 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let g0 = (Microsoft_FStar_Tc_Rel.simplify_guard env g0)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g0)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let c = (match ((((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp c) && (not ((is_function (Microsoft_FStar_Absyn_Util.comp_result c))))) && (not ((Microsoft_FStar_Absyn_Util.is_partial_return c))))) with
| true -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar (Microsoft_FStar_Absyn_Util.comp_result c))
in (let xret = (let _70_17103 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _70_17103))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _70_17106 = (lcomp_of_comp c)
in (let _70_17105 = (let _70_17104 = (lcomp_of_comp xret)
in (Some (xbinding), _70_17104))
in (bind env (Some (e)) _70_17106 _70_17105)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ())))))
end
| false -> begin
c
end)
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1307 = (destruct_comp c)
in (match (_37_1307) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _70_17115 = (let _70_17114 = (let _70_17113 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17112 = (let _70_17111 = (let _70_17108 = (let _70_17107 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _70_17107 f))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_17108))
in (let _70_17110 = (let _70_17109 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17109)::[])
in (_70_17111)::_70_17110))
in (_70_17113)::_70_17112))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _70_17114))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17115 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_17122 = (let _70_17121 = (let _70_17120 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17119 = (let _70_17118 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _70_17117 = (let _70_17116 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_17116)::[])
in (_70_17118)::_70_17117))
in (_70_17120)::_70_17119))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _70_17121))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17122 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _70_17126 = (let _37_1312 = lc
in (let _70_17125 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _70_17124 = (match (((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (let _70_17123 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.All.pipe_left Support.Prims.op_Negation _70_17123)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_17125; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1312.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _70_17124; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_70_17126, (let _37_1314 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _37_1314.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _37_1314.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env ) ( comp ) ( res_t ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _37_1324 = (let _70_17134 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _70_17133 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_70_17134, _70_17133)))
in (match (_37_1324) with
| (xexp, yexp) -> begin
(let yret = (let _70_17139 = (let _70_17138 = (let _70_17137 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17136 = (let _70_17135 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_70_17135)::[])
in (_70_17137)::_70_17136))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _70_17138))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17139 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _70_17147 = (let _70_17146 = (let _70_17145 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17144 = (let _70_17143 = (let _70_17140 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_17140))
in (let _70_17142 = (let _70_17141 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_70_17141)::[])
in (_70_17143)::_70_17142))
in (_70_17145)::_70_17144))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _70_17146))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17147 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _70_17158 = (let _70_17157 = (let _70_17156 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17155 = (let _70_17154 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17153 = (let _70_17152 = (let _70_17151 = (let _70_17150 = (let _70_17149 = (let _70_17148 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_70_17148)::[])
in (_70_17149, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_17150 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_17151))
in (_70_17152)::[])
in (_70_17154)::_70_17153))
in (_70_17156)::_70_17155))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _70_17157))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17158 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _70_17161 = (lcomp_of_comp comp)
in (let _70_17160 = (let _70_17159 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _70_17159))
in (bind env None _70_17161 _70_17160)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun ( env ) ( guard ) ( lcomp_then ) ( lcomp_else ) -> (let comp = (fun ( _37_1335 ) -> (match (()) with
| () -> begin
(let _37_1351 = (let _70_17173 = (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _70_17172 = (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _70_17173 _70_17172)))
in (match (_37_1351) with
| ((md, _37_1338, _37_1340), (res_t, wp_then, wlp_then), (_37_1347, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _70_17193 = (let _70_17191 = (let _70_17190 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17189 = (let _70_17188 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _70_17187 = (let _70_17186 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _70_17185 = (let _70_17184 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_70_17184)::[])
in (_70_17186)::_70_17185))
in (_70_17188)::_70_17187))
in (_70_17190)::_70_17189))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _70_17191))
in (let _70_17192 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17193 None _70_17192))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _70_17200 = (let _70_17199 = (let _70_17198 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17197 = (let _70_17196 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _70_17195 = (let _70_17194 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17194)::[])
in (_70_17196)::_70_17195))
in (_70_17198)::_70_17197))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _70_17199))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17200 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_17205 = (let _70_17204 = (let _70_17203 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17202 = (let _70_17201 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_17201)::[])
in (_70_17203)::_70_17202))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _70_17204))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17205 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _70_17206 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_17206; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun ( env ) ( res_t ) ( lcases ) -> (let eff = (match (lcases) with
| [] -> begin
(Support.All.failwith "Empty cases!")
end
| hd::tl -> begin
(Support.List.fold_left (fun ( eff ) ( _37_1374 ) -> (match (_37_1374) with
| (_37_1372, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun ( _37_1377 ) -> (match (()) with
| () -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _70_17236 = (let _70_17234 = (let _70_17233 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17232 = (let _70_17231 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _70_17230 = (let _70_17229 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _70_17228 = (let _70_17227 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_70_17227)::[])
in (_70_17229)::_70_17228))
in (_70_17231)::_70_17230))
in (_70_17233)::_70_17232))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _70_17234))
in (let _70_17235 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17236 None _70_17235))))
in (let default_case = (let post_k = (let _70_17239 = (let _70_17238 = (let _70_17237 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_70_17237)::[])
in (_70_17238, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_17239 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _70_17242 = (let _70_17241 = (let _70_17240 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_70_17240)::[])
in (_70_17241, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_17242 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _70_17243 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_17243 post_k))
in (let wp = (let _70_17250 = (let _70_17249 = (let _70_17244 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_70_17244)::[])
in (let _70_17248 = (let _70_17247 = (let _70_17245 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _70_17245))
in (let _70_17246 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_left _70_17247 _70_17246)))
in (_70_17249, _70_17248)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_17250 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_17254 = (let _70_17253 = (let _70_17251 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_70_17251)::[])
in (let _70_17252 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_17253, _70_17252)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_17254 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _37_1393 ) ( celse ) -> (match (_37_1393) with
| (g, cthen) -> begin
(let _37_1411 = (let _70_17257 = (cthen.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _70_17257 celse))
in (match (_37_1411) with
| ((md, _37_1397, _37_1399), (_37_1402, wp_then, wlp_then), (_37_1407, wp_else, wlp_else)) -> begin
(let _70_17259 = (ifthenelse md res_t g wp_then wp_else)
in (let _70_17258 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _70_17259 _70_17258 [])))
end))
end)) lcases default_case)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| false -> begin
(let comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env comp.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _37_1419 = (destruct_comp comp)
in (match (_37_1419) with
| (_37_1416, wp, wlp) -> begin
(let wp = (let _70_17266 = (let _70_17265 = (let _70_17264 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17263 = (let _70_17262 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _70_17261 = (let _70_17260 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17260)::[])
in (_70_17262)::_70_17261))
in (_70_17264)::_70_17263))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _70_17265))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17266 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_17271 = (let _70_17270 = (let _70_17269 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17268 = (let _70_17267 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_17267)::[])
in (_70_17269)::_70_17268))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _70_17270))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17271 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = eff; Microsoft_FStar_Absyn_Syntax.res_typ = res_t; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun ( env ) ( bindings ) ( lc ) -> (let close = (fun ( _37_1426 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let close_wp = (fun ( md ) ( res_t ) ( bindings ) ( wp0 ) -> (Support.List.fold_right (fun ( b ) ( wp ) -> (match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let bs = (let _70_17290 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_17290)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_17297 = (let _70_17296 = (let _70_17295 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17294 = (let _70_17293 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_17292 = (let _70_17291 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17291)::[])
in (_70_17293)::_70_17292))
in (_70_17295)::_70_17294))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _70_17296))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17297 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _70_17298 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_17298)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_17303 = (let _70_17302 = (let _70_17301 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_17300 = (let _70_17299 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17299)::[])
in (_70_17301)::_70_17300))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _70_17302))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17303 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((l, t)) -> begin
wp
end
| Microsoft_FStar_Tc_Env.Binding_sig (s) -> begin
(Support.All.failwith "impos")
end)) bindings wp0))
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1457 = (destruct_comp c)
in (match (_37_1457) with
| (t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.Microsoft_FStar_Absyn_Syntax.result_typ wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end))))
end))
end))
in (let _37_1461 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1461.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1461.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1461.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun ( env ) ( e ) ( lc ) -> (let refine = (fun ( _37_1467 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((not ((is_pure_or_ghost_effect env lc.Microsoft_FStar_Absyn_Syntax.eff_name)))) with
| true -> begin
c
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.is_partial_return c)) with
| true -> begin
c
end
| false -> begin
(let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let t = c.Microsoft_FStar_Absyn_Syntax.result_typ
in (let c = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let ret = (let _70_17312 = (return_value env t xexp)
in (Support.All.pipe_left lcomp_of_comp _70_17312))
in (let eq_ret = (let _70_17314 = (let _70_17313 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_70_17313))
in (weaken_precondition env ret _70_17314))
in (let _70_17317 = (let _70_17316 = (let _70_17315 = (lcomp_of_comp c)
in (bind env None _70_17315 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_70_17316.Microsoft_FStar_Absyn_Syntax.comp ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _70_17317 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
end)
end))
end))
in (let flags = (match ((((not ((Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ))) && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((Microsoft_FStar_Absyn_Util.is_lcomp_partial_return lc))))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.Microsoft_FStar_Absyn_Syntax.cflags
end
| false -> begin
lc.Microsoft_FStar_Absyn_Syntax.cflags
end)
in (let _37_1477 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1477.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1477.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun ( env ) ( e ) ( c ) ( c' ) -> (match ((Microsoft_FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _70_17329 = (let _70_17328 = (let _70_17327 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _70_17326 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_17327, _70_17326)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_17328))
in (raise (_70_17329)))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_instantiate_typ = (fun ( env ) ( t ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match ((not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs)))) with
| true -> begin
(t, k, [])
end
| false -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let rec aux = (fun ( subst ) ( _37_9 ) -> (match (_37_9) with
| (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1507 = (new_implicit_tvar env k)
in (match (_37_1507) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _37_1513 = (aux subst rest)
in (match (_37_1513) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1524 = (new_implicit_evar env t)
in (match (_37_1524) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _37_1530 = (aux subst rest)
in (match (_37_1530) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _37_1536 = (aux [] bs)
in (match (_37_1536) with
| (args, bs, subst, implicits) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst k)
in (let _70_17340 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_70_17340, k, implicits))))
end)))
end
| _37_1540 -> begin
(t, k, [])
end)
end)))

let maybe_instantiate = (fun ( env ) ( e ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match ((not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs)))) with
| true -> begin
(e, t, [])
end
| false -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let rec aux = (fun ( subst ) ( _37_10 ) -> (match (_37_10) with
| (Support.Microsoft.FStar.Util.Inl (a), _37_1556)::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1562 = (new_implicit_tvar env k)
in (match (_37_1562) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _37_1568 = (aux subst rest)
in (match (_37_1568) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1579 = (new_implicit_evar env t)
in (match (_37_1579) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _37_1585 = (aux subst rest)
in (match (_37_1585) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _37_1591 = (aux [] bs)
in (match (_37_1591) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun ( e ) ( args ) ( t ) -> (match (args) with
| [] -> begin
e
end
| _37_1598 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
in (let _70_17357 = (mk_exp_app e args (Some (t)))
in (_70_17357, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _37_1602 -> begin
(let t = (let _70_17358 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_17358 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _70_17359 = (mk_exp_app e args (Some (t)))
in (_70_17359, t, implicits)))
end))
end)))
end
| _37_1605 -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env ) ( e ) ( lc ) ( t ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _70_17368 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_70_17368, false))
end
| false -> begin
(let _70_17369 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_70_17369, true))
end)
in (match (gopt) with
| (None, _37_1613) -> begin
(Microsoft_FStar_Tc_Rel.subtype_fail env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (Microsoft_FStar_Tc_Rel.simplify_guard env g)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(let lc = (let _37_1621 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1621.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _37_1621.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _37_1621.Microsoft_FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _37_1626 = g
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _37_1626.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _37_1626.Microsoft_FStar_Tc_Rel.implicits})
in (let strengthen = (fun ( _37_1630 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _37_1632 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _70_17373 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _70_17372 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _70_17373 _70_17372)))
end
| false -> begin
()
end)
in (let ct = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1637 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_37_1637) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (let _70_17378 = (let _70_17377 = (let _70_17376 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_17375 = (let _70_17374 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_70_17374)::[])
in (_70_17376)::_70_17375))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _70_17377))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17378 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _70_17379 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.All.pipe_left lcomp_of_comp _70_17379))
in (let guard = (match (apply_guard) with
| true -> begin
(let _70_17382 = (let _70_17381 = (let _70_17380 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_70_17380)::[])
in (f, _70_17381))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17382 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _37_1647 = (let _70_17390 = (Support.All.pipe_left (fun ( _70_17387 ) -> Some (_70_17387)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _70_17389 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_17388 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _70_17390 _70_17389 e cret _70_17388))))
in (match (_37_1647) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _70_17392 = (let _70_17391 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.All.pipe_left lcomp_of_comp _70_17391))
in (bind env (Some (e)) _70_17392 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _37_1650 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _70_17393 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _70_17393))
end
| false -> begin
()
end)
in c)))
end)))))))))
end)))))
end))
in (let flags = (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _37_11 ) -> (match (_37_11) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _37_1656 -> begin
[]
end))))
in (let lc = (let _37_1658 = lc
in (let _70_17395 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_17395; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r ) ( t ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0)) with
| true -> begin
(let ue = (let _70_17400 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _70_17400))
in (let ut = (let _70_17401 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _70_17401))
in (let uk = (let _70_17402 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _70_17402))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _37_1670 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _37_1672 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _37_1674 = (let _70_17404 = (let _70_17403 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _70_17403))
in (Microsoft_FStar_Tc_Errors.report r _70_17404))
in (let _37_1676 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify ) ( env ) ( ecs ) -> (match ((let _70_17412 = (Support.Microsoft.FStar.Util.for_all (fun ( _37_1684 ) -> (match (_37_1684) with
| (_37_1682, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.All.pipe_left Support.Prims.op_Negation _70_17412))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c ) -> (let _37_1687 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _70_17415 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _70_17415))
end
| false -> begin
()
end)
in (let steps = (Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]
in (let c = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
end
| false -> begin
(Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::[]) env c)
end)
in (let _37_1691 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _70_17416 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _70_17416))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs ) -> (let _70_17419 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.All.pipe_right _70_17419 Support.Microsoft.FStar.Util.set_elements)))
in (let should_gen = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _37_1700)) -> begin
(match ((Support.All.pipe_right bs (Support.Microsoft.FStar.Util.for_some (fun ( _37_12 ) -> (match (_37_12) with
| (Support.Microsoft.FStar.Util.Inl (_37_1705), _37_1708) -> begin
true
end
| _37_1711 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
true
end)
end
| _37_1713 -> begin
true
end))
in (let uvars = (Support.All.pipe_right ecs (Support.List.map (fun ( _37_1716 ) -> (match (_37_1716) with
| (e, c) -> begin
(let t = (Support.All.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.compress_typ)
in (match ((let _70_17424 = (should_gen t)
in (Support.All.pipe_left Support.Prims.op_Negation _70_17424))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _37_1732 = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (let _70_17425 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.All.pipe_left Support.Prims.op_Negation _70_17425)))) with
| true -> begin
(let _37_1728 = (destruct_comp ct)
in (match (_37_1728) with
| (_37_1724, wp, _37_1727) -> begin
(let binder = (let _70_17426 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_17426)::[])
in (let post = (let _70_17430 = (let _70_17427 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _70_17427))
in (let _70_17429 = (let _70_17428 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_70_17428))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_17430 _70_17429 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _70_17437 = (let _70_17436 = (let _70_17435 = (let _70_17434 = (let _70_17433 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_70_17433)::[])
in (wp, _70_17434))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17435))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _70_17436))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _70_17437))
in (let _70_17438 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _70_17438)))))
end))
end
| false -> begin
()
end)
in (uvs, e, c)))))))
end))
end))))
in (let ecs = (Support.All.pipe_right uvars (Support.List.map (fun ( _37_1738 ) -> (match (_37_1738) with
| (uvs, e, c) -> begin
(let tvars = (Support.All.pipe_right uvs (Support.List.map (fun ( _37_1741 ) -> (match (_37_1741) with
| (u, k) -> begin
(let a = (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) | (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)
end
| Microsoft_FStar_Absyn_Syntax.Fixed (_37_1779) -> begin
(Support.All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _37_1782 -> begin
(let a = (let _70_17443 = (let _70_17442 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left (fun ( _70_17441 ) -> Some (_70_17441)) _70_17442))
in (Microsoft_FStar_Absyn_Util.new_bvd _70_17443))
in (let t = (let _70_17444 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _70_17444 k))
in (let _37_1785 = (Microsoft_FStar_Absyn_Util.unchecked_unify u t)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.ktype))))
end)
in (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
end))))
in (let t = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.function_formals)) with
| Some ((bs, cod)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.append tvars bs), cod) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _37_1796 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _37_1800 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _70_17445 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _70_17445)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify ) ( env ) ( lecs ) -> (let _37_1812 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_17454 = (let _70_17453 = (Support.List.map (fun ( _37_1811 ) -> (match (_37_1811) with
| (lb, _37_1808, _37_1810) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.All.pipe_right _70_17453 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _70_17454))
end
| false -> begin
()
end)
in (match ((let _70_17456 = (Support.All.pipe_right lecs (Support.List.map (fun ( _37_1818 ) -> (match (_37_1818) with
| (_37_1815, e, c) -> begin
(e, c)
end))))
in (gen verify env _70_17456))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _37_1827 ) ( _37_1830 ) -> (match ((_37_1827, _37_1830)) with
| ((l, _37_1824, _37_1826), (e, c)) -> begin
(let _37_1831 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _70_17461 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_17460 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _70_17459 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _70_17461 _70_17460 _70_17459))))
end
| false -> begin
()
end)
in (l, e, c))
end)) lecs ecs)
end)))

let unresolved = (fun ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Uvar -> begin
true
end
| _37_1836 -> begin
false
end))

let check_top_level = (fun ( env ) ( g ) ( lc ) -> (let discharge = (fun ( g ) -> (let _37_1842 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _37_1860 = (match ((Support.All.pipe_right g.Microsoft_FStar_Tc_Rel.implicits (Support.List.tryFind (fun ( _37_13 ) -> (match (_37_13) with
| Support.Microsoft.FStar.Util.Inl (u) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr ((u, _37_1849)) -> begin
(unresolved u)
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr ((_37_1853, r))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _37_1859 -> begin
()
end)
in (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Absyn_Util.is_total_lcomp lc)) with
| true -> begin
(let _70_17473 = (discharge g)
in (let _70_17472 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (_70_17473, _70_17472)))
end
| false -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _70_17474 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.All.pipe_right _70_17474 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _37_1871 = (destruct_comp c)
in (match (_37_1871) with
| (t, wp, _37_1870) -> begin
(let vc = (let _70_17480 = (let _70_17478 = (let _70_17477 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_17476 = (let _70_17475 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17475)::[])
in (_70_17477)::_70_17476))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _70_17478))
in (let _70_17479 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17480 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _70_17479)))
in (let g = (let _70_17481 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _70_17481))
in (let _70_17483 = (discharge g)
in (let _70_17482 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_70_17483, _70_17482)))))
end))))))
end))))

let short_circuit_exp = (fun ( head ) ( seen_args ) -> (let short_bin_op_e = (fun ( f ) -> (fun ( _37_14 ) -> (match (_37_14) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _37_1883)::[] -> begin
(let _70_17502 = (f fst)
in (Support.All.pipe_right _70_17502 (fun ( _70_17501 ) -> Some (_70_17501))))
end
| _37_1887 -> begin
(Support.All.failwith "Unexpexted args to binary operator")
end)))
in (let table = (let op_and_e = (fun ( e ) -> (let _70_17508 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_70_17508, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e ) -> (let _70_17512 = (let _70_17511 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _70_17511))
in (_70_17512, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _37_1895)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _37_1901 ) -> (match (_37_1901) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _70_17530 = (mk seen_args)
in Some (_70_17530))
end
| false -> begin
None
end)
end)))) with
| None -> begin
None
end
| Some (g) -> begin
g
end))
end
| _37_1906 -> begin
None
end))))

let short_circuit_typ = (fun ( head ) ( seen_args ) -> (let short_bin_op_t = (fun ( f ) -> (fun ( _37_15 ) -> (match (_37_15) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _37_1916)::[] -> begin
(f fst)
end
| _37_1920 -> begin
(Support.All.failwith "Unexpexted args to binary operator")
end)))
in (let op_and_t = (fun ( t ) -> (let _70_17551 = (unlabel t)
in (Support.All.pipe_right _70_17551 (fun ( _70_17550 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_17550)))))
in (let op_or_t = (fun ( t ) -> (let _70_17556 = (let _70_17554 = (unlabel t)
in (Support.All.pipe_right _70_17554 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.All.pipe_right _70_17556 (fun ( _70_17555 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_17555)))))
in (let op_imp_t = (fun ( t ) -> (let _70_17560 = (unlabel t)
in (Support.All.pipe_right _70_17560 (fun ( _70_17559 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_17559)))))
in (let short_op_ite = (fun ( _37_16 ) -> (match (_37_16) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _37_1932)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _37_1938)::[] -> begin
(let _70_17564 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.All.pipe_right _70_17564 (fun ( _70_17563 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_17563))))
end
| _37_1943 -> begin
(Support.All.failwith "Unexpected args to ITE")
end))
in (let table = ((Microsoft_FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((Microsoft_FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((Microsoft_FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((Microsoft_FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| Support.Microsoft.FStar.Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some ((g, _37_1951)) -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (g)
end)
end
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _37_1961; Microsoft_FStar_Absyn_Syntax.pos = _37_1959; Microsoft_FStar_Absyn_Syntax.fvs = _37_1957; Microsoft_FStar_Absyn_Syntax.uvs = _37_1955}) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _37_1969 ) -> (match (_37_1969) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _70_17591 = (mk seen_args)
in Some (_70_17591))
end
| false -> begin
None
end)
end)))) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some (g) -> begin
g
end))
end
| _37_1974 -> begin
Microsoft_FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun ( env ) ( comp ) -> (let mk_post_type = (fun ( res_t ) ( ens ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _70_17605 = (let _70_17604 = (let _70_17603 = (let _70_17602 = (let _70_17601 = (let _70_17600 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _70_17600))
in (_70_17601)::[])
in (ens, _70_17602))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17603 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _70_17604))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_17605 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
in (let norm = (fun ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Unlabel)::[]) env t))
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp comp)) with
| true -> begin
(None, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| false -> begin
(match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1984) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (req), _37_1999)::(Support.Microsoft.FStar.Util.Inl (ens), _37_1993)::_37_1989 -> begin
(let _70_17611 = (let _70_17608 = (norm req)
in Some (_70_17608))
in (let _70_17610 = (let _70_17609 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.All.pipe_left norm _70_17609))
in (_70_17611, _70_17610)))
end
| _37_2003 -> begin
(Support.All.failwith "Impossible")
end)
end
| false -> begin
(let comp = (Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_2006) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _37_2021)::(Support.Microsoft.FStar.Util.Inl (wlp), _37_2015)::_37_2011 -> begin
(let _37_2033 = (match ((let _70_17613 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _70_17612 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_70_17613, _70_17612)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _37_2030 -> begin
(Support.All.failwith "Impossible")
end)
in (match (_37_2033) with
| (as_req, as_ens) -> begin
(let req = (let _70_17617 = (let _70_17616 = (let _70_17615 = (let _70_17614 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_17614)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_70_17615)
in (as_req, _70_17616))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17617 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _70_17621 = (let _70_17620 = (let _70_17619 = (let _70_17618 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_17618)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_70_17619)
in (as_ens, _70_17620))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_17621 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _70_17625 = (let _70_17622 = (norm req)
in Some (_70_17622))
in (let _70_17624 = (let _70_17623 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _70_17623))
in (_70_17625, _70_17624)))))
end))
end
| _37_2037 -> begin
(Support.All.failwith "Impossible")
end)
end))
end)
end)
end))))




