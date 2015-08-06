
let try_solve = (fun ( env ) ( f ) -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun ( env ) ( errs ) -> (let _70_14895 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14894 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _70_14895 _70_14894))))

let discharge_guard = (fun ( env ) ( g ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env ) ( g ) -> (discharge_guard env g))

let syn' = (fun ( env ) ( k ) -> (let _70_14914 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _70_14914 k)))

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
(let _70_14938 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.All.pipe_left (fun ( _70_14937 ) -> Some (_70_14937)) _70_14938))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _70_14942 = (let _70_14941 = (let _70_14940 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _70_14939 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_14940, _70_14939)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14941))
in (raise (_70_14942)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _70_14946 = (let _70_14945 = (let _70_14944 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _70_14943 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_14944, _70_14943)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14945))
in (raise (_70_14946)))
end
| Some (g) -> begin
(let _37_49 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14947 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _70_14947))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t2) (Some (t2)) e.Microsoft_FStar_Absyn_Syntax.pos)
end
| _37_55 -> begin
(let _37_56 = e
in (let _70_14948 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _37_56.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _70_14948; Microsoft_FStar_Absyn_Syntax.pos = _37_56.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _37_56.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _37_56.Microsoft_FStar_Absyn_Syntax.uvs}))
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
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _37_71)); Microsoft_FStar_Absyn_Syntax.tk = _37_68; Microsoft_FStar_Absyn_Syntax.pos = _37_66; Microsoft_FStar_Absyn_Syntax.fvs = _37_64; Microsoft_FStar_Absyn_Syntax.uvs = _37_62} -> begin
uv
end
| _37_76 -> begin
(Support.All.failwith "Impossible")
end))

let as_uvar_t = (fun ( t ) -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _37_88)); Microsoft_FStar_Absyn_Syntax.tk = _37_85; Microsoft_FStar_Absyn_Syntax.pos = _37_83; Microsoft_FStar_Absyn_Syntax.fvs = _37_81; Microsoft_FStar_Absyn_Syntax.uvs = _37_79} -> begin
uv
end
| _37_93 -> begin
(Support.All.failwith "Impossible")
end))

let new_kvar = (fun ( env ) -> (let _70_14958 = (let _70_14957 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14956 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _70_14957 _70_14956)))
in (Support.All.pipe_right _70_14958 Support.Prims.fst)))

let new_tvar = (fun ( env ) ( k ) -> (let _70_14965 = (let _70_14964 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14963 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _70_14964 _70_14963 k)))
in (Support.All.pipe_right _70_14965 Support.Prims.fst)))

let new_evar = (fun ( env ) ( t ) -> (let _70_14972 = (let _70_14971 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14970 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _70_14971 _70_14970 t)))
in (Support.All.pipe_right _70_14972 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env ) ( k ) -> (let _37_103 = (let _70_14978 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14977 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _70_14978 _70_14977 k)))
in (match (_37_103) with
| (t, u) -> begin
(let _70_14980 = (let _70_14979 = (as_uvar_t u)
in (_70_14979, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _70_14980))
end)))

let new_implicit_evar = (fun ( env ) ( t ) -> (let _37_108 = (let _70_14986 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14985 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _70_14986 _70_14985 t)))
in (match (_37_108) with
| (e, u) -> begin
(let _70_14988 = (let _70_14987 = (as_uvar_e u)
in (_70_14987, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _70_14988))
end)))

let force_tk = (fun ( s ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _70_14991 = (let _70_14990 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _70_14990))
in (Support.All.failwith _70_14991))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args ) -> (Support.All.pipe_right args (Support.List.map (fun ( _37_2 ) -> (match (_37_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _70_14996 = (let _70_14995 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_70_14995))
in (_70_14996, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _70_14998 = (let _70_14997 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_70_14997))
in (_70_14998, imp))
end)))))

let is_implicit = (fun ( _37_3 ) -> (match (_37_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _37_127 -> begin
false
end))

let destruct_arrow_kind = (fun ( env ) ( tt ) ( k ) ( args ) -> (let ktop = (let _70_15009 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.All.pipe_right _70_15009 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_37_143, qual)::_37_141 -> begin
(is_implicit qual)
end
| _37_148 -> begin
false
end)
in (let rec mk_implicits = (fun ( vars ) ( subst ) ( bs ) -> (match (bs) with
| b::brest -> begin
(match ((Support.All.pipe_right (Support.Prims.snd b) is_implicit)) with
| true -> begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_15022 = (let _70_15019 = (let _70_15018 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _70_15018))
in (Support.All.pipe_right _70_15019 Support.Prims.fst))
in (Support.All.pipe_right _70_15022 (fun ( x ) -> (let _70_15021 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _70_15021)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_15027 = (let _70_15024 = (let _70_15023 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _70_15023))
in (Support.All.pipe_right _70_15024 Support.Prims.fst))
in (Support.All.pipe_right _70_15027 (fun ( x ) -> (let _70_15026 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _70_15026)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _70_15028 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_70_15028)::subst)
end)
in (let _37_167 = (mk_implicits vars subst brest)
in (match (_37_167) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _70_15029 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _70_15029))
end)
end
| _37_169 -> begin
(let _70_15030 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _70_15030))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _37_172 = (let _70_15031 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _70_15031 [] bs))
in (match (_37_172) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_37_174, k)) -> begin
(aux k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_37_179) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _70_15032 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.All.pipe_right _70_15032 Support.Prims.fst))
in (let bs = (let _70_15033 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _70_15033))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _37_186 = (let _70_15034 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.All.pipe_left (force_trivial env) _70_15034))
in ([], bs, kres)))))))
end
| _37_189 -> begin
(let _70_15037 = (let _70_15036 = (let _70_15035 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_70_15035, r))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15036))
in (raise (_70_15037)))
end))
in (aux ktop)))))

let pat_as_exps = (fun ( allow_implicits ) ( env ) ( p ) -> (let pvar_eq = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_198)), Microsoft_FStar_Tc_Env.Binding_var ((y, _37_203))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_209)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _37_214))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _37_219 -> begin
false
end))
in (let vars_of_bindings = (fun ( bs ) -> (Support.All.pipe_right bs (Support.List.map (fun ( _37_4 ) -> (match (_37_4) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _37_225)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_230)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _37_234 -> begin
(Support.All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _37_241)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _37_247 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_37_247) with
| (e, u) -> begin
(let p = (let _37_248 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _37_248.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_248.Microsoft_FStar_Absyn_Syntax.p})
in (let _70_15057 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _70_15057, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _37_253)) -> begin
(let k = (new_kvar env)
in (let _37_259 = (let _70_15058 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _70_15058 k))
in (match (_37_259) with
| (t, u) -> begin
(let p = (let _37_260 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _37_260.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_260.Microsoft_FStar_Absyn_Syntax.p})
in (let _70_15060 = (let _70_15059 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (t), _70_15059))
in ([], [], [], env, _70_15060, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15061 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _70_15061, p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _70_15063 = (let _70_15062 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_15062))
in Microsoft_FStar_Tc_Env.Binding_var (_70_15063))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15064 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ((w)::[], [], (w)::[], env, _70_15064, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)) -> begin
(let b = (let _70_15066 = (let _70_15065 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_15065))
in Microsoft_FStar_Tc_Env.Binding_var (_70_15066))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15068 = (let _70_15067 = (Microsoft_FStar_Absyn_Syntax.as_implicit imp)
in (Support.Microsoft.FStar.Util.Inr (e), _70_15067))
in ((b)::[], (b)::[], [], env, _70_15068, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _70_15070 = (let _70_15069 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_15069))
in Microsoft_FStar_Tc_Env.Binding_typ (_70_15070))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15071 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((w)::[], [], (w)::[], env, _70_15071, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _70_15073 = (let _70_15072 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_15072))
in Microsoft_FStar_Tc_Env.Binding_typ (_70_15073))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15074 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((b)::[], (b)::[], [], env, _70_15074, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _37_314 = (Support.All.pipe_right pats (Support.List.fold_left (fun ( _37_299 ) ( p ) -> (match (_37_299) with
| (b, a, w, env, args, pats) -> begin
(let _37_307 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_37_307) with
| (b', a', w', env, arg, pat) -> begin
((b')::b, (a')::a, (w')::w, env, (arg)::args, (pat)::pats)
end))
end)) ([], [], [], env, [], [])))
in (match (_37_314) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _70_15082 = (let _70_15081 = (let _70_15080 = (let _70_15079 = (let _70_15078 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15077 = (Support.All.pipe_right args Support.List.rev)
in (_70_15078, _70_15077)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _70_15079 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_70_15080, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_70_15081))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _70_15082))
in (let _70_15086 = (Support.All.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _70_15085 = (Support.All.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _70_15084 = (Support.All.pipe_right (Support.List.rev w) Support.List.flatten)
in (let _70_15083 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_70_15086, _70_15085, _70_15084, env, _70_15083, (let _37_316 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _37_316.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_316.Microsoft_FStar_Absyn_Syntax.p})))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_37_319) -> begin
(Support.All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let pats = (Support.List.map (elaborate_pat env) pats)
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env fv.Microsoft_FStar_Absyn_Syntax.v)
in (let pats = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _37_334 -> begin
(let _70_15093 = (let _70_15092 = (let _70_15091 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _70_15091))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15092))
in (raise (_70_15093)))
end)
end
| Some ((f, _37_337)) -> begin
(let rec aux = (fun ( formals ) ( pats ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _37_350::_37_348) -> begin
(let _70_15100 = (let _70_15099 = (let _70_15098 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _70_15098))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15099))
in (raise (_70_15100)))
end
| (_37_356::_37_354, []) -> begin
(Support.All.pipe_right formals (Support.List.map (fun ( f ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), _37_364) -> begin
(let a = (let _70_15102 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_15102 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _70_15103 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _70_15103))
end
| false -> begin
(let _70_15104 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _70_15104))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_37_368), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _70_15105 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _70_15105)))
end
| _37_375 -> begin
(let _70_15110 = (let _70_15109 = (let _70_15108 = (let _70_15106 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _70_15106))
in (let _70_15107 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_70_15108, _70_15107)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15109))
in (raise (_70_15110)))
end))))
end
| (f::formals', p::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _70_15111 = (aux formals' pats')
in (p)::_70_15111)
end
| ((Support.Microsoft.FStar.Util.Inl (_37_404), _37_407), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_410)) when allow_implicits -> begin
(let _70_15112 = (aux formals' pats')
in (p)::_70_15112)
end
| ((Support.Microsoft.FStar.Util.Inl (_37_414), _37_417), _37_420) -> begin
(let a = (let _70_15113 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_15113 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _70_15114 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _70_15114))
end
| false -> begin
(let _70_15115 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _70_15115))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_425) -> begin
pats'
end
| _37_428 -> begin
pats
end)
in (let _70_15116 = (aux formals' pats')
in (p1)::_70_15116))))
end
| ((Support.Microsoft.FStar.Util.Inr (_37_431), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_var ((_37_437, true))) -> begin
(let _70_15117 = (aux formals' pats')
in (p)::_70_15117)
end
| ((Support.Microsoft.FStar.Util.Inr (_37_443), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _37_449) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _70_15118 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _70_15118))
in (let _70_15119 = (aux formals' pats)
in (p)::_70_15119)))
end
| ((Support.Microsoft.FStar.Util.Inr (_37_454), _37_457), _37_460) -> begin
(let _70_15120 = (aux formals' pats')
in (p)::_70_15120)
end)
end))
in (aux f pats))
end)
in (let _37_463 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); Microsoft_FStar_Absyn_Syntax.sort = _37_463.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_463.Microsoft_FStar_Absyn_Syntax.p}))))
end
| _37_466 -> begin
p
end))
in (let one_pat = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (let p = (elaborate_pat env p)
in (let _37_478 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_37_478) with
| (b, a, w, env, arg, p) -> begin
(match ((Support.All.pipe_right b (Support.Microsoft.FStar.Util.find_dup pvar_eq))) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_481))) -> begin
(let _70_15129 = (let _70_15128 = (let _70_15127 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_70_15127, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15128))
in (raise (_70_15129)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_487))) -> begin
(let _70_15132 = (let _70_15131 = (let _70_15130 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_70_15130, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15131))
in (raise (_70_15132)))
end
| _37_492 -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _37_508 = (one_pat false env q)
in (match (_37_508) with
| (b, a, _37_505, arg, q) -> begin
(let _37_523 = (Support.List.fold_right (fun ( p ) ( _37_513 ) -> (match (_37_513) with
| (w, args, pats) -> begin
(let _37_519 = (one_pat false env p)
in (match (_37_519) with
| (b', a', w', arg, p) -> begin
(match ((not ((Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a')))) with
| true -> begin
(let _70_15144 = (let _70_15143 = (let _70_15142 = (let _70_15140 = (vars_of_bindings a)
in (let _70_15139 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _70_15140 _70_15139)))
in (let _70_15141 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_15142, _70_15141)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15143))
in (raise (_70_15144)))
end
| false -> begin
((Support.List.append w' w), (arg)::args, (p)::pats)
end)
end))
end)) pats ([], [], []))
in (match (_37_523) with
| (w, args, pats) -> begin
((Support.List.append b w), (arg)::args, (let _37_524 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_disj ((q)::pats); Microsoft_FStar_Absyn_Syntax.sort = _37_524.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_524.Microsoft_FStar_Absyn_Syntax.p}))
end))
end))
end
| _37_527 -> begin
(let _37_535 = (one_pat true env p)
in (match (_37_535) with
| (b, _37_530, _37_532, arg, p) -> begin
(b, (arg)::[], p)
end))
end))
in (let _37_539 = (top_level_pat_as_args env p)
in (match (_37_539) with
| (b, args, p) -> begin
(let exps = (Support.All.pipe_right args (Support.List.map (fun ( _37_5 ) -> (match (_37_5) with
| (Support.Microsoft.FStar.Util.Inl (_37_542), _37_545) -> begin
(Support.All.failwith "Impossible: top-level pattern must be an expression")
end
| (Support.Microsoft.FStar.Util.Inr (e), _37_550) -> begin
e
end))))
in (b, exps, p))
end)))))))))

let decorate_pattern = (fun ( env ) ( p ) ( exps ) -> (let qq = p
in (let rec aux = (fun ( p ) ( e ) -> (let pkg = (fun ( q ) ( t ) -> (let _70_15163 = (Support.All.pipe_left (fun ( _70_15162 ) -> Some (_70_15162)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _70_15163 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_37_566), Microsoft_FStar_Absyn_Syntax.Exp_constant (_37_569)) -> begin
(let _70_15164 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _70_15164))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _37_579 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _70_15167 = (let _70_15166 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_15165 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_15166 _70_15165)))
in (Support.All.failwith _70_15167))
end
| false -> begin
()
end)
in (let _37_581 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _70_15169 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_15168 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _70_15169 _70_15168)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _37_584 = x
in {Microsoft_FStar_Absyn_Syntax.v = _37_584.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _37_584.Microsoft_FStar_Absyn_Syntax.p})
in (let _70_15170 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp))) _70_15170))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _37_592 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _70_15173 = (let _70_15172 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_15171 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_15172 _70_15171)))
in (Support.All.failwith _70_15173))
end
| false -> begin
()
end)
in (let x = (let _37_594 = x
in (let _70_15174 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _37_594.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_15174; Microsoft_FStar_Absyn_Syntax.p = _37_594.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _37_599)), _37_603) -> begin
(let x = (let _37_605 = x
in (let _70_15175 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _37_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_15175; Microsoft_FStar_Absyn_Syntax.p = _37_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _37_615))) -> begin
(let _37_619 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _70_15176 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _70_15176))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _37_636)); Microsoft_FStar_Absyn_Syntax.tk = _37_633; Microsoft_FStar_Absyn_Syntax.pos = _37_631; Microsoft_FStar_Absyn_Syntax.fvs = _37_629; Microsoft_FStar_Absyn_Syntax.uvs = _37_627}, args))) -> begin
(let _37_644 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _70_15177 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _70_15177))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats ) ( args ) ( argpats ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _70_15184 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _70_15184))
end
| (arg::args, argpat::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_667)) -> begin
(let x = (let _70_15185 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _70_15185))
in (let q = (let _70_15187 = (Support.All.pipe_left (fun ( _70_15186 ) -> Some (_70_15186)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _70_15187 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_37_678)) -> begin
(let x = (let _70_15188 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _70_15188))
in (let q = (let _70_15190 = (Support.All.pipe_left (fun ( _70_15189 ) -> Some (_70_15189)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _70_15190 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inl (t), _37_686), _37_689) -> begin
(let pat = (aux_t argpat t)
in (match_args ((pat)::matched_pats) args argpats))
end
| ((Support.Microsoft.FStar.Util.Inr (e), _37_695), _37_698) -> begin
(let pat = (aux argpat e)
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _37_702 -> begin
(let _70_15193 = (let _70_15192 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _70_15191 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _70_15192 _70_15191)))
in (Support.All.failwith _70_15193))
end))
in (match_args [] args argpats))))
end
| _37_704 -> begin
(let _70_15198 = (let _70_15197 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15196 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _70_15195 = (let _70_15194 = (Support.All.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.All.pipe_right _70_15194 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _70_15197 _70_15196 _70_15195))))
in (Support.All.failwith _70_15198))
end))))
and aux_t = (fun ( p ) ( t0 ) -> (let pkg = (fun ( q ) ( k ) -> (let _70_15206 = (Support.All.pipe_left (fun ( _70_15205 ) -> Some (_70_15205)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _70_15206 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _37_716 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _70_15209 = (let _70_15208 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_15207 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_15208 _70_15207)))
in (Support.All.failwith _70_15209))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _37_723 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _70_15212 = (let _70_15211 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_15210 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _70_15211 _70_15210)))
in (Support.All.failwith _70_15212))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_tvar (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _37_727)), _37_731) -> begin
(let k0 = (force_tk t0)
in (let a = (let _37_734 = a
in {Microsoft_FStar_Absyn_Syntax.v = _37_734.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k0; Microsoft_FStar_Absyn_Syntax.p = _37_734.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.Microsoft_FStar_Absyn_Syntax.sort)))
end
| _37_738 -> begin
(let _70_15216 = (let _70_15215 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_15214 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _70_15213 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _70_15215 _70_15214 _70_15213))))
in (Support.All.failwith _70_15216))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _37_742) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _70_15218 = (Support.All.pipe_left (fun ( _70_15217 ) -> Some (_70_15217)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _70_15218 p.Microsoft_FStar_Absyn_Syntax.p)))
end
| (_37_746, e::[]) -> begin
(aux p e)
end
| _37_751 -> begin
(Support.All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp = (fun ( pat ) -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _37_758 -> begin
(Support.All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun ( f ) -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun ( p ) -> (let _37_766 = (decorated_pattern_as_either p)
in (match (_37_766) with
| (vars, te) -> begin
(let _70_15238 = (let _70_15237 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (te, _70_15237))
in (vars, _70_15238))
end)))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_37_768) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _70_15241 = (Support.All.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _70_15241))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) -> begin
(let _70_15244 = (Support.All.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _70_15244))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _37_785 = (let _70_15245 = (Support.All.pipe_right pats (Support.List.map pat_as_arg))
in (Support.All.pipe_right _70_15245 Support.List.unzip))
in (match (_37_785) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _70_15251 = (let _70_15250 = (let _70_15249 = (let _70_15248 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_70_15248, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _70_15249))
in (Support.All.pipe_right _70_15250 pkg))
in (vars, _70_15251)))
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
(let _70_15253 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _70_15253))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _37_809 -> begin
(Support.All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _37_822 = (decorated_pattern_as_typ p)
in (match (_37_822) with
| (vars, t) -> begin
(vars, Support.Microsoft.FStar.Util.Inl (t))
end))
end
| _37_824 -> begin
(let _37_827 = (decorated_pattern_as_exp p)
in (match (_37_827) with
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
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _37_843; Microsoft_FStar_Absyn_Syntax.pos = _37_841; Microsoft_FStar_Absyn_Syntax.fvs = _37_839; Microsoft_FStar_Absyn_Syntax.uvs = _37_837})) -> begin
(let _37_873 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _37_850 ) ( _37_854 ) -> (match ((_37_850, _37_854)) with
| ((out, subst), (b, _37_853)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_37_856) -> begin
(Support.All.failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let _70_15261 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_15261 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _70_15264 = (let _70_15263 = (let _70_15262 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_15262 Support.Prims.fst))
in (bs, _70_15263))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15264 (Some (k)) r))
end
| _37_867 -> begin
(Support.All.failwith "Impossible")
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _70_15266 = (let _70_15265 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_70_15265)::out)
in (_70_15266, subst)))))
end)
end)) ([], [])))
in (match (_37_873) with
| (args, _37_872) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, (Support.List.rev args)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
end))
end
| _37_875 -> begin
(Support.All.failwith "Impossible")
end)))))))

let extract_lb_annotation = (fun ( env ) ( t ) ( e ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun ( scope ) ( a ) -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _70_15277 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.All.pipe_right _70_15277 Support.Prims.fst))
in ((let _37_886 = a
in {Microsoft_FStar_Absyn_Syntax.v = _37_886.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _37_886.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _37_889 -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _70_15282 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_15282 Support.Prims.fst))
in (match ((Microsoft_FStar_Absyn_Syntax.null_v_binder t)) with
| (Support.Microsoft.FStar.Util.Inr (x), _37_898) -> begin
(x, false)
end
| _37_901 -> begin
(Support.All.failwith "impos")
end))
end
| _37_903 -> begin
(match ((Microsoft_FStar_Absyn_Syntax.null_v_binder x.Microsoft_FStar_Absyn_Syntax.sort)) with
| (Support.Microsoft.FStar.Util.Inr (x), _37_907) -> begin
(x, true)
end
| _37_910 -> begin
(Support.All.failwith "impos")
end)
end))
in (let rec aux = (fun ( vars ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _37_916))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _37_923)) -> begin
(e, t, true)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _37_952 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _37_933 ) ( b ) -> (match (_37_933) with
| (scope, bs, check) -> begin
(match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _37_939 = (mk_t_binder scope a)
in (match (_37_939) with
| (tb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl (tb), (Support.Prims.snd b))
in (let bs = (Support.List.append bs ((b)::[]))
in (let scope = (Support.List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _37_947 = (mk_v_binder scope x)
in (match (_37_947) with
| (vb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (vb), (Support.Prims.snd b))
in (scope, (Support.List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_37_952) with
| (scope, bs, check) -> begin
(let _37_956 = (aux scope body)
in (match (_37_956) with
| (body, res, check_res) -> begin
(let c = (Microsoft_FStar_Absyn_Util.ml_comp res r)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _37_959 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _70_15290 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _70_15289 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _70_15290 _70_15289)))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _37_963 -> begin
(let _70_15292 = (let _70_15291 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _70_15291 Support.Prims.fst))
in (e, _70_15292, false))
end))
in (let _70_15293 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _70_15293 e))))))
end
| _37_965 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun ( c ) -> (let _37_982 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _37_975)::(Support.Microsoft.FStar.Util.Inl (wlp), _37_970)::[] -> begin
(wp, wlp)
end
| _37_979 -> begin
(let _70_15298 = (let _70_15297 = (let _70_15296 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.All.pipe_right _70_15296 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _70_15297))
in (Support.All.failwith _70_15298))
end)
in (match (_37_982) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c ) ( m ) ( lift ) -> (let _37_990 = (destruct_comp c)
in (match (_37_990) with
| (_37_987, wp, wlp) -> begin
(let _70_15320 = (let _70_15319 = (let _70_15315 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15315))
in (let _70_15318 = (let _70_15317 = (let _70_15316 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15316))
in (_70_15317)::[])
in (_70_15319)::_70_15318))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _70_15320; Microsoft_FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun ( env ) ( l ) -> (let rec find = (fun ( l ) -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some ((_37_998, c)) -> begin
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
(let _37_1012 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str m)
in m)
end)
end)
in res))))

let join_effects = (fun ( env ) ( l1 ) ( l2 ) -> (let _37_1023 = (let _70_15334 = (norm_eff_name env l1)
in (let _70_15333 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _70_15334 _70_15333)))
in (match (_37_1023) with
| (m, _37_1020, _37_1022) -> begin
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
in (let _37_1035 = (Microsoft_FStar_Tc_Env.join env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (match (_37_1035) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env m)
in (let _37_1041 = (Microsoft_FStar_Tc_Env.wp_signature env md.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_37_1041) with
| (a, kwp) -> begin
(let _70_15348 = (destruct_comp m1)
in (let _70_15347 = (destruct_comp m2)
in ((md, a, kwp), _70_15348, _70_15347)))
end)))))
end)))))

let is_pure_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md ) ( result ) ( wp ) ( wlp ) ( flags ) -> (let _70_15371 = (let _70_15370 = (let _70_15369 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _70_15368 = (let _70_15367 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_15367)::[])
in (_70_15369)::_70_15368))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _70_15370; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _70_15371)))

let lcomp_of_comp = (fun ( c0 ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _37_1055 ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst ) ( lc ) -> (let _37_1058 = lc
in (let _70_15381 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1058.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _70_15381; Microsoft_FStar_Absyn_Syntax.cflags = _37_1058.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _37_1060 ) -> (match (()) with
| () -> begin
(let _70_15380 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _70_15380))
end))})))

let is_function = (fun ( t ) -> (match ((let _70_15384 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_15384.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_37_1063) -> begin
true
end
| _37_1066 -> begin
false
end))

let return_value = (fun ( env ) ( t ) ( v ) -> (let c = (match ((Microsoft_FStar_Tc_Env.effect_decl_opt env Microsoft_FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _37_1075 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_37_1075) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _70_15396 = (let _70_15395 = (let _70_15394 = (let _70_15393 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_15392 = (let _70_15391 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_70_15391)::[])
in (_70_15393)::_70_15392))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _70_15394))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15395 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _70_15396))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _37_1080 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _70_15399 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15398 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _70_15397 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _70_15399 _70_15398 _70_15397))))
end
| false -> begin
()
end)
in c)))

let bind = (fun ( env ) ( e1opt ) ( lc1 ) ( _37_1087 ) -> (match (_37_1087) with
| (b, lc2) -> begin
(let _37_1098 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1091))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| _37_1096 -> begin
"??"
end)
in (let _70_15409 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _70_15408 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _70_15409 bstr _70_15408))))
end
| false -> begin
()
end)
in (let bind_it = (fun ( _37_1101 ) -> (match (()) with
| () -> begin
(let c1 = (lc1.Microsoft_FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.Microsoft_FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun ( _37_1105 ) -> (match (()) with
| () -> begin
(let aux = (fun ( _37_1107 ) -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Absyn_Util.is_trivial_wp c1)) with
| true -> begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid (_37_1110)) -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_var (_37_1114)) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c2)) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end
| _37_1118 -> begin
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
| (Some (e), Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1123)))) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((Microsoft_FStar_Absyn_Syntax.is_null_bvd x))))) with
| true -> begin
(let _70_15417 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.All.pipe_left (fun ( _70_15416 ) -> Some (_70_15416)) _70_15417))
end
| false -> begin
(aux ())
end)
end
| _37_1129 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _37_1147 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("bind")))) with
| true -> begin
(let _70_15421 = (match (b) with
| None -> begin
"None"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1135))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, _37_1141))) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| _37_1146 -> begin
"Something else"
end)
in (let _70_15420 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _70_15419 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _70_15418 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _70_15421 _70_15420 _70_15419 _70_15418)))))
end
| false -> begin
()
end)
in c)
end
| None -> begin
(let _37_1162 = (lift_and_destruct env c1 c2)
in (match (_37_1162) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _70_15422 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_70_15422)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _70_15423 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_70_15423)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _70_15424 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_70_15424)::[])
end
| _37_1175 -> begin
(Support.All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun ( wp ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _70_15439 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _70_15438 = (let _70_15437 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _70_15436 = (let _70_15435 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _70_15434 = (let _70_15433 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _70_15432 = (let _70_15431 = (let _70_15427 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15427))
in (let _70_15430 = (let _70_15429 = (let _70_15428 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15428))
in (_70_15429)::[])
in (_70_15431)::_70_15430))
in (_70_15433)::_70_15432))
in (_70_15435)::_70_15434))
in (_70_15437)::_70_15436))
in (_70_15439)::_70_15438))
in (let wlp_args = (let _70_15447 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _70_15446 = (let _70_15445 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _70_15444 = (let _70_15443 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _70_15442 = (let _70_15441 = (let _70_15440 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15440))
in (_70_15441)::[])
in (_70_15443)::_70_15442))
in (_70_15445)::_70_15444))
in (_70_15447)::_70_15446))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _70_15448 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_15448; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env ) ( t ) ( mk_wp ) ( mk_wlp ) ( f ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _37_1193 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_37_1193) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _70_15463 = (let _70_15462 = (let _70_15461 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_15460 = (let _70_15459 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_70_15459)::[])
in (_70_15461)::_70_15460))
in (mk_wp, _70_15462))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15463 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_15468 = (let _70_15467 = (let _70_15466 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_15465 = (let _70_15464 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_70_15464)::[])
in (_70_15466)::_70_15465))
in (mk_wlp, _70_15467))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15468 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md_pure Microsoft_FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.Microsoft_FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun ( env ) ( b ) ( lc ) -> (let refresh = (fun ( _37_1202 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1205) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _37_1209 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_15480 = (let _70_15479 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_15479))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _70_15480))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1212 = (match (((Support.All.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name)) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low))) with
| true -> begin
(let _70_15483 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _70_15482 = (let _70_15481 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.All.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _70_15481))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _70_15483 _70_15482)))
end
| false -> begin
()
end)
in (let _37_1217 = (destruct_comp c')
in (match (_37_1217) with
| (t, wp, wlp) -> begin
(let wp = (let _70_15486 = (let _70_15485 = (let _70_15484 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _70_15484))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_70_15485))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_15486))
in (let wlp = (let _70_15489 = (let _70_15488 = (let _70_15487 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _70_15487))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_70_15488))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_15489))
in (let _70_15494 = (let _37_1220 = c'
in (let _70_15493 = (let _70_15492 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _70_15491 = (let _70_15490 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_15490)::[])
in (_70_15492)::_70_15491))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _37_1220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _37_1220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _70_15493; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _70_15494))))
end)))))
end)
end))
end))
in (let _37_1222 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1222.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1222.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1222.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = refresh})))

let label = (fun ( reason ) ( r ) ( f ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun ( env ) ( reason ) ( r ) ( f ) -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(match ((let _70_15518 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15518))) with
| true -> begin
f
end
| false -> begin
(let _70_15519 = (reason ())
in (label _70_15519 r f))
end)
end))

let label_guard = (fun ( reason ) ( r ) ( g ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _70_15526 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_70_15526))
end))

let weaken_guard = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _37_1249 -> begin
g2
end))

let weaken_precondition = (fun ( env ) ( lc ) ( f ) -> (let weaken = (fun ( _37_1254 ) -> (match (()) with
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
in (let _37_1263 = (destruct_comp c)
in (match (_37_1263) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _70_15545 = (let _70_15544 = (let _70_15543 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15542 = (let _70_15541 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _70_15540 = (let _70_15539 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15539)::[])
in (_70_15541)::_70_15540))
in (_70_15543)::_70_15542))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _70_15544))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15545 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_15552 = (let _70_15551 = (let _70_15550 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15549 = (let _70_15548 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _70_15547 = (let _70_15546 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_15546)::[])
in (_70_15548)::_70_15547))
in (_70_15550)::_70_15549))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _70_15551))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15552 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end)))
end)
end))
end))
in (let _37_1267 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1267.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1267.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1267.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun ( reason ) ( env ) ( e ) ( lc ) ( g0 ) -> (match ((Microsoft_FStar_Tc_Rel.is_trivial g0)) with
| true -> begin
(lc, g0)
end
| false -> begin
(let flags = (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _37_6 ) -> (match (_37_6) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _37_1278 -> begin
[]
end))))
in (let strengthen = (fun ( _37_1281 ) -> (match (()) with
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
in (let xret = (let _70_15574 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _70_15574))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _70_15577 = (lcomp_of_comp c)
in (let _70_15576 = (let _70_15575 = (lcomp_of_comp xret)
in (Some (xbinding), _70_15575))
in (bind env (Some (e)) _70_15577 _70_15576)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ())))))
end
| false -> begin
c
end)
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1296 = (destruct_comp c)
in (match (_37_1296) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _70_15586 = (let _70_15585 = (let _70_15584 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15583 = (let _70_15582 = (let _70_15579 = (let _70_15578 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _70_15578 f))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_15579))
in (let _70_15581 = (let _70_15580 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15580)::[])
in (_70_15582)::_70_15581))
in (_70_15584)::_70_15583))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _70_15585))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15586 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_15593 = (let _70_15592 = (let _70_15591 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15590 = (let _70_15589 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _70_15588 = (let _70_15587 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_15587)::[])
in (_70_15589)::_70_15588))
in (_70_15591)::_70_15590))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _70_15592))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15593 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _70_15597 = (let _37_1301 = lc
in (let _70_15596 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _70_15595 = (match (((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (let _70_15594 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15594)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_15596; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1301.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _70_15595; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_70_15597, (let _37_1303 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _37_1303.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _37_1303.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env ) ( comp ) ( res_t ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _37_1313 = (let _70_15605 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _70_15604 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_70_15605, _70_15604)))
in (match (_37_1313) with
| (xexp, yexp) -> begin
(let yret = (let _70_15610 = (let _70_15609 = (let _70_15608 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15607 = (let _70_15606 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_70_15606)::[])
in (_70_15608)::_70_15607))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _70_15609))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15610 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _70_15618 = (let _70_15617 = (let _70_15616 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15615 = (let _70_15614 = (let _70_15611 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_15611))
in (let _70_15613 = (let _70_15612 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_70_15612)::[])
in (_70_15614)::_70_15613))
in (_70_15616)::_70_15615))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _70_15617))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15618 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _70_15629 = (let _70_15628 = (let _70_15627 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15626 = (let _70_15625 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15624 = (let _70_15623 = (let _70_15622 = (let _70_15621 = (let _70_15620 = (let _70_15619 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_70_15619)::[])
in (_70_15620, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15621 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_15622))
in (_70_15623)::[])
in (_70_15625)::_70_15624))
in (_70_15627)::_70_15626))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _70_15628))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15629 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _70_15632 = (lcomp_of_comp comp)
in (let _70_15631 = (let _70_15630 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _70_15630))
in (bind env None _70_15632 _70_15631)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun ( env ) ( guard ) ( lcomp_then ) ( lcomp_else ) -> (let comp = (fun ( _37_1324 ) -> (match (()) with
| () -> begin
(let _37_1340 = (let _70_15644 = (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _70_15643 = (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _70_15644 _70_15643)))
in (match (_37_1340) with
| ((md, _37_1327, _37_1329), (res_t, wp_then, wlp_then), (_37_1336, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _70_15664 = (let _70_15662 = (let _70_15661 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15660 = (let _70_15659 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _70_15658 = (let _70_15657 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _70_15656 = (let _70_15655 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_70_15655)::[])
in (_70_15657)::_70_15656))
in (_70_15659)::_70_15658))
in (_70_15661)::_70_15660))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _70_15662))
in (let _70_15663 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15664 None _70_15663))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _70_15671 = (let _70_15670 = (let _70_15669 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15668 = (let _70_15667 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _70_15666 = (let _70_15665 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15665)::[])
in (_70_15667)::_70_15666))
in (_70_15669)::_70_15668))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _70_15670))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15671 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_15676 = (let _70_15675 = (let _70_15674 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15673 = (let _70_15672 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_15672)::[])
in (_70_15674)::_70_15673))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _70_15675))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15676 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _70_15677 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_15677; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun ( env ) ( res_t ) ( lcases ) -> (let eff = (match (lcases) with
| [] -> begin
(Support.All.failwith "Empty cases!")
end
| hd::tl -> begin
(Support.List.fold_left (fun ( eff ) ( _37_1363 ) -> (match (_37_1363) with
| (_37_1361, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun ( _37_1366 ) -> (match (()) with
| () -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _70_15707 = (let _70_15705 = (let _70_15704 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15703 = (let _70_15702 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _70_15701 = (let _70_15700 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _70_15699 = (let _70_15698 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_70_15698)::[])
in (_70_15700)::_70_15699))
in (_70_15702)::_70_15701))
in (_70_15704)::_70_15703))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _70_15705))
in (let _70_15706 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15707 None _70_15706))))
in (let default_case = (let post_k = (let _70_15710 = (let _70_15709 = (let _70_15708 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_70_15708)::[])
in (_70_15709, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_15710 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _70_15713 = (let _70_15712 = (let _70_15711 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_70_15711)::[])
in (_70_15712, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_15713 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _70_15714 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_15714 post_k))
in (let wp = (let _70_15721 = (let _70_15720 = (let _70_15715 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_70_15715)::[])
in (let _70_15719 = (let _70_15718 = (let _70_15716 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _70_15716))
in (let _70_15717 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_left _70_15718 _70_15717)))
in (_70_15720, _70_15719)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15721 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_15725 = (let _70_15724 = (let _70_15722 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_70_15722)::[])
in (let _70_15723 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_15724, _70_15723)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15725 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _37_1382 ) ( celse ) -> (match (_37_1382) with
| (g, cthen) -> begin
(let _37_1400 = (let _70_15728 = (cthen.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _70_15728 celse))
in (match (_37_1400) with
| ((md, _37_1386, _37_1388), (_37_1391, wp_then, wlp_then), (_37_1396, wp_else, wlp_else)) -> begin
(let _70_15730 = (ifthenelse md res_t g wp_then wp_else)
in (let _70_15729 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _70_15730 _70_15729 [])))
end))
end)) lcases default_case)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| false -> begin
(let comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env comp.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _37_1408 = (destruct_comp comp)
in (match (_37_1408) with
| (_37_1405, wp, wlp) -> begin
(let wp = (let _70_15737 = (let _70_15736 = (let _70_15735 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15734 = (let _70_15733 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _70_15732 = (let _70_15731 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15731)::[])
in (_70_15733)::_70_15732))
in (_70_15735)::_70_15734))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _70_15736))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15737 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _70_15742 = (let _70_15741 = (let _70_15740 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15739 = (let _70_15738 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_15738)::[])
in (_70_15740)::_70_15739))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _70_15741))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15742 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = eff; Microsoft_FStar_Absyn_Syntax.res_typ = res_t; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun ( env ) ( bindings ) ( lc ) -> (let close = (fun ( _37_1415 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let close_wp = (fun ( md ) ( res_t ) ( bindings ) ( wp0 ) -> (Support.List.fold_right (fun ( b ) ( wp ) -> (match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let bs = (let _70_15761 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_15761)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15768 = (let _70_15767 = (let _70_15766 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15765 = (let _70_15764 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_15763 = (let _70_15762 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15762)::[])
in (_70_15764)::_70_15763))
in (_70_15766)::_70_15765))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _70_15767))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15768 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _70_15769 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_15769)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15774 = (let _70_15773 = (let _70_15772 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _70_15771 = (let _70_15770 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15770)::[])
in (_70_15772)::_70_15771))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _70_15773))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15774 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((l, t)) -> begin
wp
end
| Microsoft_FStar_Tc_Env.Binding_sig (s) -> begin
(Support.All.failwith "impos")
end)) bindings wp0))
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1446 = (destruct_comp c)
in (match (_37_1446) with
| (t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.Microsoft_FStar_Absyn_Syntax.result_typ wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end))))
end))
end))
in (let _37_1450 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1450.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1450.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1450.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun ( env ) ( e ) ( lc ) -> (let refine = (fun ( _37_1456 ) -> (match (()) with
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
in (let ret = (let _70_15783 = (return_value env t xexp)
in (Support.All.pipe_left lcomp_of_comp _70_15783))
in (let eq_ret = (let _70_15785 = (let _70_15784 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_70_15784))
in (weaken_precondition env ret _70_15785))
in (let _70_15788 = (let _70_15787 = (let _70_15786 = (lcomp_of_comp c)
in (bind env None _70_15786 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_70_15787.Microsoft_FStar_Absyn_Syntax.comp ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _70_15788 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
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
in (let _37_1466 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1466.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1466.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun ( env ) ( e ) ( c ) ( c' ) -> (match ((Microsoft_FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _70_15800 = (let _70_15799 = (let _70_15798 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _70_15797 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_15798, _70_15797)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_15799))
in (raise (_70_15800)))
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
(let rec aux = (fun ( subst ) ( _37_7 ) -> (match (_37_7) with
| (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1496 = (new_implicit_tvar env k)
in (match (_37_1496) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _37_1502 = (aux subst rest)
in (match (_37_1502) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1513 = (new_implicit_evar env t)
in (match (_37_1513) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _37_1519 = (aux subst rest)
in (match (_37_1519) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _37_1525 = (aux [] bs)
in (match (_37_1525) with
| (args, bs, subst, implicits) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst k)
in (let _70_15811 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_70_15811, k, implicits))))
end)))
end
| _37_1529 -> begin
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
(let rec aux = (fun ( subst ) ( _37_8 ) -> (match (_37_8) with
| (Support.Microsoft.FStar.Util.Inl (a), _37_1545)::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1551 = (new_implicit_tvar env k)
in (match (_37_1551) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _37_1557 = (aux subst rest)
in (match (_37_1557) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1568 = (new_implicit_evar env t)
in (match (_37_1568) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _37_1574 = (aux subst rest)
in (match (_37_1574) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _37_1580 = (aux [] bs)
in (match (_37_1580) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun ( e ) ( args ) ( t ) -> (match (args) with
| [] -> begin
e
end
| _37_1587 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
in (let _70_15828 = (mk_exp_app e args (Some (t)))
in (_70_15828, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _37_1591 -> begin
(let t = (let _70_15829 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_15829 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _70_15830 = (mk_exp_app e args (Some (t)))
in (_70_15830, t, implicits)))
end))
end)))
end
| _37_1594 -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env ) ( e ) ( lc ) ( t ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _70_15839 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_70_15839, false))
end
| false -> begin
(let _70_15840 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_70_15840, true))
end)
in (match (gopt) with
| (None, _37_1602) -> begin
(Microsoft_FStar_Tc_Rel.subtype_fail env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (Microsoft_FStar_Tc_Rel.simplify_guard env g)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(let lc = (let _37_1610 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1610.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _37_1610.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _37_1610.Microsoft_FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _37_1615 = g
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _37_1615.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _37_1615.Microsoft_FStar_Tc_Rel.implicits})
in (let strengthen = (fun ( _37_1619 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _37_1621 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _70_15844 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _70_15843 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _70_15844 _70_15843)))
end
| false -> begin
()
end)
in (let ct = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1626 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_37_1626) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (let _70_15849 = (let _70_15848 = (let _70_15847 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_15846 = (let _70_15845 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_70_15845)::[])
in (_70_15847)::_70_15846))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _70_15848))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15849 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _70_15850 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.All.pipe_left lcomp_of_comp _70_15850))
in (let guard = (match (apply_guard) with
| true -> begin
(let _70_15853 = (let _70_15852 = (let _70_15851 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_70_15851)::[])
in (f, _70_15852))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15853 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _37_1636 = (let _70_15861 = (Support.All.pipe_left (fun ( _70_15858 ) -> Some (_70_15858)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _70_15860 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15859 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _70_15861 _70_15860 e cret _70_15859))))
in (match (_37_1636) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _70_15863 = (let _70_15862 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.All.pipe_left lcomp_of_comp _70_15862))
in (bind env (Some (e)) _70_15863 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _37_1639 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _70_15864 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _70_15864))
end
| false -> begin
()
end)
in c)))
end)))))))))
end)))))
end))
in (let flags = (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _37_9 ) -> (match (_37_9) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _37_1645 -> begin
[]
end))))
in (let lc = (let _37_1647 = lc
in (let _70_15866 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _70_15866; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r ) ( t ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0)) with
| true -> begin
(let ue = (let _70_15871 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _70_15871))
in (let ut = (let _70_15872 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _70_15872))
in (let uk = (let _70_15873 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _70_15873))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _37_1659 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _37_1661 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _37_1663 = (let _70_15875 = (let _70_15874 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _70_15874))
in (Microsoft_FStar_Tc_Errors.report r _70_15875))
in (let _37_1665 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify ) ( env ) ( ecs ) -> (match ((let _70_15883 = (Support.Microsoft.FStar.Util.for_all (fun ( _37_1673 ) -> (match (_37_1673) with
| (_37_1671, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15883))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c ) -> (let _37_1676 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _70_15886 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _70_15886))
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
in (let _37_1680 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _70_15887 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _70_15887))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs ) -> (let _70_15890 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.All.pipe_right _70_15890 Support.Microsoft.FStar.Util.set_elements)))
in (let should_gen = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _37_1689)) -> begin
(match ((Support.All.pipe_right bs (Support.Microsoft.FStar.Util.for_some (fun ( _37_10 ) -> (match (_37_10) with
| (Support.Microsoft.FStar.Util.Inl (_37_1694), _37_1697) -> begin
true
end
| _37_1700 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
true
end)
end
| _37_1702 -> begin
true
end))
in (let uvars = (Support.All.pipe_right ecs (Support.List.map (fun ( _37_1705 ) -> (match (_37_1705) with
| (e, c) -> begin
(let t = (Support.All.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.compress_typ)
in (match ((let _70_15895 = (should_gen t)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15895))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _37_1721 = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (let _70_15896 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15896)))) with
| true -> begin
(let _37_1717 = (destruct_comp ct)
in (match (_37_1717) with
| (_37_1713, wp, _37_1716) -> begin
(let binder = (let _70_15897 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_15897)::[])
in (let post = (let _70_15901 = (let _70_15898 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _70_15898))
in (let _70_15900 = (let _70_15899 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_70_15899))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15901 _70_15900 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _70_15908 = (let _70_15907 = (let _70_15906 = (let _70_15905 = (let _70_15904 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_70_15904)::[])
in (wp, _70_15905))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15906))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _70_15907))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _70_15908))
in (let _70_15909 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _70_15909)))))
end))
end
| false -> begin
()
end)
in (uvs, e, c)))))))
end))
end))))
in (let ecs = (Support.All.pipe_right uvars (Support.List.map (fun ( _37_1727 ) -> (match (_37_1727) with
| (uvs, e, c) -> begin
(let tvars = (Support.All.pipe_right uvs (Support.List.map (fun ( _37_1730 ) -> (match (_37_1730) with
| (u, k) -> begin
(let a = (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) | (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)
end
| Microsoft_FStar_Absyn_Syntax.Fixed (_37_1768) -> begin
(Support.All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _37_1771 -> begin
(let a = (let _70_15914 = (let _70_15913 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left (fun ( _70_15912 ) -> Some (_70_15912)) _70_15913))
in (Microsoft_FStar_Absyn_Util.new_bvd _70_15914))
in (let t = (let _70_15915 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _70_15915 k))
in (let _37_1774 = (Microsoft_FStar_Absyn_Util.unchecked_unify u t)
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
| _37_1785 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _37_1789 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _70_15916 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _70_15916)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify ) ( env ) ( lecs ) -> (let _37_1801 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_15925 = (let _70_15924 = (Support.List.map (fun ( _37_1800 ) -> (match (_37_1800) with
| (lb, _37_1797, _37_1799) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.All.pipe_right _70_15924 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _70_15925))
end
| false -> begin
()
end)
in (match ((let _70_15927 = (Support.All.pipe_right lecs (Support.List.map (fun ( _37_1807 ) -> (match (_37_1807) with
| (_37_1804, e, c) -> begin
(e, c)
end))))
in (gen verify env _70_15927))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _37_1816 ) ( _37_1819 ) -> (match ((_37_1816, _37_1819)) with
| ((l, _37_1813, _37_1815), (e, c)) -> begin
(let _37_1820 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _70_15932 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15931 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _70_15930 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _70_15932 _70_15931 _70_15930))))
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
| _37_1825 -> begin
false
end))

let check_top_level = (fun ( env ) ( g ) ( lc ) -> (let discharge = (fun ( g ) -> (let _37_1831 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _37_1849 = (match ((Support.All.pipe_right g.Microsoft_FStar_Tc_Rel.implicits (Support.List.tryFind (fun ( _37_11 ) -> (match (_37_11) with
| Support.Microsoft.FStar.Util.Inl (u) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr ((u, _37_1838)) -> begin
(unresolved u)
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr ((_37_1842, r))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _37_1848 -> begin
()
end)
in (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Absyn_Util.is_total_lcomp lc)) with
| true -> begin
(let _70_15944 = (discharge g)
in (let _70_15943 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (_70_15944, _70_15943)))
end
| false -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _70_15945 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.All.pipe_right _70_15945 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _37_1860 = (destruct_comp c)
in (match (_37_1860) with
| (t, wp, _37_1859) -> begin
(let vc = (let _70_15951 = (let _70_15949 = (let _70_15948 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _70_15947 = (let _70_15946 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_15946)::[])
in (_70_15948)::_70_15947))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _70_15949))
in (let _70_15950 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15951 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _70_15950)))
in (let g = (let _70_15952 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _70_15952))
in (let _70_15954 = (discharge g)
in (let _70_15953 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_70_15954, _70_15953)))))
end))))))
end))))

let short_circuit_exp = (fun ( head ) ( seen_args ) -> (let short_bin_op_e = (fun ( f ) -> (fun ( _37_12 ) -> (match (_37_12) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _37_1872)::[] -> begin
(let _70_15973 = (f fst)
in (Support.All.pipe_right _70_15973 (fun ( _70_15972 ) -> Some (_70_15972))))
end
| _37_1876 -> begin
(Support.All.failwith "Unexpexted args to binary operator")
end)))
in (let table = (let op_and_e = (fun ( e ) -> (let _70_15979 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_70_15979, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e ) -> (let _70_15983 = (let _70_15982 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _70_15982))
in (_70_15983, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _37_1884)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _37_1890 ) -> (match (_37_1890) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _70_16001 = (mk seen_args)
in Some (_70_16001))
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
| _37_1895 -> begin
None
end))))

let short_circuit_typ = (fun ( head ) ( seen_args ) -> (let short_bin_op_t = (fun ( f ) -> (fun ( _37_13 ) -> (match (_37_13) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _37_1905)::[] -> begin
(f fst)
end
| _37_1909 -> begin
(Support.All.failwith "Unexpexted args to binary operator")
end)))
in (let op_and_t = (fun ( t ) -> (let _70_16022 = (unlabel t)
in (Support.All.pipe_right _70_16022 (fun ( _70_16021 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_16021)))))
in (let op_or_t = (fun ( t ) -> (let _70_16027 = (let _70_16025 = (unlabel t)
in (Support.All.pipe_right _70_16025 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.All.pipe_right _70_16027 (fun ( _70_16026 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_16026)))))
in (let op_imp_t = (fun ( t ) -> (let _70_16031 = (unlabel t)
in (Support.All.pipe_right _70_16031 (fun ( _70_16030 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_16030)))))
in (let short_op_ite = (fun ( _37_14 ) -> (match (_37_14) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _37_1921)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _37_1927)::[] -> begin
(let _70_16035 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.All.pipe_right _70_16035 (fun ( _70_16034 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_70_16034))))
end
| _37_1932 -> begin
(Support.All.failwith "Unexpected args to ITE")
end))
in (let table = ((Microsoft_FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((Microsoft_FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((Microsoft_FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((Microsoft_FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| Support.Microsoft.FStar.Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some ((g, _37_1940)) -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (g)
end)
end
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _37_1950; Microsoft_FStar_Absyn_Syntax.pos = _37_1948; Microsoft_FStar_Absyn_Syntax.fvs = _37_1946; Microsoft_FStar_Absyn_Syntax.uvs = _37_1944}) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _37_1958 ) -> (match (_37_1958) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _70_16062 = (mk seen_args)
in Some (_70_16062))
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
| _37_1963 -> begin
Microsoft_FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun ( env ) ( comp ) -> (let mk_post_type = (fun ( res_t ) ( ens ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _70_16076 = (let _70_16075 = (let _70_16074 = (let _70_16073 = (let _70_16072 = (let _70_16071 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _70_16071))
in (_70_16072)::[])
in (ens, _70_16073))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16074 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _70_16075))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_16076 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
in (let norm = (fun ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Unlabel)::[]) env t))
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp comp)) with
| true -> begin
(None, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| false -> begin
(match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1973) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (req), _37_1988)::(Support.Microsoft.FStar.Util.Inl (ens), _37_1982)::_37_1978 -> begin
(let _70_16082 = (let _70_16079 = (norm req)
in Some (_70_16079))
in (let _70_16081 = (let _70_16080 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.All.pipe_left norm _70_16080))
in (_70_16082, _70_16081)))
end
| _37_1992 -> begin
(Support.All.failwith "Impossible")
end)
end
| false -> begin
(let comp = (Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1995) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _37_2010)::(Support.Microsoft.FStar.Util.Inl (wlp), _37_2004)::_37_2000 -> begin
(let _37_2022 = (match ((let _70_16084 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _70_16083 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_70_16084, _70_16083)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _37_2019 -> begin
(Support.All.failwith "Impossible")
end)
in (match (_37_2022) with
| (as_req, as_ens) -> begin
(let req = (let _70_16088 = (let _70_16087 = (let _70_16086 = (let _70_16085 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_70_16085)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_70_16086)
in (as_req, _70_16087))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16088 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _70_16092 = (let _70_16091 = (let _70_16090 = (let _70_16089 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_70_16089)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_70_16090)
in (as_ens, _70_16091))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16092 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _70_16096 = (let _70_16093 = (norm req)
in Some (_70_16093))
in (let _70_16095 = (let _70_16094 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _70_16094))
in (_70_16096, _70_16095)))))
end))
end
| _37_2026 -> begin
(Support.All.failwith "Impossible")
end)
end))
end)
end)
end))))




