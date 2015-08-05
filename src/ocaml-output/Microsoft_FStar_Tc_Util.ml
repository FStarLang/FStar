
let try_solve = (fun ( env ) ( f ) -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun ( env ) ( errs ) -> (let _68_14775 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14774 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _68_14775 _68_14774))))

let discharge_guard = (fun ( env ) ( g ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env ) ( g ) -> (discharge_guard env g))

let syn' = (fun ( env ) ( k ) -> (let _68_14794 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _68_14794 k)))

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
(let _68_14818 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.Prims.pipe_left (fun ( _68_14817 ) -> Some (_68_14817)) _68_14818))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _68_14822 = (let _68_14821 = (let _68_14820 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _68_14819 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14820, _68_14819)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14821))
in (raise (_68_14822)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _68_14826 = (let _68_14825 = (let _68_14824 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _68_14823 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14824, _68_14823)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14825))
in (raise (_68_14826)))
end
| Some (g) -> begin
(let _35_49 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14827 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _68_14827))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t2) (Some (t2)) e.Microsoft_FStar_Absyn_Syntax.pos)
end
| _35_55 -> begin
(let _35_56 = e
in (let _68_14828 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _35_56.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _68_14828; Microsoft_FStar_Absyn_Syntax.pos = _35_56.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _35_56.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _35_56.Microsoft_FStar_Absyn_Syntax.uvs}))
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

let as_uvar_e = (fun ( _35_1 ) -> (match (_35_1) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _35_71)); Microsoft_FStar_Absyn_Syntax.tk = _35_68; Microsoft_FStar_Absyn_Syntax.pos = _35_66; Microsoft_FStar_Absyn_Syntax.fvs = _35_64; Microsoft_FStar_Absyn_Syntax.uvs = _35_62} -> begin
uv
end
| _35_76 -> begin
(failwith ("Impossible"))
end))

let as_uvar_t = (fun ( t ) -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_88)); Microsoft_FStar_Absyn_Syntax.tk = _35_85; Microsoft_FStar_Absyn_Syntax.pos = _35_83; Microsoft_FStar_Absyn_Syntax.fvs = _35_81; Microsoft_FStar_Absyn_Syntax.uvs = _35_79} -> begin
uv
end
| _35_93 -> begin
(failwith ("Impossible"))
end))

let new_kvar = (fun ( env ) -> (let _68_14838 = (let _68_14837 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14836 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _68_14837 _68_14836)))
in (Support.Prims.pipe_right _68_14838 Support.Prims.fst)))

let new_tvar = (fun ( env ) ( k ) -> (let _68_14845 = (let _68_14844 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14843 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _68_14844 _68_14843 k)))
in (Support.Prims.pipe_right _68_14845 Support.Prims.fst)))

let new_evar = (fun ( env ) ( t ) -> (let _68_14852 = (let _68_14851 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14850 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _68_14851 _68_14850 t)))
in (Support.Prims.pipe_right _68_14852 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env ) ( k ) -> (let _35_103 = (let _68_14858 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14857 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _68_14858 _68_14857 k)))
in (match (_35_103) with
| (t, u) -> begin
(let _68_14860 = (let _68_14859 = (as_uvar_t u)
in (_68_14859, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _68_14860))
end)))

let new_implicit_evar = (fun ( env ) ( t ) -> (let _35_108 = (let _68_14866 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14865 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _68_14866 _68_14865 t)))
in (match (_35_108) with
| (e, u) -> begin
(let _68_14868 = (let _68_14867 = (as_uvar_e u)
in (_68_14867, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _68_14868))
end)))

let force_tk = (fun ( s ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _68_14871 = (let _68_14870 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _68_14870))
in (failwith (_68_14871)))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args ) -> (Support.Prims.pipe_right args (Support.List.map (fun ( _35_2 ) -> (match (_35_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _68_14876 = (let _68_14875 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_68_14875))
in (_68_14876, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _68_14878 = (let _68_14877 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_68_14877))
in (_68_14878, imp))
end)))))

let is_implicit = (fun ( _35_3 ) -> (match (_35_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _35_127 -> begin
false
end))

let destruct_arrow_kind = (fun ( env ) ( tt ) ( k ) ( args ) -> (let ktop = (let _68_14889 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.Prims.pipe_right _68_14889 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_35_143, qual)::_35_141 -> begin
(is_implicit qual)
end
| _35_148 -> begin
false
end)
in (let rec mk_implicits = (fun ( vars ) ( subst ) ( bs ) -> (match (bs) with
| b::brest -> begin
(match ((Support.Prims.pipe_right (Support.Prims.snd b) is_implicit)) with
| true -> begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_14902 = (let _68_14899 = (let _68_14898 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _68_14898))
in (Support.Prims.pipe_right _68_14899 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14902 (fun ( x ) -> (let _68_14901 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _68_14901)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_14907 = (let _68_14904 = (let _68_14903 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _68_14903))
in (Support.Prims.pipe_right _68_14904 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14907 (fun ( x ) -> (let _68_14906 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _68_14906)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _68_14908 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_68_14908)::subst)
end)
in (let _35_167 = (mk_implicits vars subst brest)
in (match (_35_167) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _68_14909 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _68_14909))
end)
end
| _35_169 -> begin
(let _68_14910 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _68_14910))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _35_172 = (let _68_14911 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _68_14911 [] bs))
in (match (_35_172) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_174, k)) -> begin
(aux k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_179) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _68_14912 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.Prims.pipe_right _68_14912 Support.Prims.fst))
in (let bs = (let _68_14913 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _68_14913))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _35_186 = (let _68_14914 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.Prims.pipe_left (force_trivial env) _68_14914))
in ([], bs, kres)))))))
end
| _35_189 -> begin
(let _68_14917 = (let _68_14916 = (let _68_14915 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_68_14915, r))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14916))
in (raise (_68_14917)))
end))
in (aux ktop)))))

let pat_as_exps = (fun ( allow_implicits ) ( env ) ( p ) -> (let pvar_eq = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _35_198)), Microsoft_FStar_Tc_Env.Binding_var ((y, _35_203))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _35_209)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _35_214))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _35_219 -> begin
false
end))
in (let vars_of_bindings = (fun ( bs ) -> (Support.Prims.pipe_right bs (Support.List.map (fun ( _35_4 ) -> (match (_35_4) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _35_225)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _35_230)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _35_234 -> begin
(failwith ("impos"))
end)))))
in (let rec pat_as_arg_with_env = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _35_241)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _35_247 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_35_247) with
| (e, u) -> begin
(let p = (let _35_248 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _35_248.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_248.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_14937 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _68_14937, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _35_253)) -> begin
(let k = (new_kvar env)
in (let _35_259 = (let _68_14938 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _68_14938 k))
in (match (_35_259) with
| (t, u) -> begin
(let p = (let _35_260 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _35_260.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_260.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_14940 = (let _68_14939 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (t), _68_14939))
in ([], [], [], env, _68_14940, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14941 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _68_14941, p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _68_14943 = (let _68_14942 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_14942))
in Microsoft_FStar_Tc_Env.Binding_var (_68_14943))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14944 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ((w)::[], [], (w)::[], env, _68_14944, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)) -> begin
(let b = (let _68_14946 = (let _68_14945 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_14945))
in Microsoft_FStar_Tc_Env.Binding_var (_68_14946))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14948 = (let _68_14947 = (Microsoft_FStar_Absyn_Syntax.as_implicit imp)
in (Support.Microsoft.FStar.Util.Inr (e), _68_14947))
in ((b)::[], (b)::[], [], env, _68_14948, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _68_14950 = (let _68_14949 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_14949))
in Microsoft_FStar_Tc_Env.Binding_typ (_68_14950))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14951 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((w)::[], [], (w)::[], env, _68_14951, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _68_14953 = (let _68_14952 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_14952))
in Microsoft_FStar_Tc_Env.Binding_typ (_68_14953))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14954 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((b)::[], (b)::[], [], env, _68_14954, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _35_314 = (Support.Prims.pipe_right pats (Support.List.fold_left (fun ( _35_299 ) ( p ) -> (match (_35_299) with
| (b, a, w, env, args, pats) -> begin
(let _35_307 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_307) with
| (b', a', w', env, arg, pat) -> begin
((b')::b, (a')::a, (w')::w, env, (arg)::args, (pat)::pats)
end))
end)) ([], [], [], env, [], [])))
in (match (_35_314) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _68_14962 = (let _68_14961 = (let _68_14960 = (let _68_14959 = (let _68_14958 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14957 = (Support.Prims.pipe_right args Support.List.rev)
in (_68_14958, _68_14957)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_14959 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_68_14960, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_14961))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_14962))
in (let _68_14966 = (Support.Prims.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _68_14965 = (Support.Prims.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _68_14964 = (Support.Prims.pipe_right (Support.List.rev w) Support.List.flatten)
in (let _68_14963 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_14966, _68_14965, _68_14964, env, _68_14963, (let _35_316 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _35_316.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_316.Microsoft_FStar_Absyn_Syntax.p})))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_35_319) -> begin
(failwith ("impossible"))
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
| _35_334 -> begin
(let _68_14973 = (let _68_14972 = (let _68_14971 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _68_14971))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14972))
in (raise (_68_14973)))
end)
end
| Some ((f, _35_337)) -> begin
(let rec aux = (fun ( formals ) ( pats ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _35_350::_35_348) -> begin
(let _68_14980 = (let _68_14979 = (let _68_14978 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _68_14978))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14979))
in (raise (_68_14980)))
end
| (_35_356::_35_354, []) -> begin
(Support.Prims.pipe_right formals (Support.List.map (fun ( f ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), _35_364) -> begin
(let a = (let _68_14982 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_14982 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _68_14983 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _68_14983))
end
| false -> begin
(let _68_14984 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _68_14984))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_35_368), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _68_14985 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _68_14985)))
end
| _35_375 -> begin
(let _68_14990 = (let _68_14989 = (let _68_14988 = (let _68_14986 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _68_14986))
in (let _68_14987 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_68_14988, _68_14987)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14989))
in (raise (_68_14990)))
end))))
end
| (f::formals', p::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _68_14991 = (aux formals' pats')
in (p)::_68_14991)
end
| ((Support.Microsoft.FStar.Util.Inl (_35_404), _35_407), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_35_410)) when allow_implicits -> begin
(let _68_14992 = (aux formals' pats')
in (p)::_68_14992)
end
| ((Support.Microsoft.FStar.Util.Inl (_35_414), _35_417), _35_420) -> begin
(let a = (let _68_14993 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_14993 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _68_14994 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _68_14994))
end
| false -> begin
(let _68_14995 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _68_14995))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_35_425) -> begin
pats'
end
| _35_428 -> begin
pats
end)
in (let _68_14996 = (aux formals' pats')
in (p1)::_68_14996))))
end
| ((Support.Microsoft.FStar.Util.Inr (_35_431), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_var ((_35_437, true))) -> begin
(let _68_14997 = (aux formals' pats')
in (p)::_68_14997)
end
| ((Support.Microsoft.FStar.Util.Inr (_35_443), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _35_449) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _68_14998 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _68_14998))
in (let _68_14999 = (aux formals' pats)
in (p)::_68_14999)))
end
| ((Support.Microsoft.FStar.Util.Inr (_35_454), _35_457), _35_460) -> begin
(let _68_15000 = (aux formals' pats')
in (p)::_68_15000)
end)
end))
in (aux f pats))
end)
in (let _35_463 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); Microsoft_FStar_Absyn_Syntax.sort = _35_463.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_463.Microsoft_FStar_Absyn_Syntax.p}))))
end
| _35_466 -> begin
p
end))
in (let one_pat = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (let p = (elaborate_pat env p)
in (let _35_478 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_478) with
| (b, a, w, env, arg, p) -> begin
(match ((Support.Prims.pipe_right b (Support.Microsoft.FStar.Util.find_dup pvar_eq))) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _35_481))) -> begin
(let _68_15009 = (let _68_15008 = (let _68_15007 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_68_15007, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_15008))
in (raise (_68_15009)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _35_487))) -> begin
(let _68_15012 = (let _68_15011 = (let _68_15010 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_68_15010, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_15011))
in (raise (_68_15012)))
end
| _35_492 -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _35_508 = (one_pat false env q)
in (match (_35_508) with
| (b, a, _35_505, arg, q) -> begin
(let _35_523 = (Support.List.fold_right (fun ( p ) ( _35_513 ) -> (match (_35_513) with
| (w, args, pats) -> begin
(let _35_519 = (one_pat false env p)
in (match (_35_519) with
| (b', a', w', arg, p) -> begin
(match ((not ((Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a')))) with
| true -> begin
(let _68_15024 = (let _68_15023 = (let _68_15022 = (let _68_15020 = (vars_of_bindings a)
in (let _68_15019 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _68_15020 _68_15019)))
in (let _68_15021 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_15022, _68_15021)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_15023))
in (raise (_68_15024)))
end
| false -> begin
((Support.List.append w' w), (arg)::args, (p)::pats)
end)
end))
end)) pats ([], [], []))
in (match (_35_523) with
| (w, args, pats) -> begin
((Support.List.append b w), (arg)::args, (let _35_524 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_disj ((q)::pats); Microsoft_FStar_Absyn_Syntax.sort = _35_524.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_524.Microsoft_FStar_Absyn_Syntax.p}))
end))
end))
end
| _35_527 -> begin
(let _35_535 = (one_pat true env p)
in (match (_35_535) with
| (b, _35_530, _35_532, arg, p) -> begin
(b, (arg)::[], p)
end))
end))
in (let _35_539 = (top_level_pat_as_args env p)
in (match (_35_539) with
| (b, args, p) -> begin
(let exps = (Support.Prims.pipe_right args (Support.List.map (fun ( _35_5 ) -> (match (_35_5) with
| (Support.Microsoft.FStar.Util.Inl (_35_542), _35_545) -> begin
(failwith ("Impossible: top-level pattern must be an expression"))
end
| (Support.Microsoft.FStar.Util.Inr (e), _35_550) -> begin
e
end))))
in (b, exps, p))
end)))))))))

let decorate_pattern = (fun ( env ) ( p ) ( exps ) -> (let qq = p
in (let rec aux = (fun ( p ) ( e ) -> (let pkg = (fun ( q ) ( t ) -> (let _68_15043 = (Support.Prims.pipe_left (fun ( _68_15042 ) -> Some (_68_15042)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _68_15043 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_35_566), Microsoft_FStar_Absyn_Syntax.Exp_constant (_35_569)) -> begin
(let _68_15044 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _68_15044))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_579 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15047 = (let _68_15046 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15045 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15046 _68_15045)))
in (failwith (_68_15047)))
end
| false -> begin
()
end)
in (let _35_581 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _68_15049 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15048 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _68_15049 _68_15048)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _35_584 = x
in {Microsoft_FStar_Absyn_Syntax.v = _35_584.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _35_584.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_15050 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp))) _68_15050))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_592 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15053 = (let _68_15052 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15051 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15052 _68_15051)))
in (failwith (_68_15053)))
end
| false -> begin
()
end)
in (let x = (let _35_594 = x
in (let _68_15054 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_594.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_15054; Microsoft_FStar_Absyn_Syntax.p = _35_594.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _35_599)), _35_603) -> begin
(let x = (let _35_605 = x
in (let _68_15055 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_15055; Microsoft_FStar_Absyn_Syntax.p = _35_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _35_615))) -> begin
(let _35_619 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _68_15056 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_68_15056)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _35_636)); Microsoft_FStar_Absyn_Syntax.tk = _35_633; Microsoft_FStar_Absyn_Syntax.pos = _35_631; Microsoft_FStar_Absyn_Syntax.fvs = _35_629; Microsoft_FStar_Absyn_Syntax.uvs = _35_627}, args))) -> begin
(let _35_644 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _68_15057 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_68_15057)))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats ) ( args ) ( argpats ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _68_15064 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _68_15064))
end
| (arg::args, argpat::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_35_667)) -> begin
(let x = (let _68_15065 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _68_15065))
in (let q = (let _68_15067 = (Support.Prims.pipe_left (fun ( _68_15066 ) -> Some (_68_15066)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _68_15067 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_35_678)) -> begin
(let x = (let _68_15068 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _68_15068))
in (let q = (let _68_15070 = (Support.Prims.pipe_left (fun ( _68_15069 ) -> Some (_68_15069)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _68_15070 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inl (t), _35_686), _35_689) -> begin
(let pat = (aux_t argpat t)
in (match_args ((pat)::matched_pats) args argpats))
end
| ((Support.Microsoft.FStar.Util.Inr (e), _35_695), _35_698) -> begin
(let pat = (aux argpat e)
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _35_702 -> begin
(let _68_15073 = (let _68_15072 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _68_15071 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _68_15072 _68_15071)))
in (failwith (_68_15073)))
end))
in (match_args [] args argpats))))
end
| _35_704 -> begin
(let _68_15078 = (let _68_15077 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_15076 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _68_15075 = (let _68_15074 = (Support.Prims.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.Prims.pipe_right _68_15074 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _68_15077 _68_15076 _68_15075))))
in (failwith (_68_15078)))
end))))
and aux_t = (fun ( p ) ( t0 ) -> (let pkg = (fun ( q ) ( k ) -> (let _68_15086 = (Support.Prims.pipe_left (fun ( _68_15085 ) -> Some (_68_15085)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _68_15086 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_716 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15089 = (let _68_15088 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15087 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15088 _68_15087)))
in (failwith (_68_15089)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_723 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15092 = (let _68_15091 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15090 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15091 _68_15090)))
in (failwith (_68_15092)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_tvar (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _35_727)), _35_731) -> begin
(let k0 = (force_tk t0)
in (let a = (let _35_734 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_734.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k0; Microsoft_FStar_Absyn_Syntax.p = _35_734.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.Microsoft_FStar_Absyn_Syntax.sort)))
end
| _35_738 -> begin
(let _68_15096 = (let _68_15095 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_15094 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _68_15093 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _68_15095 _68_15094 _68_15093))))
in (failwith (_68_15096)))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _35_742) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _68_15098 = (Support.Prims.pipe_left (fun ( _68_15097 ) -> Some (_68_15097)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _68_15098 p.Microsoft_FStar_Absyn_Syntax.p)))
end
| (_35_746, e::[]) -> begin
(aux p e)
end
| _35_751 -> begin
(failwith ("Unexpected number of patterns"))
end))))

let rec decorated_pattern_as_exp = (fun ( pat ) -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _35_758 -> begin
(failwith ("top-level pattern should be decorated with a type"))
end)
in (let pkg = (fun ( f ) -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun ( p ) -> (let _35_766 = (decorated_pattern_as_either p)
in (match (_35_766) with
| (vars, te) -> begin
(let _68_15118 = (let _68_15117 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (te, _68_15117))
in (vars, _68_15118))
end)))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_35_768) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _68_15121 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _68_15121))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) -> begin
(let _68_15124 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _68_15124))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _35_785 = (let _68_15125 = (Support.Prims.pipe_right pats (Support.List.map pat_as_arg))
in (Support.Prims.pipe_right _68_15125 Support.List.unzip))
in (match (_35_785) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _68_15131 = (let _68_15130 = (let _68_15129 = (let _68_15128 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_68_15128, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_15129))
in (Support.Prims.pipe_right _68_15130 pkg))
in (vars, _68_15131)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
([], e)
end
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(failwith ("Impossible: expected a term pattern"))
end)))))
and decorated_pattern_as_typ = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _68_15133 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _68_15133))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _35_809 -> begin
(failwith ("Expected a type pattern"))
end))
and decorated_pattern_as_either = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _35_822 = (decorated_pattern_as_typ p)
in (match (_35_822) with
| (vars, t) -> begin
(vars, Support.Microsoft.FStar.Util.Inl (t))
end))
end
| _35_824 -> begin
(let _35_827 = (decorated_pattern_as_exp p)
in (match (_35_827) with
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
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _35_843; Microsoft_FStar_Absyn_Syntax.pos = _35_841; Microsoft_FStar_Absyn_Syntax.fvs = _35_839; Microsoft_FStar_Absyn_Syntax.uvs = _35_837})) -> begin
(let _35_873 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _35_850 ) ( _35_854 ) -> (match ((_35_850, _35_854)) with
| ((out, subst), (b, _35_853)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_35_856) -> begin
(failwith ("impossible"))
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let _68_15141 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15141 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _68_15144 = (let _68_15143 = (let _68_15142 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15142 Support.Prims.fst))
in (bs, _68_15143))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15144 (Some (k)) r))
end
| _35_867 -> begin
(failwith ("Impossible"))
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _68_15146 = (let _68_15145 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_68_15145)::out)
in (_68_15146, subst)))))
end)
end)) ([], [])))
in (match (_35_873) with
| (args, _35_872) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, (Support.List.rev args)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
end))
end
| _35_875 -> begin
(failwith ("Impossible"))
end)))))))

let extract_lb_annotation = (fun ( env ) ( t ) ( e ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun ( scope ) ( a ) -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _68_15157 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.Prims.pipe_right _68_15157 Support.Prims.fst))
in ((let _35_886 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_886.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _35_886.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _35_889 -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _68_15162 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15162 Support.Prims.fst))
in (match ((Microsoft_FStar_Absyn_Syntax.null_v_binder t)) with
| (Support.Microsoft.FStar.Util.Inr (x), _35_898) -> begin
(x, false)
end
| _35_901 -> begin
(failwith ("impos"))
end))
end
| _35_903 -> begin
(match ((Microsoft_FStar_Absyn_Syntax.null_v_binder x.Microsoft_FStar_Absyn_Syntax.sort)) with
| (Support.Microsoft.FStar.Util.Inr (x), _35_907) -> begin
(x, true)
end
| _35_910 -> begin
(failwith ("impos"))
end)
end))
in (let rec aux = (fun ( vars ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _35_916))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _35_923)) -> begin
(e, t, true)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _35_952 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _35_933 ) ( b ) -> (match (_35_933) with
| (scope, bs, check) -> begin
(match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _35_939 = (mk_t_binder scope a)
in (match (_35_939) with
| (tb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl (tb), (Support.Prims.snd b))
in (let bs = (Support.List.append bs ((b)::[]))
in (let scope = (Support.List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _35_947 = (mk_v_binder scope x)
in (match (_35_947) with
| (vb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (vb), (Support.Prims.snd b))
in (scope, (Support.List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_35_952) with
| (scope, bs, check) -> begin
(let _35_956 = (aux scope body)
in (match (_35_956) with
| (body, res, check_res) -> begin
(let c = (Microsoft_FStar_Absyn_Util.ml_comp res r)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _35_959 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_15170 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _68_15169 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _68_15170 _68_15169)))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _35_963 -> begin
(let _68_15172 = (let _68_15171 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15171 Support.Prims.fst))
in (e, _68_15172, false))
end))
in (let _68_15173 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _68_15173 e))))))
end
| _35_965 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun ( c ) -> (let _35_982 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _35_975)::(Support.Microsoft.FStar.Util.Inl (wlp), _35_970)::[] -> begin
(wp, wlp)
end
| _35_979 -> begin
(let _68_15178 = (let _68_15177 = (let _68_15176 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.Prims.pipe_right _68_15176 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _68_15177))
in (failwith (_68_15178)))
end)
in (match (_35_982) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c ) ( m ) ( lift ) -> (let _35_990 = (destruct_comp c)
in (match (_35_990) with
| (_35_987, wp, wlp) -> begin
(let _68_15200 = (let _68_15199 = (let _68_15195 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15195))
in (let _68_15198 = (let _68_15197 = (let _68_15196 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15196))
in (_68_15197)::[])
in (_68_15199)::_68_15198))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15200; Microsoft_FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun ( env ) ( l ) -> (let rec find = (fun ( l ) -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some ((_35_998, c)) -> begin
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
(let _35_1012 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str m)
in m)
end)
end)
in res))))

let join_effects = (fun ( env ) ( l1 ) ( l2 ) -> (let _35_1023 = (let _68_15214 = (norm_eff_name env l1)
in (let _68_15213 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _68_15214 _68_15213)))
in (match (_35_1023) with
| (m, _35_1020, _35_1022) -> begin
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
in (let _35_1035 = (Microsoft_FStar_Tc_Env.join env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (match (_35_1035) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env m)
in (let _35_1041 = (Microsoft_FStar_Tc_Env.wp_signature env md.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_35_1041) with
| (a, kwp) -> begin
(let _68_15228 = (destruct_comp m1)
in (let _68_15227 = (destruct_comp m2)
in ((md, a, kwp), _68_15228, _68_15227)))
end)))))
end)))))

let is_pure_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md ) ( result ) ( wp ) ( wlp ) ( flags ) -> (let _68_15251 = (let _68_15250 = (let _68_15249 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _68_15248 = (let _68_15247 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15247)::[])
in (_68_15249)::_68_15248))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15250; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_15251)))

let lcomp_of_comp = (fun ( c0 ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1055 ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst ) ( lc ) -> (let _35_1058 = lc
in (let _68_15261 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1058.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _68_15261; Microsoft_FStar_Absyn_Syntax.cflags = _35_1058.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1060 ) -> (match (()) with
| () -> begin
(let _68_15260 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _68_15260))
end))})))

let is_function = (fun ( t ) -> (match ((let _68_15264 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_15264.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_35_1063) -> begin
true
end
| _35_1066 -> begin
false
end))

let return_value = (fun ( env ) ( t ) ( v ) -> (let c = (match ((Microsoft_FStar_Tc_Env.effect_decl_opt env Microsoft_FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _35_1075 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_35_1075) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _68_15276 = (let _68_15275 = (let _68_15274 = (let _68_15273 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15272 = (let _68_15271 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_68_15271)::[])
in (_68_15273)::_68_15272))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _68_15274))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15275 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _68_15276))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _35_1080 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_15279 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15278 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _68_15277 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _68_15279 _68_15278 _68_15277))))
end
| false -> begin
()
end)
in c)))

let bind = (fun ( env ) ( e1opt ) ( lc1 ) ( _35_1087 ) -> (match (_35_1087) with
| (b, lc2) -> begin
(let _35_1098 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _35_1091))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| _35_1096 -> begin
"??"
end)
in (let _68_15289 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _68_15288 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _68_15289 bstr _68_15288))))
end
| false -> begin
()
end)
in (let bind_it = (fun ( _35_1101 ) -> (match (()) with
| () -> begin
(let c1 = (lc1.Microsoft_FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.Microsoft_FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun ( _35_1105 ) -> (match (()) with
| () -> begin
(let aux = (fun ( _35_1107 ) -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Absyn_Util.is_trivial_wp c1)) with
| true -> begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid (_35_1110)) -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_var (_35_1114)) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c2)) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end
| _35_1118 -> begin
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
| (Some (e), Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _35_1123)))) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((Microsoft_FStar_Absyn_Syntax.is_null_bvd x))))) with
| true -> begin
(let _68_15297 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.Prims.pipe_left (fun ( _68_15296 ) -> Some (_68_15296)) _68_15297))
end
| false -> begin
(aux ())
end)
end
| _35_1129 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _35_1147 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("bind")))) with
| true -> begin
(let _68_15301 = (match (b) with
| None -> begin
"None"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _35_1135))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, _35_1141))) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| _35_1146 -> begin
"Something else"
end)
in (let _68_15300 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _68_15299 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _68_15298 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _68_15301 _68_15300 _68_15299 _68_15298)))))
end
| false -> begin
()
end)
in c)
end
| None -> begin
(let _35_1162 = (lift_and_destruct env c1 c2)
in (match (_35_1162) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _68_15302 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_68_15302)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _68_15303 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_68_15303)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _68_15304 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_68_15304)::[])
end
| _35_1175 -> begin
(failwith ("Unexpected type-variable binding"))
end)
in (let mk_lam = (fun ( wp ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _68_15319 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_15318 = (let _68_15317 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _68_15316 = (let _68_15315 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _68_15314 = (let _68_15313 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _68_15312 = (let _68_15311 = (let _68_15307 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15307))
in (let _68_15310 = (let _68_15309 = (let _68_15308 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15308))
in (_68_15309)::[])
in (_68_15311)::_68_15310))
in (_68_15313)::_68_15312))
in (_68_15315)::_68_15314))
in (_68_15317)::_68_15316))
in (_68_15319)::_68_15318))
in (let wlp_args = (let _68_15327 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_15326 = (let _68_15325 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _68_15324 = (let _68_15323 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _68_15322 = (let _68_15321 = (let _68_15320 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15320))
in (_68_15321)::[])
in (_68_15323)::_68_15322))
in (_68_15325)::_68_15324))
in (_68_15327)::_68_15326))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _68_15328 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15328; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env ) ( t ) ( mk_wp ) ( mk_wlp ) ( f ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _35_1193 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_35_1193) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _68_15343 = (let _68_15342 = (let _68_15341 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15340 = (let _68_15339 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_68_15339)::[])
in (_68_15341)::_68_15340))
in (mk_wp, _68_15342))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15343 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15348 = (let _68_15347 = (let _68_15346 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15345 = (let _68_15344 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_68_15344)::[])
in (_68_15346)::_68_15345))
in (mk_wlp, _68_15347))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15348 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md_pure Microsoft_FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.Microsoft_FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun ( env ) ( b ) ( lc ) -> (let refresh = (fun ( _35_1202 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_35_1205) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _35_1209 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_15360 = (let _68_15359 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_15359))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _68_15360))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1212 = (match (((Support.Prims.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name)) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low))) with
| true -> begin
(let _68_15363 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _68_15362 = (let _68_15361 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _68_15361))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _68_15363 _68_15362)))
end
| false -> begin
()
end)
in (let _35_1217 = (destruct_comp c')
in (match (_35_1217) with
| (t, wp, wlp) -> begin
(let wp = (let _68_15366 = (let _68_15365 = (let _68_15364 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _68_15364))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_68_15365))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_15366))
in (let wlp = (let _68_15369 = (let _68_15368 = (let _68_15367 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _68_15367))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_68_15368))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_15369))
in (let _68_15374 = (let _35_1220 = c'
in (let _68_15373 = (let _68_15372 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _68_15371 = (let _68_15370 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15370)::[])
in (_68_15372)::_68_15371))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _35_1220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _35_1220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15373; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_15374))))
end)))))
end)
end))
end))
in (let _35_1222 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1222.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1222.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _35_1222.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = refresh})))

let label = (fun ( reason ) ( r ) ( f ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun ( env ) ( reason ) ( r ) ( f ) -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(match ((let _68_15398 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15398))) with
| true -> begin
f
end
| false -> begin
(let _68_15399 = (reason ())
in (label _68_15399 r f))
end)
end))

let label_guard = (fun ( reason ) ( r ) ( g ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _68_15406 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_68_15406))
end))

let weaken_guard = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _35_1249 -> begin
g2
end))

let weaken_precondition = (fun ( env ) ( lc ) ( f ) -> (let weaken = (fun ( _35_1254 ) -> (match (()) with
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
in (let _35_1263 = (destruct_comp c)
in (match (_35_1263) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _68_15425 = (let _68_15424 = (let _68_15423 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15422 = (let _68_15421 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15420 = (let _68_15419 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15419)::[])
in (_68_15421)::_68_15420))
in (_68_15423)::_68_15422))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15424))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15425 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15432 = (let _68_15431 = (let _68_15430 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15429 = (let _68_15428 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15427 = (let _68_15426 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15426)::[])
in (_68_15428)::_68_15427))
in (_68_15430)::_68_15429))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15431))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15432 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end)))
end)
end))
end))
in (let _35_1267 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1267.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1267.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _35_1267.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun ( reason ) ( env ) ( e ) ( lc ) ( g0 ) -> (match ((Microsoft_FStar_Tc_Rel.is_trivial g0)) with
| true -> begin
(lc, g0)
end
| false -> begin
(let flags = (Support.Prims.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _35_6 ) -> (match (_35_6) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _35_1278 -> begin
[]
end))))
in (let strengthen = (fun ( _35_1281 ) -> (match (()) with
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
in (let xret = (let _68_15454 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _68_15454))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _68_15457 = (lcomp_of_comp c)
in (let _68_15456 = (let _68_15455 = (lcomp_of_comp xret)
in (Some (xbinding), _68_15455))
in (bind env (Some (e)) _68_15457 _68_15456)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ())))))
end
| false -> begin
c
end)
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1296 = (destruct_comp c)
in (match (_35_1296) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _68_15466 = (let _68_15465 = (let _68_15464 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15463 = (let _68_15462 = (let _68_15459 = (let _68_15458 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _68_15458 f))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15459))
in (let _68_15461 = (let _68_15460 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15460)::[])
in (_68_15462)::_68_15461))
in (_68_15464)::_68_15463))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _68_15465))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15466 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15473 = (let _68_15472 = (let _68_15471 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15470 = (let _68_15469 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15468 = (let _68_15467 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15467)::[])
in (_68_15469)::_68_15468))
in (_68_15471)::_68_15470))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15472))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15473 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _68_15477 = (let _35_1301 = lc
in (let _68_15476 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _68_15475 = (match (((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (let _68_15474 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15474)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15476; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1301.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _68_15475; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_68_15477, (let _35_1303 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _35_1303.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _35_1303.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env ) ( comp ) ( res_t ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _35_1313 = (let _68_15485 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _68_15484 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_68_15485, _68_15484)))
in (match (_35_1313) with
| (xexp, yexp) -> begin
(let yret = (let _68_15490 = (let _68_15489 = (let _68_15488 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15487 = (let _68_15486 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_68_15486)::[])
in (_68_15488)::_68_15487))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _68_15489))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15490 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _68_15498 = (let _68_15497 = (let _68_15496 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15495 = (let _68_15494 = (let _68_15491 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15491))
in (let _68_15493 = (let _68_15492 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_68_15492)::[])
in (_68_15494)::_68_15493))
in (_68_15496)::_68_15495))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15497))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15498 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _68_15509 = (let _68_15508 = (let _68_15507 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15506 = (let _68_15505 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15504 = (let _68_15503 = (let _68_15502 = (let _68_15501 = (let _68_15500 = (let _68_15499 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_68_15499)::[])
in (_68_15500, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15501 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15502))
in (_68_15503)::[])
in (_68_15505)::_68_15504))
in (_68_15507)::_68_15506))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _68_15508))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15509 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _68_15512 = (lcomp_of_comp comp)
in (let _68_15511 = (let _68_15510 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _68_15510))
in (bind env None _68_15512 _68_15511)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun ( env ) ( guard ) ( lcomp_then ) ( lcomp_else ) -> (let comp = (fun ( _35_1324 ) -> (match (()) with
| () -> begin
(let _35_1340 = (let _68_15524 = (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _68_15523 = (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _68_15524 _68_15523)))
in (match (_35_1340) with
| ((md, _35_1327, _35_1329), (res_t, wp_then, wlp_then), (_35_1336, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _68_15544 = (let _68_15542 = (let _68_15541 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15540 = (let _68_15539 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _68_15538 = (let _68_15537 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _68_15536 = (let _68_15535 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_68_15535)::[])
in (_68_15537)::_68_15536))
in (_68_15539)::_68_15538))
in (_68_15541)::_68_15540))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _68_15542))
in (let _68_15543 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15544 None _68_15543))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _68_15551 = (let _68_15550 = (let _68_15549 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15548 = (let _68_15547 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _68_15546 = (let _68_15545 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15545)::[])
in (_68_15547)::_68_15546))
in (_68_15549)::_68_15548))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _68_15550))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15551 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15556 = (let _68_15555 = (let _68_15554 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15553 = (let _68_15552 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15552)::[])
in (_68_15554)::_68_15553))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _68_15555))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15556 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _68_15557 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15557; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun ( env ) ( res_t ) ( lcases ) -> (let eff = (match (lcases) with
| [] -> begin
(failwith ("Empty cases!"))
end
| hd::tl -> begin
(Support.List.fold_left (fun ( eff ) ( _35_1363 ) -> (match (_35_1363) with
| (_35_1361, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun ( _35_1366 ) -> (match (()) with
| () -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _68_15587 = (let _68_15585 = (let _68_15584 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15583 = (let _68_15582 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _68_15581 = (let _68_15580 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _68_15579 = (let _68_15578 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_68_15578)::[])
in (_68_15580)::_68_15579))
in (_68_15582)::_68_15581))
in (_68_15584)::_68_15583))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _68_15585))
in (let _68_15586 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15587 None _68_15586))))
in (let default_case = (let post_k = (let _68_15590 = (let _68_15589 = (let _68_15588 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_68_15588)::[])
in (_68_15589, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_15590 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _68_15593 = (let _68_15592 = (let _68_15591 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_68_15591)::[])
in (_68_15592, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_15593 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _68_15594 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_15594 post_k))
in (let wp = (let _68_15601 = (let _68_15600 = (let _68_15595 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_68_15595)::[])
in (let _68_15599 = (let _68_15598 = (let _68_15596 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _68_15596))
in (let _68_15597 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_left _68_15598 _68_15597)))
in (_68_15600, _68_15599)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15601 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15605 = (let _68_15604 = (let _68_15602 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_68_15602)::[])
in (let _68_15603 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_68_15604, _68_15603)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15605 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _35_1382 ) ( celse ) -> (match (_35_1382) with
| (g, cthen) -> begin
(let _35_1400 = (let _68_15608 = (cthen.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _68_15608 celse))
in (match (_35_1400) with
| ((md, _35_1386, _35_1388), (_35_1391, wp_then, wlp_then), (_35_1396, wp_else, wlp_else)) -> begin
(let _68_15610 = (ifthenelse md res_t g wp_then wp_else)
in (let _68_15609 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _68_15610 _68_15609 [])))
end))
end)) lcases default_case)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| false -> begin
(let comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env comp.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _35_1408 = (destruct_comp comp)
in (match (_35_1408) with
| (_35_1405, wp, wlp) -> begin
(let wp = (let _68_15617 = (let _68_15616 = (let _68_15615 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15614 = (let _68_15613 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _68_15612 = (let _68_15611 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15611)::[])
in (_68_15613)::_68_15612))
in (_68_15615)::_68_15614))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _68_15616))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15617 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15622 = (let _68_15621 = (let _68_15620 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15619 = (let _68_15618 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15618)::[])
in (_68_15620)::_68_15619))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _68_15621))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15622 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = eff; Microsoft_FStar_Absyn_Syntax.res_typ = res_t; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun ( env ) ( bindings ) ( lc ) -> (let close = (fun ( _35_1415 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let close_wp = (fun ( md ) ( res_t ) ( bindings ) ( wp0 ) -> (Support.List.fold_right (fun ( b ) ( wp ) -> (match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let bs = (let _68_15641 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_68_15641)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15648 = (let _68_15647 = (let _68_15646 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15645 = (let _68_15644 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15643 = (let _68_15642 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15642)::[])
in (_68_15644)::_68_15643))
in (_68_15646)::_68_15645))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _68_15647))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15648 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _68_15649 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_68_15649)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15654 = (let _68_15653 = (let _68_15652 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15651 = (let _68_15650 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15650)::[])
in (_68_15652)::_68_15651))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _68_15653))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15654 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((l, t)) -> begin
wp
end
| Microsoft_FStar_Tc_Env.Binding_sig (s) -> begin
(failwith ("impos"))
end)) bindings wp0))
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1446 = (destruct_comp c)
in (match (_35_1446) with
| (t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.Microsoft_FStar_Absyn_Syntax.result_typ wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end))))
end))
end))
in (let _35_1450 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1450.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1450.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _35_1450.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun ( env ) ( e ) ( lc ) -> (let refine = (fun ( _35_1456 ) -> (match (()) with
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
in (let ret = (let _68_15663 = (return_value env t xexp)
in (Support.Prims.pipe_left lcomp_of_comp _68_15663))
in (let eq_ret = (let _68_15665 = (let _68_15664 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_68_15664))
in (weaken_precondition env ret _68_15665))
in (let _68_15668 = (let _68_15667 = (let _68_15666 = (lcomp_of_comp c)
in (bind env None _68_15666 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_68_15667.Microsoft_FStar_Absyn_Syntax.comp ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _68_15668 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
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
in (let _35_1466 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1466.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1466.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun ( env ) ( e ) ( c ) ( c' ) -> (match ((Microsoft_FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _68_15680 = (let _68_15679 = (let _68_15678 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _68_15677 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_15678, _68_15677)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_15679))
in (raise (_68_15680)))
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
(let rec aux = (fun ( subst ) ( _35_7 ) -> (match (_35_7) with
| (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_1496 = (new_implicit_tvar env k)
in (match (_35_1496) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _35_1502 = (aux subst rest)
in (match (_35_1502) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_1513 = (new_implicit_evar env t)
in (match (_35_1513) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _35_1519 = (aux subst rest)
in (match (_35_1519) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _35_1525 = (aux [] bs)
in (match (_35_1525) with
| (args, bs, subst, implicits) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst k)
in (let _68_15691 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_15691, k, implicits))))
end)))
end
| _35_1529 -> begin
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
(let rec aux = (fun ( subst ) ( _35_8 ) -> (match (_35_8) with
| (Support.Microsoft.FStar.Util.Inl (a), _35_1545)::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_1551 = (new_implicit_tvar env k)
in (match (_35_1551) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _35_1557 = (aux subst rest)
in (match (_35_1557) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_1568 = (new_implicit_evar env t)
in (match (_35_1568) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _35_1574 = (aux subst rest)
in (match (_35_1574) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _35_1580 = (aux [] bs)
in (match (_35_1580) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun ( e ) ( args ) ( t ) -> (match (args) with
| [] -> begin
e
end
| _35_1587 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
in (let _68_15708 = (mk_exp_app e args (Some (t)))
in (_68_15708, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _35_1591 -> begin
(let t = (let _68_15709 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _68_15709 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _68_15710 = (mk_exp_app e args (Some (t)))
in (_68_15710, t, implicits)))
end))
end)))
end
| _35_1594 -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env ) ( e ) ( lc ) ( t ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _68_15719 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_68_15719, false))
end
| false -> begin
(let _68_15720 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_68_15720, true))
end)
in (match (gopt) with
| (None, _35_1602) -> begin
(Microsoft_FStar_Tc_Rel.subtype_fail env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (Microsoft_FStar_Tc_Rel.simplify_guard env g)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(let lc = (let _35_1610 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1610.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _35_1610.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _35_1610.Microsoft_FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _35_1615 = g
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _35_1615.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _35_1615.Microsoft_FStar_Tc_Rel.implicits})
in (let strengthen = (fun ( _35_1619 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _35_1621 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_15724 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _68_15723 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _68_15724 _68_15723)))
end
| false -> begin
()
end)
in (let ct = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1626 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_35_1626) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (let _68_15729 = (let _68_15728 = (let _68_15727 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15726 = (let _68_15725 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_68_15725)::[])
in (_68_15727)::_68_15726))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _68_15728))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15729 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _68_15730 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.Prims.pipe_left lcomp_of_comp _68_15730))
in (let guard = (match (apply_guard) with
| true -> begin
(let _68_15733 = (let _68_15732 = (let _68_15731 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_68_15731)::[])
in (f, _68_15732))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15733 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _35_1636 = (let _68_15741 = (Support.Prims.pipe_left (fun ( _68_15738 ) -> Some (_68_15738)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _68_15740 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15739 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _68_15741 _68_15740 e cret _68_15739))))
in (match (_35_1636) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _68_15743 = (let _68_15742 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.Prims.pipe_left lcomp_of_comp _68_15742))
in (bind env (Some (e)) _68_15743 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _35_1639 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_15744 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _68_15744))
end
| false -> begin
()
end)
in c)))
end)))))))))
end)))))
end))
in (let flags = (Support.Prims.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _35_9 ) -> (match (_35_9) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _35_1645 -> begin
[]
end))))
in (let lc = (let _35_1647 = lc
in (let _68_15746 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15746; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r ) ( t ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0)) with
| true -> begin
(let ue = (let _68_15751 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _68_15751))
in (let ut = (let _68_15752 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _68_15752))
in (let uk = (let _68_15753 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _68_15753))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _35_1659 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _35_1661 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _35_1663 = (let _68_15755 = (let _68_15754 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _68_15754))
in (Microsoft_FStar_Tc_Errors.report r _68_15755))
in (let _35_1665 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify ) ( env ) ( ecs ) -> (match ((let _68_15763 = (Support.Microsoft.FStar.Util.for_all (fun ( _35_1673 ) -> (match (_35_1673) with
| (_35_1671, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15763))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c ) -> (let _35_1676 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15766 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _68_15766))
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
in (let _35_1680 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15767 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _68_15767))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs ) -> (let _68_15770 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.Prims.pipe_right _68_15770 Support.Microsoft.FStar.Util.set_elements)))
in (let should_gen = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _35_1689)) -> begin
(match ((Support.Prims.pipe_right bs (Support.Microsoft.FStar.Util.for_some (fun ( _35_10 ) -> (match (_35_10) with
| (Support.Microsoft.FStar.Util.Inl (_35_1694), _35_1697) -> begin
true
end
| _35_1700 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
true
end)
end
| _35_1702 -> begin
true
end))
in (let uvars = (Support.Prims.pipe_right ecs (Support.List.map (fun ( _35_1705 ) -> (match (_35_1705) with
| (e, c) -> begin
(let t = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.compress_typ)
in (match ((let _68_15775 = (should_gen t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15775))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _35_1721 = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (let _68_15776 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15776)))) with
| true -> begin
(let _35_1717 = (destruct_comp ct)
in (match (_35_1717) with
| (_35_1713, wp, _35_1716) -> begin
(let binder = (let _68_15777 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_68_15777)::[])
in (let post = (let _68_15781 = (let _68_15778 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _68_15778))
in (let _68_15780 = (let _68_15779 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_68_15779))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15781 _68_15780 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _68_15788 = (let _68_15787 = (let _68_15786 = (let _68_15785 = (let _68_15784 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_68_15784)::[])
in (wp, _68_15785))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15786))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _68_15787))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _68_15788))
in (let _68_15789 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _68_15789)))))
end))
end
| false -> begin
()
end)
in (uvs, e, c)))))))
end))
end))))
in (let ecs = (Support.Prims.pipe_right uvars (Support.List.map (fun ( _35_1727 ) -> (match (_35_1727) with
| (uvs, e, c) -> begin
(let tvars = (Support.Prims.pipe_right uvs (Support.List.map (fun ( _35_1730 ) -> (match (_35_1730) with
| (u, k) -> begin
(let a = (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) | (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)
end
| Microsoft_FStar_Absyn_Syntax.Fixed (_35_1768) -> begin
(failwith ("Unexpected instantiation of mutually recursive uvar"))
end
| _35_1771 -> begin
(let a = (let _68_15794 = (let _68_15793 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left (fun ( _68_15792 ) -> Some (_68_15792)) _68_15793))
in (Microsoft_FStar_Absyn_Util.new_bvd _68_15794))
in (let t = (let _68_15795 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _68_15795 k))
in (let _35_1774 = (Microsoft_FStar_Absyn_Util.unchecked_unify u t)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.ktype))))
end)
in (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
end))))
in (let t = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.function_formals)) with
| Some ((bs, cod)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.append tvars bs), cod) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _35_1785 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _35_1789 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _68_15796 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _68_15796)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify ) ( env ) ( lecs ) -> (let _35_1801 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_15805 = (let _68_15804 = (Support.List.map (fun ( _35_1800 ) -> (match (_35_1800) with
| (lb, _35_1797, _35_1799) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.Prims.pipe_right _68_15804 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _68_15805))
end
| false -> begin
()
end)
in (match ((let _68_15807 = (Support.Prims.pipe_right lecs (Support.List.map (fun ( _35_1807 ) -> (match (_35_1807) with
| (_35_1804, e, c) -> begin
(e, c)
end))))
in (gen verify env _68_15807))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _35_1816 ) ( _35_1819 ) -> (match ((_35_1816, _35_1819)) with
| ((l, _35_1813, _35_1815), (e, c)) -> begin
(let _35_1820 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15812 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15811 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _68_15810 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _68_15812 _68_15811 _68_15810))))
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
| _35_1825 -> begin
false
end))

let check_top_level = (fun ( env ) ( g ) ( lc ) -> (let discharge = (fun ( g ) -> (let _35_1831 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _35_1849 = (match ((Support.Prims.pipe_right g.Microsoft_FStar_Tc_Rel.implicits (Support.List.tryFind (fun ( _35_11 ) -> (match (_35_11) with
| Support.Microsoft.FStar.Util.Inl (u) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr ((u, _35_1838)) -> begin
(unresolved u)
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr ((_35_1842, r))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _35_1848 -> begin
()
end)
in (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Absyn_Util.is_total_lcomp lc)) with
| true -> begin
(let _68_15824 = (discharge g)
in (let _68_15823 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (_68_15824, _68_15823)))
end
| false -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _68_15825 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.Prims.pipe_right _68_15825 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _35_1860 = (destruct_comp c)
in (match (_35_1860) with
| (t, wp, _35_1859) -> begin
(let vc = (let _68_15831 = (let _68_15829 = (let _68_15828 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15827 = (let _68_15826 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15826)::[])
in (_68_15828)::_68_15827))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _68_15829))
in (let _68_15830 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15831 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _68_15830)))
in (let g = (let _68_15832 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_15832))
in (let _68_15834 = (discharge g)
in (let _68_15833 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_68_15834, _68_15833)))))
end))))))
end))))

let short_circuit_exp = (fun ( head ) ( seen_args ) -> (let short_bin_op_e = (fun ( f ) -> (fun ( _35_12 ) -> (match (_35_12) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _35_1872)::[] -> begin
(let _68_15853 = (f fst)
in (Support.Prims.pipe_right _68_15853 (fun ( _68_15852 ) -> Some (_68_15852))))
end
| _35_1876 -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let table = (let op_and_e = (fun ( e ) -> (let _68_15859 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_68_15859, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e ) -> (let _68_15863 = (let _68_15862 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _68_15862))
in (_68_15863, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _35_1884)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1890 ) -> (match (_35_1890) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _68_15881 = (mk seen_args)
in Some (_68_15881))
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
| _35_1895 -> begin
None
end))))

let short_circuit_typ = (fun ( head ) ( seen_args ) -> (let short_bin_op_t = (fun ( f ) -> (fun ( _35_13 ) -> (match (_35_13) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _35_1905)::[] -> begin
(f fst)
end
| _35_1909 -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let op_and_t = (fun ( t ) -> (let _68_15902 = (unlabel t)
in (Support.Prims.pipe_right _68_15902 (fun ( _68_15901 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15901)))))
in (let op_or_t = (fun ( t ) -> (let _68_15907 = (let _68_15905 = (unlabel t)
in (Support.Prims.pipe_right _68_15905 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.Prims.pipe_right _68_15907 (fun ( _68_15906 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15906)))))
in (let op_imp_t = (fun ( t ) -> (let _68_15911 = (unlabel t)
in (Support.Prims.pipe_right _68_15911 (fun ( _68_15910 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15910)))))
in (let short_op_ite = (fun ( _35_14 ) -> (match (_35_14) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _35_1921)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _35_1927)::[] -> begin
(let _68_15915 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.Prims.pipe_right _68_15915 (fun ( _68_15914 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15914))))
end
| _35_1932 -> begin
(failwith ("Unexpected args to ITE"))
end))
in (let table = ((Microsoft_FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((Microsoft_FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((Microsoft_FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((Microsoft_FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| Support.Microsoft.FStar.Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some ((g, _35_1940)) -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (g)
end)
end
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _35_1950; Microsoft_FStar_Absyn_Syntax.pos = _35_1948; Microsoft_FStar_Absyn_Syntax.fvs = _35_1946; Microsoft_FStar_Absyn_Syntax.uvs = _35_1944}) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1958 ) -> (match (_35_1958) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _68_15942 = (mk seen_args)
in Some (_68_15942))
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
| _35_1963 -> begin
Microsoft_FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun ( env ) ( comp ) -> (let mk_post_type = (fun ( res_t ) ( ens ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _68_15956 = (let _68_15955 = (let _68_15954 = (let _68_15953 = (let _68_15952 = (let _68_15951 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _68_15951))
in (_68_15952)::[])
in (ens, _68_15953))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15954 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _68_15955))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _68_15956 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
in (let norm = (fun ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Unlabel)::[]) env t))
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp comp)) with
| true -> begin
(None, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| false -> begin
(match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_35_1973) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (req), _35_1988)::(Support.Microsoft.FStar.Util.Inl (ens), _35_1982)::_35_1978 -> begin
(let _68_15962 = (let _68_15959 = (norm req)
in Some (_68_15959))
in (let _68_15961 = (let _68_15960 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.Prims.pipe_left norm _68_15960))
in (_68_15962, _68_15961)))
end
| _35_1992 -> begin
(failwith ("Impossible"))
end)
end
| false -> begin
(let comp = (Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_35_1995) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _35_2010)::(Support.Microsoft.FStar.Util.Inl (wlp), _35_2004)::_35_2000 -> begin
(let _35_2022 = (match ((let _68_15964 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _68_15963 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_68_15964, _68_15963)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _35_2019 -> begin
(failwith ("Impossible"))
end)
in (match (_35_2022) with
| (as_req, as_ens) -> begin
(let req = (let _68_15968 = (let _68_15967 = (let _68_15966 = (let _68_15965 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15965)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_15966)
in (as_req, _68_15967))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15968 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _68_15972 = (let _68_15971 = (let _68_15970 = (let _68_15969 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15969)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_15970)
in (as_ens, _68_15971))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15972 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _68_15976 = (let _68_15973 = (norm req)
in Some (_68_15973))
in (let _68_15975 = (let _68_15974 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _68_15974))
in (_68_15976, _68_15975)))))
end))
end
| _35_2026 -> begin
(failwith ("Impossible"))
end)
end))
end)
end)
end))))




