
let try_solve = (fun ( env ) ( f ) -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun ( env ) ( errs ) -> (let _68_14744 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14743 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _68_14744 _68_14743))))

let discharge_guard = (fun ( env ) ( g ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env ) ( g ) -> (discharge_guard env g))

let syn' = (fun ( env ) ( k ) -> (let _68_14763 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _68_14763 k)))

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
(let _68_14787 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.Prims.pipe_left (fun ( _68_14786 ) -> Some (_68_14786)) _68_14787))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _68_14791 = (let _68_14790 = (let _68_14789 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _68_14788 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14789, _68_14788)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14790))
in (raise (_68_14791)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _68_14795 = (let _68_14794 = (let _68_14793 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _68_14792 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14793, _68_14792)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14794))
in (raise (_68_14795)))
end
| Some (g) -> begin
(let _35_49 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14796 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _68_14796))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t2) (Some (t2)) e.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(let _35_56 = e
in (let _68_14797 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _35_56.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _68_14797; Microsoft_FStar_Absyn_Syntax.pos = _35_56.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _35_56.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _35_56.Microsoft_FStar_Absyn_Syntax.uvs}))
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
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
uv
end
| _ -> begin
(failwith ("Impossible"))
end))

let as_uvar_t = (fun ( t ) -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
uv
end
| _ -> begin
(failwith ("Impossible"))
end))

let new_kvar = (fun ( env ) -> (let _68_14807 = (let _68_14806 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14805 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _68_14806 _68_14805)))
in (Support.Prims.pipe_right _68_14807 Support.Prims.fst)))

let new_tvar = (fun ( env ) ( k ) -> (let _68_14814 = (let _68_14813 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14812 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _68_14813 _68_14812 k)))
in (Support.Prims.pipe_right _68_14814 Support.Prims.fst)))

let new_evar = (fun ( env ) ( t ) -> (let _68_14821 = (let _68_14820 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14819 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _68_14820 _68_14819 t)))
in (Support.Prims.pipe_right _68_14821 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env ) ( k ) -> (let _35_103 = (let _68_14827 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14826 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _68_14827 _68_14826 k)))
in (match (_35_103) with
| (t, u) -> begin
(let _68_14829 = (let _68_14828 = (as_uvar_t u)
in (_68_14828, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _68_14829))
end)))

let new_implicit_evar = (fun ( env ) ( t ) -> (let _35_108 = (let _68_14835 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14834 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _68_14835 _68_14834 t)))
in (match (_35_108) with
| (e, u) -> begin
(let _68_14837 = (let _68_14836 = (as_uvar_e u)
in (_68_14836, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _68_14837))
end)))

let force_tk = (fun ( s ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _68_14840 = (let _68_14839 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _68_14839))
in (failwith (_68_14840)))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args ) -> (Support.Prims.pipe_right args (Support.List.map (fun ( _35_2 ) -> (match (_35_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _68_14845 = (let _68_14844 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_68_14844))
in (_68_14845, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _68_14847 = (let _68_14846 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_68_14846))
in (_68_14847, imp))
end)))))

let is_implicit = (fun ( _35_3 ) -> (match (_35_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _ -> begin
false
end))

let destruct_arrow_kind = (fun ( env ) ( tt ) ( k ) ( args ) -> (let ktop = (let _68_14858 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.Prims.pipe_right _68_14858 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_, qual)::_ -> begin
(is_implicit qual)
end
| _ -> begin
false
end)
in (let rec mk_implicits = (fun ( vars ) ( subst ) ( bs ) -> (match (bs) with
| b::brest -> begin
(match ((Support.Prims.pipe_right (Support.Prims.snd b) is_implicit)) with
| true -> begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_14871 = (let _68_14868 = (let _68_14867 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _68_14867))
in (Support.Prims.pipe_right _68_14868 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14871 (fun ( x ) -> (let _68_14870 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _68_14870)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_14876 = (let _68_14873 = (let _68_14872 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _68_14872))
in (Support.Prims.pipe_right _68_14873 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14876 (fun ( x ) -> (let _68_14875 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _68_14875)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _68_14877 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_68_14877)::subst)
end)
in (let _35_167 = (mk_implicits vars subst brest)
in (match (_35_167) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _68_14878 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _68_14878))
end)
end
| _ -> begin
(let _68_14879 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _68_14879))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _35_172 = (let _68_14880 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _68_14880 [] bs))
in (match (_35_172) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _68_14881 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.Prims.pipe_right _68_14881 Support.Prims.fst))
in (let bs = (let _68_14882 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _68_14882))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _35_186 = (let _68_14883 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.Prims.pipe_left (force_trivial env) _68_14883))
in ([], bs, kres)))))))
end
| _ -> begin
(let _68_14886 = (let _68_14885 = (let _68_14884 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_68_14884, r))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14885))
in (raise (_68_14886)))
end))
in (aux ktop)))))

let pat_as_exps = (fun ( allow_implicits ) ( env ) ( p ) -> (let pvar_eq = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _)), Microsoft_FStar_Tc_Env.Binding_var ((y, _))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _ -> begin
false
end))
in (let vars_of_bindings = (fun ( bs ) -> (Support.Prims.pipe_right bs (Support.List.map (fun ( _35_4 ) -> (match (_35_4) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _ -> begin
(failwith ("impos"))
end)))))
in (let rec pat_as_arg_with_env = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _35_247 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_35_247) with
| (e, u) -> begin
(let p = (let _35_248 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _35_248.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_248.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_14906 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _68_14906, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _)) -> begin
(let k = (new_kvar env)
in (let _35_259 = (let _68_14907 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _68_14907 k))
in (match (_35_259) with
| (t, u) -> begin
(let p = (let _35_260 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _35_260.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_260.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_14909 = (let _68_14908 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (t), _68_14908))
in ([], [], [], env, _68_14909, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14910 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _68_14910, p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _68_14912 = (let _68_14911 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_14911))
in Microsoft_FStar_Tc_Env.Binding_var (_68_14912))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14913 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ((w)::[], [], (w)::[], env, _68_14913, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)) -> begin
(let b = (let _68_14915 = (let _68_14914 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_14914))
in Microsoft_FStar_Tc_Env.Binding_var (_68_14915))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14917 = (let _68_14916 = (Microsoft_FStar_Absyn_Syntax.as_implicit imp)
in (Support.Microsoft.FStar.Util.Inr (e), _68_14916))
in ((b)::[], (b)::[], [], env, _68_14917, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _68_14919 = (let _68_14918 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_14918))
in Microsoft_FStar_Tc_Env.Binding_typ (_68_14919))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14920 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((w)::[], [], (w)::[], env, _68_14920, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _68_14922 = (let _68_14921 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_14921))
in Microsoft_FStar_Tc_Env.Binding_typ (_68_14922))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14923 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((b)::[], (b)::[], [], env, _68_14923, p)))))
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
(let e = (let _68_14931 = (let _68_14930 = (let _68_14929 = (let _68_14928 = (let _68_14927 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14926 = (Support.Prims.pipe_right args Support.List.rev)
in (_68_14927, _68_14926)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_14928 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_68_14929, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_14930))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_14931))
in (let _68_14935 = (Support.Prims.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _68_14934 = (Support.Prims.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _68_14933 = (Support.Prims.pipe_right (Support.List.rev w) Support.List.flatten)
in (let _68_14932 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_14935, _68_14934, _68_14933, env, _68_14932, (let _35_316 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _35_316.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_316.Microsoft_FStar_Absyn_Syntax.p})))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
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
| _ -> begin
(let _68_14942 = (let _68_14941 = (let _68_14940 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _68_14940))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14941))
in (raise (_68_14942)))
end)
end
| Some ((f, _)) -> begin
(let rec aux = (fun ( formals ) ( pats ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _::_) -> begin
(let _68_14949 = (let _68_14948 = (let _68_14947 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _68_14947))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14948))
in (raise (_68_14949)))
end
| (_::_, []) -> begin
(Support.Prims.pipe_right formals (Support.List.map (fun ( f ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let a = (let _68_14951 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_14951 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _68_14952 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _68_14952))
end
| false -> begin
(let _68_14953 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _68_14953))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _68_14954 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _68_14954)))
end
| _ -> begin
(let _68_14959 = (let _68_14958 = (let _68_14957 = (let _68_14955 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _68_14955))
in (let _68_14956 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_68_14957, _68_14956)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14958))
in (raise (_68_14959)))
end))))
end
| (f::formals', p::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _68_14960 = (aux formals' pats')
in (p)::_68_14960)
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) when allow_implicits -> begin
(let _68_14961 = (aux formals' pats')
in (p)::_68_14961)
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), _) -> begin
(let a = (let _68_14962 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_14962 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _68_14963 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _68_14963))
end
| false -> begin
(let _68_14964 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _68_14964))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_) -> begin
pats'
end
| _ -> begin
pats
end)
in (let _68_14965 = (aux formals' pats')
in (p1)::_68_14965))))
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_var ((_, true))) -> begin
(let _68_14966 = (aux formals' pats')
in (p)::_68_14966)
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _68_14967 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _68_14967))
in (let _68_14968 = (aux formals' pats)
in (p)::_68_14968)))
end
| ((Support.Microsoft.FStar.Util.Inr (_), _), _) -> begin
(let _68_14969 = (aux formals' pats')
in (p)::_68_14969)
end)
end))
in (aux f pats))
end)
in (let _35_463 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); Microsoft_FStar_Absyn_Syntax.sort = _35_463.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_463.Microsoft_FStar_Absyn_Syntax.p}))))
end
| _ -> begin
p
end))
in (let one_pat = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (let p = (elaborate_pat env p)
in (let _35_478 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_478) with
| (b, a, w, env, arg, p) -> begin
(match ((Support.Prims.pipe_right b (Support.Microsoft.FStar.Util.find_dup pvar_eq))) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _))) -> begin
(let _68_14978 = (let _68_14977 = (let _68_14976 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_68_14976, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14977))
in (raise (_68_14978)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _))) -> begin
(let _68_14981 = (let _68_14980 = (let _68_14979 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_68_14979, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14980))
in (raise (_68_14981)))
end
| _ -> begin
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
| (b, a, _, arg, q) -> begin
(let _35_523 = (Support.List.fold_right (fun ( p ) ( _35_513 ) -> (match (_35_513) with
| (w, args, pats) -> begin
(let _35_519 = (one_pat false env p)
in (match (_35_519) with
| (b', a', w', arg, p) -> begin
(match ((not ((Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a')))) with
| true -> begin
(let _68_14993 = (let _68_14992 = (let _68_14991 = (let _68_14989 = (vars_of_bindings a)
in (let _68_14988 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _68_14989 _68_14988)))
in (let _68_14990 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14991, _68_14990)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14992))
in (raise (_68_14993)))
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
| _ -> begin
(let _35_535 = (one_pat true env p)
in (match (_35_535) with
| (b, _, _, arg, p) -> begin
(b, (arg)::[], p)
end))
end))
in (let _35_539 = (top_level_pat_as_args env p)
in (match (_35_539) with
| (b, args, p) -> begin
(let exps = (Support.Prims.pipe_right args (Support.List.map (fun ( _35_5 ) -> (match (_35_5) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(failwith ("Impossible: top-level pattern must be an expression"))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
e
end))))
in (b, exps, p))
end)))))))))

let decorate_pattern = (fun ( env ) ( p ) ( exps ) -> (let qq = p
in (let rec aux = (fun ( p ) ( e ) -> (let pkg = (fun ( q ) ( t ) -> (let _68_15012 = (Support.Prims.pipe_left (fun ( _68_15011 ) -> Some (_68_15011)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _68_15012 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_), Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(let _68_15013 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _68_15013))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_579 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15016 = (let _68_15015 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15014 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15015 _68_15014)))
in (failwith (_68_15016)))
end
| false -> begin
()
end)
in (let _35_581 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _68_15018 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15017 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _68_15018 _68_15017)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _35_584 = x
in {Microsoft_FStar_Absyn_Syntax.v = _35_584.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _35_584.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_15019 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp))) _68_15019))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_592 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15022 = (let _68_15021 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15020 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15021 _68_15020)))
in (failwith (_68_15022)))
end
| false -> begin
()
end)
in (let x = (let _35_594 = x
in (let _68_15023 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_594.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_15023; Microsoft_FStar_Absyn_Syntax.p = _35_594.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)), _) -> begin
(let x = (let _35_605 = x
in (let _68_15024 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_15024; Microsoft_FStar_Absyn_Syntax.p = _35_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _))) -> begin
(let _35_619 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _68_15025 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_68_15025)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) -> begin
(let _35_644 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _68_15026 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_68_15026)))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats ) ( args ) ( argpats ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _68_15033 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _68_15033))
end
| (arg::args, argpat::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let x = (let _68_15034 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _68_15034))
in (let q = (let _68_15036 = (Support.Prims.pipe_left (fun ( _68_15035 ) -> Some (_68_15035)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _68_15036 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) -> begin
(let x = (let _68_15037 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _68_15037))
in (let q = (let _68_15039 = (Support.Prims.pipe_left (fun ( _68_15038 ) -> Some (_68_15038)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _68_15039 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inl (t), _), _) -> begin
(let pat = (aux_t argpat t)
in (match_args ((pat)::matched_pats) args argpats))
end
| ((Support.Microsoft.FStar.Util.Inr (e), _), _) -> begin
(let pat = (aux argpat e)
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _ -> begin
(let _68_15042 = (let _68_15041 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _68_15040 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _68_15041 _68_15040)))
in (failwith (_68_15042)))
end))
in (match_args [] args argpats))))
end
| _ -> begin
(let _68_15047 = (let _68_15046 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_15045 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _68_15044 = (let _68_15043 = (Support.Prims.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.Prims.pipe_right _68_15043 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _68_15046 _68_15045 _68_15044))))
in (failwith (_68_15047)))
end))))
and aux_t = (fun ( p ) ( t0 ) -> (let pkg = (fun ( q ) ( k ) -> (let _68_15055 = (Support.Prims.pipe_left (fun ( _68_15054 ) -> Some (_68_15054)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _68_15055 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_716 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15058 = (let _68_15057 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15056 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15057 _68_15056)))
in (failwith (_68_15058)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_723 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15061 = (let _68_15060 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15059 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15060 _68_15059)))
in (failwith (_68_15061)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_tvar (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _)), _) -> begin
(let k0 = (force_tk t0)
in (let a = (let _35_734 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_734.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k0; Microsoft_FStar_Absyn_Syntax.p = _35_734.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.Microsoft_FStar_Absyn_Syntax.sort)))
end
| _ -> begin
(let _68_15065 = (let _68_15064 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_15063 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _68_15062 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _68_15064 _68_15063 _68_15062))))
in (failwith (_68_15065)))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _68_15067 = (Support.Prims.pipe_left (fun ( _68_15066 ) -> Some (_68_15066)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _68_15067 p.Microsoft_FStar_Absyn_Syntax.p)))
end
| (_, e::[]) -> begin
(aux p e)
end
| _ -> begin
(failwith ("Unexpected number of patterns"))
end))))

let rec decorated_pattern_as_exp = (fun ( pat ) -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _ -> begin
(failwith ("top-level pattern should be decorated with a type"))
end)
in (let pkg = (fun ( f ) -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun ( p ) -> (let _35_766 = (decorated_pattern_as_either p)
in (match (_35_766) with
| (vars, te) -> begin
(let _68_15087 = (let _68_15086 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (te, _68_15086))
in (vars, _68_15087))
end)))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _68_15090 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _68_15090))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) -> begin
(let _68_15093 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _68_15093))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _35_785 = (let _68_15094 = (Support.Prims.pipe_right pats (Support.List.map pat_as_arg))
in (Support.Prims.pipe_right _68_15094 Support.List.unzip))
in (match (_35_785) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _68_15100 = (let _68_15099 = (let _68_15098 = (let _68_15097 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_68_15097, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_15098))
in (Support.Prims.pipe_right _68_15099 pkg))
in (vars, _68_15100)))
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
(let _68_15102 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _68_15102))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _ -> begin
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
| _ -> begin
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
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _35_873 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _35_850 ) ( _35_854 ) -> (match ((_35_850, _35_854)) with
| ((out, subst), (b, _)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(failwith ("impossible"))
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let _68_15110 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15110 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _68_15113 = (let _68_15112 = (let _68_15111 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15111 Support.Prims.fst))
in (bs, _68_15112))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15113 (Some (k)) r))
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _68_15115 = (let _68_15114 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_68_15114)::out)
in (_68_15115, subst)))))
end)
end)) ([], [])))
in (match (_35_873) with
| (args, _) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, (Support.List.rev args)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
end))
end
| _ -> begin
(failwith ("Impossible"))
end)))))))

let extract_lb_annotation = (fun ( env ) ( t ) ( e ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun ( scope ) ( a ) -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _68_15126 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.Prims.pipe_right _68_15126 Support.Prims.fst))
in ((let _35_886 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_886.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _35_886.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _ -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _68_15131 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15131 Support.Prims.fst))
in (match ((Microsoft_FStar_Absyn_Syntax.null_v_binder t)) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(x, false)
end
| _ -> begin
(failwith ("impos"))
end))
end
| _ -> begin
(match ((Microsoft_FStar_Absyn_Syntax.null_v_binder x.Microsoft_FStar_Absyn_Syntax.sort)) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(x, true)
end
| _ -> begin
(failwith ("impos"))
end)
end))
in (let rec aux = (fun ( vars ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
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
(let _68_15139 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _68_15138 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _68_15139 _68_15138)))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _ -> begin
(let _68_15141 = (let _68_15140 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15140 Support.Prims.fst))
in (e, _68_15141, false))
end))
in (let _68_15142 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _68_15142 e))))))
end
| _ -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun ( c ) -> (let _35_982 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (wlp), _)::[] -> begin
(wp, wlp)
end
| _ -> begin
(let _68_15147 = (let _68_15146 = (let _68_15145 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.Prims.pipe_right _68_15145 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _68_15146))
in (failwith (_68_15147)))
end)
in (match (_35_982) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c ) ( m ) ( lift ) -> (let _35_990 = (destruct_comp c)
in (match (_35_990) with
| (_, wp, wlp) -> begin
(let _68_15169 = (let _68_15168 = (let _68_15164 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15164))
in (let _68_15167 = (let _68_15166 = (let _68_15165 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15165))
in (_68_15166)::[])
in (_68_15168)::_68_15167))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15169; Microsoft_FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun ( env ) ( l ) -> (let rec find = (fun ( l ) -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some ((_, c)) -> begin
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

let join_effects = (fun ( env ) ( l1 ) ( l2 ) -> (let _35_1023 = (let _68_15183 = (norm_eff_name env l1)
in (let _68_15182 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _68_15183 _68_15182)))
in (match (_35_1023) with
| (m, _, _) -> begin
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
(let _68_15197 = (destruct_comp m1)
in (let _68_15196 = (destruct_comp m2)
in ((md, a, kwp), _68_15197, _68_15196)))
end)))))
end)))))

let is_pure_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md ) ( result ) ( wp ) ( wlp ) ( flags ) -> (let _68_15220 = (let _68_15219 = (let _68_15218 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _68_15217 = (let _68_15216 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15216)::[])
in (_68_15218)::_68_15217))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15219; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_15220)))

let lcomp_of_comp = (fun ( c0 ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1055 ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst ) ( lc ) -> (let _35_1058 = lc
in (let _68_15230 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1058.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _68_15230; Microsoft_FStar_Absyn_Syntax.cflags = _35_1058.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1060 ) -> (match (()) with
| () -> begin
(let _68_15229 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _68_15229))
end))})))

let is_function = (fun ( t ) -> (match ((let _68_15233 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_15233.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
true
end
| _ -> begin
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
in (let wp = (let _68_15245 = (let _68_15244 = (let _68_15243 = (let _68_15242 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15241 = (let _68_15240 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_68_15240)::[])
in (_68_15242)::_68_15241))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _68_15243))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15244 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _68_15245))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _35_1080 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_15248 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15247 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _68_15246 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _68_15248 _68_15247 _68_15246))))
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
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| _ -> begin
"??"
end)
in (let _68_15258 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _68_15257 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _68_15258 bstr _68_15257))))
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
| Some (Microsoft_FStar_Tc_Env.Binding_lid (_)) -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_var (_)) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c2)) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end
| _ -> begin
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
| (Some (e), Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _)))) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((Microsoft_FStar_Absyn_Syntax.is_null_bvd x))))) with
| true -> begin
(let _68_15266 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.Prims.pipe_left (fun ( _68_15265 ) -> Some (_68_15265)) _68_15266))
end
| false -> begin
(aux ())
end)
end
| _ -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _35_1147 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("bind")))) with
| true -> begin
(let _68_15270 = (match (b) with
| None -> begin
"None"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, _))) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| _ -> begin
"Something else"
end)
in (let _68_15269 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _68_15268 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _68_15267 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _68_15270 _68_15269 _68_15268 _68_15267)))))
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
(let _68_15271 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_68_15271)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _68_15272 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_68_15272)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _68_15273 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_68_15273)::[])
end
| _ -> begin
(failwith ("Unexpected type-variable binding"))
end)
in (let mk_lam = (fun ( wp ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _68_15288 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_15287 = (let _68_15286 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _68_15285 = (let _68_15284 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _68_15283 = (let _68_15282 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _68_15281 = (let _68_15280 = (let _68_15276 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15276))
in (let _68_15279 = (let _68_15278 = (let _68_15277 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15277))
in (_68_15278)::[])
in (_68_15280)::_68_15279))
in (_68_15282)::_68_15281))
in (_68_15284)::_68_15283))
in (_68_15286)::_68_15285))
in (_68_15288)::_68_15287))
in (let wlp_args = (let _68_15296 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_15295 = (let _68_15294 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _68_15293 = (let _68_15292 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _68_15291 = (let _68_15290 = (let _68_15289 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15289))
in (_68_15290)::[])
in (_68_15292)::_68_15291))
in (_68_15294)::_68_15293))
in (_68_15296)::_68_15295))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _68_15297 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15297; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env ) ( t ) ( mk_wp ) ( mk_wlp ) ( f ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _35_1193 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_35_1193) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _68_15312 = (let _68_15311 = (let _68_15310 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15309 = (let _68_15308 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_68_15308)::[])
in (_68_15310)::_68_15309))
in (mk_wp, _68_15311))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15312 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15317 = (let _68_15316 = (let _68_15315 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15314 = (let _68_15313 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_68_15313)::[])
in (_68_15315)::_68_15314))
in (mk_wlp, _68_15316))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15317 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
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
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _35_1209 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_15329 = (let _68_15328 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_15328))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _68_15329))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1212 = (match (((Support.Prims.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name)) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low))) with
| true -> begin
(let _68_15332 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _68_15331 = (let _68_15330 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _68_15330))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _68_15332 _68_15331)))
end
| false -> begin
()
end)
in (let _35_1217 = (destruct_comp c')
in (match (_35_1217) with
| (t, wp, wlp) -> begin
(let wp = (let _68_15335 = (let _68_15334 = (let _68_15333 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _68_15333))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_68_15334))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_15335))
in (let wlp = (let _68_15338 = (let _68_15337 = (let _68_15336 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _68_15336))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_68_15337))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_15338))
in (let _68_15343 = (let _35_1220 = c'
in (let _68_15342 = (let _68_15341 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _68_15340 = (let _68_15339 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15339)::[])
in (_68_15341)::_68_15340))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _35_1220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _35_1220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15342; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_15343))))
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
(match ((let _68_15367 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15367))) with
| true -> begin
f
end
| false -> begin
(let _68_15368 = (reason ())
in (label _68_15368 r f))
end)
end))

let label_guard = (fun ( reason ) ( r ) ( g ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _68_15375 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_68_15375))
end))

let weaken_guard = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _ -> begin
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
in (let wp = (let _68_15394 = (let _68_15393 = (let _68_15392 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15391 = (let _68_15390 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15389 = (let _68_15388 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15388)::[])
in (_68_15390)::_68_15389))
in (_68_15392)::_68_15391))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15393))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15394 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15401 = (let _68_15400 = (let _68_15399 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15398 = (let _68_15397 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15396 = (let _68_15395 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15395)::[])
in (_68_15397)::_68_15396))
in (_68_15399)::_68_15398))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15400))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15401 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
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
| _ -> begin
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
in (let xret = (let _68_15423 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _68_15423))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _68_15426 = (lcomp_of_comp c)
in (let _68_15425 = (let _68_15424 = (lcomp_of_comp xret)
in (Some (xbinding), _68_15424))
in (bind env (Some (e)) _68_15426 _68_15425)))
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
in (let wp = (let _68_15435 = (let _68_15434 = (let _68_15433 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15432 = (let _68_15431 = (let _68_15428 = (let _68_15427 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _68_15427 f))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15428))
in (let _68_15430 = (let _68_15429 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15429)::[])
in (_68_15431)::_68_15430))
in (_68_15433)::_68_15432))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _68_15434))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15435 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15442 = (let _68_15441 = (let _68_15440 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15439 = (let _68_15438 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15437 = (let _68_15436 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15436)::[])
in (_68_15438)::_68_15437))
in (_68_15440)::_68_15439))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15441))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15442 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _68_15446 = (let _35_1301 = lc
in (let _68_15445 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _68_15444 = (match (((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (let _68_15443 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15443)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15445; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1301.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _68_15444; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_68_15446, (let _35_1303 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _35_1303.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _35_1303.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env ) ( comp ) ( res_t ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _35_1313 = (let _68_15454 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _68_15453 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_68_15454, _68_15453)))
in (match (_35_1313) with
| (xexp, yexp) -> begin
(let yret = (let _68_15459 = (let _68_15458 = (let _68_15457 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15456 = (let _68_15455 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_68_15455)::[])
in (_68_15457)::_68_15456))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _68_15458))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15459 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _68_15467 = (let _68_15466 = (let _68_15465 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15464 = (let _68_15463 = (let _68_15460 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15460))
in (let _68_15462 = (let _68_15461 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_68_15461)::[])
in (_68_15463)::_68_15462))
in (_68_15465)::_68_15464))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15466))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15467 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _68_15478 = (let _68_15477 = (let _68_15476 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15475 = (let _68_15474 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15473 = (let _68_15472 = (let _68_15471 = (let _68_15470 = (let _68_15469 = (let _68_15468 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_68_15468)::[])
in (_68_15469, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15470 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15471))
in (_68_15472)::[])
in (_68_15474)::_68_15473))
in (_68_15476)::_68_15475))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _68_15477))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15478 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _68_15481 = (lcomp_of_comp comp)
in (let _68_15480 = (let _68_15479 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _68_15479))
in (bind env None _68_15481 _68_15480)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun ( env ) ( guard ) ( lcomp_then ) ( lcomp_else ) -> (let comp = (fun ( _35_1324 ) -> (match (()) with
| () -> begin
(let _35_1340 = (let _68_15493 = (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _68_15492 = (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _68_15493 _68_15492)))
in (match (_35_1340) with
| ((md, _, _), (res_t, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _68_15513 = (let _68_15511 = (let _68_15510 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15509 = (let _68_15508 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _68_15507 = (let _68_15506 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _68_15505 = (let _68_15504 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_68_15504)::[])
in (_68_15506)::_68_15505))
in (_68_15508)::_68_15507))
in (_68_15510)::_68_15509))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _68_15511))
in (let _68_15512 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15513 None _68_15512))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _68_15520 = (let _68_15519 = (let _68_15518 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15517 = (let _68_15516 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _68_15515 = (let _68_15514 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15514)::[])
in (_68_15516)::_68_15515))
in (_68_15518)::_68_15517))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _68_15519))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15520 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15525 = (let _68_15524 = (let _68_15523 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15522 = (let _68_15521 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15521)::[])
in (_68_15523)::_68_15522))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _68_15524))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15525 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _68_15526 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15526; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun ( env ) ( res_t ) ( lcases ) -> (let eff = (match (lcases) with
| [] -> begin
(failwith ("Empty cases!"))
end
| hd::tl -> begin
(Support.List.fold_left (fun ( eff ) ( _35_1363 ) -> (match (_35_1363) with
| (_, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun ( _35_1366 ) -> (match (()) with
| () -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _68_15556 = (let _68_15554 = (let _68_15553 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15552 = (let _68_15551 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _68_15550 = (let _68_15549 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _68_15548 = (let _68_15547 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_68_15547)::[])
in (_68_15549)::_68_15548))
in (_68_15551)::_68_15550))
in (_68_15553)::_68_15552))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _68_15554))
in (let _68_15555 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15556 None _68_15555))))
in (let default_case = (let post_k = (let _68_15559 = (let _68_15558 = (let _68_15557 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_68_15557)::[])
in (_68_15558, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_15559 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _68_15562 = (let _68_15561 = (let _68_15560 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_68_15560)::[])
in (_68_15561, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_15562 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _68_15563 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_15563 post_k))
in (let wp = (let _68_15570 = (let _68_15569 = (let _68_15564 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_68_15564)::[])
in (let _68_15568 = (let _68_15567 = (let _68_15565 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _68_15565))
in (let _68_15566 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_left _68_15567 _68_15566)))
in (_68_15569, _68_15568)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15570 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15574 = (let _68_15573 = (let _68_15571 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_68_15571)::[])
in (let _68_15572 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_68_15573, _68_15572)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15574 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _35_1382 ) ( celse ) -> (match (_35_1382) with
| (g, cthen) -> begin
(let _35_1400 = (let _68_15577 = (cthen.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _68_15577 celse))
in (match (_35_1400) with
| ((md, _, _), (_, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let _68_15579 = (ifthenelse md res_t g wp_then wp_else)
in (let _68_15578 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _68_15579 _68_15578 [])))
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
| (_, wp, wlp) -> begin
(let wp = (let _68_15586 = (let _68_15585 = (let _68_15584 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15583 = (let _68_15582 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _68_15581 = (let _68_15580 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15580)::[])
in (_68_15582)::_68_15581))
in (_68_15584)::_68_15583))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _68_15585))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15586 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15591 = (let _68_15590 = (let _68_15589 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15588 = (let _68_15587 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15587)::[])
in (_68_15589)::_68_15588))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _68_15590))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15591 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
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
(let bs = (let _68_15610 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_68_15610)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15617 = (let _68_15616 = (let _68_15615 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15614 = (let _68_15613 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15612 = (let _68_15611 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15611)::[])
in (_68_15613)::_68_15612))
in (_68_15615)::_68_15614))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _68_15616))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15617 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _68_15618 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_68_15618)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15623 = (let _68_15622 = (let _68_15621 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15620 = (let _68_15619 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15619)::[])
in (_68_15621)::_68_15620))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _68_15622))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15623 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
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
in (let ret = (let _68_15632 = (return_value env t xexp)
in (Support.Prims.pipe_left lcomp_of_comp _68_15632))
in (let eq_ret = (let _68_15634 = (let _68_15633 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_68_15633))
in (weaken_precondition env ret _68_15634))
in (let _68_15637 = (let _68_15636 = (let _68_15635 = (lcomp_of_comp c)
in (bind env None _68_15635 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_68_15636.Microsoft_FStar_Absyn_Syntax.comp ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _68_15637 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
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
(let _68_15649 = (let _68_15648 = (let _68_15647 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _68_15646 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_15647, _68_15646)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_15648))
in (raise (_68_15649)))
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
in (let _68_15660 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_15660, k, implicits))))
end)))
end
| _ -> begin
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
| (Support.Microsoft.FStar.Util.Inl (a), _)::rest -> begin
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
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
in (let _68_15677 = (mk_exp_app e args (Some (t)))
in (_68_15677, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _ -> begin
(let t = (let _68_15678 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _68_15678 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _68_15679 = (mk_exp_app e args (Some (t)))
in (_68_15679, t, implicits)))
end))
end)))
end
| _ -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env ) ( e ) ( lc ) ( t ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _68_15688 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_68_15688, false))
end
| false -> begin
(let _68_15689 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_68_15689, true))
end)
in (match (gopt) with
| (None, _) -> begin
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
(let _68_15693 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _68_15692 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _68_15693 _68_15692)))
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
in (let wp = (let _68_15698 = (let _68_15697 = (let _68_15696 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15695 = (let _68_15694 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_68_15694)::[])
in (_68_15696)::_68_15695))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _68_15697))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15698 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _68_15699 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.Prims.pipe_left lcomp_of_comp _68_15699))
in (let guard = (match (apply_guard) with
| true -> begin
(let _68_15702 = (let _68_15701 = (let _68_15700 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_68_15700)::[])
in (f, _68_15701))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15702 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _35_1636 = (let _68_15710 = (Support.Prims.pipe_left (fun ( _68_15707 ) -> Some (_68_15707)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _68_15709 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15708 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _68_15710 _68_15709 e cret _68_15708))))
in (match (_35_1636) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _68_15712 = (let _68_15711 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.Prims.pipe_left lcomp_of_comp _68_15711))
in (bind env (Some (e)) _68_15712 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _35_1639 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_15713 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _68_15713))
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
| _ -> begin
[]
end))))
in (let lc = (let _35_1647 = lc
in (let _68_15715 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15715; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r ) ( t ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0)) with
| true -> begin
(let ue = (let _68_15720 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _68_15720))
in (let ut = (let _68_15721 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _68_15721))
in (let uk = (let _68_15722 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _68_15722))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _35_1659 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _35_1661 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _35_1663 = (let _68_15724 = (let _68_15723 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _68_15723))
in (Microsoft_FStar_Tc_Errors.report r _68_15724))
in (let _35_1665 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify ) ( env ) ( ecs ) -> (match ((let _68_15732 = (Support.Microsoft.FStar.Util.for_all (fun ( _35_1673 ) -> (match (_35_1673) with
| (_, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15732))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c ) -> (let _35_1676 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15735 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _68_15735))
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
(let _68_15736 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _68_15736))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs ) -> (let _68_15739 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.Prims.pipe_right _68_15739 Support.Microsoft.FStar.Util.set_elements)))
in (let should_gen = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _)) -> begin
(match ((Support.Prims.pipe_right bs (Support.Microsoft.FStar.Util.for_some (fun ( _35_10 ) -> (match (_35_10) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
true
end)
end
| _ -> begin
true
end))
in (let uvars = (Support.Prims.pipe_right ecs (Support.List.map (fun ( _35_1705 ) -> (match (_35_1705) with
| (e, c) -> begin
(let t = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.compress_typ)
in (match ((let _68_15744 = (should_gen t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15744))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _35_1721 = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (let _68_15745 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15745)))) with
| true -> begin
(let _35_1717 = (destruct_comp ct)
in (match (_35_1717) with
| (_, wp, _) -> begin
(let binder = (let _68_15746 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_68_15746)::[])
in (let post = (let _68_15750 = (let _68_15747 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _68_15747))
in (let _68_15749 = (let _68_15748 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_68_15748))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15750 _68_15749 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _68_15757 = (let _68_15756 = (let _68_15755 = (let _68_15754 = (let _68_15753 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_68_15753)::[])
in (wp, _68_15754))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15755))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _68_15756))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _68_15757))
in (let _68_15758 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _68_15758)))))
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
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
(failwith ("Unexpected instantiation of mutually recursive uvar"))
end
| _ -> begin
(let a = (let _68_15763 = (let _68_15762 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left (fun ( _68_15761 ) -> Some (_68_15761)) _68_15762))
in (Microsoft_FStar_Absyn_Util.new_bvd _68_15763))
in (let t = (let _68_15764 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _68_15764 k))
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
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _68_15765 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _68_15765)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify ) ( env ) ( lecs ) -> (let _35_1801 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_15774 = (let _68_15773 = (Support.List.map (fun ( _35_1800 ) -> (match (_35_1800) with
| (lb, _, _) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.Prims.pipe_right _68_15773 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _68_15774))
end
| false -> begin
()
end)
in (match ((let _68_15776 = (Support.Prims.pipe_right lecs (Support.List.map (fun ( _35_1807 ) -> (match (_35_1807) with
| (_, e, c) -> begin
(e, c)
end))))
in (gen verify env _68_15776))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _35_1816 ) ( _35_1819 ) -> (match ((_35_1816, _35_1819)) with
| ((l, _, _), (e, c)) -> begin
(let _35_1820 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15781 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15780 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _68_15779 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _68_15781 _68_15780 _68_15779))))
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
| _ -> begin
false
end))

let check_top_level = (fun ( env ) ( g ) ( lc ) -> (let discharge = (fun ( g ) -> (let _35_1831 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _35_1849 = (match ((Support.Prims.pipe_right g.Microsoft_FStar_Tc_Rel.implicits (Support.List.tryFind (fun ( _35_11 ) -> (match (_35_11) with
| Support.Microsoft.FStar.Util.Inl (u) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr ((u, _)) -> begin
(unresolved u)
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr ((_, r))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _ -> begin
()
end)
in (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Absyn_Util.is_total_lcomp lc)) with
| true -> begin
(let _68_15793 = (discharge g)
in (let _68_15792 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (_68_15793, _68_15792)))
end
| false -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _68_15794 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.Prims.pipe_right _68_15794 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _35_1860 = (destruct_comp c)
in (match (_35_1860) with
| (t, wp, _) -> begin
(let vc = (let _68_15800 = (let _68_15798 = (let _68_15797 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15796 = (let _68_15795 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15795)::[])
in (_68_15797)::_68_15796))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _68_15798))
in (let _68_15799 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15800 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _68_15799)))
in (let g = (let _68_15801 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_15801))
in (let _68_15803 = (discharge g)
in (let _68_15802 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_68_15803, _68_15802)))))
end))))))
end))))

let short_circuit_exp = (fun ( head ) ( seen_args ) -> (let short_bin_op_e = (fun ( f ) -> (fun ( _35_12 ) -> (match (_35_12) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _)::[] -> begin
(let _68_15822 = (f fst)
in (Support.Prims.pipe_right _68_15822 (fun ( _68_15821 ) -> Some (_68_15821))))
end
| _ -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let table = (let op_and_e = (fun ( e ) -> (let _68_15828 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_68_15828, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e ) -> (let _68_15832 = (let _68_15831 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _68_15831))
in (_68_15832, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1890 ) -> (match (_35_1890) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _68_15850 = (mk seen_args)
in Some (_68_15850))
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
| _ -> begin
None
end))))

let short_circuit_typ = (fun ( head ) ( seen_args ) -> (let short_bin_op_t = (fun ( f ) -> (fun ( _35_13 ) -> (match (_35_13) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _)::[] -> begin
(f fst)
end
| _ -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let op_and_t = (fun ( t ) -> (let _68_15871 = (unlabel t)
in (Support.Prims.pipe_right _68_15871 (fun ( _68_15870 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15870)))))
in (let op_or_t = (fun ( t ) -> (let _68_15876 = (let _68_15874 = (unlabel t)
in (Support.Prims.pipe_right _68_15874 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.Prims.pipe_right _68_15876 (fun ( _68_15875 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15875)))))
in (let op_imp_t = (fun ( t ) -> (let _68_15880 = (unlabel t)
in (Support.Prims.pipe_right _68_15880 (fun ( _68_15879 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15879)))))
in (let short_op_ite = (fun ( _35_14 ) -> (match (_35_14) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
(let _68_15884 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.Prims.pipe_right _68_15884 (fun ( _68_15883 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15883))))
end
| _ -> begin
(failwith ("Unexpected args to ITE"))
end))
in (let table = ((Microsoft_FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((Microsoft_FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((Microsoft_FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((Microsoft_FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| Support.Microsoft.FStar.Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some ((g, _)) -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (g)
end)
end
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1958 ) -> (match (_35_1958) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _68_15911 = (mk seen_args)
in Some (_68_15911))
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
| _ -> begin
Microsoft_FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun ( env ) ( comp ) -> (let mk_post_type = (fun ( res_t ) ( ens ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _68_15925 = (let _68_15924 = (let _68_15923 = (let _68_15922 = (let _68_15921 = (let _68_15920 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _68_15920))
in (_68_15921)::[])
in (ens, _68_15922))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15923 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _68_15924))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _68_15925 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
in (let norm = (fun ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Unlabel)::[]) env t))
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp comp)) with
| true -> begin
(None, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| false -> begin
(match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (req), _)::(Support.Microsoft.FStar.Util.Inl (ens), _)::_ -> begin
(let _68_15931 = (let _68_15928 = (norm req)
in Some (_68_15928))
in (let _68_15930 = (let _68_15929 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.Prims.pipe_left norm _68_15929))
in (_68_15931, _68_15930)))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| false -> begin
(let comp = (Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (wlp), _)::_ -> begin
(let _35_2022 = (match ((let _68_15933 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _68_15932 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_68_15933, _68_15932)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _ -> begin
(failwith ("Impossible"))
end)
in (match (_35_2022) with
| (as_req, as_ens) -> begin
(let req = (let _68_15937 = (let _68_15936 = (let _68_15935 = (let _68_15934 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15934)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_15935)
in (as_req, _68_15936))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15937 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _68_15941 = (let _68_15940 = (let _68_15939 = (let _68_15938 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15938)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_15939)
in (as_ens, _68_15940))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15941 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _68_15945 = (let _68_15942 = (norm req)
in Some (_68_15942))
in (let _68_15944 = (let _68_15943 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _68_15943))
in (_68_15945, _68_15944)))))
end))
end
| _ -> begin
(failwith ("Impossible"))
end)
end))
end)
end)
end))))




