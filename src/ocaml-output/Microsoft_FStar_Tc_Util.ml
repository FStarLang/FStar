
let try_solve = (fun ( env ) ( f ) -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun ( env ) ( errs ) -> (let _68_14747 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14746 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _68_14747 _68_14746))))

let discharge_guard = (fun ( env ) ( g ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env ) ( g ) -> (discharge_guard env g))

let syn' = (fun ( env ) ( k ) -> (let _68_14766 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _68_14766 k)))

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
(let _68_14790 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.Prims.pipe_left (fun ( _68_14789 ) -> Some (_68_14789)) _68_14790))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _68_14794 = (let _68_14793 = (let _68_14792 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _68_14791 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14792, _68_14791)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14793))
in (raise (_68_14794)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _68_14798 = (let _68_14797 = (let _68_14796 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _68_14795 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14796, _68_14795)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14797))
in (raise (_68_14798)))
end
| Some (g) -> begin
(let _35_49 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14799 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _68_14799))
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
in (let _68_14800 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _35_56.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _68_14800; Microsoft_FStar_Absyn_Syntax.pos = _35_56.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _35_56.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _35_56.Microsoft_FStar_Absyn_Syntax.uvs}))
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

let new_kvar = (fun ( env ) -> (let _68_14810 = (let _68_14809 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14808 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _68_14809 _68_14808)))
in (Support.Prims.pipe_right _68_14810 Support.Prims.fst)))

let new_tvar = (fun ( env ) ( k ) -> (let _68_14817 = (let _68_14816 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14815 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _68_14816 _68_14815 k)))
in (Support.Prims.pipe_right _68_14817 Support.Prims.fst)))

let new_evar = (fun ( env ) ( t ) -> (let _68_14824 = (let _68_14823 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14822 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _68_14823 _68_14822 t)))
in (Support.Prims.pipe_right _68_14824 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env ) ( k ) -> (let _35_103 = (let _68_14830 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14829 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _68_14830 _68_14829 k)))
in (match (_35_103) with
| (t, u) -> begin
(let _68_14832 = (let _68_14831 = (as_uvar_t u)
in (_68_14831, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _68_14832))
end)))

let new_implicit_evar = (fun ( env ) ( t ) -> (let _35_108 = (let _68_14838 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14837 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _68_14838 _68_14837 t)))
in (match (_35_108) with
| (e, u) -> begin
(let _68_14840 = (let _68_14839 = (as_uvar_e u)
in (_68_14839, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _68_14840))
end)))

let force_tk = (fun ( s ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _68_14843 = (let _68_14842 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _68_14842))
in (failwith (_68_14843)))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args ) -> (Support.Prims.pipe_right args (Support.List.map (fun ( _35_2 ) -> (match (_35_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _68_14848 = (let _68_14847 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_68_14847))
in (_68_14848, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _68_14850 = (let _68_14849 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_68_14849))
in (_68_14850, imp))
end)))))

let is_implicit = (fun ( _35_3 ) -> (match (_35_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _ -> begin
false
end))

let destruct_arrow_kind = (fun ( env ) ( tt ) ( k ) ( args ) -> (let ktop = (let _68_14861 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.Prims.pipe_right _68_14861 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
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
(let _68_14874 = (let _68_14871 = (let _68_14870 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _68_14870))
in (Support.Prims.pipe_right _68_14871 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14874 (fun ( x ) -> (let _68_14873 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _68_14873)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_14879 = (let _68_14876 = (let _68_14875 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _68_14875))
in (Support.Prims.pipe_right _68_14876 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14879 (fun ( x ) -> (let _68_14878 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _68_14878)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _68_14880 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_68_14880)::subst)
end)
in (let _35_167 = (mk_implicits vars subst brest)
in (match (_35_167) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _68_14881 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _68_14881))
end)
end
| _ -> begin
(let _68_14882 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _68_14882))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _35_172 = (let _68_14883 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _68_14883 [] bs))
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
in (let kres = (let _68_14884 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.Prims.pipe_right _68_14884 Support.Prims.fst))
in (let bs = (let _68_14885 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _68_14885))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _35_186 = (let _68_14886 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.Prims.pipe_left (force_trivial env) _68_14886))
in ([], bs, kres)))))))
end
| _ -> begin
(let _68_14889 = (let _68_14888 = (let _68_14887 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_68_14887, r))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14888))
in (raise (_68_14889)))
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
in (let _68_14909 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _68_14909, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _)) -> begin
(let k = (new_kvar env)
in (let _35_259 = (let _68_14910 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _68_14910 k))
in (match (_35_259) with
| (t, u) -> begin
(let p = (let _35_260 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _35_260.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_260.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_14912 = (let _68_14911 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (t), _68_14911))
in ([], [], [], env, _68_14912, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14913 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _68_14913, p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _68_14915 = (let _68_14914 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_14914))
in Microsoft_FStar_Tc_Env.Binding_var (_68_14915))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14916 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ((w)::[], [], (w)::[], env, _68_14916, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)) -> begin
(let b = (let _68_14918 = (let _68_14917 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_14917))
in Microsoft_FStar_Tc_Env.Binding_var (_68_14918))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14920 = (let _68_14919 = (Microsoft_FStar_Absyn_Syntax.as_implicit imp)
in (Support.Microsoft.FStar.Util.Inr (e), _68_14919))
in ((b)::[], (b)::[], [], env, _68_14920, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _68_14922 = (let _68_14921 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_14921))
in Microsoft_FStar_Tc_Env.Binding_typ (_68_14922))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14923 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((w)::[], [], (w)::[], env, _68_14923, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _68_14925 = (let _68_14924 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_14924))
in Microsoft_FStar_Tc_Env.Binding_typ (_68_14925))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14926 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((b)::[], (b)::[], [], env, _68_14926, p)))))
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
(let e = (let _68_14934 = (let _68_14933 = (let _68_14932 = (let _68_14931 = (let _68_14930 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_14929 = (Support.Prims.pipe_right args Support.List.rev)
in (_68_14930, _68_14929)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_14931 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_68_14932, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_14933))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_14934))
in (let _68_14938 = (Support.Prims.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _68_14937 = (Support.Prims.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _68_14936 = (Support.Prims.pipe_right (Support.List.rev w) Support.List.flatten)
in (let _68_14935 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_14938, _68_14937, _68_14936, env, _68_14935, (let _35_316 = p
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
(let _68_14945 = (let _68_14944 = (let _68_14943 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _68_14943))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14944))
in (raise (_68_14945)))
end)
end
| Some ((f, _)) -> begin
(let rec aux = (fun ( formals ) ( pats ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _::_) -> begin
(let _68_14952 = (let _68_14951 = (let _68_14950 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _68_14950))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14951))
in (raise (_68_14952)))
end
| (_::_, []) -> begin
(Support.Prims.pipe_right formals (Support.List.map (fun ( f ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let a = (let _68_14954 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_14954 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _68_14955 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _68_14955))
end
| false -> begin
(let _68_14956 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _68_14956))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _68_14957 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _68_14957)))
end
| _ -> begin
(let _68_14962 = (let _68_14961 = (let _68_14960 = (let _68_14958 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _68_14958))
in (let _68_14959 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_68_14960, _68_14959)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14961))
in (raise (_68_14962)))
end))))
end
| (f::formals', p::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _68_14963 = (aux formals' pats')
in (p)::_68_14963)
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) when allow_implicits -> begin
(let _68_14964 = (aux formals' pats')
in (p)::_68_14964)
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), _) -> begin
(let a = (let _68_14965 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_14965 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _68_14966 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _68_14966))
end
| false -> begin
(let _68_14967 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _68_14967))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_) -> begin
pats'
end
| _ -> begin
pats
end)
in (let _68_14968 = (aux formals' pats')
in (p1)::_68_14968))))
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_var ((_, true))) -> begin
(let _68_14969 = (aux formals' pats')
in (p)::_68_14969)
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _68_14970 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _68_14970))
in (let _68_14971 = (aux formals' pats)
in (p)::_68_14971)))
end
| ((Support.Microsoft.FStar.Util.Inr (_), _), _) -> begin
(let _68_14972 = (aux formals' pats')
in (p)::_68_14972)
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
(let _68_14981 = (let _68_14980 = (let _68_14979 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_68_14979, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14980))
in (raise (_68_14981)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _))) -> begin
(let _68_14984 = (let _68_14983 = (let _68_14982 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_68_14982, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14983))
in (raise (_68_14984)))
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
(let _68_14996 = (let _68_14995 = (let _68_14994 = (let _68_14992 = (vars_of_bindings a)
in (let _68_14991 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _68_14992 _68_14991)))
in (let _68_14993 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14994, _68_14993)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14995))
in (raise (_68_14996)))
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
in (let rec aux = (fun ( p ) ( e ) -> (let pkg = (fun ( q ) ( t ) -> (let _68_15015 = (Support.Prims.pipe_left (fun ( _68_15014 ) -> Some (_68_15014)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _68_15015 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_), Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(let _68_15016 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _68_15016))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_579 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15019 = (let _68_15018 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15017 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15018 _68_15017)))
in (failwith (_68_15019)))
end
| false -> begin
()
end)
in (let _35_581 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _68_15021 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15020 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _68_15021 _68_15020)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _35_584 = x
in {Microsoft_FStar_Absyn_Syntax.v = _35_584.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _35_584.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_15022 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp))) _68_15022))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_592 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15025 = (let _68_15024 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15023 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15024 _68_15023)))
in (failwith (_68_15025)))
end
| false -> begin
()
end)
in (let x = (let _35_594 = x
in (let _68_15026 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_594.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_15026; Microsoft_FStar_Absyn_Syntax.p = _35_594.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)), _) -> begin
(let x = (let _35_605 = x
in (let _68_15027 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_15027; Microsoft_FStar_Absyn_Syntax.p = _35_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _))) -> begin
(let _35_619 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _68_15028 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_68_15028)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) -> begin
(let _35_644 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _68_15029 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_68_15029)))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats ) ( args ) ( argpats ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _68_15036 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _68_15036))
end
| (arg::args, argpat::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let x = (let _68_15037 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _68_15037))
in (let q = (let _68_15039 = (Support.Prims.pipe_left (fun ( _68_15038 ) -> Some (_68_15038)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _68_15039 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) -> begin
(let x = (let _68_15040 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _68_15040))
in (let q = (let _68_15042 = (Support.Prims.pipe_left (fun ( _68_15041 ) -> Some (_68_15041)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _68_15042 p.Microsoft_FStar_Absyn_Syntax.p))
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
(let _68_15045 = (let _68_15044 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _68_15043 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _68_15044 _68_15043)))
in (failwith (_68_15045)))
end))
in (match_args [] args argpats))))
end
| _ -> begin
(let _68_15050 = (let _68_15049 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_15048 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _68_15047 = (let _68_15046 = (Support.Prims.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.Prims.pipe_right _68_15046 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _68_15049 _68_15048 _68_15047))))
in (failwith (_68_15050)))
end))))
and aux_t = (fun ( p ) ( t0 ) -> (let pkg = (fun ( q ) ( k ) -> (let _68_15058 = (Support.Prims.pipe_left (fun ( _68_15057 ) -> Some (_68_15057)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _68_15058 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_716 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15061 = (let _68_15060 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15059 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15060 _68_15059)))
in (failwith (_68_15061)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_723 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _68_15064 = (let _68_15063 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_15062 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _68_15063 _68_15062)))
in (failwith (_68_15064)))
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
(let _68_15068 = (let _68_15067 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_15066 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _68_15065 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _68_15067 _68_15066 _68_15065))))
in (failwith (_68_15068)))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _68_15070 = (Support.Prims.pipe_left (fun ( _68_15069 ) -> Some (_68_15069)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _68_15070 p.Microsoft_FStar_Absyn_Syntax.p)))
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
(let _68_15090 = (let _68_15089 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (te, _68_15089))
in (vars, _68_15090))
end)))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _68_15093 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _68_15093))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) -> begin
(let _68_15096 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _68_15096))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _35_785 = (let _68_15097 = (Support.Prims.pipe_right pats (Support.List.map pat_as_arg))
in (Support.Prims.pipe_right _68_15097 Support.List.unzip))
in (match (_35_785) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _68_15103 = (let _68_15102 = (let _68_15101 = (let _68_15100 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_68_15100, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_15101))
in (Support.Prims.pipe_right _68_15102 pkg))
in (vars, _68_15103)))
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
(let _68_15105 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _68_15105))
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
(let _68_15113 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15113 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _68_15116 = (let _68_15115 = (let _68_15114 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15114 Support.Prims.fst))
in (bs, _68_15115))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15116 (Some (k)) r))
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _68_15118 = (let _68_15117 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_68_15117)::out)
in (_68_15118, subst)))))
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
(let k = (let _68_15129 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.Prims.pipe_right _68_15129 Support.Prims.fst))
in ((let _35_886 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_886.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _35_886.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _ -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _68_15134 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15134 Support.Prims.fst))
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
(let _68_15142 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _68_15141 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _68_15142 _68_15141)))
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
(let _68_15144 = (let _68_15143 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_15143 Support.Prims.fst))
in (e, _68_15144, false))
end))
in (let _68_15145 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _68_15145 e))))))
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
(let _68_15150 = (let _68_15149 = (let _68_15148 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.Prims.pipe_right _68_15148 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _68_15149))
in (failwith (_68_15150)))
end)
in (match (_35_982) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c ) ( m ) ( lift ) -> (let _35_990 = (destruct_comp c)
in (match (_35_990) with
| (_, wp, wlp) -> begin
(let _68_15172 = (let _68_15171 = (let _68_15167 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15167))
in (let _68_15170 = (let _68_15169 = (let _68_15168 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15168))
in (_68_15169)::[])
in (_68_15171)::_68_15170))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15172; Microsoft_FStar_Absyn_Syntax.flags = []})
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

let join_effects = (fun ( env ) ( l1 ) ( l2 ) -> (let _35_1023 = (let _68_15186 = (norm_eff_name env l1)
in (let _68_15185 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _68_15186 _68_15185)))
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
(let _68_15200 = (destruct_comp m1)
in (let _68_15199 = (destruct_comp m2)
in ((md, a, kwp), _68_15200, _68_15199)))
end)))))
end)))))

let is_pure_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md ) ( result ) ( wp ) ( wlp ) ( flags ) -> (let _68_15223 = (let _68_15222 = (let _68_15221 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _68_15220 = (let _68_15219 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15219)::[])
in (_68_15221)::_68_15220))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15222; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_15223)))

let lcomp_of_comp = (fun ( c0 ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1055 ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst ) ( lc ) -> (let _35_1058 = lc
in (let _68_15233 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1058.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _68_15233; Microsoft_FStar_Absyn_Syntax.cflags = _35_1058.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1060 ) -> (match (()) with
| () -> begin
(let _68_15232 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _68_15232))
end))})))

let is_function = (fun ( t ) -> (match ((let _68_15236 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_15236.Microsoft_FStar_Absyn_Syntax.n)) with
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
in (let wp = (let _68_15248 = (let _68_15247 = (let _68_15246 = (let _68_15245 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15244 = (let _68_15243 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_68_15243)::[])
in (_68_15245)::_68_15244))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _68_15246))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15247 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _68_15248))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _35_1080 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_15251 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15250 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _68_15249 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _68_15251 _68_15250 _68_15249))))
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
in (let _68_15261 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _68_15260 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _68_15261 bstr _68_15260))))
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
(let _68_15269 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.Prims.pipe_left (fun ( _68_15268 ) -> Some (_68_15268)) _68_15269))
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
(let _68_15273 = (match (b) with
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
in (let _68_15272 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _68_15271 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _68_15270 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _68_15273 _68_15272 _68_15271 _68_15270)))))
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
(let _68_15274 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_68_15274)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _68_15275 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_68_15275)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _68_15276 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_68_15276)::[])
end
| _ -> begin
(failwith ("Unexpected type-variable binding"))
end)
in (let mk_lam = (fun ( wp ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _68_15291 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_15290 = (let _68_15289 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _68_15288 = (let _68_15287 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _68_15286 = (let _68_15285 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _68_15284 = (let _68_15283 = (let _68_15279 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15279))
in (let _68_15282 = (let _68_15281 = (let _68_15280 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15280))
in (_68_15281)::[])
in (_68_15283)::_68_15282))
in (_68_15285)::_68_15284))
in (_68_15287)::_68_15286))
in (_68_15289)::_68_15288))
in (_68_15291)::_68_15290))
in (let wlp_args = (let _68_15299 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_15298 = (let _68_15297 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _68_15296 = (let _68_15295 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _68_15294 = (let _68_15293 = (let _68_15292 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _68_15292))
in (_68_15293)::[])
in (_68_15295)::_68_15294))
in (_68_15297)::_68_15296))
in (_68_15299)::_68_15298))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _68_15300 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15300; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env ) ( t ) ( mk_wp ) ( mk_wlp ) ( f ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _35_1193 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_35_1193) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _68_15315 = (let _68_15314 = (let _68_15313 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15312 = (let _68_15311 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_68_15311)::[])
in (_68_15313)::_68_15312))
in (mk_wp, _68_15314))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15315 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15320 = (let _68_15319 = (let _68_15318 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15317 = (let _68_15316 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_68_15316)::[])
in (_68_15318)::_68_15317))
in (mk_wlp, _68_15319))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15320 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _68_15332 = (let _68_15331 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_15331))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _68_15332))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1212 = (match (((Support.Prims.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name)) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low))) with
| true -> begin
(let _68_15335 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _68_15334 = (let _68_15333 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _68_15333))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _68_15335 _68_15334)))
end
| false -> begin
()
end)
in (let _35_1217 = (destruct_comp c')
in (match (_35_1217) with
| (t, wp, wlp) -> begin
(let wp = (let _68_15338 = (let _68_15337 = (let _68_15336 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _68_15336))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_68_15337))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_15338))
in (let wlp = (let _68_15341 = (let _68_15340 = (let _68_15339 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _68_15339))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_68_15340))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_15341))
in (let _68_15346 = (let _35_1220 = c'
in (let _68_15345 = (let _68_15344 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _68_15343 = (let _68_15342 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15342)::[])
in (_68_15344)::_68_15343))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _35_1220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _35_1220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_15345; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_15346))))
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
(match ((let _68_15370 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15370))) with
| true -> begin
f
end
| false -> begin
(let _68_15371 = (reason ())
in (label _68_15371 r f))
end)
end))

let label_guard = (fun ( reason ) ( r ) ( g ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _68_15378 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_68_15378))
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
in (let wp = (let _68_15397 = (let _68_15396 = (let _68_15395 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15394 = (let _68_15393 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15392 = (let _68_15391 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15391)::[])
in (_68_15393)::_68_15392))
in (_68_15395)::_68_15394))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15396))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15397 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15404 = (let _68_15403 = (let _68_15402 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15401 = (let _68_15400 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15399 = (let _68_15398 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15398)::[])
in (_68_15400)::_68_15399))
in (_68_15402)::_68_15401))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15403))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15404 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
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
in (let xret = (let _68_15426 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _68_15426))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _68_15429 = (lcomp_of_comp c)
in (let _68_15428 = (let _68_15427 = (lcomp_of_comp xret)
in (Some (xbinding), _68_15427))
in (bind env (Some (e)) _68_15429 _68_15428)))
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
in (let wp = (let _68_15438 = (let _68_15437 = (let _68_15436 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15435 = (let _68_15434 = (let _68_15431 = (let _68_15430 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _68_15430 f))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15431))
in (let _68_15433 = (let _68_15432 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15432)::[])
in (_68_15434)::_68_15433))
in (_68_15436)::_68_15435))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _68_15437))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15438 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15445 = (let _68_15444 = (let _68_15443 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15442 = (let _68_15441 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _68_15440 = (let _68_15439 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15439)::[])
in (_68_15441)::_68_15440))
in (_68_15443)::_68_15442))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15444))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15445 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _68_15449 = (let _35_1301 = lc
in (let _68_15448 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _68_15447 = (match (((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (let _68_15446 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15446)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15448; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1301.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _68_15447; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_68_15449, (let _35_1303 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _35_1303.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _35_1303.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env ) ( comp ) ( res_t ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _35_1313 = (let _68_15457 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _68_15456 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_68_15457, _68_15456)))
in (match (_35_1313) with
| (xexp, yexp) -> begin
(let yret = (let _68_15462 = (let _68_15461 = (let _68_15460 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15459 = (let _68_15458 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_68_15458)::[])
in (_68_15460)::_68_15459))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _68_15461))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15462 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _68_15470 = (let _68_15469 = (let _68_15468 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15467 = (let _68_15466 = (let _68_15463 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15463))
in (let _68_15465 = (let _68_15464 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_68_15464)::[])
in (_68_15466)::_68_15465))
in (_68_15468)::_68_15467))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _68_15469))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15470 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _68_15481 = (let _68_15480 = (let _68_15479 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15478 = (let _68_15477 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15476 = (let _68_15475 = (let _68_15474 = (let _68_15473 = (let _68_15472 = (let _68_15471 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_68_15471)::[])
in (_68_15472, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15473 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_15474))
in (_68_15475)::[])
in (_68_15477)::_68_15476))
in (_68_15479)::_68_15478))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _68_15480))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15481 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _68_15484 = (lcomp_of_comp comp)
in (let _68_15483 = (let _68_15482 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _68_15482))
in (bind env None _68_15484 _68_15483)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun ( env ) ( guard ) ( lcomp_then ) ( lcomp_else ) -> (let comp = (fun ( _35_1324 ) -> (match (()) with
| () -> begin
(let _35_1340 = (let _68_15496 = (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _68_15495 = (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _68_15496 _68_15495)))
in (match (_35_1340) with
| ((md, _, _), (res_t, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _68_15516 = (let _68_15514 = (let _68_15513 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15512 = (let _68_15511 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _68_15510 = (let _68_15509 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _68_15508 = (let _68_15507 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_68_15507)::[])
in (_68_15509)::_68_15508))
in (_68_15511)::_68_15510))
in (_68_15513)::_68_15512))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _68_15514))
in (let _68_15515 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15516 None _68_15515))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _68_15523 = (let _68_15522 = (let _68_15521 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15520 = (let _68_15519 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _68_15518 = (let _68_15517 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15517)::[])
in (_68_15519)::_68_15518))
in (_68_15521)::_68_15520))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _68_15522))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15523 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15528 = (let _68_15527 = (let _68_15526 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15525 = (let _68_15524 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15524)::[])
in (_68_15526)::_68_15525))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _68_15527))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15528 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _68_15529 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15529; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

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
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _68_15559 = (let _68_15557 = (let _68_15556 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15555 = (let _68_15554 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _68_15553 = (let _68_15552 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _68_15551 = (let _68_15550 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_68_15550)::[])
in (_68_15552)::_68_15551))
in (_68_15554)::_68_15553))
in (_68_15556)::_68_15555))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _68_15557))
in (let _68_15558 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15559 None _68_15558))))
in (let default_case = (let post_k = (let _68_15562 = (let _68_15561 = (let _68_15560 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_68_15560)::[])
in (_68_15561, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_15562 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _68_15565 = (let _68_15564 = (let _68_15563 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_68_15563)::[])
in (_68_15564, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_15565 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _68_15566 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _68_15566 post_k))
in (let wp = (let _68_15573 = (let _68_15572 = (let _68_15567 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_68_15567)::[])
in (let _68_15571 = (let _68_15570 = (let _68_15568 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _68_15568))
in (let _68_15569 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_left _68_15570 _68_15569)))
in (_68_15572, _68_15571)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15573 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15577 = (let _68_15576 = (let _68_15574 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_68_15574)::[])
in (let _68_15575 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_68_15576, _68_15575)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15577 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _35_1382 ) ( celse ) -> (match (_35_1382) with
| (g, cthen) -> begin
(let _35_1400 = (let _68_15580 = (cthen.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _68_15580 celse))
in (match (_35_1400) with
| ((md, _, _), (_, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let _68_15582 = (ifthenelse md res_t g wp_then wp_else)
in (let _68_15581 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _68_15582 _68_15581 [])))
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
(let wp = (let _68_15589 = (let _68_15588 = (let _68_15587 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15586 = (let _68_15585 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _68_15584 = (let _68_15583 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15583)::[])
in (_68_15585)::_68_15584))
in (_68_15587)::_68_15586))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _68_15588))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15589 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _68_15594 = (let _68_15593 = (let _68_15592 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15591 = (let _68_15590 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15590)::[])
in (_68_15592)::_68_15591))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _68_15593))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15594 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
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
(let bs = (let _68_15613 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_68_15613)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15620 = (let _68_15619 = (let _68_15618 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15617 = (let _68_15616 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15615 = (let _68_15614 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15614)::[])
in (_68_15616)::_68_15615))
in (_68_15618)::_68_15617))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _68_15619))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15620 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _68_15621 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_68_15621)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15626 = (let _68_15625 = (let _68_15624 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _68_15623 = (let _68_15622 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15622)::[])
in (_68_15624)::_68_15623))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _68_15625))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15626 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
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
in (let ret = (let _68_15635 = (return_value env t xexp)
in (Support.Prims.pipe_left lcomp_of_comp _68_15635))
in (let eq_ret = (let _68_15637 = (let _68_15636 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_68_15636))
in (weaken_precondition env ret _68_15637))
in (let _68_15640 = (let _68_15639 = (let _68_15638 = (lcomp_of_comp c)
in (bind env None _68_15638 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_68_15639.Microsoft_FStar_Absyn_Syntax.comp ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _68_15640 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
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
(let _68_15652 = (let _68_15651 = (let _68_15650 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _68_15649 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_15650, _68_15649)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_15651))
in (raise (_68_15652)))
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
in (let _68_15663 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_15663, k, implicits))))
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
in (let _68_15680 = (mk_exp_app e args (Some (t)))
in (_68_15680, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _ -> begin
(let t = (let _68_15681 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _68_15681 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _68_15682 = (mk_exp_app e args (Some (t)))
in (_68_15682, t, implicits)))
end))
end)))
end
| _ -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env ) ( e ) ( lc ) ( t ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _68_15691 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_68_15691, false))
end
| false -> begin
(let _68_15692 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_68_15692, true))
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
(let _68_15696 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _68_15695 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _68_15696 _68_15695)))
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
in (let wp = (let _68_15701 = (let _68_15700 = (let _68_15699 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15698 = (let _68_15697 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_68_15697)::[])
in (_68_15699)::_68_15698))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _68_15700))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15701 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _68_15702 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.Prims.pipe_left lcomp_of_comp _68_15702))
in (let guard = (match (apply_guard) with
| true -> begin
(let _68_15705 = (let _68_15704 = (let _68_15703 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_68_15703)::[])
in (f, _68_15704))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15705 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _35_1636 = (let _68_15713 = (Support.Prims.pipe_left (fun ( _68_15710 ) -> Some (_68_15710)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _68_15712 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15711 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _68_15713 _68_15712 e cret _68_15711))))
in (match (_35_1636) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _68_15715 = (let _68_15714 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.Prims.pipe_left lcomp_of_comp _68_15714))
in (bind env (Some (e)) _68_15715 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _35_1639 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_15716 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _68_15716))
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
in (let _68_15718 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _68_15718; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r ) ( t ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0)) with
| true -> begin
(let ue = (let _68_15723 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _68_15723))
in (let ut = (let _68_15724 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _68_15724))
in (let uk = (let _68_15725 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _68_15725))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _35_1659 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _35_1661 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _35_1663 = (let _68_15727 = (let _68_15726 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _68_15726))
in (Microsoft_FStar_Tc_Errors.report r _68_15727))
in (let _35_1665 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify ) ( env ) ( ecs ) -> (match ((let _68_15735 = (Support.Microsoft.FStar.Util.for_all (fun ( _35_1673 ) -> (match (_35_1673) with
| (_, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15735))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c ) -> (let _35_1676 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15738 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _68_15738))
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
(let _68_15739 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _68_15739))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs ) -> (let _68_15742 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.Prims.pipe_right _68_15742 Support.Microsoft.FStar.Util.set_elements)))
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
in (match ((let _68_15747 = (should_gen t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15747))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _35_1721 = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (let _68_15748 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_15748)))) with
| true -> begin
(let _35_1717 = (destruct_comp ct)
in (match (_35_1717) with
| (_, wp, _) -> begin
(let binder = (let _68_15749 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_68_15749)::[])
in (let post = (let _68_15753 = (let _68_15750 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _68_15750))
in (let _68_15752 = (let _68_15751 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_68_15751))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_15753 _68_15752 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _68_15760 = (let _68_15759 = (let _68_15758 = (let _68_15757 = (let _68_15756 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_68_15756)::[])
in (wp, _68_15757))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15758))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _68_15759))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _68_15760))
in (let _68_15761 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _68_15761)))))
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
(let a = (let _68_15766 = (let _68_15765 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left (fun ( _68_15764 ) -> Some (_68_15764)) _68_15765))
in (Microsoft_FStar_Absyn_Util.new_bvd _68_15766))
in (let t = (let _68_15767 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _68_15767 k))
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
in (let _68_15768 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _68_15768)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify ) ( env ) ( lecs ) -> (let _35_1801 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_15777 = (let _68_15776 = (Support.List.map (fun ( _35_1800 ) -> (match (_35_1800) with
| (lb, _, _) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.Prims.pipe_right _68_15776 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _68_15777))
end
| false -> begin
()
end)
in (match ((let _68_15779 = (Support.Prims.pipe_right lecs (Support.List.map (fun ( _35_1807 ) -> (match (_35_1807) with
| (_, e, c) -> begin
(e, c)
end))))
in (gen verify env _68_15779))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _35_1816 ) ( _35_1819 ) -> (match ((_35_1816, _35_1819)) with
| ((l, _, _), (e, c)) -> begin
(let _35_1820 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_15784 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_15783 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _68_15782 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _68_15784 _68_15783 _68_15782))))
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
(let _68_15796 = (discharge g)
in (let _68_15795 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (_68_15796, _68_15795)))
end
| false -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _68_15797 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.Prims.pipe_right _68_15797 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _35_1860 = (destruct_comp c)
in (match (_35_1860) with
| (t, wp, _) -> begin
(let vc = (let _68_15803 = (let _68_15801 = (let _68_15800 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _68_15799 = (let _68_15798 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15798)::[])
in (_68_15800)::_68_15799))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _68_15801))
in (let _68_15802 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15803 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _68_15802)))
in (let g = (let _68_15804 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_15804))
in (let _68_15806 = (discharge g)
in (let _68_15805 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_68_15806, _68_15805)))))
end))))))
end))))

let short_circuit_exp = (fun ( head ) ( seen_args ) -> (let short_bin_op_e = (fun ( f ) -> (fun ( _35_12 ) -> (match (_35_12) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _)::[] -> begin
(let _68_15825 = (f fst)
in (Support.Prims.pipe_right _68_15825 (fun ( _68_15824 ) -> Some (_68_15824))))
end
| _ -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let table = (let op_and_e = (fun ( e ) -> (let _68_15831 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_68_15831, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e ) -> (let _68_15835 = (let _68_15834 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _68_15834))
in (_68_15835, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1890 ) -> (match (_35_1890) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _68_15853 = (mk seen_args)
in Some (_68_15853))
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
in (let op_and_t = (fun ( t ) -> (let _68_15874 = (unlabel t)
in (Support.Prims.pipe_right _68_15874 (fun ( _68_15873 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15873)))))
in (let op_or_t = (fun ( t ) -> (let _68_15879 = (let _68_15877 = (unlabel t)
in (Support.Prims.pipe_right _68_15877 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.Prims.pipe_right _68_15879 (fun ( _68_15878 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15878)))))
in (let op_imp_t = (fun ( t ) -> (let _68_15883 = (unlabel t)
in (Support.Prims.pipe_right _68_15883 (fun ( _68_15882 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15882)))))
in (let short_op_ite = (fun ( _35_14 ) -> (match (_35_14) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
(let _68_15887 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.Prims.pipe_right _68_15887 (fun ( _68_15886 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_15886))))
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
(let _68_15914 = (mk seen_args)
in Some (_68_15914))
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
in (let _68_15928 = (let _68_15927 = (let _68_15926 = (let _68_15925 = (let _68_15924 = (let _68_15923 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _68_15923))
in (_68_15924)::[])
in (ens, _68_15925))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15926 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _68_15927))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _68_15928 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
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
(let _68_15934 = (let _68_15931 = (norm req)
in Some (_68_15931))
in (let _68_15933 = (let _68_15932 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.Prims.pipe_left norm _68_15932))
in (_68_15934, _68_15933)))
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
(let _35_2022 = (match ((let _68_15936 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _68_15935 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_68_15936, _68_15935)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _ -> begin
(failwith ("Impossible"))
end)
in (match (_35_2022) with
| (as_req, as_ens) -> begin
(let req = (let _68_15940 = (let _68_15939 = (let _68_15938 = (let _68_15937 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_68_15937)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_15938)
in (as_req, _68_15939))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15940 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _68_15944 = (let _68_15943 = (let _68_15942 = (let _68_15941 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_68_15941)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_15942)
in (as_ens, _68_15943))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_15944 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _68_15948 = (let _68_15945 = (norm req)
in Some (_68_15945))
in (let _68_15947 = (let _68_15946 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _68_15946))
in (_68_15948, _68_15947)))))
end))
end
| _ -> begin
(failwith ("Impossible"))
end)
end))
end)
end)
end))))




