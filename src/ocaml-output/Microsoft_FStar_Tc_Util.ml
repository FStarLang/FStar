
let try_solve = (fun env f -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun env errs -> (Microsoft_FStar_Tc_Errors.report (Microsoft_FStar_Tc_Env.get_range env) (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)))

let discharge_guard = (fun env g -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun env g -> (discharge_guard env g))

let syn' = (fun env k -> (Microsoft_FStar_Absyn_Syntax.syn (Microsoft_FStar_Tc_Env.get_range env) k))

let is_xvar_free = (fun x t -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) f.Microsoft_FStar_Absyn_Syntax.fxvs)))

let is_tvar_free = (fun a t -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun) f.Microsoft_FStar_Absyn_Syntax.ftvs)))

let check_and_ascribe = (fun env e t1 t2 -> (let env = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.Microsoft_FStar_Tc_Env.use_eq then begin
(Microsoft_FStar_Tc_Rel.try_teq env t1 t2)
end else begin
(match ((Microsoft_FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Tc_Rel.apply_guard f e))
end)
end)
in if (env.Microsoft_FStar_Tc_Env.is_pattern && false) then begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1), (Microsoft_FStar_Tc_Env.get_range env)))))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1), (Microsoft_FStar_Tc_Env.get_range env)))))
end
| Some (g) -> begin
(let _302022 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
((Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") (Microsoft_FStar_Tc_Rel.guard_to_string env g))
end
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t2) (Some (t2)) e.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(let _302029 = e
in {Microsoft_FStar_Absyn_Syntax.n = _302029.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = (Support.Microsoft.FStar.Util.mk_ref (Some (t2))); Microsoft_FStar_Absyn_Syntax.pos = _302029.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _302029.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _302029.Microsoft_FStar_Absyn_Syntax.uvs})
end)
in (e, g))))
end)
end)))

let env_binders = (fun env -> if (! (Microsoft_FStar_Options.full_context_dependency)) then begin
(Microsoft_FStar_Tc_Env.binders env)
end else begin
(Microsoft_FStar_Tc_Env.t_binders env)
end)

let as_uvar_e = (fun _301974 -> (match (_301974) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
uv
end
| _ -> begin
(failwith "Impossible")
end))

let as_uvar_t = (fun t -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
uv
end
| _ -> begin
(failwith "Impossible")
end))

let new_kvar = (fun env -> ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_kvar (Microsoft_FStar_Tc_Env.get_range env) (env_binders env))))

let new_tvar = (fun env k -> ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_tvar (Microsoft_FStar_Tc_Env.get_range env) (env_binders env) k)))

let new_evar = (fun env t -> ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_evar (Microsoft_FStar_Tc_Env.get_range env) (env_binders env) t)))

let new_implicit_tvar = (fun env k -> (let _302076 = (Microsoft_FStar_Tc_Rel.new_tvar (Microsoft_FStar_Tc_Env.get_range env) (env_binders env) k)
in (match (_302076) with
| (t, u) -> begin
(t, ((as_uvar_t u), u.Microsoft_FStar_Absyn_Syntax.pos))
end)))

let new_implicit_evar = (fun env t -> (let _302081 = (Microsoft_FStar_Tc_Rel.new_evar (Microsoft_FStar_Tc_Env.get_range env) (env_binders env) t)
in (match (_302081) with
| (e, u) -> begin
(e, ((as_uvar_e u), u.Microsoft_FStar_Absyn_Syntax.pos))
end)))

let force_tk = (fun s -> (match ((! (s.Microsoft_FStar_Absyn_Syntax.tk))) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun args -> ((Support.List.map (fun _301975 -> (match (_301975) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((force_tk t)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((force_tk v)), imp)
end))) args))

let is_implicit = (fun _301976 -> (match (_301976) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _ -> begin
false
end))

let destruct_arrow_kind = (fun env tt k args -> (let ktop = ((Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env) (Microsoft_FStar_Absyn_Util.compress_kind k))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun k -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_, qual)::_ -> begin
(is_implicit qual)
end
| _ -> begin
false
end)
in (let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (is_implicit (Support.Prims.snd b)) then begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
((fun x -> (Support.Microsoft.FStar.Util.Inl (x), (Microsoft_FStar_Absyn_Syntax.as_implicit true))) ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_tvar r vars (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
((fun x -> (Support.Microsoft.FStar.Util.Inr (x), (Microsoft_FStar_Absyn_Syntax.as_implicit true))) ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_evar r vars (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort))))
end)
in (let subst = if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
((Microsoft_FStar_Absyn_Util.subst_formal b imp_arg))::subst
end
in (let _302140 = (mk_implicits vars subst brest)
in (match (_302140) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
([], (Microsoft_FStar_Absyn_Util.subst_binders subst bs))
end
end
| _ -> begin
([], (Microsoft_FStar_Absyn_Util.subst_binders subst bs))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(let _302145 = (mk_implicits (Microsoft_FStar_Tc_Env.binders env) [] bs)
in (match (_302145) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_kvar r binders))
in (let bs = (Microsoft_FStar_Absyn_Util.null_binders_of_tks (tks_of_args args))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _302159 = ((force_trivial env) (Microsoft_FStar_Tc_Rel.keq env None k kar))
in ([], bs, kres)))))))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop), r))))
end))
in (aux ktop)))))

let pat_as_exps = (fun allow_implicits env p -> (let pvar_eq = (fun x y -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _)), Microsoft_FStar_Tc_Env.Binding_var ((y, _))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _ -> begin
false
end))
in (let vars_of_bindings = (fun bs -> ((Support.List.map (fun _301977 -> (match (_301977) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _ -> begin
(failwith "impos")
end))) bs))
in (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _302220 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_302220) with
| (e, u) -> begin
(let p = (let _302221 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _302221.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _302221.Microsoft_FStar_Absyn_Syntax.p})
in ([], [], [], env, (Microsoft_FStar_Absyn_Syntax.varg e), p))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _)) -> begin
(let k = (new_kvar env)
in (let _302232 = (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p (Microsoft_FStar_Tc_Env.binders env) k)
in (match (_302232) with
| (t, u) -> begin
(let p = (let _302233 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _302233.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _302233.Microsoft_FStar_Absyn_Syntax.p})
in ([], [], [], env, (Support.Microsoft.FStar.Util.Inl (t), (Microsoft_FStar_Absyn_Syntax.as_implicit true)), p))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in ([], [], [], env, (Microsoft_FStar_Absyn_Syntax.varg e), p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)))
in (let env = if allow_wc_dependence then begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, (Microsoft_FStar_Absyn_Syntax.varg e), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)) -> begin
(let b = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, (Support.Microsoft.FStar.Util.Inr (e), (Microsoft_FStar_Absyn_Syntax.as_implicit imp)), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = Microsoft_FStar_Tc_Env.Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, (new_kvar env)))
in (let env = if allow_wc_dependence then begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, (Microsoft_FStar_Absyn_Syntax.targ t), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = Microsoft_FStar_Tc_Env.Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, (new_kvar env)))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, (Microsoft_FStar_Absyn_Syntax.targ t), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, pats)) -> begin
(let _302286 = ((Support.List.fold_left (fun _302271 p -> (match (_302271) with
| (b, a, w, env, args, pats) -> begin
(let _302279 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_302279) with
| (b', a', w', env, arg, pat) -> begin
((b')::b, (a')::a, (w')::w, env, (arg)::args, (pat)::pats)
end))
end)) ([], [], [], env, [], [])) pats)
in (match (_302286) with
| (b, a, w, env, args, pats) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (((Microsoft_FStar_Absyn_Syntax.mk_Exp_app' ((Microsoft_FStar_Absyn_Util.fvar true fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p), ((Support.List.rev) args)) None p.Microsoft_FStar_Absyn_Syntax.p), Microsoft_FStar_Absyn_Syntax.Data_app))))
in (((Support.List.flatten) (Support.List.rev b)), ((Support.List.flatten) (Support.List.rev a)), ((Support.List.flatten) (Support.List.rev w)), env, (Microsoft_FStar_Absyn_Syntax.varg e), (let _302288 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _302288.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _302288.Microsoft_FStar_Absyn_Syntax.p})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, pats)) -> begin
(let pats = (Support.List.map (elaborate_pat env) pats)
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env fv.Microsoft_FStar_Absyn_Syntax.v)
in (let pats = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Too many pattern arguments", (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)))))
end)
end
| Some ((f, _)) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _::_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Too many pattern arguments", (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)))))
end
| (_::_, []) -> begin
((Support.List.map (fun f -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let a = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s (Microsoft_FStar_Absyn_Util.new_bvd None) Microsoft_FStar_Absyn_Syntax.kun)
in if allow_implicits then begin
(Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v))
end else begin
(Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v))
end)
end
| (Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" (Microsoft_FStar_Absyn_Print.pat_to_string p)), (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)))))
end))) formals)
end
| (f::formals', p::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(p)::(aux formals' pats')
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) when allow_implicits -> begin
(p)::(aux formals' pats')
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), _) -> begin
(let a = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s (Microsoft_FStar_Absyn_Util.new_bvd None) Microsoft_FStar_Absyn_Syntax.kun)
in (let p1 = if allow_implicits then begin
(Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v))
end else begin
(Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v))
end
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_) -> begin
pats'
end
| _ -> begin
pats
end)
in (p1)::(aux formals' pats'))))
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_var ((_, true))) -> begin
(p)::(aux formals' pats')
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v))
in (p)::(aux formals' pats)))
end
| ((Support.Microsoft.FStar.Util.Inr (_), _), _) -> begin
(p)::(aux formals' pats')
end)
end))
in (aux f pats))
end)
in (let _302434 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, pats)); Microsoft_FStar_Absyn_Syntax.sort = _302434.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _302434.Microsoft_FStar_Absyn_Syntax.p}))))
end
| _ -> begin
p
end))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _302449 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_302449) with
| (b, a, w, env, arg, p) -> begin
(match (((Support.Microsoft.FStar.Util.find_dup pvar_eq) b)) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x))), p.Microsoft_FStar_Absyn_Syntax.p))))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x))), p.Microsoft_FStar_Absyn_Syntax.p))))
end
| _ -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun env p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _302479 = (one_pat false env q)
in (match (_302479) with
| (b, a, _, arg, q) -> begin
(let _302494 = (Support.List.fold_right (fun p _302484 -> (match (_302484) with
| (w, args, pats) -> begin
(let _302490 = (one_pat false env p)
in (match (_302490) with
| (b', a', w', arg, p) -> begin
if (not ((Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a'))) then begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars (vars_of_bindings a) (vars_of_bindings a')), (Microsoft_FStar_Tc_Env.get_range env)))))
end else begin
((Support.List.append w' w), (arg)::args, (p)::pats)
end
end))
end)) pats ([], [], []))
in (match (_302494) with
| (w, args, pats) -> begin
((Support.List.append b w), (arg)::args, (let _302495 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_disj ((q)::pats); Microsoft_FStar_Absyn_Syntax.sort = _302495.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _302495.Microsoft_FStar_Absyn_Syntax.p}))
end))
end))
end
| _ -> begin
(let _302506 = (one_pat true env p)
in (match (_302506) with
| (b, _, _, arg, p) -> begin
(b, (arg)::[], p)
end))
end))
in (let _302510 = (top_level_pat_as_args env p)
in (match (_302510) with
| (b, args, p) -> begin
(let exps = ((Support.List.map (fun _301978 -> (match (_301978) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(failwith "Impossible: top-level pattern must be an expression")
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
e
end))) args)
in (b, exps, p))
end)))))))))

let decorate_pattern = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (Microsoft_FStar_Absyn_Syntax.withinfo q ((fun __dataconst_1 -> Some (__dataconst_1)) (Support.Microsoft.FStar.Util.Inr (t))) p.Microsoft_FStar_Absyn_Syntax.p))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_), Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(pkg p.Microsoft_FStar_Absyn_Syntax.v (force_tk e))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _302550 = if (not ((Microsoft_FStar_Absyn_Util.bvar_eq x y))) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v) (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)))
end
in (let _302552 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort))
end
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _302555 = x
in {Microsoft_FStar_Absyn_Syntax.v = _302555.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _302555.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp))) (force_tk e))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _302563 = if (not ((Microsoft_FStar_Absyn_Util.bvar_eq x y))) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v) (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)))
end
in (let x = (let _302565 = x
in {Microsoft_FStar_Absyn_Syntax.v = _302565.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = (force_tk e); Microsoft_FStar_Absyn_Syntax.p = _302565.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)), _) -> begin
(let x = (let _302576 = x
in {Microsoft_FStar_Absyn_Syntax.v = _302576.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = (force_tk e); Microsoft_FStar_Absyn_Syntax.p = _302576.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _))) -> begin
(let _302589 = if (not ((Microsoft_FStar_Absyn_Util.fvar_eq fv fv'))) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str))
end
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) -> begin
(let _302613 = if (not ((Microsoft_FStar_Absyn_Util.fvar_eq fv fv'))) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str))
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, (Support.List.rev matched_pats)))) (force_tk e))
end
| (arg::args, argpat::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p (force_tk t))
in (let q = (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) ((fun __dataconst_1 -> Some (__dataconst_1)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort))) p.Microsoft_FStar_Absyn_Syntax.p)
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p (force_tk e))
in (let q = (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) ((fun __dataconst_1 -> Some (__dataconst_1)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort))) p.Microsoft_FStar_Absyn_Syntax.p)
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
(failwith (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" (Microsoft_FStar_Absyn_Print.pat_to_string p) (Microsoft_FStar_Absyn_Print.exp_to_string e)))
end))
in (match_args [] args argpats))))
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p) (Microsoft_FStar_Absyn_Print.pat_to_string qq) ((Support.String.concat "\n\t") ((Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string) exps))))
end))))
and aux_t = (fun p t0 -> (let pkg = (fun q k -> (Microsoft_FStar_Absyn_Syntax.withinfo q ((fun __dataconst_1 -> Some (__dataconst_1)) (Support.Microsoft.FStar.Util.Inl (k))) p.Microsoft_FStar_Absyn_Syntax.p))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _302685 = if (not ((Microsoft_FStar_Absyn_Util.bvar_eq a b))) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v) (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)))
end
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _302692 = if (not ((Microsoft_FStar_Absyn_Util.bvar_eq a b))) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v) (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)))
end
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_tvar (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _)), _) -> begin
(let k0 = (force_tk t0)
in (let a = (let _302703 = a
in {Microsoft_FStar_Absyn_Syntax.v = _302703.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k0; Microsoft_FStar_Absyn_Syntax.p = _302703.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.Microsoft_FStar_Absyn_Syntax.sort)))
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p) (Microsoft_FStar_Absyn_Print.pat_to_string p) (Microsoft_FStar_Absyn_Print.typ_to_string t)))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) ((fun __dataconst_1 -> Some (__dataconst_1)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun))) p.Microsoft_FStar_Absyn_Syntax.p))
end
| (_, e::[]) -> begin
(aux p e)
end
| _ -> begin
(failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp = (fun pat -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _ -> begin
(failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun f -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun p -> (let _302735 = (decorated_pattern_as_either p)
in (match (_302735) with
| (vars, te) -> begin
(vars, (te, (Microsoft_FStar_Absyn_Syntax.as_implicit true)))
end)))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
([], (pkg (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) -> begin
((Support.Microsoft.FStar.Util.Inr (x))::[], (pkg (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, pats)) -> begin
(let _302753 = ((Support.List.unzip) ((Support.List.map pat_as_arg) pats))
in (match (_302753) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (vars, (pkg (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' ((Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, true) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p), args)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
([], e)
end
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
((Support.Microsoft.FStar.Util.Inl (a))::[], (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _ -> begin
(failwith "Expected a type pattern")
end))
and decorated_pattern_as_either = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _302790 = (decorated_pattern_as_typ p)
in (match (_302790) with
| (vars, t) -> begin
(vars, Support.Microsoft.FStar.Util.Inl (t))
end))
end
| _ -> begin
(let _302795 = (decorated_pattern_as_exp p)
in (match (_302795) with
| (vars, e) -> begin
(vars, Support.Microsoft.FStar.Util.Inr (e))
end))
end))

let mk_basic_dtuple_type = (fun env n -> (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let l = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (Microsoft_FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (Microsoft_FStar_Absyn_Util.ftv l k)
in (let vars = (Microsoft_FStar_Tc_Env.binders env)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _302841 = ((Support.List.fold_left (fun _302818 _302822 -> (match ((_302818, _302822)) with
| ((out, subst), (b, _)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype))) (Some (k)) r)
end
| _ -> begin
(failwith "Impossible")
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (((Microsoft_FStar_Absyn_Syntax.targ arg))::out, subst))))
end)
end)) ([], [])) bs)
in (match (_302841) with
| (args, _) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, (Support.List.rev args)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
end))
end
| _ -> begin
(failwith "Impossible")
end)))))))

let extract_lb_annotation = (fun env t e -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun scope a -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope))
in ((let _302854 = a
in {Microsoft_FStar_Absyn_Syntax.v = _302854.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _302854.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _ -> begin
(a, true)
end))
in (let mk_v_binder = (fun scope x -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype))
in (match ((Microsoft_FStar_Absyn_Syntax.null_v_binder t)) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(x, false)
end
| _ -> begin
(failwith "impos")
end))
end
| _ -> begin
(match ((Microsoft_FStar_Absyn_Syntax.null_v_binder x.Microsoft_FStar_Absyn_Syntax.sort)) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(x, true)
end
| _ -> begin
(failwith "impos")
end)
end))
in (let rec aux = (fun vars e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(e, t, true)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _302918 = ((Support.List.fold_left (fun _302899 b -> (match (_302899) with
| (scope, bs, check) -> begin
(match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _302905 = (mk_t_binder scope a)
in (match (_302905) with
| (tb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl (tb), (Support.Prims.snd b))
in (let bs = (Support.List.append bs ((b)::[]))
in (let scope = (Support.List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _302913 = (mk_v_binder scope x)
in (match (_302913) with
| (vb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (vb), (Support.Prims.snd b))
in (scope, (Support.List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)) bs)
in (match (_302918) with
| (scope, bs, check) -> begin
(let _302922 = (aux scope body)
in (match (_302922) with
| (body, res, check_res) -> begin
(let c = (Microsoft_FStar_Absyn_Util.ml_comp res r)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _302925 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High) then begin
(Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" (Support.Microsoft.FStar.Range.string_of_range r) (Microsoft_FStar_Absyn_Print.typ_to_string t))
end
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _ -> begin
(e, ((Support.Prims.fst) (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)), false)
end))
in (aux (Microsoft_FStar_Tc_Env.t_binders env) e)))))
end
| _ -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun c -> (let _302948 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (wlp), _)::[] -> begin
(wp, wlp)
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str ((Support.String.concat ", ") (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args))))
end)
in (match (_302948) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun c m lift -> (let _302956 = (destruct_comp c)
in (match (_302956) with
| (_, wp, wlp) -> begin
{Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = ((Microsoft_FStar_Absyn_Syntax.targ (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)))::((Microsoft_FStar_Absyn_Syntax.targ (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)))::[]; Microsoft_FStar_Absyn_Syntax.flags = []}
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
l
end
| Some ((_, c)) -> begin
(find (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c).Microsoft_FStar_Absyn_Syntax.effect_name)
end))
in (match ((Support.Microsoft.FStar.Util.smap_try_find cache l.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(let m = (find l)
in (let _302972 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str m)
in m))
end))))

let join_effects = (fun env l1 l2 -> (let _302982 = (Microsoft_FStar_Tc_Env.join env (norm_eff_name env l1) (norm_eff_name env l2))
in (match (_302982) with
| (m, _, _) -> begin
m
end)))

let join_lcomp = (fun env c1 c2 -> if ((Microsoft_FStar_Absyn_Syntax.lid_equals c1.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.tot_effect_lid) && (Microsoft_FStar_Absyn_Syntax.lid_equals c2.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.tot_effect_lid)) then begin
Microsoft_FStar_Absyn_Const.tot_effect_lid
end else begin
(join_effects env c1.Microsoft_FStar_Absyn_Syntax.eff_name c2.Microsoft_FStar_Absyn_Syntax.eff_name)
end)

let lift_and_destruct = (fun env c1 c2 -> (let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _302994 = (Microsoft_FStar_Tc_Env.join env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (match (_302994) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env m)
in (let _303000 = (Microsoft_FStar_Tc_Env.wp_signature env md.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_303000) with
| (a, kwp) -> begin
((md, a, kwp), (destruct_comp m1), (destruct_comp m2))
end)))))
end)))))

let is_pure_effect = (fun env l -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.pure_effect_lid)))

let mk_comp = (fun md result wp wlp flags -> (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = ((Microsoft_FStar_Absyn_Syntax.targ wp))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::[]; Microsoft_FStar_Absyn_Syntax.flags = flags}))

let lcomp_of_comp = (fun c0 -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun _303011 -> (match (_303011) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun subst lc -> (let _303014 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _303014.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ); Microsoft_FStar_Absyn_Syntax.cflags = _303014.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun _303016 -> (match (_303016) with
| () -> begin
(Microsoft_FStar_Absyn_Util.subst_comp subst (lc.Microsoft_FStar_Absyn_Syntax.comp ()))
end))}))

let is_function = (fun t -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

let return_value = (fun env t v -> (let c = (match ((Microsoft_FStar_Tc_Env.effect_decl_opt env Microsoft_FStar_Absyn_Const.pure_effect_lid)) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _303031 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.pure_effect_lid)
in (match (_303031) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = ((Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (m.Microsoft_FStar_Absyn_Syntax.ret, ((Microsoft_FStar_Absyn_Syntax.targ t))::((Microsoft_FStar_Absyn_Syntax.varg v))::[]) (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _303036 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High) then begin
(Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Absyn_Print.exp_to_string v) (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c))
end
in c)))

let bind = (fun env e1opt lc1 _303043 -> (match (_303043) with
| (b, lc2) -> begin
(let _303054 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme) then begin
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
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1) bstr (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)))
end
in (let bind_it = (fun _303057 -> (match (_303057) with
| () -> begin
(let c1 = (lc1.Microsoft_FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.Microsoft_FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun _303061 -> (match (_303061) with
| () -> begin
(let aux = (fun _303063 -> (match (_303063) with
| () -> begin
if (Microsoft_FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid (_)) -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_var (_)) -> begin
if (Microsoft_FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _ -> begin
None
end)
end else begin
if ((Microsoft_FStar_Absyn_Util.is_ml_comp c1) && (Microsoft_FStar_Absyn_Util.is_ml_comp c2)) then begin
Some (c2)
end else begin
None
end
end
end))
in (match ((e1opt, b)) with
| (Some (e), Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _)))) -> begin
if ((Microsoft_FStar_Absyn_Util.is_total_comp c1) && (not ((Microsoft_FStar_Absyn_Syntax.is_null_bvd x)))) then begin
((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2))
end else begin
(aux ())
end
end
| _ -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _303103 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("bind"))) then begin
(Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" (match (b) with
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
end) (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1) (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2) (Microsoft_FStar_Absyn_Print.comp_typ_to_string c))
end
in c)
end
| None -> begin
(let _303118 = (lift_and_destruct env c1 c2)
in (match (_303118) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
((Microsoft_FStar_Absyn_Syntax.null_v_binder t1))::[]
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
((Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1)))::[]
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
((Microsoft_FStar_Absyn_Syntax.null_v_binder t1))::[]
end
| _ -> begin
(failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun wp -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = ((Microsoft_FStar_Absyn_Syntax.targ t1))::((Microsoft_FStar_Absyn_Syntax.targ t2))::((Microsoft_FStar_Absyn_Syntax.targ wp1))::((Microsoft_FStar_Absyn_Syntax.targ wlp1))::((Microsoft_FStar_Absyn_Syntax.targ (mk_lam wp2)))::((Microsoft_FStar_Absyn_Syntax.targ (mk_lam wlp2)))::[]
in (let wlp_args = ((Microsoft_FStar_Absyn_Syntax.targ t1))::((Microsoft_FStar_Absyn_Syntax.targ t2))::((Microsoft_FStar_Absyn_Syntax.targ wlp1))::((Microsoft_FStar_Absyn_Syntax.targ (mk_lam wlp2)))::[]
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = (join_lcomp env lc1 lc2); Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it}))
end))

let lift_formula = (fun env t mk_wp mk_wlp f -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.pure_effect_lid)
in (let _303149 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_303149) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (mk_wp, ((Microsoft_FStar_Absyn_Syntax.targ t))::((Microsoft_FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (mk_wlp, ((Microsoft_FStar_Absyn_Syntax.targ t))::((Microsoft_FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos)
in (mk_comp md_pure Microsoft_FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun t -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.Microsoft_FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun env b lc -> (let refresh = (fun _303158 -> (match (_303158) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in if (Microsoft_FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _303165 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range env)))
end
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _303168 = if ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name))) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) then begin
(Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" (Microsoft_FStar_Absyn_Print.comp_typ_to_string c) (Microsoft_FStar_Absyn_Print.comp_typ_to_string (Microsoft_FStar_Absyn_Syntax.mk_Comp c')))
end
in (let _303173 = (destruct_comp c')
in (match (_303173) with
| (t, wp, wlp) -> begin
(let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((wp, Some (b), (Microsoft_FStar_Tc_Env.get_range env)))))
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((wlp, Some (b), (Microsoft_FStar_Tc_Env.get_range env)))))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _303176 = c'
in {Microsoft_FStar_Absyn_Syntax.effect_name = _303176.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _303176.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = ((Microsoft_FStar_Absyn_Syntax.targ wp))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::[]; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))))
end)))))
end)
end)
end))
in (let _303178 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _303178.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _303178.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _303178.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = refresh})))

let label = (fun reason r f -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str))) then begin
f
end else begin
(label (reason ()) r f)
end
end))

let label_guard = (fun reason r g -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
Microsoft_FStar_Tc_Rel.NonTrivial ((label reason r f))
end))

let weaken_guard = (fun g1 g2 -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _ -> begin
g2
end))

let weaken_precondition = (fun env lc f -> (let weaken = (fun _303210 -> (match (_303210) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match (f) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
if (Microsoft_FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _303219 = (destruct_comp c)
in (match (_303219) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.assume_p, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ f))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.assume_p, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ f))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::[]) None wlp.Microsoft_FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (let _303223 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _303223.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _303223.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _303223.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun reason env e lc g0 -> if (Microsoft_FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let flags = ((Support.List.collect (fun _301979 -> (match (_301979) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _ -> begin
[]
end))) lc.Microsoft_FStar_Absyn_Syntax.cflags)
in (let strengthen = (fun _303237 -> (match (_303237) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let g0 = (Microsoft_FStar_Tc_Rel.simplify_guard env g0)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g0)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let c = if (((Microsoft_FStar_Absyn_Util.is_pure_comp c) && (not ((is_function (Microsoft_FStar_Absyn_Util.comp_result c))))) && (not ((Microsoft_FStar_Absyn_Util.is_partial_return c)))) then begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar (Microsoft_FStar_Absyn_Util.comp_result c))
in (let xret = (return_value env x.Microsoft_FStar_Absyn_Syntax.sort (Microsoft_FStar_Absyn_Util.bvar_to_exp x))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (bind env (Some (e)) (lcomp_of_comp c) (Some (xbinding), (lcomp_of_comp xret)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _303252 = (destruct_comp c)
in (match (_303252) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.assert_p, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ (label_opt env reason (Microsoft_FStar_Tc_Env.get_range env) f)))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.assume_p, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ f))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::[]) None wlp.Microsoft_FStar_Absyn_Syntax.pos)
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in ((let _303257 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name); Microsoft_FStar_Absyn_Syntax.res_typ = _303257.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = if ((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (not ((Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)))) then begin
flags
end else begin
[]
end; Microsoft_FStar_Absyn_Syntax.comp = strengthen}), (let _303259 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _303259.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _303259.Microsoft_FStar_Tc_Rel.implicits}))))
end)

let ite = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _303266 -> (match (_303266) with
| () -> begin
(let _303282 = (lift_and_destruct env (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ()) (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ()))
in (match (_303282) with
| ((md, _, _), (res_t, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.if_then_else, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ g))::((Microsoft_FStar_Absyn_Syntax.targ wp_t))::((Microsoft_FStar_Absyn_Syntax.targ wp_e))::[]) None (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.ite_wp, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::[]) None wlp.Microsoft_FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp []))))))
end))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name); Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp}))

let bind_cases = (fun env res_t lcases -> (let eff = (match (lcases) with
| [] -> begin
(failwith "Empty cases!")
end
| hd::tl -> begin
(Support.List.fold_left (fun eff _303304 -> (match (_303304) with
| (_, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun _303307 -> (match (_303307) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.if_then_else, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ g))::((Microsoft_FStar_Absyn_Syntax.targ wp_t))::((Microsoft_FStar_Absyn_Syntax.targ wp_e))::[]) None (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)))
in (let default_case = (let post_k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_v_binder res_t))::[], Microsoft_FStar_Absyn_Syntax.ktype) res_t.Microsoft_FStar_Absyn_Syntax.pos)
in (let kwp = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder post_k))::[], Microsoft_FStar_Absyn_Syntax.ktype) res_t.Microsoft_FStar_Absyn_Syntax.pos)
in (let post = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s (Microsoft_FStar_Absyn_Util.new_bvd None) post_k)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.t_binder post))::[], ((label Microsoft_FStar_Tc_Errors.exhaustiveness_check (Microsoft_FStar_Tc_Env.get_range env)) (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype))) (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.t_binder post))::[], (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)) (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.pure_effect_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun _303323 celse -> (match (_303323) with
| (g, cthen) -> begin
(let _303341 = (lift_and_destruct env (cthen.Microsoft_FStar_Absyn_Syntax.comp ()) celse)
in (match (_303341) with
| ((md, _, _), (_, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(mk_comp md res_t (ifthenelse md res_t g wp_then wp_else) (ifthenelse md res_t g wlp_then wlp_else) [])
end))
end)) lcases default_case)
in (let comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env comp.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _303349 = (destruct_comp comp)
in (match (_303349) with
| (_, wp, wlp) -> begin
(let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.ite_wp, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ wlp))::[]) None wlp.Microsoft_FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp [])))
end)))))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = eff; Microsoft_FStar_Absyn_Syntax.res_typ = res_t; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun env bindings lc -> (let close = (fun _303356 -> (match (_303356) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in if (Microsoft_FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bindings wp0 -> (Support.List.fold_right (fun b wp -> (match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let bs = ((Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)))::[]
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.close_wp, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ t))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) None wp0.Microsoft_FStar_Absyn_Syntax.pos)))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = ((Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)))::[]
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, ((Microsoft_FStar_Absyn_Syntax.targ res_t))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) None wp0.Microsoft_FStar_Absyn_Syntax.pos)))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((l, t)) -> begin
wp
end
| Microsoft_FStar_Tc_Env.Binding_sig (s) -> begin
(failwith "impos")
end)) bindings wp0))
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _303387 = (destruct_comp c)
in (match (_303387) with
| (t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.Microsoft_FStar_Absyn_Syntax.result_typ wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (let _303391 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _303391.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _303391.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _303391.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun env e lc -> (let refine = (fun _303397 -> (match (_303397) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in if (not ((is_pure_effect env lc.Microsoft_FStar_Absyn_Syntax.eff_name))) then begin
c
end else begin
if (Microsoft_FStar_Absyn_Util.is_partial_return c) then begin
c
end else begin
(let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let t = c.Microsoft_FStar_Absyn_Syntax.result_typ
in (let c = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let ret = (lcomp_of_comp (return_value env t xexp))
in (let eq_ret = (weaken_precondition env ret (Microsoft_FStar_Tc_Rel.NonTrivial ((Microsoft_FStar_Absyn_Util.mk_eq t t xexp e))))
in (Microsoft_FStar_Absyn_Util.comp_set_flags ((bind env None (lcomp_of_comp c) (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)).Microsoft_FStar_Absyn_Syntax.comp ()) ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c))))))))))
end
end)
end))
in (let flags = if (((not ((Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ))) && (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc)) && (not ((Microsoft_FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.Microsoft_FStar_Absyn_Syntax.cflags
end else begin
lc.Microsoft_FStar_Absyn_Syntax.cflags
end
in (let _303407 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _303407.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _303407.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun env e c c' -> (match ((Microsoft_FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c'), (Microsoft_FStar_Tc_Env.get_range env)))))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_instantiate_typ = (fun env t k -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in if (not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs))) then begin
(t, k, [])
end else begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let rec aux = (fun subst _301980 -> (match (_301980) with
| (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _303437 = (new_implicit_tvar env k)
in (match (_303437) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _303443 = (aux subst rest)
in (match (_303443) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _303454 = (new_implicit_evar env t)
in (match (_303454) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _303460 = (aux subst rest)
in (match (_303460) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _303466 = (aux [] bs)
in (match (_303466) with
| (args, bs, subst, implicits) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst k)
in ((Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos), k, implicits)))
end)))
end
| _ -> begin
(t, k, [])
end)
end))

let maybe_instantiate = (fun env e t -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in if (not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let rec aux = (fun subst _301981 -> (match (_301981) with
| (Support.Microsoft.FStar.Util.Inl (a), _)::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _303492 = (new_implicit_tvar env k)
in (match (_303492) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _303498 = (aux subst rest)
in (match (_303498) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _303509 = (new_implicit_evar env t)
in (match (_303509) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _303515 = (aux subst rest)
in (match (_303515) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _303521 = (aux [] bs)
in (match (_303521) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (Microsoft_FStar_Absyn_Util.is_total_comp c) then begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
in ((mk_exp_app e args (Some (t))), t, implicits))
end else begin
(e, t, [])
end
end
| _ -> begin
(let t = ((Microsoft_FStar_Absyn_Util.subst_typ subst) (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos))
in ((mk_exp_app e args (Some (t))), t, implicits))
end))
end)))
end
| _ -> begin
(e, t, [])
end)
end))

let weaken_result_typ = (fun env e lc t -> (let gopt = if env.Microsoft_FStar_Tc_Env.use_eq then begin
((Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t), false)
end else begin
((Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t), true)
end
in (match (gopt) with
| (None, _) -> begin
(Microsoft_FStar_Tc_Rel.subtype_fail env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (Microsoft_FStar_Tc_Rel.simplify_guard env g)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(let lc = (let _303551 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _303551.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _303551.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _303551.Microsoft_FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _303556 = g
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _303556.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _303556.Microsoft_FStar_Tc_Rel.implicits})
in (let strengthen = (fun _303560 -> (match (_303560) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _303562 = if ((Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme) then begin
(Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f))
end
in (let ct = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _303567 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.pure_effect_lid)
in (match (_303567) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.ret, ((Microsoft_FStar_Absyn_Syntax.targ t))::((Microsoft_FStar_Absyn_Syntax.varg xexp))::[]) (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos)
in (let cret = (lcomp_of_comp (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))
in (let guard = if apply_guard then begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (f, ((Microsoft_FStar_Absyn_Syntax.varg xexp))::[]) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos)
end else begin
f
end
in (let _303577 = (strengthen_precondition ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)) (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos) e cret (Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard))))
in (match (_303577) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (bind env (Some (e)) (lcomp_of_comp (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)) (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _303580 = if ((Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme) then begin
(Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c))
end
in c)))
end)))))))))
end)))))
end))
in (let flags = ((Support.List.collect (fun _301982 -> (match (_301982) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _ -> begin
[]
end))) lc.Microsoft_FStar_Absyn_Syntax.cflags)
in (let lc = (let _303588 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name); Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen})
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun r t -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in if (((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(let ue = (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e))
in (let ut = (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t))
in (let uk = (Support.List.map (Microsoft_FStar_Absyn_Print.uvar_k_to_string) (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (! (Microsoft_FStar_Options.hide_uvar_nums))
in (let print_implicits_saved = (! (Microsoft_FStar_Options.print_implicits))
in (let _303600 = (Microsoft_FStar_Options.hide_uvar_nums := false)
in (let _303602 = (Microsoft_FStar_Options.print_implicits := true)
in (let _303604 = (Microsoft_FStar_Tc_Errors.report r (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union (Microsoft_FStar_Absyn_Print.typ_to_string t)))
in (let _303606 = (Microsoft_FStar_Options.hide_uvar_nums := hide_uvar_nums_saved)
in (Microsoft_FStar_Options.print_implicits := print_implicits_saved)))))))))))
end))

let gen = (fun verify env ecs -> if (not ((Support.Microsoft.FStar.Util.for_all (fun _303614 -> (match (_303614) with
| (_, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs))) then begin
None
end else begin
(let norm = (fun c -> (let _303617 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium) then begin
(Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" (Microsoft_FStar_Absyn_Print.comp_typ_to_string c))
end
in (let steps = (Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]
in (let c = if (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) then begin
(Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::[]) env c)
end
in (let _303621 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium) then begin
(Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" (Microsoft_FStar_Absyn_Print.comp_typ_to_string c))
end
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> ((Support.Microsoft.FStar.Util.set_elements) (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)))
in (let should_gen = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _)) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _301983 -> (match (_301983) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
true
end
| _ -> begin
false
end))) bs) then begin
false
end else begin
true
end
end
| _ -> begin
true
end))
in (let uvars = ((Support.List.map (fun _303646 -> (match (_303646) with
| (e, c) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ (Microsoft_FStar_Absyn_Util.comp_result c))
in if (not ((should_gen t))) then begin
([], e, c)
end else begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _303662 = if (((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (not ((Microsoft_FStar_Absyn_Util.is_total_comp c)))) then begin
(let _303658 = (destruct_comp ct)
in (match (_303658) with
| (_, wp, _) -> begin
(let binder = ((Microsoft_FStar_Absyn_Syntax.null_v_binder t))::[]
in (let post = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binder, (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)) (Some ((Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos))) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let vc = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env ((Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (wp, ((Microsoft_FStar_Absyn_Syntax.targ post))::[]))))
in (discharge_guard env (Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))))))
end))
end
in (uvs, e, c)))))))
end)
end))) ecs)
in (let ecs = ((Support.List.map (fun _303668 -> (match (_303668) with
| (uvs, e, c) -> begin
(let tvars = ((Support.List.map (fun _303671 -> (match (_303671) with
| (u, k) -> begin
(let a = (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) | (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)
end
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| _ -> begin
(let a = (Microsoft_FStar_Absyn_Util.new_bvd ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Tc_Env.get_range env)))
in (let t = (Microsoft_FStar_Absyn_Util.close_for_kind (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype) k)
in (let _303715 = (Microsoft_FStar_Absyn_Util.unchecked_unify u t)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.ktype))))
end)
in (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
end))) uvs)
in (let t = (match ((Microsoft_FStar_Absyn_Util.function_formals (Microsoft_FStar_Absyn_Util.comp_result c))) with
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
in (e, (Microsoft_FStar_Absyn_Syntax.mk_Total t)))))
end))) uvars)
in Some (ecs)))))))
end)

let generalize = (fun verify env lecs -> (let _303742 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" ((Support.String.concat ", ") (Support.List.map (fun _303741 -> (match (_303741) with
| (lb, _, _) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)))
end
in (match ((gen verify env ((Support.List.map (fun _303748 -> (match (_303748) with
| (_, e, c) -> begin
(e, c)
end))) lecs))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun _303757 _303760 -> (match ((_303757, _303760)) with
| ((l, _, _), (e, c)) -> begin
(let _303761 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium) then begin
(Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Absyn_Print.lbname_to_string l) (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c)))
end
in (l, e, c))
end)) lecs ecs)
end)))

let unresolved = (fun u -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Uvar -> begin
true
end
| _ -> begin
false
end))

let check_top_level = (fun env g lc -> (let discharge = (fun g -> (let _303772 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _303790 = (match (((Support.List.tryFind (fun _301984 -> (match (_301984) with
| Support.Microsoft.FStar.Util.Inl (u) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr ((u, _)) -> begin
(unresolved u)
end))) g.Microsoft_FStar_Tc_Rel.implicits)) with
| Some (Support.Microsoft.FStar.Util.Inr ((_, r))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _ -> begin
()
end)
in (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in if (Microsoft_FStar_Absyn_Util.is_total_lcomp lc) then begin
((discharge g), (lc.Microsoft_FStar_Absyn_Syntax.comp ()))
end else begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ (Microsoft_FStar_Tc_Normalize.norm_comp steps env c))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _303801 = (destruct_comp c)
in (match (_303801) with
| (t, wp, _) -> begin
(let vc = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.trivial, ((Microsoft_FStar_Absyn_Syntax.targ t))::((Microsoft_FStar_Absyn_Syntax.targ wp))::[]) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) (Microsoft_FStar_Tc_Env.get_range env))
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g (Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc))))
in ((discharge g), (Microsoft_FStar_Absyn_Syntax.mk_Comp c))))
end))))))
end)))

let short_circuit_exp = (fun head seen_args -> (let short_bin_op_e = (fun f _301985 -> (match (_301985) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _)::[] -> begin
((fun __dataconst_1 -> Some (__dataconst_1)) (f fst))
end
| _ -> begin
(failwith "Unexpexted args to binary operator")
end))
in (let table = (let op_and_e = (fun e -> ((Microsoft_FStar_Absyn_Util.b2t e), Microsoft_FStar_Absyn_Const.exp_false_bool))
in (let op_or_e = (fun e -> ((Microsoft_FStar_Absyn_Util.mk_neg (Microsoft_FStar_Absyn_Util.b2t e)), Microsoft_FStar_Absyn_Const.exp_true_bool))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun _303831 -> (match (_303831) with
| (x, mk) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals x lid) then begin
Some ((mk seen_args))
end else begin
None
end
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

let short_circuit_typ = (fun head seen_args -> (let short_bin_op_t = (fun f _301986 -> (match (_301986) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _)::[] -> begin
(f fst)
end
| _ -> begin
(failwith "Unexpexted args to binary operator")
end))
in (let op_and_t = (fun t -> Microsoft_FStar_Tc_Rel.NonTrivial ((unlabel t)))
in (let op_or_t = (fun t -> Microsoft_FStar_Tc_Rel.NonTrivial ((Microsoft_FStar_Absyn_Util.mk_neg (unlabel t))))
in (let op_imp_t = (fun t -> Microsoft_FStar_Tc_Rel.NonTrivial ((unlabel t)))
in (let short_op_ite = (fun _301987 -> (match (_301987) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial ((Microsoft_FStar_Absyn_Util.mk_neg guard))
end
| _ -> begin
(failwith "Unexpected args to ITE")
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
in (match ((Support.Microsoft.FStar.Util.find_map table (fun _303899 -> (match (_303899) with
| (x, mk) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals x lid) then begin
Some ((mk seen_args))
end else begin
None
end
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




