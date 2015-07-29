
let try_solve = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( f  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (Microsoft_FStar_Tc_Env_Mksolver_t.solve env.Microsoft_FStar_Tc_Env.solver env f))

let report = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( errs  :  string list ) -> (let _52_11366 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11365 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _52_11366 _52_11365))))

let discharge_guard = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( g  :  Microsoft_FStar_Tc_Rel.guard_t ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( g  :  Microsoft_FStar_Tc_Rel.guard_t ) -> (discharge_guard env g))

let syn' = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  'u35u2082 ) -> (let _52_11385 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _52_11385 k)))

let is_xvar_free = (fun ( x  :  Microsoft_FStar_Absyn_Syntax.bvvdef ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) f.Microsoft_FStar_Absyn_Syntax.fxvs)))

let is_tvar_free = (fun ( a  :  Microsoft_FStar_Absyn_Syntax.btvdef ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun) f.Microsoft_FStar_Absyn_Syntax.ftvs)))

let check_and_ascribe = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let check = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(Microsoft_FStar_Tc_Rel.try_teq env t1 t2)
end
| false -> begin
(match ((Microsoft_FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _52_11409 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.Prims.pipe_left (fun ( _52_11408  :  Microsoft_FStar_Tc_Rel.guard_t ) -> Some (_52_11408)) _52_11409))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _52_11413 = (let _52_11412 = (let _52_11411 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _52_11410 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_11411, _52_11410)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11412))
in (raise (_52_11413)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _52_11417 = (let _52_11416 = (let _52_11415 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _52_11414 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_11415, _52_11414)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11416))
in (raise (_52_11417)))
end
| Some (g) -> begin
(let _35_49 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11418 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _52_11418))
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
in (let _52_11419 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _35_56.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _52_11419; Microsoft_FStar_Absyn_Syntax.pos = _35_56.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _35_56.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _35_56.Microsoft_FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end))))

let env_binders = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (match ((Support.ST.read Microsoft_FStar_Options.full_context_dependency)) with
| true -> begin
(Microsoft_FStar_Tc_Env.binders env)
end
| false -> begin
(Microsoft_FStar_Tc_Env.t_binders env)
end))

let as_uvar_e = (fun ( _35_1  :  (Microsoft_FStar_Absyn_Syntax.exp', 'u35u2579) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (_35_1) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
uv
end
| _ -> begin
(failwith ("Impossible"))
end))

let as_uvar_t = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
uv
end
| _ -> begin
(failwith ("Impossible"))
end))

let new_kvar = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (let _52_11429 = (let _52_11428 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11427 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _52_11428 _52_11427)))
in (Support.Prims.pipe_right _52_11429 Support.Prims.fst)))

let new_tvar = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_11436 = (let _52_11435 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11434 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _52_11435 _52_11434 k)))
in (Support.Prims.pipe_right _52_11436 Support.Prims.fst)))

let new_evar = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_11443 = (let _52_11442 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11441 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _52_11442 _52_11441 t)))
in (Support.Prims.pipe_right _52_11443 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _35_103 = (let _52_11449 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11448 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _52_11449 _52_11448 k)))
in (match (_35_103) with
| (t, u) -> begin
(let _52_11451 = (let _52_11450 = (as_uvar_t u)
in (_52_11450, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _52_11451))
end)))

let new_implicit_evar = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _35_108 = (let _52_11457 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11456 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _52_11457 _52_11456 t)))
in (match (_35_108) with
| (e, u) -> begin
(let _52_11459 = (let _52_11458 = (as_uvar_e u)
in (_52_11458, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _52_11459))
end)))

let force_tk = (fun ( s  :  ('a, 'b) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_11462 = (let _52_11461 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _52_11461))
in (failwith (_52_11462)))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args  :  Microsoft_FStar_Absyn_Syntax.args ) -> (Support.Prims.pipe_right args (Support.List.map (fun ( _35_2  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_35_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _52_11467 = (let _52_11466 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_52_11466))
in (_52_11467, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _52_11469 = (let _52_11468 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_52_11468))
in (_52_11469, imp))
end)))))

let is_implicit = (fun ( _35_3  :  Microsoft_FStar_Absyn_Syntax.arg_qualifier option ) -> (match (_35_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _ -> begin
false
end))

let destruct_arrow_kind = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( tt  :  Microsoft_FStar_Absyn_Syntax.typ ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) ( args  :  Microsoft_FStar_Absyn_Syntax.args ) -> (let ktop = (let _52_11480 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.Prims.pipe_right _52_11480 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_, qual)::_ -> begin
(is_implicit qual)
end
| _ -> begin
false
end)
in (let rec mk_implicits = (fun ( vars  :  Microsoft_FStar_Absyn_Syntax.binders ) ( subst  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (bs) with
| b::brest -> begin
(match ((Support.Prims.pipe_right (Support.Prims.snd b) is_implicit)) with
| true -> begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_11493 = (let _52_11490 = (let _52_11489 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _52_11489))
in (Support.Prims.pipe_right _52_11490 Support.Prims.fst))
in (Support.Prims.pipe_right _52_11493 (fun ( x  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_11492 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _52_11492)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_11498 = (let _52_11495 = (let _52_11494 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _52_11494))
in (Support.Prims.pipe_right _52_11495 Support.Prims.fst))
in (Support.Prims.pipe_right _52_11498 (fun ( x  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (let _52_11497 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _52_11497)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _52_11499 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_52_11499)::subst)
end)
in (let _35_167 = (mk_implicits vars subst brest)
in (match (_35_167) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _52_11500 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _52_11500))
end)
end
| _ -> begin
(let _52_11501 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _52_11501))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _35_172 = (let _52_11502 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _52_11502 [] bs))
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
in (let kres = (let _52_11503 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.Prims.pipe_right _52_11503 Support.Prims.fst))
in (let bs = (let _52_11504 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _52_11504))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _35_186 = (let _52_11505 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.Prims.pipe_left (force_trivial env) _52_11505))
in ([], bs, kres)))))))
end
| _ -> begin
(let _52_11508 = (let _52_11507 = (let _52_11506 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_52_11506, r))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11507))
in (raise (_52_11508)))
end))
in (aux ktop)))))

let pat_as_exps = (fun ( allow_implicits  :  bool ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (let pvar_eq = (fun ( x  :  Microsoft_FStar_Tc_Env.binding ) ( y  :  Microsoft_FStar_Tc_Env.binding ) -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _)), Microsoft_FStar_Tc_Env.Binding_var ((y, _))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _ -> begin
false
end))
in (let vars_of_bindings = (fun ( bs  :  Microsoft_FStar_Tc_Env.binding list ) -> (Support.Prims.pipe_right bs (Support.List.map (fun ( _35_4  :  Microsoft_FStar_Tc_Env.binding ) -> (match (_35_4) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _ -> begin
(failwith ("impos"))
end)))))
in (let rec pat_as_arg_with_env = (fun ( allow_wc_dependence  :  bool ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _35_247 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_35_247) with
| (e, u) -> begin
(let p = (let _35_248 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _35_248.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_248.Microsoft_FStar_Absyn_Syntax.p})
in (let _52_11528 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _52_11528, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _)) -> begin
(let k = (new_kvar env)
in (let _35_259 = (let _52_11529 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _52_11529 k))
in (match (_35_259) with
| (t, u) -> begin
(let p = (let _35_260 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _35_260.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_260.Microsoft_FStar_Absyn_Syntax.p})
in (let _52_11531 = (let _52_11530 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (t), _52_11530))
in ([], [], [], env, _52_11531, p)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11532 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ([], [], [], env, _52_11532, p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _52_11534 = (let _52_11533 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_11533))
in Microsoft_FStar_Tc_Env.Binding_var (_52_11534))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11535 = (Microsoft_FStar_Absyn_Syntax.varg e)
in ((w)::[], [], (w)::[], env, _52_11535, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)) -> begin
(let b = (let _52_11537 = (let _52_11536 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_11536))
in Microsoft_FStar_Tc_Env.Binding_var (_52_11537))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11539 = (let _52_11538 = (Microsoft_FStar_Absyn_Syntax.as_implicit imp)
in (Support.Microsoft.FStar.Util.Inr (e), _52_11538))
in ((b)::[], (b)::[], [], env, _52_11539, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _52_11541 = (let _52_11540 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _52_11540))
in Microsoft_FStar_Tc_Env.Binding_typ (_52_11541))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11542 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((w)::[], [], (w)::[], env, _52_11542, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _52_11544 = (let _52_11543 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _52_11543))
in Microsoft_FStar_Tc_Env.Binding_typ (_52_11544))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11545 = (Microsoft_FStar_Absyn_Syntax.targ t)
in ((b)::[], (b)::[], [], env, _52_11545, p)))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _35_314 = (Support.Prims.pipe_right pats (Support.List.fold_left (fun ( _35_299  :  (Microsoft_FStar_Tc_Env.binding list list * Microsoft_FStar_Tc_Env.binding list list * Microsoft_FStar_Tc_Env.binding list list * Microsoft_FStar_Tc_Env.env * Microsoft_FStar_Absyn_Syntax.arg list * Microsoft_FStar_Absyn_Syntax.pat list) ) ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (match (_35_299) with
| (b, a, w, env, args, pats) -> begin
(let _35_307 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_307) with
| (b', a', w', env, arg, pat) -> begin
((b')::b, (a')::a, (w')::w, env, (arg)::args, (pat)::pats)
end))
end)) ([], [], [], env, [], [])))
in (match (_35_314) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _52_11553 = (let _52_11552 = (let _52_11551 = (let _52_11550 = (let _52_11549 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11548 = (Support.Prims.pipe_right args Support.List.rev)
in (_52_11549, _52_11548)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _52_11550 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_52_11551, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_11552))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _52_11553))
in (let _52_11557 = (Support.Prims.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _52_11556 = (Support.Prims.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _52_11555 = (Support.Prims.pipe_right (Support.List.rev w) Support.List.flatten)
in (let _52_11554 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_52_11557, _52_11556, _52_11555, env, _52_11554, (let _35_316 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _35_316.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _35_316.Microsoft_FStar_Absyn_Syntax.p})))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("impossible"))
end))
in (let rec elaborate_pat = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( p  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
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
(let _52_11564 = (let _52_11563 = (let _52_11562 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _52_11562))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11563))
in (raise (_52_11564)))
end)
end
| Some ((f, _)) -> begin
(let rec aux = (fun ( formals  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( pats  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t list ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _::_) -> begin
(let _52_11571 = (let _52_11570 = (let _52_11569 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _52_11569))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11570))
in (raise (_52_11571)))
end
| (_::_, []) -> begin
(Support.Prims.pipe_right formals (Support.List.map (fun ( f  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let a = (let _52_11573 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _52_11573 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _52_11574 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _52_11574))
end
| false -> begin
(let _52_11575 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _52_11575))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _52_11576 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _52_11576)))
end
| _ -> begin
(let _52_11581 = (let _52_11580 = (let _52_11579 = (let _52_11577 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _52_11577))
in (let _52_11578 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_52_11579, _52_11578)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11580))
in (raise (_52_11581)))
end))))
end
| (f::formals', p::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _52_11582 = (aux formals' pats')
in (p)::_52_11582)
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) when allow_implicits -> begin
(let _52_11583 = (aux formals' pats')
in (p)::_52_11583)
end
| ((Support.Microsoft.FStar.Util.Inl (_), _), _) -> begin
(let a = (let _52_11584 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _52_11584 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _52_11585 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _52_11585))
end
| false -> begin
(let _52_11586 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _52_11586))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_) -> begin
pats'
end
| _ -> begin
pats
end)
in (let _52_11587 = (aux formals' pats')
in (p1)::_52_11587))))
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_var ((_, true))) -> begin
(let _52_11588 = (aux formals' pats')
in (p)::_52_11588)
end
| ((Support.Microsoft.FStar.Util.Inr (_), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _52_11589 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var ((a, true))) None _52_11589))
in (let _52_11590 = (aux formals' pats)
in (p)::_52_11590)))
end
| ((Support.Microsoft.FStar.Util.Inr (_), _), _) -> begin
(let _52_11591 = (aux formals' pats')
in (p)::_52_11591)
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
in (let one_pat = (fun ( allow_wc_dependence  :  bool ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( p  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (let p = (elaborate_pat env p)
in (let _35_478 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_478) with
| (b, a, w, env, arg, p) -> begin
(match ((Support.Prims.pipe_right b (Support.Microsoft.FStar.Util.find_dup pvar_eq))) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _))) -> begin
(let _52_11600 = (let _52_11599 = (let _52_11598 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_52_11598, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11599))
in (raise (_52_11600)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _))) -> begin
(let _52_11603 = (let _52_11602 = (let _52_11601 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_52_11601, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11602))
in (raise (_52_11603)))
end
| _ -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _35_508 = (one_pat false env q)
in (match (_35_508) with
| (b, a, _, arg, q) -> begin
(let _35_523 = (Support.List.fold_right (fun ( p  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) ( _35_513  :  (Microsoft_FStar_Tc_Env.binding list * Microsoft_FStar_Absyn_Syntax.arg list * Microsoft_FStar_Absyn_Syntax.pat list) ) -> (match (_35_513) with
| (w, args, pats) -> begin
(let _35_519 = (one_pat false env p)
in (match (_35_519) with
| (b', a', w', arg, p) -> begin
(match ((let _52_11610 = (Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a')
in (not (_52_11610)))) with
| true -> begin
(let _52_11616 = (let _52_11615 = (let _52_11614 = (let _52_11612 = (vars_of_bindings a)
in (let _52_11611 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _52_11612 _52_11611)))
in (let _52_11613 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_11614, _52_11613)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11615))
in (raise (_52_11616)))
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
(let exps = (Support.Prims.pipe_right args (Support.List.map (fun ( _35_5  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_35_5) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(failwith ("Impossible: top-level pattern must be an expression"))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
e
end))))
in (b, exps, p))
end)))))))))

let decorate_pattern = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) ( exps  :  Microsoft_FStar_Absyn_Syntax.exp list ) -> (let qq = p
in (let rec aux = (fun ( p  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let pkg = (fun ( q  :  Microsoft_FStar_Absyn_Syntax.pat' ) ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_11635 = (Support.Prims.pipe_left (fun ( _52_11634  :  ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either ) -> Some (_52_11634)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _52_11635 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_), Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(let _52_11636 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _52_11636))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp)), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_579 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _52_11639 = (let _52_11638 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_11637 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _52_11638 _52_11637)))
in (failwith (_52_11639)))
end
| false -> begin
()
end)
in (let _35_581 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _52_11641 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_11640 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _52_11641 _52_11640)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _35_584 = x
in {Microsoft_FStar_Absyn_Syntax.v = _35_584.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _35_584.Microsoft_FStar_Absyn_Syntax.p})
in (let _52_11642 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, imp))) _52_11642))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _35_592 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _52_11645 = (let _52_11644 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_11643 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _52_11644 _52_11643)))
in (failwith (_52_11645)))
end
| false -> begin
()
end)
in (let x = (let _35_594 = x
in (let _52_11646 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_594.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _52_11646; Microsoft_FStar_Absyn_Syntax.p = _35_594.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _)), _) -> begin
(let x = (let _35_605 = x
in (let _52_11647 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _35_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _52_11647; Microsoft_FStar_Absyn_Syntax.p = _35_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _))) -> begin
(let _35_619 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _52_11648 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_52_11648)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) -> begin
(let _35_644 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _52_11649 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (failwith (_52_11649)))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats  :  Microsoft_FStar_Absyn_Syntax.pat list ) ( args  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( argpats  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t list ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _52_11656 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _52_11656))
end
| (arg::args, argpat::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let x = (let _52_11657 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _52_11657))
in (let q = (let _52_11659 = (Support.Prims.pipe_left (fun ( _52_11658  :  ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either ) -> Some (_52_11658)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _52_11659 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args ((q)::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) -> begin
(let x = (let _52_11660 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _52_11660))
in (let q = (let _52_11662 = (Support.Prims.pipe_left (fun ( _52_11661  :  ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either ) -> Some (_52_11661)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _52_11662 p.Microsoft_FStar_Absyn_Syntax.p))
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
(let _52_11665 = (let _52_11664 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _52_11663 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _52_11664 _52_11663)))
in (failwith (_52_11665)))
end))
in (match_args [] args argpats))))
end
| _ -> begin
(let _52_11670 = (let _52_11669 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11668 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _52_11667 = (let _52_11666 = (Support.Prims.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.Prims.pipe_right _52_11666 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _52_11669 _52_11668 _52_11667))))
in (failwith (_52_11670)))
end))))
and aux_t = (fun ( p  :  (Microsoft_FStar_Absyn_Syntax.pat', ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either option) Microsoft_FStar_Absyn_Syntax.withinfo_t ) ( t0  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let pkg = (fun ( q  :  Microsoft_FStar_Absyn_Syntax.pat' ) ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_11678 = (Support.Prims.pipe_left (fun ( _52_11677  :  ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either ) -> Some (_52_11677)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _52_11678 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_716 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _52_11681 = (let _52_11680 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_11679 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _52_11680 _52_11679)))
in (failwith (_52_11681)))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _35_723 = (match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _52_11684 = (let _52_11683 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_11682 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _52_11683 _52_11682)))
in (failwith (_52_11684)))
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
(let _52_11688 = (let _52_11687 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_11686 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _52_11685 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _52_11687 _52_11686 _52_11685))))
in (failwith (_52_11688)))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _52_11690 = (Support.Prims.pipe_left (fun ( _52_11689  :  ((Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax, Microsoft_FStar_Absyn_Syntax.typ) Support.Microsoft.FStar.Util.either ) -> Some (_52_11689)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _52_11690 p.Microsoft_FStar_Absyn_Syntax.p)))
end
| (_, e::[]) -> begin
(aux p e)
end
| _ -> begin
(failwith ("Unexpected number of patterns"))
end))))

let rec decorated_pattern_as_exp = (fun ( pat  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _ -> begin
(failwith ("top-level pattern should be decorated with a type"))
end)
in (let pkg = (fun ( f  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax option  ->  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.exp ) -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (let _35_766 = (decorated_pattern_as_either p)
in (match (_35_766) with
| (vars, te) -> begin
(let _52_11710 = (let _52_11709 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (te, _52_11709))
in (vars, _52_11710))
end)))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _52_11713 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _52_11713))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) -> begin
(let _52_11716 = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _52_11716))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _35_785 = (let _52_11717 = (Support.Prims.pipe_right pats (Support.List.map pat_as_arg))
in (Support.Prims.pipe_right _52_11717 Support.List.unzip))
in (match (_35_785) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _52_11723 = (let _52_11722 = (let _52_11721 = (let _52_11720 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_52_11720, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _52_11721))
in (Support.Prims.pipe_right _52_11722 pkg))
in (vars, _52_11723)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
([], e)
end
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(failwith ("Impossible: expected a term pattern"))
end)))))
and decorated_pattern_as_typ = (fun ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _52_11725 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _52_11725))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _ -> begin
(failwith ("Expected a type pattern"))
end))
and decorated_pattern_as_either = (fun ( p  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
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

let mk_basic_dtuple_type = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( n  :  int ) -> (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let l = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (Microsoft_FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (Microsoft_FStar_Absyn_Util.ftv l k)
in (let vars = (Microsoft_FStar_Tc_Env.binders env)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _35_873 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _35_850  :  (Microsoft_FStar_Absyn_Syntax.arg list * (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list) ) ( _35_854  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match ((_35_850, _35_854)) with
| ((out, subst), (b, _)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(failwith ("impossible"))
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let _52_11733 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_11733 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _52_11736 = (let _52_11735 = (let _52_11734 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_11734 Support.Prims.fst))
in (bs, _52_11735))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_11736 (Some (k)) r))
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _52_11738 = (let _52_11737 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_52_11737)::out)
in (_52_11738, subst)))))
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

let extract_lb_annotation = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun ( scope  :  Microsoft_FStar_Absyn_Syntax.binders ) ( a  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _52_11749 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.Prims.pipe_right _52_11749 Support.Prims.fst))
in ((let _35_886 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_886.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _35_886.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _ -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope  :  Microsoft_FStar_Absyn_Syntax.binders ) ( x  :  ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _52_11754 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_11754 Support.Prims.fst))
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
in (let rec aux = (fun ( vars  :  Microsoft_FStar_Absyn_Syntax.binders ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
(e, t, true)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _35_952 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _35_933  :  (Microsoft_FStar_Absyn_Syntax.binders * ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list * bool) ) ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_35_933) with
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
(let _52_11762 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _52_11761 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _52_11762 _52_11761)))
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
(let _52_11764 = (let _52_11763 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_11763 Support.Prims.fst))
in (e, _52_11764, false))
end))
in (let _52_11765 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _52_11765 e))))))
end
| _ -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun ( c  :  Microsoft_FStar_Absyn_Syntax.comp_typ ) -> (let _35_982 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (wlp), _)::[] -> begin
(wp, wlp)
end
| _ -> begin
(let _52_11770 = (let _52_11769 = (let _52_11768 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.Prims.pipe_right _52_11768 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _52_11769))
in (failwith (_52_11770)))
end)
in (match (_35_982) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c  :  Microsoft_FStar_Absyn_Syntax.comp_typ ) ( m  :  Microsoft_FStar_Absyn_Syntax.lident ) ( lift  :  Microsoft_FStar_Absyn_Syntax.typ  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _35_990 = (destruct_comp c)
in (match (_35_990) with
| (_, wp, wlp) -> begin
(let _52_11792 = (let _52_11791 = (let _52_11787 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _52_11787))
in (let _52_11790 = (let _52_11789 = (let _52_11788 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _52_11788))
in (_52_11789)::[])
in (_52_11791)::_52_11790))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _52_11792; Microsoft_FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let rec find = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
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

let join_effects = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( l1  :  Microsoft_FStar_Absyn_Syntax.lident ) ( l2  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let _35_1023 = (let _52_11806 = (norm_eff_name env l1)
in (let _52_11805 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _52_11806 _52_11805)))
in (match (_35_1023) with
| (m, _, _) -> begin
m
end)))

let join_lcomp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( c1  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( c2  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (match (((Microsoft_FStar_Absyn_Syntax.lid_equals c1.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) && (Microsoft_FStar_Absyn_Syntax.lid_equals c2.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid))) with
| true -> begin
Microsoft_FStar_Absyn_Const.effect_Tot_lid
end
| false -> begin
(join_effects env c1.Microsoft_FStar_Absyn_Syntax.eff_name c2.Microsoft_FStar_Absyn_Syntax.eff_name)
end))

let lift_and_destruct = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( c1  :  Microsoft_FStar_Absyn_Syntax.comp ) ( c2  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c1)
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
(let _52_11820 = (destruct_comp m1)
in (let _52_11819 = (destruct_comp m2)
in ((md, a, kwp), _52_11820, _52_11819)))
end)))))
end)))))

let is_pure_effect = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md  :  Microsoft_FStar_Absyn_Syntax.eff_decl ) ( result  :  Microsoft_FStar_Absyn_Syntax.typ ) ( wp  :  Microsoft_FStar_Absyn_Syntax.typ ) ( wlp  :  Microsoft_FStar_Absyn_Syntax.typ ) ( flags  :  Microsoft_FStar_Absyn_Syntax.cflags list ) -> (let _52_11843 = (let _52_11842 = (let _52_11841 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _52_11840 = (let _52_11839 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_11839)::[])
in (_52_11841)::_52_11840))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _52_11842; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _52_11843)))

let lcomp_of_comp = (fun ( c0  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1055  :  unit ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst  :  Microsoft_FStar_Absyn_Syntax.subst ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let _35_1058 = lc
in (let _52_11853 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1058.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _52_11853; Microsoft_FStar_Absyn_Syntax.cflags = _35_1058.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _35_1060  :  unit ) -> (match (()) with
| () -> begin
(let _52_11852 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _52_11852))
end))})))

let is_function = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match ((let _52_11856 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_11856.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

let return_value = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( v  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (let c = (match ((Microsoft_FStar_Tc_Env.effect_decl_opt env Microsoft_FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _35_1075 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_35_1075) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _52_11868 = (let _52_11867 = (let _52_11866 = (let _52_11865 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _52_11864 = (let _52_11863 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_52_11863)::[])
in (_52_11865)::_52_11864))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _52_11866))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_11867 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _52_11868))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _35_1080 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_11871 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_11870 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _52_11869 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _52_11871 _52_11870 _52_11869))))
end
| false -> begin
()
end)
in c)))

let bind = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e1opt  :  Microsoft_FStar_Absyn_Syntax.exp option ) ( lc1  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( _35_1087  :  lcomp_with_binder ) -> (match (_35_1087) with
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
in (let _52_11881 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _52_11880 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _52_11881 bstr _52_11880))))
end
| false -> begin
()
end)
in (let bind_it = (fun ( _35_1101  :  unit ) -> (match (()) with
| () -> begin
(let c1 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc1 ())
in (let c2 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc2 ())
in (let try_simplify = (fun ( _35_1105  :  unit ) -> (match (()) with
| () -> begin
(let aux = (fun ( _35_1107  :  unit ) -> (match (()) with
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
(match ((let _52_11889 = (Microsoft_FStar_Absyn_Util.is_ml_comp c1)
in (let _52_11888 = (Microsoft_FStar_Absyn_Util.is_ml_comp c2)
in (_52_11889 && _52_11888)))) with
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
(match ((let _52_11892 = (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp c1)
in (let _52_11891 = (let _52_11890 = (Microsoft_FStar_Absyn_Syntax.is_null_bvd x)
in (not (_52_11890)))
in (_52_11892 && _52_11891)))) with
| true -> begin
(let _52_11894 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.Prims.pipe_left (fun ( _52_11893  :  (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> Some (_52_11893)) _52_11894))
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
(let _52_11898 = (match (b) with
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
in (let _52_11897 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _52_11896 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _52_11895 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _52_11898 _52_11897 _52_11896 _52_11895)))))
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
(let _52_11899 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_52_11899)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _52_11900 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_52_11900)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _52_11901 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_52_11901)::[])
end
| _ -> begin
(failwith ("Unexpected type-variable binding"))
end)
in (let mk_lam = (fun ( wp  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _52_11916 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _52_11915 = (let _52_11914 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _52_11913 = (let _52_11912 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _52_11911 = (let _52_11910 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _52_11909 = (let _52_11908 = (let _52_11904 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _52_11904))
in (let _52_11907 = (let _52_11906 = (let _52_11905 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _52_11905))
in (_52_11906)::[])
in (_52_11908)::_52_11907))
in (_52_11910)::_52_11909))
in (_52_11912)::_52_11911))
in (_52_11914)::_52_11913))
in (_52_11916)::_52_11915))
in (let wlp_args = (let _52_11924 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _52_11923 = (let _52_11922 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _52_11921 = (let _52_11920 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _52_11919 = (let _52_11918 = (let _52_11917 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _52_11917))
in (_52_11918)::[])
in (_52_11920)::_52_11919))
in (_52_11922)::_52_11921))
in (_52_11924)::_52_11923))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _52_11925 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _52_11925; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( mk_wp  :  Microsoft_FStar_Absyn_Syntax.typ ) ( mk_wlp  :  Microsoft_FStar_Absyn_Syntax.typ ) ( f  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _35_1193 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_35_1193) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _52_11940 = (let _52_11939 = (let _52_11938 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _52_11937 = (let _52_11936 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_52_11936)::[])
in (_52_11938)::_52_11937))
in (mk_wp, _52_11939))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_11940 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _52_11945 = (let _52_11944 = (let _52_11943 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _52_11942 = (let _52_11941 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_52_11941)::[])
in (_52_11943)::_52_11942))
in (mk_wlp, _52_11944))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_11945 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md_pure Microsoft_FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.Microsoft_FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( b  :  bool ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let refresh = (fun ( _35_1202  :  unit ) -> (match (()) with
| () -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
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
(let _52_11957 = (let _52_11956 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _52_11956))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _52_11957))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1212 = (match ((let _52_11959 = (Support.Prims.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name))
in (let _52_11958 = (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)
in (_52_11959 && _52_11958)))) with
| true -> begin
(let _52_11962 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _52_11961 = (let _52_11960 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _52_11960))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _52_11962 _52_11961)))
end
| false -> begin
()
end)
in (let _35_1217 = (destruct_comp c')
in (match (_35_1217) with
| (t, wp, wlp) -> begin
(let wp = (let _52_11965 = (let _52_11964 = (let _52_11963 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _52_11963))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_52_11964))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _52_11965))
in (let wlp = (let _52_11968 = (let _52_11967 = (let _52_11966 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _52_11966))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_52_11967))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _52_11968))
in (let _52_11973 = (let _35_1220 = c'
in (let _52_11972 = (let _52_11971 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _52_11970 = (let _52_11969 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_11969)::[])
in (_52_11971)::_52_11970))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _35_1220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _35_1220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _52_11972; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _52_11973))))
end)))))
end)
end))
end))
in (let _35_1222 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1222.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1222.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _35_1222.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = refresh})))

let label = (fun ( reason  :  string ) ( r  :  Support.Microsoft.FStar.Range.range ) ( f  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( reason  :  (unit  ->  string) option ) ( r  :  Support.Microsoft.FStar.Range.range ) ( f  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(match ((let _52_11997 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_11997))) with
| true -> begin
f
end
| false -> begin
(let _52_11998 = (reason ())
in (label _52_11998 r f))
end)
end))

let label_guard = (fun ( reason  :  string ) ( r  :  Support.Microsoft.FStar.Range.range ) ( g  :  Microsoft_FStar_Tc_Rel.guard_formula ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _52_12005 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_52_12005))
end))

let weaken_guard = (fun ( g1  :  Microsoft_FStar_Tc_Rel.guard_formula ) ( g2  :  Microsoft_FStar_Tc_Rel.guard_formula ) -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _ -> begin
g2
end))

let weaken_precondition = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( f  :  Microsoft_FStar_Tc_Rel.guard_formula ) -> (let weaken = (fun ( _35_1254  :  unit ) -> (match (()) with
| () -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
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
in (let wp = (let _52_12024 = (let _52_12023 = (let _52_12022 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12021 = (let _52_12020 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _52_12019 = (let _52_12018 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12018)::[])
in (_52_12020)::_52_12019))
in (_52_12022)::_52_12021))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _52_12023))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12024 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _52_12031 = (let _52_12030 = (let _52_12029 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12028 = (let _52_12027 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _52_12026 = (let _52_12025 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_12025)::[])
in (_52_12027)::_52_12026))
in (_52_12029)::_52_12028))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _52_12030))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12031 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end)))
end)
end))
end))
in (let _35_1267 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1267.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1267.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _35_1267.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun ( reason  :  (unit  ->  string) option ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( g0  :  Microsoft_FStar_Tc_Rel.guard_t ) -> (match ((Microsoft_FStar_Tc_Rel.is_trivial g0)) with
| true -> begin
(lc, g0)
end
| false -> begin
(let flags = (Support.Prims.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _35_6  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_35_6) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _ -> begin
[]
end))))
in (let strengthen = (fun ( _35_1281  :  unit ) -> (match (()) with
| () -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (let g0 = (Microsoft_FStar_Tc_Rel.simplify_guard env g0)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g0)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let c = (match ((let _52_12058 = (let _52_12055 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp c)
in (let _52_12054 = (let _52_12053 = (is_function (Microsoft_FStar_Absyn_Util.comp_result c))
in (not (_52_12053)))
in (_52_12055 && _52_12054)))
in (let _52_12057 = (let _52_12056 = (Microsoft_FStar_Absyn_Util.is_partial_return c)
in (not (_52_12056)))
in (_52_12058 && _52_12057)))) with
| true -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar (Microsoft_FStar_Absyn_Util.comp_result c))
in (let xret = (let _52_12059 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _52_12059))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _52_12062 = (lcomp_of_comp c)
in (let _52_12061 = (let _52_12060 = (lcomp_of_comp xret)
in (Some (xbinding), _52_12060))
in (bind env (Some (e)) _52_12062 _52_12061)))
in (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())))))
end
| false -> begin
c
end)
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _35_1296 = (destruct_comp c)
in (match (_35_1296) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _52_12071 = (let _52_12070 = (let _52_12069 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12068 = (let _52_12067 = (let _52_12064 = (let _52_12063 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _52_12063 f))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_12064))
in (let _52_12066 = (let _52_12065 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12065)::[])
in (_52_12067)::_52_12066))
in (_52_12069)::_52_12068))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _52_12070))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12071 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _52_12078 = (let _52_12077 = (let _52_12076 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12075 = (let _52_12074 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _52_12073 = (let _52_12072 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_12072)::[])
in (_52_12074)::_52_12073))
in (_52_12076)::_52_12075))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _52_12077))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12078 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _52_12084 = (let _35_1301 = lc
in (let _52_12083 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _52_12082 = (match ((let _52_12081 = (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc)
in (let _52_12080 = (let _52_12079 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_12079))
in (_52_12081 && _52_12080)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _52_12083; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1301.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _52_12082; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_52_12084, (let _35_1303 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _35_1303.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _35_1303.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( comp  :  Microsoft_FStar_Absyn_Syntax.comp ) ( res_t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _35_1313 = (let _52_12092 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _52_12091 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_52_12092, _52_12091)))
in (match (_35_1313) with
| (xexp, yexp) -> begin
(let yret = (let _52_12097 = (let _52_12096 = (let _52_12095 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12094 = (let _52_12093 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_52_12093)::[])
in (_52_12095)::_52_12094))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _52_12096))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12097 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _52_12105 = (let _52_12104 = (let _52_12103 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12102 = (let _52_12101 = (let _52_12098 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_12098))
in (let _52_12100 = (let _52_12099 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_52_12099)::[])
in (_52_12101)::_52_12100))
in (_52_12103)::_52_12102))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _52_12104))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12105 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _52_12116 = (let _52_12115 = (let _52_12114 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12113 = (let _52_12112 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12111 = (let _52_12110 = (let _52_12109 = (let _52_12108 = (let _52_12107 = (let _52_12106 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_52_12106)::[])
in (_52_12107, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_12108 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_12109))
in (_52_12110)::[])
in (_52_12112)::_52_12111))
in (_52_12114)::_52_12113))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _52_12115))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12116 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _52_12119 = (lcomp_of_comp comp)
in (let _52_12118 = (let _52_12117 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _52_12117))
in (bind env None _52_12119 _52_12118)))
in (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ()))))))
end))))))

let ite = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( guard  :  Microsoft_FStar_Absyn_Syntax.formula ) ( lcomp_then  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( lcomp_else  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let comp = (fun ( _35_1324  :  unit ) -> (match (()) with
| () -> begin
(let _35_1340 = (let _52_12131 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lcomp_then ())
in (let _52_12130 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lcomp_else ())
in (lift_and_destruct env _52_12131 _52_12130)))
in (match (_35_1340) with
| ((md, _, _), (res_t, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md  :  Microsoft_FStar_Absyn_Syntax.eff_decl ) ( res_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( g  :  Microsoft_FStar_Absyn_Syntax.typ ) ( wp_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( wp_e  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_12151 = (let _52_12149 = (let _52_12148 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12147 = (let _52_12146 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _52_12145 = (let _52_12144 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _52_12143 = (let _52_12142 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_52_12142)::[])
in (_52_12144)::_52_12143))
in (_52_12146)::_52_12145))
in (_52_12148)::_52_12147))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _52_12149))
in (let _52_12150 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12151 None _52_12150))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match ((let _52_12152 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (_52_12152 > 0))) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _52_12159 = (let _52_12158 = (let _52_12157 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12156 = (let _52_12155 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _52_12154 = (let _52_12153 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12153)::[])
in (_52_12155)::_52_12154))
in (_52_12157)::_52_12156))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _52_12158))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12159 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _52_12164 = (let _52_12163 = (let _52_12162 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12161 = (let _52_12160 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_12160)::[])
in (_52_12162)::_52_12161))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _52_12163))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12164 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _52_12165 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _52_12165; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( res_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( lcases  :  (Microsoft_FStar_Absyn_Syntax.formula * Microsoft_FStar_Absyn_Syntax.lcomp) list ) -> (let eff = (match (lcases) with
| [] -> begin
(failwith ("Empty cases!"))
end
| hd::tl -> begin
(Support.List.fold_left (fun ( eff  :  Microsoft_FStar_Absyn_Syntax.lident ) ( _35_1363  :  (Microsoft_FStar_Absyn_Syntax.formula * Microsoft_FStar_Absyn_Syntax.lcomp) ) -> (match (_35_1363) with
| (_, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun ( _35_1366  :  unit ) -> (match (()) with
| () -> begin
(let ifthenelse = (fun ( md  :  Microsoft_FStar_Absyn_Syntax.eff_decl ) ( res_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( g  :  Microsoft_FStar_Absyn_Syntax.typ ) ( wp_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( wp_e  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_12195 = (let _52_12193 = (let _52_12192 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12191 = (let _52_12190 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _52_12189 = (let _52_12188 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _52_12187 = (let _52_12186 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_52_12186)::[])
in (_52_12188)::_52_12187))
in (_52_12190)::_52_12189))
in (_52_12192)::_52_12191))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _52_12193))
in (let _52_12194 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12195 None _52_12194))))
in (let default_case = (let post_k = (let _52_12198 = (let _52_12197 = (let _52_12196 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_52_12196)::[])
in (_52_12197, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_12198 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _52_12201 = (let _52_12200 = (let _52_12199 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_52_12199)::[])
in (_52_12200, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_12201 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _52_12202 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _52_12202 post_k))
in (let wp = (let _52_12209 = (let _52_12208 = (let _52_12203 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_52_12203)::[])
in (let _52_12207 = (let _52_12206 = (let _52_12204 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _52_12204))
in (let _52_12205 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_left _52_12206 _52_12205)))
in (_52_12208, _52_12207)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_12209 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _52_12213 = (let _52_12212 = (let _52_12210 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_52_12210)::[])
in (let _52_12211 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_52_12212, _52_12211)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_12213 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _35_1382  :  (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.lcomp) ) ( celse  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (match (_35_1382) with
| (g, cthen) -> begin
(let _35_1400 = (let _52_12216 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp cthen ())
in (lift_and_destruct env _52_12216 celse))
in (match (_35_1400) with
| ((md, _, _), (_, wp_then, wlp_then), (_, wp_else, wlp_else)) -> begin
(let _52_12218 = (ifthenelse md res_t g wp_then wp_else)
in (let _52_12217 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _52_12218 _52_12217 [])))
end))
end)) lcases default_case)
in (match ((let _52_12219 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (_52_12219 > 0))) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| false -> begin
(let comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env comp.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _35_1408 = (destruct_comp comp)
in (match (_35_1408) with
| (_, wp, wlp) -> begin
(let wp = (let _52_12226 = (let _52_12225 = (let _52_12224 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12223 = (let _52_12222 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _52_12221 = (let _52_12220 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12220)::[])
in (_52_12222)::_52_12221))
in (_52_12224)::_52_12223))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _52_12225))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12226 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _52_12231 = (let _52_12230 = (let _52_12229 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12228 = (let _52_12227 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_12227)::[])
in (_52_12229)::_52_12228))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _52_12230))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12231 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = eff; Microsoft_FStar_Absyn_Syntax.res_typ = res_t; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( bindings  :  Microsoft_FStar_Tc_Env.binding list ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let close = (fun ( _35_1415  :  unit ) -> (match (()) with
| () -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let close_wp = (fun ( md  :  Microsoft_FStar_Absyn_Syntax.eff_decl ) ( res_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( bindings  :  Microsoft_FStar_Tc_Env.binding list ) ( wp0  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (Support.List.fold_right (fun ( b  :  Microsoft_FStar_Tc_Env.binding ) ( wp  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let bs = (let _52_12250 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_52_12250)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12257 = (let _52_12256 = (let _52_12255 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12254 = (let _52_12253 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _52_12252 = (let _52_12251 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12251)::[])
in (_52_12253)::_52_12252))
in (_52_12255)::_52_12254))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _52_12256))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12257 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _52_12258 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_52_12258)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12263 = (let _52_12262 = (let _52_12261 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _52_12260 = (let _52_12259 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12259)::[])
in (_52_12261)::_52_12260))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _52_12262))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12263 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
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

let maybe_assume_result_eq_pure_term = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let refine = (fun ( _35_1456  :  unit ) -> (match (()) with
| () -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (match ((let _52_12272 = (is_pure_or_ghost_effect env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (not (_52_12272)))) with
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
in (let ret = (let _52_12273 = (return_value env t xexp)
in (Support.Prims.pipe_left lcomp_of_comp _52_12273))
in (let eq_ret = (let _52_12275 = (let _52_12274 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_52_12274))
in (weaken_precondition env ret _52_12275))
in (let _52_12278 = (let _52_12277 = (let _52_12276 = (lcomp_of_comp c)
in (bind env None _52_12276 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp _52_12277 ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _52_12278 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
end)
end))
end))
in (let flags = (match ((let _52_12284 = (let _52_12281 = (let _52_12279 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (not (_52_12279)))
in (let _52_12280 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)
in (_52_12281 && _52_12280)))
in (let _52_12283 = (let _52_12282 = (Microsoft_FStar_Absyn_Util.is_lcomp_partial_return lc)
in (not (_52_12282)))
in (_52_12284 && _52_12283)))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.Microsoft_FStar_Absyn_Syntax.cflags
end
| false -> begin
lc.Microsoft_FStar_Absyn_Syntax.cflags
end)
in (let _35_1466 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _35_1466.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _35_1466.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( c  :  Microsoft_FStar_Absyn_Syntax.comp ) ( c'  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (match ((Microsoft_FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _52_12296 = (let _52_12295 = (let _52_12294 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _52_12293 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_12294, _52_12293)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12295))
in (raise (_52_12296)))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_instantiate_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match ((not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs)))) with
| true -> begin
(t, k, [])
end
| false -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let rec aux = (fun ( subst  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list ) ( _35_7  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_35_7) with
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
in (let _52_12307 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_12307, k, implicits))))
end)))
end
| _ -> begin
(t, k, [])
end)
end)))

let maybe_instantiate = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match ((not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs)))) with
| true -> begin
(e, t, [])
end
| false -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let rec aux = (fun ( subst  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list ) ( _35_8  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_35_8) with
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
(let mk_exp_app = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( args  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ option ) -> (match (args) with
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
in (let _52_12324 = (mk_exp_app e args (Some (t)))
in (_52_12324, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _ -> begin
(let t = (let _52_12325 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _52_12325 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_12326 = (mk_exp_app e args (Some (t)))
in (_52_12326, t, implicits)))
end))
end)))
end
| _ -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _52_12335 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_52_12335, false))
end
| false -> begin
(let _52_12336 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_52_12336, true))
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
in (let strengthen = (fun ( _35_1619  :  unit ) -> (match (()) with
| () -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (let _35_1621 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_12340 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _52_12339 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _52_12340 _52_12339)))
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
in (let wp = (let _52_12345 = (let _52_12344 = (let _52_12343 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _52_12342 = (let _52_12341 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_52_12341)::[])
in (_52_12343)::_52_12342))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _52_12344))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12345 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _52_12346 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.Prims.pipe_left lcomp_of_comp _52_12346))
in (let guard = (match (apply_guard) with
| true -> begin
(let _52_12349 = (let _52_12348 = (let _52_12347 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_52_12347)::[])
in (f, _52_12348))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12349 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _35_1636 = (let _52_12357 = (Support.Prims.pipe_left (fun ( _52_12354  :  (unit  ->  string) ) -> Some (_52_12354)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _52_12356 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12355 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _52_12357 _52_12356 e cret _52_12355))))
in (match (_35_1636) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _52_12359 = (let _52_12358 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.Prims.pipe_left lcomp_of_comp _52_12358))
in (bind env (Some (e)) _52_12359 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp c ())
in (let _35_1639 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_12360 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _52_12360))
end
| false -> begin
()
end)
in c)))
end)))))))))
end)))))
end))
in (let flags = (Support.Prims.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _35_9  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_35_9) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _ -> begin
[]
end))))
in (let lc = (let _35_1647 = lc
in (let _52_12362 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _52_12362; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((let _52_12371 = (let _52_12370 = (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (let _52_12369 = (let _52_12368 = (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _52_12367 = (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (_52_12368 + _52_12367)))
in (_52_12370 + _52_12369)))
in (_52_12371 > 0))) with
| true -> begin
(let ue = (let _52_12372 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _52_12372))
in (let ut = (let _52_12373 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _52_12373))
in (let uk = (let _52_12374 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _52_12374))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _35_1659 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _35_1661 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _35_1663 = (let _52_12376 = (let _52_12375 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _52_12375))
in (Microsoft_FStar_Tc_Errors.report r _52_12376))
in (let _35_1665 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify  :  bool ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( ecs  :  (Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.comp) list ) -> (match ((let _52_12384 = (Support.Microsoft.FStar.Util.for_all (fun ( _35_1673  :  (Microsoft_FStar_Absyn_Syntax.exp * (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_35_1673) with
| (_, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_12384))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (let _35_1676 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _52_12387 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _52_12387))
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
(let _52_12388 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _52_12388))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs  :  (Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd) Support.Microsoft.FStar.Util.set ) -> (let _52_12391 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.Prims.pipe_right _52_12391 Support.Microsoft.FStar.Util.set_elements)))
in (let should_gen = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _)) -> begin
(match ((Support.Prims.pipe_right bs (Support.Microsoft.FStar.Util.for_some (fun ( _35_10  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_35_10) with
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
in (let uvars = (Support.Prims.pipe_right ecs (Support.List.map (fun ( _35_1705  :  (Microsoft_FStar_Absyn_Syntax.exp * (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_35_1705) with
| (e, c) -> begin
(let t = (Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.compress_typ)
in (match ((let _52_12396 = (should_gen t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_12396))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _35_1721 = (match ((let _52_12400 = (let _52_12397 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (_52_12397 && verify))
in (let _52_12399 = (let _52_12398 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_12398))
in (_52_12400 && _52_12399)))) with
| true -> begin
(let _35_1717 = (destruct_comp ct)
in (match (_35_1717) with
| (_, wp, _) -> begin
(let binder = (let _52_12401 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_52_12401)::[])
in (let post = (let _52_12405 = (let _52_12402 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _52_12402))
in (let _52_12404 = (let _52_12403 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_52_12403))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_12405 _52_12404 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _52_12412 = (let _52_12411 = (let _52_12410 = (let _52_12409 = (let _52_12408 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_52_12408)::[])
in (wp, _52_12409))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12410))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _52_12411))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _52_12412))
in (let _52_12413 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _52_12413)))))
end))
end
| false -> begin
()
end)
in (uvs, e, c)))))))
end))
end))))
in (let ecs = (Support.Prims.pipe_right uvars (Support.List.map (fun ( _35_1727  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) list * Microsoft_FStar_Absyn_Syntax.exp * (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_35_1727) with
| (uvs, e, c) -> begin
(let tvars = (Support.Prims.pipe_right uvs (Support.List.map (fun ( _35_1730  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_35_1730) with
| (u, k) -> begin
(let a = (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) | (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)
end
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
(failwith ("Unexpected instantiation of mutually recursive uvar"))
end
| _ -> begin
(let a = (let _52_12418 = (let _52_12417 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left (fun ( _52_12416  :  Support.Microsoft.FStar.Range.range ) -> Some (_52_12416)) _52_12417))
in (Microsoft_FStar_Absyn_Util.new_bvd _52_12418))
in (let t = (let _52_12419 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _52_12419 k))
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
in (let _52_12420 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _52_12420)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify  :  bool ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( lecs  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.comp) list ) -> (let _35_1801 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_12429 = (let _52_12428 = (Support.List.map (fun ( _35_1800  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.comp) ) -> (match (_35_1800) with
| (lb, _, _) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.Prims.pipe_right _52_12428 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _52_12429))
end
| false -> begin
()
end)
in (match ((let _52_12431 = (Support.Prims.pipe_right lecs (Support.List.map (fun ( _35_1807  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.comp) ) -> (match (_35_1807) with
| (_, e, c) -> begin
(e, c)
end))))
in (gen verify env _52_12431))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _35_1816  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.comp) ) ( _35_1819  :  ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax * (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match ((_35_1816, _35_1819)) with
| ((l, _, _), (e, c)) -> begin
(let _35_1820 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _52_12436 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12435 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _52_12434 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _52_12436 _52_12435 _52_12434))))
end
| false -> begin
()
end)
in (l, e, c))
end)) lecs ecs)
end)))

let unresolved = (fun ( u  :  'u35u35300 Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Uvar -> begin
true
end
| _ -> begin
false
end))

let check_top_level = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( g  :  Microsoft_FStar_Tc_Rel.guard_t ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (let discharge = (fun ( g  :  Microsoft_FStar_Tc_Rel.guard_t ) -> (let _35_1831 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _35_1849 = (match ((Support.Prims.pipe_right g.Microsoft_FStar_Tc_Rel.implicits (Support.List.tryFind (fun ( _35_11  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * Int64.t), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * Int64.t)) Support.Microsoft.FStar.Util.either ) -> (match (_35_11) with
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
(let _52_12448 = (discharge g)
in (let _52_12447 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (_52_12448, _52_12447)))
end
| false -> begin
(let c = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _52_12449 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.Prims.pipe_right _52_12449 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _35_1860 = (destruct_comp c)
in (match (_35_1860) with
| (t, wp, _) -> begin
(let vc = (let _52_12455 = (let _52_12453 = (let _52_12452 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _52_12451 = (let _52_12450 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12450)::[])
in (_52_12452)::_52_12451))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _52_12453))
in (let _52_12454 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12455 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _52_12454)))
in (let g = (let _52_12456 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _52_12456))
in (let _52_12458 = (discharge g)
in (let _52_12457 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_52_12458, _52_12457)))))
end))))))
end))))

let short_circuit_exp = (fun ( head  :  Microsoft_FStar_Absyn_Syntax.exp ) ( seen_args  :  Microsoft_FStar_Absyn_Syntax.args ) -> (let short_bin_op_e = (fun ( f  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax  ->  (Microsoft_FStar_Absyn_Syntax.formula * Microsoft_FStar_Absyn_Syntax.exp) ) -> (fun ( _35_12  :  Microsoft_FStar_Absyn_Syntax.args ) -> (match (_35_12) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _)::[] -> begin
(let _52_12477 = (f fst)
in (Support.Prims.pipe_right _52_12477 (fun ( _52_12476  :  (Microsoft_FStar_Absyn_Syntax.formula * Microsoft_FStar_Absyn_Syntax.exp) ) -> Some (_52_12476))))
end
| _ -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let table = (let op_and_e = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (let _52_12483 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_52_12483, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (let _52_12487 = (let _52_12486 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _52_12486))
in (_52_12487, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1890  :  (Microsoft_FStar_Absyn_Syntax.lident * (Microsoft_FStar_Absyn_Syntax.args  ->  (Microsoft_FStar_Absyn_Syntax.formula * Microsoft_FStar_Absyn_Syntax.exp) option)) ) -> (match (_35_1890) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _52_12505 = (mk seen_args)
in Some (_52_12505))
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

let short_circuit_typ = (fun ( head  :  (Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either ) ( seen_args  :  Microsoft_FStar_Absyn_Syntax.args ) -> (let short_bin_op_t = (fun ( f  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax  ->  Microsoft_FStar_Tc_Rel.guard_formula ) -> (fun ( _35_13  :  Microsoft_FStar_Absyn_Syntax.args ) -> (match (_35_13) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _)::[] -> begin
(f fst)
end
| _ -> begin
(failwith ("Unexpexted args to binary operator"))
end)))
in (let op_and_t = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_12526 = (unlabel t)
in (Support.Prims.pipe_right _52_12526 (fun ( _52_12525  :  Microsoft_FStar_Absyn_Syntax.formula ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_52_12525)))))
in (let op_or_t = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_12531 = (let _52_12529 = (unlabel t)
in (Support.Prims.pipe_right _52_12529 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.Prims.pipe_right _52_12531 (fun ( _52_12530  :  Microsoft_FStar_Absyn_Syntax.formula ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_52_12530)))))
in (let op_imp_t = (fun ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_12535 = (unlabel t)
in (Support.Prims.pipe_right _52_12535 (fun ( _52_12534  :  Microsoft_FStar_Absyn_Syntax.formula ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_52_12534)))))
in (let short_op_ite = (fun ( _35_14  :  Microsoft_FStar_Absyn_Syntax.args ) -> (match (_35_14) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _)::[] -> begin
(let _52_12539 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.Prims.pipe_right _52_12539 (fun ( _52_12538  :  Microsoft_FStar_Absyn_Syntax.formula ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_52_12538))))
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
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _35_1958  :  (Microsoft_FStar_Absyn_Syntax.lident * (Microsoft_FStar_Absyn_Syntax.args  ->  Microsoft_FStar_Tc_Rel.guard_formula)) ) -> (match (_35_1958) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _52_12566 = (mk seen_args)
in Some (_52_12566))
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

let pure_or_ghost_pre_and_post = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( comp  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (let mk_post_type = (fun ( res_t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( ens  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _52_12580 = (let _52_12579 = (let _52_12578 = (let _52_12577 = (let _52_12576 = (let _52_12575 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _52_12575))
in (_52_12576)::[])
in (ens, _52_12577))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12578 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _52_12579))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _52_12580 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
in (let norm = (fun ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Unlabel)::[]) env t))
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
(let _52_12586 = (let _52_12583 = (norm req)
in Some (_52_12583))
in (let _52_12585 = (let _52_12584 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.Prims.pipe_left norm _52_12584))
in (_52_12586, _52_12585)))
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
(let _35_2022 = (match ((let _52_12588 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _52_12587 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_52_12588, _52_12587)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _ -> begin
(failwith ("Impossible"))
end)
in (match (_35_2022) with
| (as_req, as_ens) -> begin
(let req = (let _52_12592 = (let _52_12591 = (let _52_12590 = (let _52_12589 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_52_12589)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_52_12590)
in (as_req, _52_12591))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12592 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _52_12596 = (let _52_12595 = (let _52_12594 = (let _52_12593 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_52_12593)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_52_12594)
in (as_ens, _52_12595))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12596 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _52_12600 = (let _52_12597 = (norm req)
in Some (_52_12597))
in (let _52_12599 = (let _52_12598 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _52_12598))
in (_52_12600, _52_12599)))))
end))
end
| _ -> begin
(failwith ("Impossible"))
end)
end))
end)
end)
end))))




