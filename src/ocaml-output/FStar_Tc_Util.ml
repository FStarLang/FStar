
open Prims
let try_solve = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

let report = (fun env errs -> (let _130_10 = (FStar_Tc_Env.get_range env)
in (let _130_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _130_10 _130_9))))

let discharge_guard = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun env g -> (discharge_guard env g))

let syn' = (fun env k -> (let _130_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _130_29 k)))

let is_xvar_free = (fun x t -> (let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) f.FStar_Absyn_Syntax.fxvs)))

let is_tvar_free = (fun a t -> (let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun) f.FStar_Absyn_Syntax.ftvs)))

let check_and_ascribe = (fun env e t1 t2 -> (let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _130_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _130_52 -> Some (_130_52)) _130_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _130_57 = (let _130_56 = (let _130_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _130_54 = (FStar_Tc_Env.get_range env)
in (_130_55, _130_54)))
in FStar_Absyn_Syntax.Error (_130_56))
in (Prims.raise _130_57))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _130_61 = (let _130_60 = (let _130_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _130_58 = (FStar_Tc_Env.get_range env)
in (_130_59, _130_58)))
in FStar_Absyn_Syntax.Error (_130_60))
in (Prims.raise _130_61))
end
| Some (g) -> begin
(let _53_51 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _130_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _130_62))
end else begin
()
end
in (let e = (FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(FStar_Absyn_Syntax.mk_Exp_bvar (FStar_Absyn_Util.bvd_to_bvar_s x.FStar_Absyn_Syntax.v t2) (Some (t2)) e.FStar_Absyn_Syntax.pos)
end
| _53_57 -> begin
(let _53_58 = e
in (let _130_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _53_58.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _130_63; FStar_Absyn_Syntax.pos = _53_58.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _53_58.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _53_58.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))

let env_binders = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

let as_uvar_e = (fun _53_1 -> (match (_53_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _53_73); FStar_Absyn_Syntax.tk = _53_70; FStar_Absyn_Syntax.pos = _53_68; FStar_Absyn_Syntax.fvs = _53_66; FStar_Absyn_Syntax.uvs = _53_64} -> begin
uv
end
| _53_78 -> begin
(FStar_All.failwith "Impossible")
end))

let as_uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _53_90); FStar_Absyn_Syntax.tk = _53_87; FStar_Absyn_Syntax.pos = _53_85; FStar_Absyn_Syntax.fvs = _53_83; FStar_Absyn_Syntax.uvs = _53_81} -> begin
uv
end
| _53_95 -> begin
(FStar_All.failwith "Impossible")
end))

let new_kvar = (fun env -> (let _130_73 = (let _130_72 = (FStar_Tc_Env.get_range env)
in (let _130_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _130_72 _130_71)))
in (FStar_All.pipe_right _130_73 Prims.fst)))

let new_tvar = (fun env k -> (let _130_80 = (let _130_79 = (FStar_Tc_Env.get_range env)
in (let _130_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _130_79 _130_78 k)))
in (FStar_All.pipe_right _130_80 Prims.fst)))

let new_evar = (fun env t -> (let _130_87 = (let _130_86 = (FStar_Tc_Env.get_range env)
in (let _130_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _130_86 _130_85 t)))
in (FStar_All.pipe_right _130_87 Prims.fst)))

let new_implicit_tvar = (fun env k -> (let _53_105 = (let _130_93 = (FStar_Tc_Env.get_range env)
in (let _130_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _130_93 _130_92 k)))
in (match (_53_105) with
| (t, u) -> begin
(let _130_95 = (let _130_94 = (as_uvar_t u)
in (_130_94, u.FStar_Absyn_Syntax.pos))
in (t, _130_95))
end)))

let new_implicit_evar = (fun env t -> (let _53_110 = (let _130_101 = (FStar_Tc_Env.get_range env)
in (let _130_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _130_101 _130_100 t)))
in (match (_53_110) with
| (e, u) -> begin
(let _130_103 = (let _130_102 = (as_uvar_e u)
in (_130_102, u.FStar_Absyn_Syntax.pos))
in (e, _130_103))
end)))

let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _130_106 = (let _130_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _130_105))
in (FStar_All.failwith _130_106))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_2 -> (match (_53_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _130_111 = (let _130_110 = (force_tk t)
in FStar_Util.Inl (_130_110))
in (_130_111, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _130_113 = (let _130_112 = (force_tk v)
in FStar_Util.Inr (_130_112))
in (_130_113, imp))
end)))))

let is_implicit = (fun _53_3 -> (match (_53_3) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _53_129 -> begin
false
end))

let destruct_arrow_kind = (fun env tt k args -> (let ktop = (let _130_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _130_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (FStar_Tc_Env.get_range env)
in (let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(let imp_follows = (match (args) with
| (_53_145, qual)::_53_143 -> begin
(is_implicit qual)
end
| _53_150 -> begin
false
end)
in (let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _130_136 = (let _130_134 = (let _130_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _130_133))
in (FStar_All.pipe_right _130_134 Prims.fst))
in (FStar_All.pipe_right _130_136 (fun x -> (FStar_Util.Inl (x), (FStar_Absyn_Syntax.as_implicit true)))))
end
| FStar_Util.Inr (x) -> begin
(let _130_140 = (let _130_138 = (let _130_137 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _130_137))
in (FStar_All.pipe_right _130_138 Prims.fst))
in (FStar_All.pipe_right _130_140 (fun x -> (FStar_Util.Inr (x), (FStar_Absyn_Syntax.as_implicit true)))))
end)
in (let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _130_141 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_130_141)::subst)
end
in (let _53_169 = (mk_implicits vars subst brest)
in (match (_53_169) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _130_142 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _130_142))
end
end
| _53_171 -> begin
(let _130_143 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _130_143))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(let _53_174 = (let _130_144 = (FStar_Tc_Env.binders env)
in (mk_implicits _130_144 [] bs))
in (match (_53_174) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_176, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_53_181) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _130_145 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _130_145 Prims.fst))
in (let bs = (let _130_146 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _130_146))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _53_188 = (let _130_147 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _130_147))
in ([], bs, kres)))))))
end
| _53_191 -> begin
(let _130_150 = (let _130_149 = (let _130_148 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_130_148, r))
in FStar_Absyn_Syntax.Error (_130_149))
in (Prims.raise _130_150))
end))
in (aux ktop)))))

let as_imp = (fun _53_4 -> (match (_53_4) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _53_196 -> begin
false
end))

let pat_as_exps = (fun allow_implicits env p -> (let pvar_eq = (fun x y -> (match ((x, y)) with
| (FStar_Tc_Env.Binding_var (x, _53_205), FStar_Tc_Env.Binding_var (y, _53_210)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _53_216), FStar_Tc_Env.Binding_typ (y, _53_221)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _53_226 -> begin
false
end))
in (let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _53_5 -> (match (_53_5) with
| FStar_Tc_Env.Binding_var (x, _53_232) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _53_237) -> begin
FStar_Util.Inl (x)
end
| _53_241 -> begin
(FStar_All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _53_248) -> begin
(let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (let _53_254 = (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p [] t)
in (match (_53_254) with
| (e, u) -> begin
(let p = (let _53_255 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _53_255.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _53_255.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _53_260) -> begin
(let k = (new_kvar env)
in (let _53_266 = (let _130_172 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _130_172 k))
in (match (_53_266) with
| (t, u) -> begin
(let p = (let _53_267 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _53_267.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _53_267.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inl (t), p))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in ([], [], [], env, FStar_Util.Inr (e), p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _130_174 = (let _130_173 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _130_173))
in FStar_Tc_Env.Binding_var (_130_174))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let b = (let _130_176 = (let _130_175 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _130_175))
in FStar_Tc_Env.Binding_var (_130_176))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _130_178 = (let _130_177 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _130_177))
in FStar_Tc_Env.Binding_typ (_130_178))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _130_180 = (let _130_179 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _130_179))
in FStar_Tc_Env.Binding_typ (_130_180))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _53_326 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_304 _53_307 -> (match ((_53_304, _53_307)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _53_314 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_53_314) with
| (b', a', w', env, te, pat) -> begin
(let arg = (match (te) with
| FStar_Util.Inl (t) -> begin
if imp then begin
(FStar_Absyn_Syntax.itarg t)
end else begin
(FStar_Absyn_Syntax.targ t)
end
end
| FStar_Util.Inr (e) -> begin
if imp then begin
(FStar_Absyn_Syntax.ivarg e)
end else begin
(FStar_Absyn_Syntax.varg e)
end
end)
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_53_326) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _130_188 = (let _130_187 = (let _130_186 = (let _130_185 = (let _130_184 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _130_183 = (FStar_All.pipe_right args FStar_List.rev)
in (_130_184, _130_183)))
in (FStar_Absyn_Syntax.mk_Exp_app' _130_185 None p.FStar_Absyn_Syntax.p))
in (_130_186, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_130_187))
in (FStar_Absyn_Syntax.mk_Exp_meta _130_188))
in (let _130_191 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _130_190 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _130_189 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_130_191, _130_190, _130_189, env, FStar_Util.Inr (e), (let _53_328 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _53_328.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _53_328.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_53_331) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let pats = (FStar_List.map (fun _53_343 -> (match (_53_343) with
| (p, imp) -> begin
(let _130_197 = (elaborate_pat env p)
in (_130_197, imp))
end)) pats)
in (let t = (FStar_Tc_Env.lookup_datacon env fv.FStar_Absyn_Syntax.v)
in (let pats = (match ((FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _53_349 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end)
end
| Some (f, _53_352) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _53_365::_53_363) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end
| (_53_371::_53_369, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(let a = (let _130_203 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _130_203 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), (as_imp imp))
end else begin
((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), (as_imp imp))
end)
end
| (FStar_Util.Inr (_53_382), Some (FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in ((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), true))
end
| _53_389 -> begin
(let _130_207 = (let _130_206 = (let _130_205 = (let _130_204 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _130_204))
in (_130_205, (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_130_206))
in (Prims.raise _130_207))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _130_208 = (aux formals' pats')
in ((p, (as_imp imp)))::_130_208)
end
| ((FStar_Util.Inl (_53_417), imp), FStar_Absyn_Syntax.Pat_dot_typ (_53_422)) when allow_implicits -> begin
(let _130_209 = (aux formals' pats')
in ((p, (as_imp imp)))::_130_209)
end
| ((FStar_Util.Inl (_53_426), imp), _53_431) -> begin
(let a = (let _130_210 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _130_210 FStar_Absyn_Syntax.kun))
in (let p1 = if allow_implicits then begin
(FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
end else begin
(FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
end
in (let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_53_436) -> begin
pats'
end
| _53_439 -> begin
pats
end)
in (let _130_211 = (aux formals' pats')
in ((p1, (as_imp imp)))::_130_211))))
end
| ((FStar_Util.Inr (_53_442), Some (FStar_Absyn_Syntax.Implicit)), _53_448) when p_imp -> begin
(let _130_212 = (aux formals' pats')
in ((p, true))::_130_212)
end
| ((FStar_Util.Inr (_53_451), Some (FStar_Absyn_Syntax.Implicit)), _53_457) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let p = (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
in (let _130_213 = (aux formals' pats)
in ((p, true))::_130_213)))
end
| ((FStar_Util.Inr (_53_462), imp), _53_467) -> begin
(let _130_214 = (aux formals' pats')
in ((p, (as_imp imp)))::_130_214)
end)
end))
in (aux f pats))
end)
in (let _53_470 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _53_470.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _53_470.FStar_Absyn_Syntax.p}))))
end
| _53_473 -> begin
p
end))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _53_485 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_53_485) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _53_488)) -> begin
(let _130_223 = (let _130_222 = (let _130_221 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_130_221, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_130_222))
in (Prims.raise _130_223))
end
| Some (FStar_Tc_Env.Binding_typ (x, _53_494)) -> begin
(let _130_226 = (let _130_225 = (let _130_224 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_130_224, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_130_225))
in (Prims.raise _130_226))
end
| _53_499 -> begin
(b, a, w, arg, p)
end)
end))))
in (let as_arg = (fun _53_6 -> (match (_53_6) with
| FStar_Util.Inl (t) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Util.Inr (e) -> begin
(FStar_Absyn_Syntax.varg e)
end))
in (let top_level_pat_as_args = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _53_521 = (one_pat false env q)
in (match (_53_521) with
| (b, a, _53_518, te, q) -> begin
(let _53_536 = (FStar_List.fold_right (fun p _53_526 -> (match (_53_526) with
| (w, args, pats) -> begin
(let _53_532 = (one_pat false env p)
in (match (_53_532) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _130_240 = (let _130_239 = (let _130_238 = (let _130_236 = (vars_of_bindings a)
in (let _130_235 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _130_236 _130_235)))
in (let _130_237 = (FStar_Tc_Env.get_range env)
in (_130_238, _130_237)))
in FStar_Absyn_Syntax.Error (_130_239))
in (Prims.raise _130_240))
end else begin
(let _130_242 = (let _130_241 = (as_arg arg)
in (_130_241)::args)
in ((FStar_List.append w' w), _130_242, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_53_536) with
| (w, args, pats) -> begin
(let _130_244 = (let _130_243 = (as_arg te)
in (_130_243)::args)
in ((FStar_List.append b w), _130_244, (let _53_537 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _53_537.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _53_537.FStar_Absyn_Syntax.p})))
end))
end))
end
| _53_540 -> begin
(let _53_548 = (one_pat true env p)
in (match (_53_548) with
| (b, _53_543, _53_545, arg, p) -> begin
(let _130_246 = (let _130_245 = (as_arg arg)
in (_130_245)::[])
in (b, _130_246, p))
end))
end))
in (let _53_552 = (top_level_pat_as_args env p)
in (match (_53_552) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map (fun _53_7 -> (match (_53_7) with
| (FStar_Util.Inl (_53_555), _53_558) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _53_563) -> begin
e
end))))
in (b, exps, p))
end))))))))))

let decorate_pattern = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (let _130_265 = (FStar_All.pipe_left (fun _130_264 -> Some (_130_264)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _130_265 p.FStar_Absyn_Syntax.p)))
in (let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_53_579), FStar_Absyn_Syntax.Exp_constant (_53_582)) -> begin
(let _130_266 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _130_266))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _53_590 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _130_269 = (let _130_268 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _130_267 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _130_268 _130_267)))
in (FStar_All.failwith _130_269))
end else begin
()
end
in (let _53_592 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _130_271 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _130_270 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _130_271 _130_270)))
end else begin
()
end
in (let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (let x = (let _53_595 = x
in {FStar_Absyn_Syntax.v = _53_595.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _53_595.FStar_Absyn_Syntax.p})
in (let _130_272 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _130_272))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _53_603 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _130_275 = (let _130_274 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _130_273 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _130_274 _130_273)))
in (FStar_All.failwith _130_275))
end else begin
()
end
in (let x = (let _53_605 = x
in (let _130_276 = (force_tk e)
in {FStar_Absyn_Syntax.v = _53_605.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _130_276; FStar_Absyn_Syntax.p = _53_605.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _53_610), _53_614) -> begin
(let x = (let _53_616 = x
in (let _130_277 = (force_tk e)
in {FStar_Absyn_Syntax.v = _53_616.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _130_277; FStar_Absyn_Syntax.p = _53_616.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _53_626)) -> begin
(let _53_630 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _130_278 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _130_278))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _53_647); FStar_Absyn_Syntax.tk = _53_644; FStar_Absyn_Syntax.pos = _53_642; FStar_Absyn_Syntax.fvs = _53_640; FStar_Absyn_Syntax.uvs = _53_638}, args)) -> begin
(let _53_655 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _130_279 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _130_279))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _130_286 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _130_286))
end
| (arg::args, (argpat, _53_671)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)), FStar_Absyn_Syntax.Pat_dot_typ (_53_681)) -> begin
(let x = (let _130_287 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _130_287))
in (let q = (let _130_289 = (FStar_All.pipe_left (fun _130_288 -> Some (_130_288)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _130_289 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit)), FStar_Absyn_Syntax.Pat_dot_term (_53_692)) -> begin
(let x = (let _130_290 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _130_290))
in (let q = (let _130_292 = (FStar_All.pipe_left (fun _130_291 -> Some (_130_291)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _130_292 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _53_702) -> begin
(let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _53_710) -> begin
(let pat = (let _130_293 = (aux argpat e)
in (_130_293, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _53_714 -> begin
(let _130_296 = (let _130_295 = (FStar_Absyn_Print.pat_to_string p)
in (let _130_294 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _130_295 _130_294)))
in (FStar_All.failwith _130_296))
end))
in (match_args [] args argpats))))
end
| _53_716 -> begin
(let _130_301 = (let _130_300 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _130_299 = (FStar_Absyn_Print.pat_to_string qq)
in (let _130_298 = (let _130_297 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _130_297 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _130_300 _130_299 _130_298))))
in (FStar_All.failwith _130_301))
end))))
and aux_t = (fun p t0 -> (let pkg = (fun q k -> (let _130_309 = (FStar_All.pipe_left (fun _130_308 -> Some (_130_308)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _130_309 p.FStar_Absyn_Syntax.p)))
in (let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _53_728 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _130_312 = (let _130_311 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _130_310 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _130_311 _130_310)))
in (FStar_All.failwith _130_312))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _53_735 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _130_315 = (let _130_314 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _130_313 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _130_314 _130_313)))
in (FStar_All.failwith _130_315))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _53_739), _53_743) -> begin
(let k0 = (force_tk t0)
in (let a = (let _53_746 = a
in {FStar_Absyn_Syntax.v = _53_746.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _53_746.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _53_750 -> begin
(let _130_319 = (let _130_318 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _130_317 = (FStar_Absyn_Print.pat_to_string p)
in (let _130_316 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _130_318 _130_317 _130_316))))
in (FStar_All.failwith _130_319))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _53_754) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (let _130_321 = (FStar_All.pipe_left (fun _130_320 -> Some (_130_320)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _130_321 p.FStar_Absyn_Syntax.p)))
end
| (_53_758, e::[]) -> begin
(aux p e)
end
| _53_763 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp = (fun pat -> (let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _53_770 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun _53_777 -> (match (_53_777) with
| (p, i) -> begin
(let _53_780 = (decorated_pattern_as_either p)
in (match (_53_780) with
| (vars, te) -> begin
(vars, (te, (FStar_Absyn_Syntax.as_implicit i)))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_782) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _130_342 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _130_342))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _130_345 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _130_345))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _53_796 = (let _130_346 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _130_346 FStar_List.unzip))
in (match (_53_796) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _130_352 = (let _130_351 = (let _130_350 = (let _130_349 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_130_349, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _130_350))
in (FStar_All.pipe_right _130_351 pkg))
in (vars, _130_352)))
end))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(FStar_All.failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (a)) | (FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _130_354 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _130_354))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _53_820 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _53_833 = (decorated_pattern_as_typ p)
in (match (_53_833) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _53_835 -> begin
(let _53_838 = (decorated_pattern_as_exp p)
in (match (_53_838) with
| (vars, e) -> begin
(vars, FStar_Util.Inr (e))
end))
end))

let mk_basic_dtuple_type = (fun env n -> (let r = (FStar_Tc_Env.get_range env)
in (let l = (FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (FStar_Absyn_Util.ftv l k)
in (let vars = (FStar_Tc_Env.binders env)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _53_854; FStar_Absyn_Syntax.pos = _53_852; FStar_Absyn_Syntax.fvs = _53_850; FStar_Absyn_Syntax.uvs = _53_848}) -> begin
(let _53_884 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_861 _53_865 -> (match ((_53_861, _53_865)) with
| ((out, subst), (b, _53_864)) -> begin
(match (b) with
| FStar_Util.Inr (_53_867) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _130_362 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _130_362 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _130_365 = (let _130_364 = (let _130_363 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _130_363 Prims.fst))
in (bs, _130_364))
in (FStar_Absyn_Syntax.mk_Typ_lam _130_365 (Some (k)) r))
end
| _53_878 -> begin
(FStar_All.failwith "Impossible")
end)
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (((FStar_Absyn_Syntax.targ arg))::out, subst))))
end)
end)) ([], [])))
in (match (_53_884) with
| (args, _53_883) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _53_886 -> begin
(FStar_All.failwith "Impossible")
end)))))))

let extract_lb_annotation = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _130_376 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _130_376 Prims.fst))
in ((let _53_897 = a
in {FStar_Absyn_Syntax.v = _53_897.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_897.FStar_Absyn_Syntax.p}), false))
end
| _53_900 -> begin
(a, true)
end))
in (let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _130_381 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _130_381 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _53_909) -> begin
(x, false)
end
| _53_912 -> begin
(FStar_All.failwith "impos")
end))
end
| _53_914 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _53_918) -> begin
(x, true)
end
| _53_921 -> begin
(FStar_All.failwith "impos")
end)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_927)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_934) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _53_963 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_944 b -> (match (_53_944) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _53_950 = (mk_t_binder scope a)
in (match (_53_950) with
| (tb, c) -> begin
(let b = (FStar_Util.Inl (tb), (Prims.snd b))
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _53_958 = (mk_v_binder scope x)
in (match (_53_958) with
| (vb, c) -> begin
(let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_53_963) with
| (scope, bs, check) -> begin
(let _53_967 = (aux scope body)
in (match (_53_967) with
| (body, res, check_res) -> begin
(let c = (FStar_Absyn_Util.ml_comp res r)
in (let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (let _53_970 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _130_389 = (FStar_Range.string_of_range r)
in (let _130_388 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _130_389 _130_388)))
end else begin
()
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _53_974 -> begin
(let _130_391 = (let _130_390 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _130_390 Prims.fst))
in (e, _130_391, false))
end))
in (let _130_392 = (FStar_Tc_Env.t_binders env)
in (aux _130_392 e))))))
end
| _53_976 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun c -> (let _53_993 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _53_986)::(FStar_Util.Inl (wlp), _53_981)::[] -> begin
(wp, wlp)
end
| _53_990 -> begin
(let _130_397 = (let _130_396 = (let _130_395 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _130_395 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _130_396))
in (FStar_All.failwith _130_397))
end)
in (match (_53_993) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun c m lift -> (let _53_1001 = (destruct_comp c)
in (match (_53_1001) with
| (_53_998, wp, wlp) -> begin
(let _130_419 = (let _130_418 = (let _130_414 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _130_414))
in (let _130_417 = (let _130_416 = (let _130_415 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _130_415))
in (_130_416)::[])
in (_130_418)::_130_417))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _130_419; FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_53_1009, c) -> begin
(let l = (FStar_Absyn_Util.comp_to_comp_typ c).FStar_Absyn_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (let res = (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(let _53_1023 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

let join_effects = (fun env l1 l2 -> (let _53_1034 = (let _130_433 = (norm_eff_name env l1)
in (let _130_432 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _130_433 _130_432)))
in (match (_53_1034) with
| (m, _53_1031, _53_1033) -> begin
m
end)))

let join_lcomp = (fun env c1 c2 -> if ((FStar_Ident.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Ident.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)

let lift_and_destruct = (fun env c1 c2 -> (let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _53_1046 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_53_1046) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_Tc_Env.get_effect_decl env m)
in (let _53_1052 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_53_1052) with
| (a, kwp) -> begin
(let _130_447 = (destruct_comp m1)
in (let _130_446 = (destruct_comp m2)
in ((md, a, kwp), _130_447, _130_446)))
end)))))
end)))))

let is_pure_effect = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun md result wp wlp flags -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = ((FStar_Absyn_Syntax.targ wp))::((FStar_Absyn_Syntax.targ wlp))::[]; FStar_Absyn_Syntax.flags = flags}))

let lcomp_of_comp = (fun c0 -> (let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _53_1066 -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun subst lc -> (let _53_1069 = lc
in (let _130_475 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _53_1069.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _130_475; FStar_Absyn_Syntax.cflags = _53_1069.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _53_1071 -> (match (()) with
| () -> begin
(let _130_474 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _130_474))
end))})))

let is_function = (fun t -> (match ((let _130_478 = (FStar_Absyn_Util.compress_typ t)
in _130_478.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_53_1074) -> begin
true
end
| _53_1077 -> begin
false
end))

let return_value = (fun env t v -> (let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _53_1086 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_53_1086) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _130_485 = (FStar_Absyn_Syntax.mk_Typ_app (m.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.varg v))::[]) (Some (k)) v.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _130_485))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _53_1091 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _130_488 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _130_487 = (FStar_Absyn_Print.exp_to_string v)
in (let _130_486 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _130_488 _130_487 _130_486))))
end else begin
()
end
in c)))

let bind = (fun env e1opt lc1 _53_1098 -> (match (_53_1098) with
| (b, lc2) -> begin
(let _53_1109 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _53_1102)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _53_1107 -> begin
"??"
end)
in (let _130_498 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _130_497 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _130_498 bstr _130_497))))
end else begin
()
end
in (let bind_it = (fun _53_1112 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun _53_1116 -> (match (()) with
| () -> begin
(let aux = (fun _53_1118 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_53_1121)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_53_1125)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _53_1129 -> begin
None
end)
end else begin
if ((FStar_Absyn_Util.is_ml_comp c1) && (FStar_Absyn_Util.is_ml_comp c2)) then begin
Some (c2)
end else begin
None
end
end
end))
in (match ((e1opt, b)) with
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _53_1134))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _130_506 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _130_505 -> Some (_130_505)) _130_506))
end else begin
(aux ())
end
end
| _53_1140 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _53_1158 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _130_510 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _53_1146)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _53_1152)) -> begin
(FStar_Absyn_Print.sli l)
end
| _53_1157 -> begin
"Something else"
end)
in (let _130_509 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _130_508 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _130_507 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _130_510 _130_509 _130_508 _130_507)))))
end else begin
()
end
in c)
end
| None -> begin
(let _53_1173 = (lift_and_destruct env c1 c2)
in (match (_53_1173) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
((FStar_Absyn_Syntax.null_v_binder t1))::[]
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1)))::[]
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
((FStar_Absyn_Syntax.null_v_binder t1))::[]
end
| _53_1186 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (let wp_args = (let _130_521 = (let _130_520 = (let _130_519 = (let _130_518 = (let _130_517 = (let _130_513 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _130_513))
in (let _130_516 = (let _130_515 = (let _130_514 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _130_514))
in (_130_515)::[])
in (_130_517)::_130_516))
in ((FStar_Absyn_Syntax.targ wlp1))::_130_518)
in ((FStar_Absyn_Syntax.targ wp1))::_130_519)
in ((FStar_Absyn_Syntax.targ t2))::_130_520)
in ((FStar_Absyn_Syntax.targ t1))::_130_521)
in (let wlp_args = (let _130_526 = (let _130_525 = (let _130_524 = (let _130_523 = (let _130_522 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _130_522))
in (_130_523)::[])
in ((FStar_Absyn_Syntax.targ wlp1))::_130_524)
in ((FStar_Absyn_Syntax.targ t2))::_130_525)
in ((FStar_Absyn_Syntax.targ t1))::_130_526)
in (let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wp, wp_args) None t2.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _130_527 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _130_527; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let _53_1204 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_53_1204) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (mk_wp, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (mk_wlp, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.FStar_Absyn_Syntax.pos)
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun env b lc -> (let refresh = (fun _53_1213 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_53_1216) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _53_1220 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _130_549 = (let _130_548 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _130_548))
in (FStar_Util.print1 "Refreshing label at %s\n" _130_549))
end else begin
()
end
in (let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _53_1223 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _130_552 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _130_551 = (let _130_550 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _130_550))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _130_552 _130_551)))
end else begin
()
end
in (let _53_1228 = (destruct_comp c')
in (match (_53_1228) with
| (t, wp, wlp) -> begin
(let wp = (let _130_555 = (let _130_554 = (let _130_553 = (FStar_Tc_Env.get_range env)
in (wp, Some (b), _130_553))
in FStar_Absyn_Syntax.Meta_refresh_label (_130_554))
in (FStar_Absyn_Syntax.mk_Typ_meta _130_555))
in (let wlp = (let _130_558 = (let _130_557 = (let _130_556 = (FStar_Tc_Env.get_range env)
in (wlp, Some (b), _130_556))
in FStar_Absyn_Syntax.Meta_refresh_label (_130_557))
in (FStar_Absyn_Syntax.mk_Typ_meta _130_558))
in (FStar_Absyn_Syntax.mk_Comp (let _53_1231 = c'
in {FStar_Absyn_Syntax.effect_name = _53_1231.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _53_1231.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = ((FStar_Absyn_Syntax.targ wp))::((FStar_Absyn_Syntax.targ wlp))::[]; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))))
end)))))
end)
end)
end))
in (let _53_1233 = lc
in {FStar_Absyn_Syntax.eff_name = _53_1233.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _53_1233.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _53_1233.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

let label = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _130_582 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _130_582)) then begin
f
end else begin
(let _130_583 = (reason ())
in (label _130_583 r f))
end
end))

let label_guard = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _130_590 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_130_590))
end))

let weaken_guard = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _53_1260 -> begin
g2
end))

let weaken_precondition = (fun env lc f -> (let weaken = (fun _53_1265 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (match (f) with
| FStar_Tc_Rel.Trivial -> begin
c
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _53_1274 = (destruct_comp c)
in (match (_53_1274) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (let _53_1278 = lc
in {FStar_Absyn_Syntax.eff_name = _53_1278.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _53_1278.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _53_1278.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _53_8 -> (match (_53_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _53_1289 -> begin
[]
end))))
in (let strengthen = (fun _53_1292 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let g0 = (FStar_Tc_Rel.simplify_guard env g0)
in (match ((FStar_Tc_Rel.guard_form g0)) with
| FStar_Tc_Rel.Trivial -> begin
c
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let c = if (((FStar_Absyn_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Absyn_Util.comp_result c))))) && (not ((FStar_Absyn_Util.is_partial_return c)))) then begin
(let x = (FStar_Absyn_Util.gen_bvar (FStar_Absyn_Util.comp_result c))
in (let xret = (let _130_624 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _130_624))
in (let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (let lc = (let _130_627 = (lcomp_of_comp c)
in (let _130_626 = (let _130_625 = (lcomp_of_comp xret)
in (Some (xbinding), _130_625))
in (bind env (Some (e)) _130_627 _130_626)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _53_1307 = (destruct_comp c)
in (match (_53_1307) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (let _130_633 = (let _130_632 = (let _130_631 = (let _130_630 = (let _130_629 = (let _130_628 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _130_628 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_629))
in (_130_630)::((FStar_Absyn_Syntax.targ wp))::[])
in ((FStar_Absyn_Syntax.targ res_t))::_130_631)
in (md.FStar_Absyn_Syntax.assert_p, _130_632))
in (FStar_Absyn_Syntax.mk_Typ_app _130_633 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _130_637 = (let _53_1312 = lc
in (let _130_636 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _130_635 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _130_634 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _130_634))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _130_636; FStar_Absyn_Syntax.res_typ = _53_1312.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _130_635; FStar_Absyn_Syntax.comp = strengthen})))
in (_130_637, (let _53_1314 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _53_1314.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _53_1314.FStar_Tc_Rel.implicits})))))
end)

let add_equality_to_post_condition = (fun env comp res_t -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let y = (FStar_Absyn_Util.gen_bvar res_t)
in (let _53_1324 = (let _130_645 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _130_644 = (FStar_Absyn_Util.bvar_to_exp y)
in (_130_645, _130_644)))
in (match (_53_1324) with
| (xexp, yexp) -> begin
(let yret = (FStar_Absyn_Syntax.mk_Typ_app (md_pure.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.varg yexp))::[]) None res_t.FStar_Absyn_Syntax.pos)
in (let x_eq_y_yret = (let _130_652 = (let _130_651 = (let _130_650 = (let _130_649 = (let _130_646 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_646))
in (let _130_648 = (let _130_647 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_130_647)::[])
in (_130_649)::_130_648))
in ((FStar_Absyn_Syntax.targ res_t))::_130_650)
in (md_pure.FStar_Absyn_Syntax.assume_p, _130_651))
in (FStar_Absyn_Syntax.mk_Typ_app _130_652 None res_t.FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _130_658 = (let _130_657 = (let _130_656 = (let _130_655 = (let _130_654 = (let _130_653 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder y))::[], x_eq_y_yret) None res_t.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_653))
in (_130_654)::[])
in ((FStar_Absyn_Syntax.targ res_t))::_130_655)
in ((FStar_Absyn_Syntax.targ res_t))::_130_656)
in (md_pure.FStar_Absyn_Syntax.close_wp, _130_657))
in (FStar_Absyn_Syntax.mk_Typ_app _130_658 None res_t.FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _130_661 = (lcomp_of_comp comp)
in (let _130_660 = (let _130_659 = (lcomp_of_comp lc2)
in (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), _130_659))
in (bind env None _130_661 _130_660)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _53_1335 -> (match (()) with
| () -> begin
(let _53_1351 = (let _130_673 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _130_672 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _130_673 _130_672)))
in (match (_53_1351) with
| ((md, _53_1338, _53_1340), (res_t, wp_then, wlp_then), (_53_1347, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _130_684 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.if_then_else, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ g))::((FStar_Absyn_Syntax.targ wp_t))::((FStar_Absyn_Syntax.targ wp_e))::[]) None _130_684)))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wlp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _130_685 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _130_685; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun env res_t lcases -> (let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _53_1374 -> (match (_53_1374) with
| (_53_1372, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun _53_1377 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _130_706 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.if_then_else, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ g))::((FStar_Absyn_Syntax.targ wp_t))::((FStar_Absyn_Syntax.targ wp_e))::[]) None _130_706)))
in (let default_case = (let post_k = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_v_binder res_t))::[], FStar_Absyn_Syntax.ktype) res_t.FStar_Absyn_Syntax.pos)
in (let kwp = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder post_k))::[], FStar_Absyn_Syntax.ktype) res_t.FStar_Absyn_Syntax.pos)
in (let post = (let _130_707 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _130_707 post_k))
in (let wp = (let _130_712 = (let _130_711 = (let _130_710 = (let _130_708 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _130_708))
in (let _130_709 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _130_710 _130_709)))
in (((FStar_Absyn_Syntax.t_binder post))::[], _130_711))
in (FStar_Absyn_Syntax.mk_Typ_lam _130_712 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let wlp = (let _130_714 = (let _130_713 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (((FStar_Absyn_Syntax.t_binder post))::[], _130_713))
in (FStar_Absyn_Syntax.mk_Typ_lam _130_714 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _53_1393 celse -> (match (_53_1393) with
| (g, cthen) -> begin
(let _53_1411 = (let _130_717 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _130_717 celse))
in (match (_53_1411) with
| ((md, _53_1397, _53_1399), (_53_1402, wp_then, wlp_then), (_53_1407, wp_else, wlp_else)) -> begin
(let _130_719 = (ifthenelse md res_t g wp_then wp_else)
in (let _130_718 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _130_719 _130_718 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (let _53_1419 = (destruct_comp comp)
in (match (_53_1419) with
| (_53_1416, wp, wlp) -> begin
(let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wlp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun env bindings lc -> (let close = (fun _53_1426 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bindings wp0 -> (FStar_List.fold_right (fun b wp -> (match (b) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let bs = (let _130_738 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_130_738)::[])
in (let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.close_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ wp))::[]) None wp0.FStar_Absyn_Syntax.pos)))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let bs = (let _130_739 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_130_739)::[])
in (let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.close_wp_t, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wp))::[]) None wp0.FStar_Absyn_Syntax.pos)))
end
| FStar_Tc_Env.Binding_lid (l, t) -> begin
wp
end
| FStar_Tc_Env.Binding_sig (s) -> begin
(FStar_All.failwith "impos")
end)) bindings wp0))
in (let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _53_1457 = (destruct_comp c)
in (match (_53_1457) with
| (t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.FStar_Absyn_Syntax.result_typ wp wlp c.FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (let _53_1461 = lc
in {FStar_Absyn_Syntax.eff_name = _53_1461.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _53_1461.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _53_1461.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun env e lc -> (let refine = (fun _53_1467 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Absyn_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Absyn_Util.is_partial_return c) then begin
c
end else begin
(let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let t = c.FStar_Absyn_Syntax.result_typ
in (let c = (FStar_Absyn_Syntax.mk_Comp c)
in (let x = (FStar_Absyn_Util.new_bvd None)
in (let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (let ret = (let _130_748 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _130_748))
in (let eq_ret = (let _130_750 = (let _130_749 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_130_749))
in (weaken_precondition env ret _130_750))
in (let _130_753 = (let _130_752 = (let _130_751 = (lcomp_of_comp c)
in (bind env None _130_751 (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_130_752.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _130_753 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
end
end)
end))
in (let flags = if (((not ((FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.FStar_Absyn_Syntax.cflags
end else begin
lc.FStar_Absyn_Syntax.cflags
end
in (let _53_1477 = lc
in {FStar_Absyn_Syntax.eff_name = _53_1477.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _53_1477.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _130_765 = (let _130_764 = (let _130_763 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _130_762 = (FStar_Tc_Env.get_range env)
in (_130_763, _130_762)))
in FStar_Absyn_Syntax.Error (_130_764))
in (Prims.raise _130_765))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_instantiate_typ = (fun env t k -> (let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(t, k, [])
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let rec aux = (fun subst _53_9 -> (match (_53_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _53_1507 = (new_implicit_tvar env k)
in (match (_53_1507) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _53_1513 = (aux subst rest)
in (match (_53_1513) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inl (u))::us)
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _53_1524 = (new_implicit_evar env t)
in (match (_53_1524) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _53_1530 = (aux subst rest)
in (match (_53_1530) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inr (v), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _53_1536 = (aux [] bs)
in (match (_53_1536) with
| (args, bs, subst, implicits) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _130_776 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_130_776, k, implicits))))
end)))
end
| _53_1540 -> begin
(t, k, [])
end)
end))

let maybe_instantiate = (fun env e t -> (let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let rec aux = (fun subst _53_10 -> (match (_53_10) with
| (FStar_Util.Inl (a), _53_1556)::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _53_1562 = (new_implicit_tvar env k)
in (match (_53_1562) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _53_1568 = (aux subst rest)
in (match (_53_1568) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inl (u))::us)
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _53_1579 = (new_implicit_evar env t)
in (match (_53_1579) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _53_1585 = (aux subst rest)
in (match (_53_1585) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inr (v), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _53_1591 = (aux [] bs)
in (match (_53_1591) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _53_1598 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _130_793 = (mk_exp_app e args (Some (t)))
in (_130_793, t, implicits)))
end else begin
(e, t, [])
end
end
| _53_1602 -> begin
(let t = (let _130_794 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _130_794 (FStar_Absyn_Util.subst_typ subst)))
in (let _130_795 = (mk_exp_app e args (Some (t)))
in (_130_795, t, implicits)))
end))
end)))
end
| _53_1605 -> begin
(e, t, [])
end)
end))

let weaken_result_typ = (fun env e lc t -> (let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _130_804 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_130_804, false))
end else begin
(let _130_805 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_130_805, true))
end
in (match (gopt) with
| (None, _53_1613) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(let lc = (let _53_1621 = lc
in {FStar_Absyn_Syntax.eff_name = _53_1621.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _53_1621.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _53_1621.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _53_1626 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _53_1626.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _53_1626.FStar_Tc_Rel.implicits})
in (let strengthen = (fun _53_1630 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let _53_1632 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _130_809 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _130_808 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _130_809 _130_808)))
end else begin
()
end
in (let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _53_1637 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_53_1637) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (let x = (FStar_Absyn_Util.new_bvd None)
in (let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.varg xexp))::[]) (Some (k)) xexp.FStar_Absyn_Syntax.pos)
in (let cret = (let _130_810 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _130_810))
in (let guard = if apply_guard then begin
(FStar_Absyn_Syntax.mk_Typ_app (f, ((FStar_Absyn_Syntax.varg xexp))::[]) (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos)
end else begin
f
end
in (let _53_1647 = (let _130_818 = (FStar_All.pipe_left (fun _130_815 -> Some (_130_815)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _130_817 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _130_816 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _130_818 _130_817 e cret _130_816))))
in (match (_53_1647) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _130_820 = (let _130_819 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _130_819))
in (bind env (Some (e)) _130_820 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.FStar_Absyn_Syntax.comp ())
in (let _53_1650 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _130_821 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _130_821))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _53_11 -> (match (_53_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _53_1656 -> begin
[]
end))))
in (let lc = (let _53_1658 = lc
in (let _130_823 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _130_823; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun r t -> (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(let ue = (let _130_828 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _130_828))
in (let ut = (let _130_829 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _130_829))
in (let uk = (let _130_830 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _130_830))
in (let union = (FStar_String.concat "," (FStar_List.append (FStar_List.append ue ut) uk))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _53_1670 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _53_1672 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _53_1674 = (let _130_832 = (let _130_831 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _130_831))
in (FStar_Tc_Errors.report r _130_832))
in (let _53_1676 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))

let gen = (fun verify env ecs -> if (let _130_840 = (FStar_Util.for_all (fun _53_1684 -> (match (_53_1684) with
| (_53_1682, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _130_840)) then begin
None
end else begin
(let norm = (fun c -> (let _53_1687 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _130_843 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _130_843))
end else begin
()
end
in (let steps = (FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
in (let c = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::[]) env c)
end
in (let _53_1691 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _130_844 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _130_844))
end else begin
()
end
in c)))))
in (let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _130_847 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _130_847 FStar_Util.set_elements)))
in (let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _53_1700) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (_53_1705), _53_1708) -> begin
true
end
| _53_1711 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _53_1713 -> begin
true
end))
in (let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _53_1716 -> (match (_53_1716) with
| (e, c) -> begin
(let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _130_852 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _130_852)) then begin
([], e, c)
end else begin
(let c = (norm c)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.FStar_Absyn_Syntax.result_typ
in (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.FStar_Absyn_Syntax.uvars_t)
in (let _53_1732 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _130_853 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _130_853))) then begin
(let _53_1728 = (destruct_comp ct)
in (match (_53_1728) with
| (_53_1724, wp, _53_1727) -> begin
(let binder = ((FStar_Absyn_Syntax.null_v_binder t))::[]
in (let post = (let _130_857 = (let _130_854 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _130_854))
in (let _130_856 = (let _130_855 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_130_855))
in (FStar_Absyn_Syntax.mk_Typ_lam _130_857 _130_856 t.FStar_Absyn_Syntax.pos)))
in (let vc = (let _130_860 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) (FStar_Absyn_Syntax.mk_Typ_app (wp, ((FStar_Absyn_Syntax.targ post))::[])))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _130_860))
in (let _130_861 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _130_861)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _53_1738 -> (match (_53_1738) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _53_1741 -> (match (_53_1741) with
| (u, k) -> begin
(let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_53_1779) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _53_1782 -> begin
(let a = (let _130_866 = (let _130_865 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _130_864 -> Some (_130_864)) _130_865))
in (FStar_Absyn_Util.new_bvd _130_866))
in (let t = (let _130_867 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _130_867 k))
in (let _53_1785 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))
end))))
in (let t = (match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.function_formals)) with
| Some (bs, cod) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.append tvars bs), cod) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(FStar_Absyn_Util.comp_result c)
end
| _53_1796 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _53_1800 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _130_868 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _130_868)))))
end))))
in Some (ecs)))))))
end)

let generalize = (fun verify env lecs -> (let _53_1812 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _130_877 = (let _130_876 = (FStar_List.map (fun _53_1811 -> (match (_53_1811) with
| (lb, _53_1808, _53_1810) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _130_876 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _130_877))
end else begin
()
end
in (match ((let _130_879 = (FStar_All.pipe_right lecs (FStar_List.map (fun _53_1818 -> (match (_53_1818) with
| (_53_1815, e, c) -> begin
(e, c)
end))))
in (gen verify env _130_879))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _53_1827 _53_1830 -> (match ((_53_1827, _53_1830)) with
| ((l, _53_1824, _53_1826), (e, c)) -> begin
(let _53_1831 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _130_884 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _130_883 = (FStar_Absyn_Print.lbname_to_string l)
in (let _130_882 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _130_884 _130_883 _130_882))))
end else begin
()
end
in (l, e, c))
end)) lecs ecs)
end)))

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Uvar -> begin
true
end
| _53_1836 -> begin
false
end))

let check_top_level = (fun env g lc -> (let discharge = (fun g -> (let _53_1842 = (FStar_Tc_Rel.try_discharge_guard env g)
in (let _53_1860 = (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _53_13 -> (match (_53_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _53_1849) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_53_1853, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _53_1859 -> begin
()
end)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _130_896 = (discharge g)
in (let _130_895 = (lc.FStar_Absyn_Syntax.comp ())
in (_130_896, _130_895)))
end else begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _130_897 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _130_897 FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let _53_1871 = (destruct_comp c)
in (match (_53_1871) with
| (t, wp, _53_1870) -> begin
(let vc = (let _130_898 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.trivial, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ wp))::[]) (Some (FStar_Absyn_Syntax.ktype)) _130_898))
in (let g = (let _130_899 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _130_899))
in (let _130_901 = (discharge g)
in (let _130_900 = (FStar_Absyn_Syntax.mk_Comp c)
in (_130_901, _130_900)))))
end))))))
end)))

let short_circuit_exp = (fun head seen_args -> (let short_bin_op_e = (fun f _53_14 -> (match (_53_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _53_1883)::[] -> begin
(let _130_920 = (f fst)
in (FStar_All.pipe_right _130_920 (fun _130_919 -> Some (_130_919))))
end
| _53_1887 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let table = (let op_and_e = (fun e -> (let _130_926 = (FStar_Absyn_Util.b2t e)
in (_130_926, FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun e -> (let _130_930 = (let _130_929 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _130_929))
in (_130_930, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1895) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _53_1901 -> (match (_53_1901) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _130_948 = (mk seen_args)
in Some (_130_948))
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
| _53_1906 -> begin
None
end))))

let short_circuit_typ = (fun head seen_args -> (let short_bin_op_t = (fun f _53_15 -> (match (_53_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _53_1916)::[] -> begin
(f fst)
end
| _53_1920 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_t = (fun t -> (let _130_969 = (unlabel t)
in (FStar_All.pipe_right _130_969 (fun _130_968 -> FStar_Tc_Rel.NonTrivial (_130_968)))))
in (let op_or_t = (fun t -> (let _130_974 = (let _130_972 = (unlabel t)
in (FStar_All.pipe_right _130_972 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _130_974 (fun _130_973 -> FStar_Tc_Rel.NonTrivial (_130_973)))))
in (let op_imp_t = (fun t -> (let _130_978 = (unlabel t)
in (FStar_All.pipe_right _130_978 (fun _130_977 -> FStar_Tc_Rel.NonTrivial (_130_977)))))
in (let short_op_ite = (fun _53_16 -> (match (_53_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _53_1932)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _53_1938)::[] -> begin
(let _130_982 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _130_982 (fun _130_981 -> FStar_Tc_Rel.NonTrivial (_130_981))))
end
| _53_1943 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _53_1951) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _53_1961; FStar_Absyn_Syntax.pos = _53_1959; FStar_Absyn_Syntax.fvs = _53_1957; FStar_Absyn_Syntax.uvs = _53_1955}) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _53_1969 -> (match (_53_1969) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _130_1009 = (mk seen_args)
in Some (_130_1009))
end else begin
None
end
end)))) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g) -> begin
g
end))
end
| _53_1974 -> begin
FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _130_1023 = (let _130_1022 = (let _130_1021 = (let _130_1020 = (let _130_1019 = (let _130_1018 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _130_1018))
in (_130_1019)::[])
in (ens, _130_1020))
in (FStar_Absyn_Syntax.mk_Typ_app _130_1021 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _130_1022))
in (FStar_Absyn_Syntax.mk_Typ_refine _130_1023 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_53_1984) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _53_1999)::(FStar_Util.Inl (ens), _53_1993)::_53_1989 -> begin
(let _130_1029 = (let _130_1026 = (norm req)
in Some (_130_1026))
in (let _130_1028 = (let _130_1027 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _130_1027))
in (_130_1029, _130_1028)))
end
| _53_2003 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_53_2006) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _53_2021)::(FStar_Util.Inl (wlp), _53_2015)::_53_2011 -> begin
(let _53_2033 = (match ((let _130_1031 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _130_1030 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_130_1031, _130_1030)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _53_2030 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_53_2033) with
| (as_req, as_ens) -> begin
(let req = (FStar_Absyn_Syntax.mk_Typ_app (as_req, ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Absyn_Syntax.targ wp))::[]) (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let ens = (FStar_Absyn_Syntax.mk_Typ_app (as_ens, ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Absyn_Syntax.targ wlp))::[]) None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let _130_1035 = (let _130_1032 = (norm req)
in Some (_130_1032))
in (let _130_1034 = (let _130_1033 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _130_1033))
in (_130_1035, _130_1034)))))
end))
end
| _53_2037 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




