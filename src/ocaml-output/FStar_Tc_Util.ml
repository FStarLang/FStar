
open Prims
let try_solve = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

let report = (fun env errs -> (let _103_10 = (FStar_Tc_Env.get_range env)
in (let _103_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _103_10 _103_9))))

let discharge_guard = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun env g -> (discharge_guard env g))

let syn' = (fun env k -> (let _103_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _103_29 k)))

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
(let _103_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _103_52 -> Some (_103_52)) _103_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _103_57 = (let _103_56 = (let _103_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _103_54 = (FStar_Tc_Env.get_range env)
in (_103_55, _103_54)))
in FStar_Absyn_Syntax.Error (_103_56))
in (Prims.raise _103_57))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _103_61 = (let _103_60 = (let _103_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _103_58 = (FStar_Tc_Env.get_range env)
in (_103_59, _103_58)))
in FStar_Absyn_Syntax.Error (_103_60))
in (Prims.raise _103_61))
end
| Some (g) -> begin
(let _38_51 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _103_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.fprint1 "Applied guard is %s\n") _103_62))
end else begin
()
end
in (let e = (FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(FStar_Absyn_Syntax.mk_Exp_bvar (FStar_Absyn_Util.bvd_to_bvar_s x.FStar_Absyn_Syntax.v t2) (Some (t2)) e.FStar_Absyn_Syntax.pos)
end
| _38_57 -> begin
(let _38_58 = e
in (let _103_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _38_58.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _103_63; FStar_Absyn_Syntax.pos = _38_58.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _38_58.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _38_58.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))

let env_binders = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

let as_uvar_e = (fun _38_1 -> (match (_38_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _38_73); FStar_Absyn_Syntax.tk = _38_70; FStar_Absyn_Syntax.pos = _38_68; FStar_Absyn_Syntax.fvs = _38_66; FStar_Absyn_Syntax.uvs = _38_64} -> begin
uv
end
| _38_78 -> begin
(FStar_All.failwith "Impossible")
end))

let as_uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _38_90); FStar_Absyn_Syntax.tk = _38_87; FStar_Absyn_Syntax.pos = _38_85; FStar_Absyn_Syntax.fvs = _38_83; FStar_Absyn_Syntax.uvs = _38_81} -> begin
uv
end
| _38_95 -> begin
(FStar_All.failwith "Impossible")
end))

let new_kvar = (fun env -> (let _103_73 = (let _103_72 = (FStar_Tc_Env.get_range env)
in (let _103_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _103_72 _103_71)))
in (FStar_All.pipe_right _103_73 Prims.fst)))

let new_tvar = (fun env k -> (let _103_80 = (let _103_79 = (FStar_Tc_Env.get_range env)
in (let _103_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _103_79 _103_78 k)))
in (FStar_All.pipe_right _103_80 Prims.fst)))

let new_evar = (fun env t -> (let _103_87 = (let _103_86 = (FStar_Tc_Env.get_range env)
in (let _103_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _103_86 _103_85 t)))
in (FStar_All.pipe_right _103_87 Prims.fst)))

let new_implicit_tvar = (fun env k -> (let _38_105 = (let _103_93 = (FStar_Tc_Env.get_range env)
in (let _103_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _103_93 _103_92 k)))
in (match (_38_105) with
| (t, u) -> begin
(let _103_95 = (let _103_94 = (as_uvar_t u)
in (_103_94, u.FStar_Absyn_Syntax.pos))
in (t, _103_95))
end)))

let new_implicit_evar = (fun env t -> (let _38_110 = (let _103_101 = (FStar_Tc_Env.get_range env)
in (let _103_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _103_101 _103_100 t)))
in (match (_38_110) with
| (e, u) -> begin
(let _103_103 = (let _103_102 = (as_uvar_e u)
in (_103_102, u.FStar_Absyn_Syntax.pos))
in (e, _103_103))
end)))

let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _103_106 = (let _103_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _103_105))
in (FStar_All.failwith _103_106))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_2 -> (match (_38_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _103_111 = (let _103_110 = (force_tk t)
in FStar_Util.Inl (_103_110))
in (_103_111, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _103_113 = (let _103_112 = (force_tk v)
in FStar_Util.Inr (_103_112))
in (_103_113, imp))
end)))))

let is_implicit = (fun _38_3 -> (match (_38_3) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _38_129 -> begin
false
end))

let destruct_arrow_kind = (fun env tt k args -> (let ktop = (let _103_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _103_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (FStar_Tc_Env.get_range env)
in (let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(let imp_follows = (match (args) with
| (_38_145, qual)::_38_143 -> begin
(is_implicit qual)
end
| _38_150 -> begin
false
end)
in (let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _103_137 = (let _103_134 = (let _103_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _103_133))
in (FStar_All.pipe_right _103_134 Prims.fst))
in (FStar_All.pipe_right _103_137 (fun x -> (let _103_136 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (x), _103_136)))))
end
| FStar_Util.Inr (x) -> begin
(let _103_142 = (let _103_139 = (let _103_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _103_138))
in (FStar_All.pipe_right _103_139 Prims.fst))
in (FStar_All.pipe_right _103_142 (fun x -> (let _103_141 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (x), _103_141)))))
end)
in (let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _103_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_103_143)::subst)
end
in (let _38_169 = (mk_implicits vars subst brest)
in (match (_38_169) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _103_144 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _103_144))
end
end
| _38_171 -> begin
(let _103_145 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _103_145))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(let _38_174 = (let _103_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _103_146 [] bs))
in (match (_38_174) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_38_176, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_38_181) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _103_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _103_147 Prims.fst))
in (let bs = (let _103_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _103_148))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _38_188 = (let _103_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _103_149))
in ([], bs, kres)))))))
end
| _38_191 -> begin
(let _103_152 = (let _103_151 = (let _103_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_103_150, r))
in FStar_Absyn_Syntax.Error (_103_151))
in (Prims.raise _103_152))
end))
in (aux ktop)))))

let as_imp = (fun _38_4 -> (match (_38_4) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _38_196 -> begin
false
end))

let pat_as_exps = (fun allow_implicits env p -> (let pvar_eq = (fun x y -> (match ((x, y)) with
| (FStar_Tc_Env.Binding_var (x, _38_205), FStar_Tc_Env.Binding_var (y, _38_210)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _38_216), FStar_Tc_Env.Binding_typ (y, _38_221)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _38_226 -> begin
false
end))
in (let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _38_5 -> (match (_38_5) with
| FStar_Tc_Env.Binding_var (x, _38_232) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _38_237) -> begin
FStar_Util.Inl (x)
end
| _38_241 -> begin
(FStar_All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _38_248) -> begin
(let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (let _38_254 = (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p [] t)
in (match (_38_254) with
| (e, u) -> begin
(let p = (let _38_255 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _38_255.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _38_255.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _38_260) -> begin
(let k = (new_kvar env)
in (let _38_266 = (let _103_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _103_174 k))
in (match (_38_266) with
| (t, u) -> begin
(let p = (let _38_267 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _38_267.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _38_267.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inl (t), p))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in ([], [], [], env, FStar_Util.Inr (e), p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _103_176 = (let _103_175 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _103_175))
in FStar_Tc_Env.Binding_var (_103_176))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let b = (let _103_178 = (let _103_177 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _103_177))
in FStar_Tc_Env.Binding_var (_103_178))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _103_180 = (let _103_179 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _103_179))
in FStar_Tc_Env.Binding_typ (_103_180))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _103_182 = (let _103_181 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _103_181))
in FStar_Tc_Env.Binding_typ (_103_182))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _38_326 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _38_304 _38_307 -> (match ((_38_304, _38_307)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _38_314 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_38_314) with
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
in (match (_38_326) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _103_190 = (let _103_189 = (let _103_188 = (let _103_187 = (let _103_186 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _103_185 = (FStar_All.pipe_right args FStar_List.rev)
in (_103_186, _103_185)))
in (FStar_Absyn_Syntax.mk_Exp_app' _103_187 None p.FStar_Absyn_Syntax.p))
in (_103_188, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_103_189))
in (FStar_Absyn_Syntax.mk_Exp_meta _103_190))
in (let _103_193 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _103_192 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _103_191 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_103_193, _103_192, _103_191, env, FStar_Util.Inr (e), (let _38_328 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _38_328.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _38_328.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_38_331) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let pats = (FStar_List.map (fun _38_343 -> (match (_38_343) with
| (p, imp) -> begin
(let _103_199 = (elaborate_pat env p)
in (_103_199, imp))
end)) pats)
in (let t = (FStar_Tc_Env.lookup_datacon env fv.FStar_Absyn_Syntax.v)
in (let pats = (match ((FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _38_349 -> begin
(let _103_202 = (let _103_201 = (let _103_200 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _103_200))
in FStar_Absyn_Syntax.Error (_103_201))
in (Prims.raise _103_202))
end)
end
| Some (f, _38_352) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _38_365::_38_363) -> begin
(let _103_209 = (let _103_208 = (let _103_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _103_207))
in FStar_Absyn_Syntax.Error (_103_208))
in (Prims.raise _103_209))
end
| (_38_371::_38_369, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(let a = (let _103_211 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _103_211 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _103_213 = (let _103_212 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _103_212))
in (_103_213, (as_imp imp)))
end else begin
(let _103_215 = (let _103_214 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _103_214))
in (_103_215, (as_imp imp)))
end)
end
| (FStar_Util.Inr (_38_382), Some (FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let _103_217 = (let _103_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _103_216))
in (_103_217, true)))
end
| _38_389 -> begin
(let _103_222 = (let _103_221 = (let _103_220 = (let _103_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _103_218))
in (let _103_219 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (_103_220, _103_219)))
in FStar_Absyn_Syntax.Error (_103_221))
in (Prims.raise _103_222))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _103_223 = (aux formals' pats')
in ((p, (as_imp imp)))::_103_223)
end
| ((FStar_Util.Inl (_38_417), imp), FStar_Absyn_Syntax.Pat_dot_typ (_38_422)) when allow_implicits -> begin
(let _103_224 = (aux formals' pats')
in ((p, (as_imp imp)))::_103_224)
end
| ((FStar_Util.Inl (_38_426), imp), _38_431) -> begin
(let a = (let _103_225 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _103_225 FStar_Absyn_Syntax.kun))
in (let p1 = if allow_implicits then begin
(let _103_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _103_226))
end else begin
(let _103_227 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _103_227))
end
in (let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_38_436) -> begin
pats'
end
| _38_439 -> begin
pats
end)
in (let _103_228 = (aux formals' pats')
in ((p1, (as_imp imp)))::_103_228))))
end
| ((FStar_Util.Inr (_38_442), Some (FStar_Absyn_Syntax.Implicit)), _38_448) when p_imp -> begin
(let _103_229 = (aux formals' pats')
in ((p, true))::_103_229)
end
| ((FStar_Util.Inr (_38_451), Some (FStar_Absyn_Syntax.Implicit)), _38_457) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let p = (let _103_230 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _103_230))
in (let _103_231 = (aux formals' pats)
in ((p, true))::_103_231)))
end
| ((FStar_Util.Inr (_38_462), imp), _38_467) -> begin
(let _103_232 = (aux formals' pats')
in ((p, (as_imp imp)))::_103_232)
end)
end))
in (aux f pats))
end)
in (let _38_470 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _38_470.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _38_470.FStar_Absyn_Syntax.p}))))
end
| _38_473 -> begin
p
end))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _38_485 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_38_485) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _38_488)) -> begin
(let _103_241 = (let _103_240 = (let _103_239 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_103_239, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_103_240))
in (Prims.raise _103_241))
end
| Some (FStar_Tc_Env.Binding_typ (x, _38_494)) -> begin
(let _103_244 = (let _103_243 = (let _103_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_103_242, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_103_243))
in (Prims.raise _103_244))
end
| _38_499 -> begin
(b, a, w, arg, p)
end)
end))))
in (let as_arg = (fun _38_6 -> (match (_38_6) with
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
(let _38_521 = (one_pat false env q)
in (match (_38_521) with
| (b, a, _38_518, te, q) -> begin
(let _38_536 = (FStar_List.fold_right (fun p _38_526 -> (match (_38_526) with
| (w, args, pats) -> begin
(let _38_532 = (one_pat false env p)
in (match (_38_532) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _103_258 = (let _103_257 = (let _103_256 = (let _103_254 = (vars_of_bindings a)
in (let _103_253 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _103_254 _103_253)))
in (let _103_255 = (FStar_Tc_Env.get_range env)
in (_103_256, _103_255)))
in FStar_Absyn_Syntax.Error (_103_257))
in (Prims.raise _103_258))
end else begin
(let _103_260 = (let _103_259 = (as_arg arg)
in (_103_259)::args)
in ((FStar_List.append w' w), _103_260, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_38_536) with
| (w, args, pats) -> begin
(let _103_262 = (let _103_261 = (as_arg te)
in (_103_261)::args)
in ((FStar_List.append b w), _103_262, (let _38_537 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _38_537.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _38_537.FStar_Absyn_Syntax.p})))
end))
end))
end
| _38_540 -> begin
(let _38_548 = (one_pat true env p)
in (match (_38_548) with
| (b, _38_543, _38_545, arg, p) -> begin
(let _103_264 = (let _103_263 = (as_arg arg)
in (_103_263)::[])
in (b, _103_264, p))
end))
end))
in (let _38_552 = (top_level_pat_as_args env p)
in (match (_38_552) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map (fun _38_7 -> (match (_38_7) with
| (FStar_Util.Inl (_38_555), _38_558) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _38_563) -> begin
e
end))))
in (b, exps, p))
end))))))))))

let decorate_pattern = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (let _103_283 = (FStar_All.pipe_left (fun _103_282 -> Some (_103_282)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _103_283 p.FStar_Absyn_Syntax.p)))
in (let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_38_579), FStar_Absyn_Syntax.Exp_constant (_38_582)) -> begin
(let _103_284 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _103_284))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _38_590 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _103_287 = (let _103_286 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _103_285 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _103_286 _103_285)))
in (FStar_All.failwith _103_287))
end else begin
()
end
in (let _38_592 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _103_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _103_288 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.fprint2 "Pattern variable %s introduced at type %s\n" _103_289 _103_288)))
end else begin
()
end
in (let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (let x = (let _38_595 = x
in {FStar_Absyn_Syntax.v = _38_595.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _38_595.FStar_Absyn_Syntax.p})
in (let _103_290 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _103_290))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _38_603 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _103_293 = (let _103_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _103_291 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _103_292 _103_291)))
in (FStar_All.failwith _103_293))
end else begin
()
end
in (let x = (let _38_605 = x
in (let _103_294 = (force_tk e)
in {FStar_Absyn_Syntax.v = _38_605.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _103_294; FStar_Absyn_Syntax.p = _38_605.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _38_610), _38_614) -> begin
(let x = (let _38_616 = x
in (let _103_295 = (force_tk e)
in {FStar_Absyn_Syntax.v = _38_616.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _103_295; FStar_Absyn_Syntax.p = _38_616.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _38_626)) -> begin
(let _38_630 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _103_296 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str fv'.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
in (FStar_All.failwith _103_296))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _38_647); FStar_Absyn_Syntax.tk = _38_644; FStar_Absyn_Syntax.pos = _38_642; FStar_Absyn_Syntax.fvs = _38_640; FStar_Absyn_Syntax.uvs = _38_638}, args)) -> begin
(let _38_655 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _103_297 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str fv'.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
in (FStar_All.failwith _103_297))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _103_304 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _103_304))
end
| (arg::args, (argpat, _38_671)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)), FStar_Absyn_Syntax.Pat_dot_typ (_38_681)) -> begin
(let x = (let _103_305 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _103_305))
in (let q = (let _103_307 = (FStar_All.pipe_left (fun _103_306 -> Some (_103_306)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _103_307 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit)), FStar_Absyn_Syntax.Pat_dot_term (_38_692)) -> begin
(let x = (let _103_308 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _103_308))
in (let q = (let _103_310 = (FStar_All.pipe_left (fun _103_309 -> Some (_103_309)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _103_310 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _38_702) -> begin
(let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _38_710) -> begin
(let pat = (let _103_311 = (aux argpat e)
in (_103_311, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _38_714 -> begin
(let _103_314 = (let _103_313 = (FStar_Absyn_Print.pat_to_string p)
in (let _103_312 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _103_313 _103_312)))
in (FStar_All.failwith _103_314))
end))
in (match_args [] args argpats))))
end
| _38_716 -> begin
(let _103_319 = (let _103_318 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _103_317 = (FStar_Absyn_Print.pat_to_string qq)
in (let _103_316 = (let _103_315 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _103_315 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _103_318 _103_317 _103_316))))
in (FStar_All.failwith _103_319))
end))))
and aux_t = (fun p t0 -> (let pkg = (fun q k -> (let _103_327 = (FStar_All.pipe_left (fun _103_326 -> Some (_103_326)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _103_327 p.FStar_Absyn_Syntax.p)))
in (let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _38_728 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _103_330 = (let _103_329 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _103_328 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _103_329 _103_328)))
in (FStar_All.failwith _103_330))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _38_735 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _103_333 = (let _103_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _103_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _103_332 _103_331)))
in (FStar_All.failwith _103_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _38_739), _38_743) -> begin
(let k0 = (force_tk t0)
in (let a = (let _38_746 = a
in {FStar_Absyn_Syntax.v = _38_746.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _38_746.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _38_750 -> begin
(let _103_337 = (let _103_336 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _103_335 = (FStar_Absyn_Print.pat_to_string p)
in (let _103_334 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _103_336 _103_335 _103_334))))
in (FStar_All.failwith _103_337))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _38_754) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (let _103_339 = (FStar_All.pipe_left (fun _103_338 -> Some (_103_338)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _103_339 p.FStar_Absyn_Syntax.p)))
end
| (_38_758, e::[]) -> begin
(aux p e)
end
| _38_763 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp = (fun pat -> (let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _38_770 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun _38_777 -> (match (_38_777) with
| (p, i) -> begin
(let _38_780 = (decorated_pattern_as_either p)
in (match (_38_780) with
| (vars, te) -> begin
(let _103_359 = (let _103_358 = (FStar_Absyn_Syntax.as_implicit i)
in (te, _103_358))
in (vars, _103_359))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_38_782) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _103_362 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _103_362))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _103_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _103_365))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _38_796 = (let _103_366 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _103_366 FStar_List.unzip))
in (match (_38_796) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _103_372 = (let _103_371 = (let _103_370 = (let _103_369 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_103_369, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _103_370))
in (FStar_All.pipe_right _103_371 pkg))
in (vars, _103_372)))
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
(let _103_374 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _103_374))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _38_820 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _38_833 = (decorated_pattern_as_typ p)
in (match (_38_833) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _38_835 -> begin
(let _38_838 = (decorated_pattern_as_exp p)
in (match (_38_838) with
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
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _38_854; FStar_Absyn_Syntax.pos = _38_852; FStar_Absyn_Syntax.fvs = _38_850; FStar_Absyn_Syntax.uvs = _38_848}) -> begin
(let _38_884 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _38_861 _38_865 -> (match ((_38_861, _38_865)) with
| ((out, subst), (b, _38_864)) -> begin
(match (b) with
| FStar_Util.Inr (_38_867) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _103_382 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _103_382 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _103_385 = (let _103_384 = (let _103_383 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _103_383 Prims.fst))
in (bs, _103_384))
in (FStar_Absyn_Syntax.mk_Typ_lam _103_385 (Some (k)) r))
end
| _38_878 -> begin
(FStar_All.failwith "Impossible")
end)
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (let _103_387 = (let _103_386 = (FStar_Absyn_Syntax.targ arg)
in (_103_386)::out)
in (_103_387, subst)))))
end)
end)) ([], [])))
in (match (_38_884) with
| (args, _38_883) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _38_886 -> begin
(FStar_All.failwith "Impossible")
end)))))))

let extract_lb_annotation = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _103_398 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _103_398 Prims.fst))
in ((let _38_897 = a
in {FStar_Absyn_Syntax.v = _38_897.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _38_897.FStar_Absyn_Syntax.p}), false))
end
| _38_900 -> begin
(a, true)
end))
in (let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _103_403 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _103_403 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _38_909) -> begin
(x, false)
end
| _38_912 -> begin
(FStar_All.failwith "impos")
end))
end
| _38_914 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _38_918) -> begin
(x, true)
end
| _38_921 -> begin
(FStar_All.failwith "impos")
end)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _38_927)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _38_934) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _38_963 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _38_944 b -> (match (_38_944) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _38_950 = (mk_t_binder scope a)
in (match (_38_950) with
| (tb, c) -> begin
(let b = (FStar_Util.Inl (tb), (Prims.snd b))
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _38_958 = (mk_v_binder scope x)
in (match (_38_958) with
| (vb, c) -> begin
(let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_38_963) with
| (scope, bs, check) -> begin
(let _38_967 = (aux scope body)
in (match (_38_967) with
| (body, res, check_res) -> begin
(let c = (FStar_Absyn_Util.ml_comp res r)
in (let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (let _38_970 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _103_411 = (FStar_Range.string_of_range r)
in (let _103_410 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "(%s) Using type %s\n" _103_411 _103_410)))
end else begin
()
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _38_974 -> begin
(let _103_413 = (let _103_412 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _103_412 Prims.fst))
in (e, _103_413, false))
end))
in (let _103_414 = (FStar_Tc_Env.t_binders env)
in (aux _103_414 e))))))
end
| _38_976 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun c -> (let _38_993 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _38_986)::(FStar_Util.Inl (wlp), _38_981)::[] -> begin
(wp, wlp)
end
| _38_990 -> begin
(let _103_419 = (let _103_418 = (let _103_417 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _103_417 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Absyn_Syntax.str _103_418))
in (FStar_All.failwith _103_419))
end)
in (match (_38_993) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun c m lift -> (let _38_1001 = (destruct_comp c)
in (match (_38_1001) with
| (_38_998, wp, wlp) -> begin
(let _103_441 = (let _103_440 = (let _103_436 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _103_436))
in (let _103_439 = (let _103_438 = (let _103_437 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _103_437))
in (_103_438)::[])
in (_103_440)::_103_439))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _103_441; FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_38_1009, c) -> begin
(let l = (FStar_Absyn_Util.comp_to_comp_typ c).FStar_Absyn_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (let res = (match ((FStar_Util.smap_try_find cache l.FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(let _38_1023 = (FStar_Util.smap_add cache l.FStar_Absyn_Syntax.str m)
in m)
end)
end)
in res))))

let join_effects = (fun env l1 l2 -> (let _38_1034 = (let _103_455 = (norm_eff_name env l1)
in (let _103_454 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _103_455 _103_454)))
in (match (_38_1034) with
| (m, _38_1031, _38_1033) -> begin
m
end)))

let join_lcomp = (fun env c1 c2 -> if ((FStar_Absyn_Syntax.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Absyn_Syntax.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)

let lift_and_destruct = (fun env c1 c2 -> (let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _38_1046 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_38_1046) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_Tc_Env.get_effect_decl env m)
in (let _38_1052 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_38_1052) with
| (a, kwp) -> begin
(let _103_469 = (destruct_comp m1)
in (let _103_468 = (destruct_comp m2)
in ((md, a, kwp), _103_469, _103_468)))
end)))))
end)))))

let is_pure_effect = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun md result wp wlp flags -> (let _103_492 = (let _103_491 = (let _103_490 = (FStar_Absyn_Syntax.targ wp)
in (let _103_489 = (let _103_488 = (FStar_Absyn_Syntax.targ wlp)
in (_103_488)::[])
in (_103_490)::_103_489))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _103_491; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _103_492)))

let lcomp_of_comp = (fun c0 -> (let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _38_1066 -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun subst lc -> (let _38_1069 = lc
in (let _103_502 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _38_1069.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _103_502; FStar_Absyn_Syntax.cflags = _38_1069.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _38_1071 -> (match (()) with
| () -> begin
(let _103_501 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _103_501))
end))})))

let is_function = (fun t -> (match ((let _103_505 = (FStar_Absyn_Util.compress_typ t)
in _103_505.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_38_1074) -> begin
true
end
| _38_1077 -> begin
false
end))

let return_value = (fun env t v -> (let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _38_1086 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_38_1086) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _103_517 = (let _103_516 = (let _103_515 = (let _103_514 = (FStar_Absyn_Syntax.targ t)
in (let _103_513 = (let _103_512 = (FStar_Absyn_Syntax.varg v)
in (_103_512)::[])
in (_103_514)::_103_513))
in (m.FStar_Absyn_Syntax.ret, _103_515))
in (FStar_Absyn_Syntax.mk_Typ_app _103_516 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _103_517))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _38_1091 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _103_520 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _103_519 = (FStar_Absyn_Print.exp_to_string v)
in (let _103_518 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.fprint3 "(%s) returning %s at comp type %s\n" _103_520 _103_519 _103_518))))
end else begin
()
end
in c)))

let bind = (fun env e1opt lc1 _38_1098 -> (match (_38_1098) with
| (b, lc2) -> begin
(let _38_1109 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _38_1102)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _38_1107 -> begin
"??"
end)
in (let _103_530 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _103_529 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _103_530 bstr _103_529))))
end else begin
()
end
in (let bind_it = (fun _38_1112 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun _38_1116 -> (match (()) with
| () -> begin
(let aux = (fun _38_1118 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_38_1121)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_38_1125)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _38_1129 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _38_1134))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _103_538 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _103_537 -> Some (_103_537)) _103_538))
end else begin
(aux ())
end
end
| _38_1140 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _38_1158 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _103_542 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _38_1146)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _38_1152)) -> begin
(FStar_Absyn_Print.sli l)
end
| _38_1157 -> begin
"Something else"
end)
in (let _103_541 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _103_540 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _103_539 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _103_542 _103_541 _103_540 _103_539)))))
end else begin
()
end
in c)
end
| None -> begin
(let _38_1173 = (lift_and_destruct env c1 c2)
in (match (_38_1173) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _103_543 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_103_543)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _103_544 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_103_544)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _103_545 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_103_545)::[])
end
| _38_1186 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (let wp_args = (let _103_560 = (FStar_Absyn_Syntax.targ t1)
in (let _103_559 = (let _103_558 = (FStar_Absyn_Syntax.targ t2)
in (let _103_557 = (let _103_556 = (FStar_Absyn_Syntax.targ wp1)
in (let _103_555 = (let _103_554 = (FStar_Absyn_Syntax.targ wlp1)
in (let _103_553 = (let _103_552 = (let _103_548 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _103_548))
in (let _103_551 = (let _103_550 = (let _103_549 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _103_549))
in (_103_550)::[])
in (_103_552)::_103_551))
in (_103_554)::_103_553))
in (_103_556)::_103_555))
in (_103_558)::_103_557))
in (_103_560)::_103_559))
in (let wlp_args = (let _103_568 = (FStar_Absyn_Syntax.targ t1)
in (let _103_567 = (let _103_566 = (FStar_Absyn_Syntax.targ t2)
in (let _103_565 = (let _103_564 = (FStar_Absyn_Syntax.targ wlp1)
in (let _103_563 = (let _103_562 = (let _103_561 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _103_561))
in (_103_562)::[])
in (_103_564)::_103_563))
in (_103_566)::_103_565))
in (_103_568)::_103_567))
in (let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wp, wp_args) None t2.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _103_569 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _103_569; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let _38_1204 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_38_1204) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _103_584 = (let _103_583 = (let _103_582 = (FStar_Absyn_Syntax.targ t)
in (let _103_581 = (let _103_580 = (FStar_Absyn_Syntax.targ f)
in (_103_580)::[])
in (_103_582)::_103_581))
in (mk_wp, _103_583))
in (FStar_Absyn_Syntax.mk_Typ_app _103_584 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (let wlp = (let _103_589 = (let _103_588 = (let _103_587 = (FStar_Absyn_Syntax.targ t)
in (let _103_586 = (let _103_585 = (FStar_Absyn_Syntax.targ f)
in (_103_585)::[])
in (_103_587)::_103_586))
in (mk_wlp, _103_588))
in (FStar_Absyn_Syntax.mk_Typ_app _103_589 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun env b lc -> (let refresh = (fun _38_1213 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_38_1216) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _38_1220 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _103_601 = (let _103_600 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _103_600))
in (FStar_Util.fprint1 "Refreshing label at %s\n" _103_601))
end else begin
()
end
in (let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _38_1223 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _103_604 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _103_603 = (let _103_602 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _103_602))
in (FStar_Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _103_604 _103_603)))
end else begin
()
end
in (let _38_1228 = (destruct_comp c')
in (match (_38_1228) with
| (t, wp, wlp) -> begin
(let wp = (let _103_607 = (let _103_606 = (let _103_605 = (FStar_Tc_Env.get_range env)
in (wp, Some (b), _103_605))
in FStar_Absyn_Syntax.Meta_refresh_label (_103_606))
in (FStar_Absyn_Syntax.mk_Typ_meta _103_607))
in (let wlp = (let _103_610 = (let _103_609 = (let _103_608 = (FStar_Tc_Env.get_range env)
in (wlp, Some (b), _103_608))
in FStar_Absyn_Syntax.Meta_refresh_label (_103_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _103_610))
in (let _103_615 = (let _38_1231 = c'
in (let _103_614 = (let _103_613 = (FStar_Absyn_Syntax.targ wp)
in (let _103_612 = (let _103_611 = (FStar_Absyn_Syntax.targ wlp)
in (_103_611)::[])
in (_103_613)::_103_612))
in {FStar_Absyn_Syntax.effect_name = _38_1231.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _38_1231.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _103_614; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _103_615))))
end)))))
end)
end)
end))
in (let _38_1233 = lc
in {FStar_Absyn_Syntax.eff_name = _38_1233.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _38_1233.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _38_1233.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

let label = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _103_639 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)
in (FStar_All.pipe_left Prims.op_Negation _103_639)) then begin
f
end else begin
(let _103_640 = (reason ())
in (label _103_640 r f))
end
end))

let label_guard = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _103_647 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_103_647))
end))

let weaken_guard = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _38_1260 -> begin
g2
end))

let weaken_precondition = (fun env lc f -> (let weaken = (fun _38_1265 -> (match (()) with
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
in (let _38_1274 = (destruct_comp c)
in (match (_38_1274) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (let _103_666 = (let _103_665 = (let _103_664 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_663 = (let _103_662 = (FStar_Absyn_Syntax.targ f)
in (let _103_661 = (let _103_660 = (FStar_Absyn_Syntax.targ wp)
in (_103_660)::[])
in (_103_662)::_103_661))
in (_103_664)::_103_663))
in (md.FStar_Absyn_Syntax.assume_p, _103_665))
in (FStar_Absyn_Syntax.mk_Typ_app _103_666 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (let _103_673 = (let _103_672 = (let _103_671 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_670 = (let _103_669 = (FStar_Absyn_Syntax.targ f)
in (let _103_668 = (let _103_667 = (FStar_Absyn_Syntax.targ wlp)
in (_103_667)::[])
in (_103_669)::_103_668))
in (_103_671)::_103_670))
in (md.FStar_Absyn_Syntax.assume_p, _103_672))
in (FStar_Absyn_Syntax.mk_Typ_app _103_673 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (let _38_1278 = lc
in {FStar_Absyn_Syntax.eff_name = _38_1278.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _38_1278.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _38_1278.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _38_8 -> (match (_38_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _38_1289 -> begin
[]
end))))
in (let strengthen = (fun _38_1292 -> (match (()) with
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
in (let xret = (let _103_695 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _103_695))
in (let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (let lc = (let _103_698 = (lcomp_of_comp c)
in (let _103_697 = (let _103_696 = (lcomp_of_comp xret)
in (Some (xbinding), _103_696))
in (bind env (Some (e)) _103_698 _103_697)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _38_1307 = (destruct_comp c)
in (match (_38_1307) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (let _103_707 = (let _103_706 = (let _103_705 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_704 = (let _103_703 = (let _103_700 = (let _103_699 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _103_699 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _103_700))
in (let _103_702 = (let _103_701 = (FStar_Absyn_Syntax.targ wp)
in (_103_701)::[])
in (_103_703)::_103_702))
in (_103_705)::_103_704))
in (md.FStar_Absyn_Syntax.assert_p, _103_706))
in (FStar_Absyn_Syntax.mk_Typ_app _103_707 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (let _103_714 = (let _103_713 = (let _103_712 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_711 = (let _103_710 = (FStar_Absyn_Syntax.targ f)
in (let _103_709 = (let _103_708 = (FStar_Absyn_Syntax.targ wlp)
in (_103_708)::[])
in (_103_710)::_103_709))
in (_103_712)::_103_711))
in (md.FStar_Absyn_Syntax.assume_p, _103_713))
in (FStar_Absyn_Syntax.mk_Typ_app _103_714 None wlp.FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _103_718 = (let _38_1312 = lc
in (let _103_717 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _103_716 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _103_715 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _103_715))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _103_717; FStar_Absyn_Syntax.res_typ = _38_1312.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _103_716; FStar_Absyn_Syntax.comp = strengthen})))
in (_103_718, (let _38_1314 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _38_1314.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _38_1314.FStar_Tc_Rel.implicits})))))
end)

let add_equality_to_post_condition = (fun env comp res_t -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let y = (FStar_Absyn_Util.gen_bvar res_t)
in (let _38_1324 = (let _103_726 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _103_725 = (FStar_Absyn_Util.bvar_to_exp y)
in (_103_726, _103_725)))
in (match (_38_1324) with
| (xexp, yexp) -> begin
(let yret = (let _103_731 = (let _103_730 = (let _103_729 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_728 = (let _103_727 = (FStar_Absyn_Syntax.varg yexp)
in (_103_727)::[])
in (_103_729)::_103_728))
in (md_pure.FStar_Absyn_Syntax.ret, _103_730))
in (FStar_Absyn_Syntax.mk_Typ_app _103_731 None res_t.FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _103_739 = (let _103_738 = (let _103_737 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_736 = (let _103_735 = (let _103_732 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _103_732))
in (let _103_734 = (let _103_733 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_103_733)::[])
in (_103_735)::_103_734))
in (_103_737)::_103_736))
in (md_pure.FStar_Absyn_Syntax.assume_p, _103_738))
in (FStar_Absyn_Syntax.mk_Typ_app _103_739 None res_t.FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _103_750 = (let _103_749 = (let _103_748 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_747 = (let _103_746 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_745 = (let _103_744 = (let _103_743 = (let _103_742 = (let _103_741 = (let _103_740 = (FStar_Absyn_Syntax.v_binder y)
in (_103_740)::[])
in (_103_741, x_eq_y_yret))
in (FStar_Absyn_Syntax.mk_Typ_lam _103_742 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _103_743))
in (_103_744)::[])
in (_103_746)::_103_745))
in (_103_748)::_103_747))
in (md_pure.FStar_Absyn_Syntax.close_wp, _103_749))
in (FStar_Absyn_Syntax.mk_Typ_app _103_750 None res_t.FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _103_753 = (lcomp_of_comp comp)
in (let _103_752 = (let _103_751 = (lcomp_of_comp lc2)
in (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), _103_751))
in (bind env None _103_753 _103_752)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _38_1335 -> (match (()) with
| () -> begin
(let _38_1351 = (let _103_765 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _103_764 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _103_765 _103_764)))
in (match (_38_1351) with
| ((md, _38_1338, _38_1340), (res_t, wp_then, wlp_then), (_38_1347, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _103_785 = (let _103_783 = (let _103_782 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_781 = (let _103_780 = (FStar_Absyn_Syntax.targ g)
in (let _103_779 = (let _103_778 = (FStar_Absyn_Syntax.targ wp_t)
in (let _103_777 = (let _103_776 = (FStar_Absyn_Syntax.targ wp_e)
in (_103_776)::[])
in (_103_778)::_103_777))
in (_103_780)::_103_779))
in (_103_782)::_103_781))
in (md.FStar_Absyn_Syntax.if_then_else, _103_783))
in (let _103_784 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _103_785 None _103_784))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(let wp = (let _103_792 = (let _103_791 = (let _103_790 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_789 = (let _103_788 = (FStar_Absyn_Syntax.targ wlp)
in (let _103_787 = (let _103_786 = (FStar_Absyn_Syntax.targ wp)
in (_103_786)::[])
in (_103_788)::_103_787))
in (_103_790)::_103_789))
in (md.FStar_Absyn_Syntax.ite_wp, _103_791))
in (FStar_Absyn_Syntax.mk_Typ_app _103_792 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (let _103_797 = (let _103_796 = (let _103_795 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_794 = (let _103_793 = (FStar_Absyn_Syntax.targ wlp)
in (_103_793)::[])
in (_103_795)::_103_794))
in (md.FStar_Absyn_Syntax.ite_wlp, _103_796))
in (FStar_Absyn_Syntax.mk_Typ_app _103_797 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _103_798 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _103_798; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun env res_t lcases -> (let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _38_1374 -> (match (_38_1374) with
| (_38_1372, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun _38_1377 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _103_828 = (let _103_826 = (let _103_825 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_824 = (let _103_823 = (FStar_Absyn_Syntax.targ g)
in (let _103_822 = (let _103_821 = (FStar_Absyn_Syntax.targ wp_t)
in (let _103_820 = (let _103_819 = (FStar_Absyn_Syntax.targ wp_e)
in (_103_819)::[])
in (_103_821)::_103_820))
in (_103_823)::_103_822))
in (_103_825)::_103_824))
in (md.FStar_Absyn_Syntax.if_then_else, _103_826))
in (let _103_827 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _103_828 None _103_827))))
in (let default_case = (let post_k = (let _103_831 = (let _103_830 = (let _103_829 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_103_829)::[])
in (_103_830, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _103_831 res_t.FStar_Absyn_Syntax.pos))
in (let kwp = (let _103_834 = (let _103_833 = (let _103_832 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_103_832)::[])
in (_103_833, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _103_834 res_t.FStar_Absyn_Syntax.pos))
in (let post = (let _103_835 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _103_835 post_k))
in (let wp = (let _103_842 = (let _103_841 = (let _103_836 = (FStar_Absyn_Syntax.t_binder post)
in (_103_836)::[])
in (let _103_840 = (let _103_839 = (let _103_837 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _103_837))
in (let _103_838 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _103_839 _103_838)))
in (_103_841, _103_840)))
in (FStar_Absyn_Syntax.mk_Typ_lam _103_842 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let wlp = (let _103_846 = (let _103_845 = (let _103_843 = (FStar_Absyn_Syntax.t_binder post)
in (_103_843)::[])
in (let _103_844 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_103_845, _103_844)))
in (FStar_Absyn_Syntax.mk_Typ_lam _103_846 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _38_1393 celse -> (match (_38_1393) with
| (g, cthen) -> begin
(let _38_1411 = (let _103_849 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _103_849 celse))
in (match (_38_1411) with
| ((md, _38_1397, _38_1399), (_38_1402, wp_then, wlp_then), (_38_1407, wp_else, wlp_else)) -> begin
(let _103_851 = (ifthenelse md res_t g wp_then wp_else)
in (let _103_850 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _103_851 _103_850 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (let _38_1419 = (destruct_comp comp)
in (match (_38_1419) with
| (_38_1416, wp, wlp) -> begin
(let wp = (let _103_858 = (let _103_857 = (let _103_856 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_855 = (let _103_854 = (FStar_Absyn_Syntax.targ wlp)
in (let _103_853 = (let _103_852 = (FStar_Absyn_Syntax.targ wp)
in (_103_852)::[])
in (_103_854)::_103_853))
in (_103_856)::_103_855))
in (md.FStar_Absyn_Syntax.ite_wp, _103_857))
in (FStar_Absyn_Syntax.mk_Typ_app _103_858 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (let _103_863 = (let _103_862 = (let _103_861 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_860 = (let _103_859 = (FStar_Absyn_Syntax.targ wlp)
in (_103_859)::[])
in (_103_861)::_103_860))
in (md.FStar_Absyn_Syntax.ite_wlp, _103_862))
in (FStar_Absyn_Syntax.mk_Typ_app _103_863 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun env bindings lc -> (let close = (fun _38_1426 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bindings wp0 -> (FStar_List.fold_right (fun b wp -> (match (b) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let bs = (let _103_882 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_103_882)::[])
in (let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _103_889 = (let _103_888 = (let _103_887 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_886 = (let _103_885 = (FStar_Absyn_Syntax.targ t)
in (let _103_884 = (let _103_883 = (FStar_Absyn_Syntax.targ wp)
in (_103_883)::[])
in (_103_885)::_103_884))
in (_103_887)::_103_886))
in (md.FStar_Absyn_Syntax.close_wp, _103_888))
in (FStar_Absyn_Syntax.mk_Typ_app _103_889 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let bs = (let _103_890 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_103_890)::[])
in (let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _103_895 = (let _103_894 = (let _103_893 = (FStar_Absyn_Syntax.targ res_t)
in (let _103_892 = (let _103_891 = (FStar_Absyn_Syntax.targ wp)
in (_103_891)::[])
in (_103_893)::_103_892))
in (md.FStar_Absyn_Syntax.close_wp_t, _103_894))
in (FStar_Absyn_Syntax.mk_Typ_app _103_895 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_lid (l, t) -> begin
wp
end
| FStar_Tc_Env.Binding_sig (s) -> begin
(FStar_All.failwith "impos")
end)) bindings wp0))
in (let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _38_1457 = (destruct_comp c)
in (match (_38_1457) with
| (t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.FStar_Absyn_Syntax.result_typ wp wlp c.FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (let _38_1461 = lc
in {FStar_Absyn_Syntax.eff_name = _38_1461.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _38_1461.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _38_1461.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun env e lc -> (let refine = (fun _38_1467 -> (match (()) with
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
in (let ret = (let _103_904 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _103_904))
in (let eq_ret = (let _103_906 = (let _103_905 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_103_905))
in (weaken_precondition env ret _103_906))
in (let _103_909 = (let _103_908 = (let _103_907 = (lcomp_of_comp c)
in (bind env None _103_907 (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_103_908.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _103_909 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
end
end)
end))
in (let flags = if (((not ((FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.FStar_Absyn_Syntax.cflags
end else begin
lc.FStar_Absyn_Syntax.cflags
end
in (let _38_1477 = lc
in {FStar_Absyn_Syntax.eff_name = _38_1477.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _38_1477.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _103_921 = (let _103_920 = (let _103_919 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _103_918 = (FStar_Tc_Env.get_range env)
in (_103_919, _103_918)))
in FStar_Absyn_Syntax.Error (_103_920))
in (Prims.raise _103_921))
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
(let rec aux = (fun subst _38_9 -> (match (_38_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _38_1507 = (new_implicit_tvar env k)
in (match (_38_1507) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _38_1513 = (aux subst rest)
in (match (_38_1513) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inl (u))::us)
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _38_1524 = (new_implicit_evar env t)
in (match (_38_1524) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _38_1530 = (aux subst rest)
in (match (_38_1530) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inr (v), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _38_1536 = (aux [] bs)
in (match (_38_1536) with
| (args, bs, subst, implicits) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _103_932 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_103_932, k, implicits))))
end)))
end
| _38_1540 -> begin
(t, k, [])
end)
end))

let maybe_instantiate = (fun env e t -> (let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let rec aux = (fun subst _38_10 -> (match (_38_10) with
| (FStar_Util.Inl (a), _38_1556)::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _38_1562 = (new_implicit_tvar env k)
in (match (_38_1562) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _38_1568 = (aux subst rest)
in (match (_38_1568) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inl (u))::us)
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _38_1579 = (new_implicit_evar env t)
in (match (_38_1579) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _38_1585 = (aux subst rest)
in (match (_38_1585) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inr (v), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _38_1591 = (aux [] bs)
in (match (_38_1591) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _38_1598 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _103_949 = (mk_exp_app e args (Some (t)))
in (_103_949, t, implicits)))
end else begin
(e, t, [])
end
end
| _38_1602 -> begin
(let t = (let _103_950 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _103_950 (FStar_Absyn_Util.subst_typ subst)))
in (let _103_951 = (mk_exp_app e args (Some (t)))
in (_103_951, t, implicits)))
end))
end)))
end
| _38_1605 -> begin
(e, t, [])
end)
end))

let weaken_result_typ = (fun env e lc t -> (let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _103_960 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_103_960, false))
end else begin
(let _103_961 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_103_961, true))
end
in (match (gopt) with
| (None, _38_1613) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(let lc = (let _38_1621 = lc
in {FStar_Absyn_Syntax.eff_name = _38_1621.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _38_1621.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _38_1621.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _38_1626 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _38_1626.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _38_1626.FStar_Tc_Rel.implicits})
in (let strengthen = (fun _38_1630 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let _38_1632 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _103_965 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _103_964 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.fprint2 "Strengthening %s with guard %s\n" _103_965 _103_964)))
end else begin
()
end
in (let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _38_1637 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_38_1637) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (let x = (FStar_Absyn_Util.new_bvd None)
in (let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (let _103_970 = (let _103_969 = (let _103_968 = (FStar_Absyn_Syntax.targ t)
in (let _103_967 = (let _103_966 = (FStar_Absyn_Syntax.varg xexp)
in (_103_966)::[])
in (_103_968)::_103_967))
in (md.FStar_Absyn_Syntax.ret, _103_969))
in (FStar_Absyn_Syntax.mk_Typ_app _103_970 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (let cret = (let _103_971 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _103_971))
in (let guard = if apply_guard then begin
(let _103_974 = (let _103_973 = (let _103_972 = (FStar_Absyn_Syntax.varg xexp)
in (_103_972)::[])
in (f, _103_973))
in (FStar_Absyn_Syntax.mk_Typ_app _103_974 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (let _38_1647 = (let _103_982 = (FStar_All.pipe_left (fun _103_979 -> Some (_103_979)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _103_981 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _103_980 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _103_982 _103_981 e cret _103_980))))
in (match (_38_1647) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _103_984 = (let _103_983 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _103_983))
in (bind env (Some (e)) _103_984 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.FStar_Absyn_Syntax.comp ())
in (let _38_1650 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _103_985 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.fprint1 "Strengthened to %s\n" _103_985))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _38_11 -> (match (_38_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _38_1656 -> begin
[]
end))))
in (let lc = (let _38_1658 = lc
in (let _103_987 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _103_987; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun r t -> (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(let ue = (let _103_992 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _103_992))
in (let ut = (let _103_993 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _103_993))
in (let uk = (let _103_994 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _103_994))
in (let union = (FStar_String.concat "," (FStar_List.append (FStar_List.append ue ut) uk))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _38_1670 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _38_1672 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _38_1674 = (let _103_996 = (let _103_995 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _103_995))
in (FStar_Tc_Errors.report r _103_996))
in (let _38_1676 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))

let gen = (fun verify env ecs -> if (let _103_1004 = (FStar_Util.for_all (fun _38_1684 -> (match (_38_1684) with
| (_38_1682, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _103_1004)) then begin
None
end else begin
(let norm = (fun c -> (let _38_1687 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _103_1007 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.fprint1 "Normalizing before generalizing:\n\t %s" _103_1007))
end else begin
()
end
in (let steps = (FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
in (let c = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
(FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::[]) env c)
end
in (let _38_1691 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _103_1008 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.fprint1 "Normalized to:\n\t %s" _103_1008))
end else begin
()
end
in c)))))
in (let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _103_1011 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _103_1011 FStar_Util.set_elements)))
in (let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _38_1700) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _38_12 -> (match (_38_12) with
| (FStar_Util.Inl (_38_1705), _38_1708) -> begin
true
end
| _38_1711 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _38_1713 -> begin
true
end))
in (let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _38_1716 -> (match (_38_1716) with
| (e, c) -> begin
(let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _103_1016 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _103_1016)) then begin
([], e, c)
end else begin
(let c = (norm c)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.FStar_Absyn_Syntax.result_typ
in (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.FStar_Absyn_Syntax.uvars_t)
in (let _38_1732 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) && verify) && (let _103_1017 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _103_1017))) then begin
(let _38_1728 = (destruct_comp ct)
in (match (_38_1728) with
| (_38_1724, wp, _38_1727) -> begin
(let binder = (let _103_1018 = (FStar_Absyn_Syntax.null_v_binder t)
in (_103_1018)::[])
in (let post = (let _103_1022 = (let _103_1019 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _103_1019))
in (let _103_1021 = (let _103_1020 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_103_1020))
in (FStar_Absyn_Syntax.mk_Typ_lam _103_1022 _103_1021 t.FStar_Absyn_Syntax.pos)))
in (let vc = (let _103_1029 = (let _103_1028 = (let _103_1027 = (let _103_1026 = (let _103_1025 = (FStar_Absyn_Syntax.targ post)
in (_103_1025)::[])
in (wp, _103_1026))
in (FStar_Absyn_Syntax.mk_Typ_app _103_1027))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _103_1028))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _103_1029))
in (let _103_1030 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _103_1030)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _38_1738 -> (match (_38_1738) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _38_1741 -> (match (_38_1741) with
| (u, k) -> begin
(let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_38_1779) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _38_1782 -> begin
(let a = (let _103_1035 = (let _103_1034 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _103_1033 -> Some (_103_1033)) _103_1034))
in (FStar_Absyn_Util.new_bvd _103_1035))
in (let t = (let _103_1036 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _103_1036 k))
in (let _38_1785 = (FStar_Absyn_Util.unchecked_unify u t)
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
| _38_1796 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _38_1800 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _103_1037 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _103_1037)))))
end))))
in Some (ecs)))))))
end)

let generalize = (fun verify env lecs -> (let _38_1812 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _103_1046 = (let _103_1045 = (FStar_List.map (fun _38_1811 -> (match (_38_1811) with
| (lb, _38_1808, _38_1810) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _103_1045 (FStar_String.concat ", ")))
in (FStar_Util.fprint1 "Generalizing: %s" _103_1046))
end else begin
()
end
in (match ((let _103_1048 = (FStar_All.pipe_right lecs (FStar_List.map (fun _38_1818 -> (match (_38_1818) with
| (_38_1815, e, c) -> begin
(e, c)
end))))
in (gen verify env _103_1048))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _38_1827 _38_1830 -> (match ((_38_1827, _38_1830)) with
| ((l, _38_1824, _38_1826), (e, c)) -> begin
(let _38_1831 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _103_1053 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _103_1052 = (FStar_Absyn_Print.lbname_to_string l)
in (let _103_1051 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.fprint3 "(%s) Generalized %s to %s" _103_1053 _103_1052 _103_1051))))
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
| _38_1836 -> begin
false
end))

let check_top_level = (fun env g lc -> (let discharge = (fun g -> (let _38_1842 = (FStar_Tc_Rel.try_discharge_guard env g)
in (let _38_1860 = (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _38_13 -> (match (_38_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _38_1849) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_38_1853, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _38_1859 -> begin
()
end)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _103_1065 = (discharge g)
in (let _103_1064 = (lc.FStar_Absyn_Syntax.comp ())
in (_103_1065, _103_1064)))
end else begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _103_1066 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _103_1066 FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let _38_1871 = (destruct_comp c)
in (match (_38_1871) with
| (t, wp, _38_1870) -> begin
(let vc = (let _103_1072 = (let _103_1070 = (let _103_1069 = (FStar_Absyn_Syntax.targ t)
in (let _103_1068 = (let _103_1067 = (FStar_Absyn_Syntax.targ wp)
in (_103_1067)::[])
in (_103_1069)::_103_1068))
in (md.FStar_Absyn_Syntax.trivial, _103_1070))
in (let _103_1071 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _103_1072 (Some (FStar_Absyn_Syntax.ktype)) _103_1071)))
in (let g = (let _103_1073 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _103_1073))
in (let _103_1075 = (discharge g)
in (let _103_1074 = (FStar_Absyn_Syntax.mk_Comp c)
in (_103_1075, _103_1074)))))
end))))))
end)))

let short_circuit_exp = (fun head seen_args -> (let short_bin_op_e = (fun f _38_14 -> (match (_38_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _38_1883)::[] -> begin
(let _103_1094 = (f fst)
in (FStar_All.pipe_right _103_1094 (fun _103_1093 -> Some (_103_1093))))
end
| _38_1887 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let table = (let op_and_e = (fun e -> (let _103_1100 = (FStar_Absyn_Util.b2t e)
in (_103_1100, FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun e -> (let _103_1104 = (let _103_1103 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _103_1103))
in (_103_1104, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _38_1895) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _38_1901 -> (match (_38_1901) with
| (x, mk) -> begin
if (FStar_Absyn_Syntax.lid_equals x lid) then begin
(let _103_1122 = (mk seen_args)
in Some (_103_1122))
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
| _38_1906 -> begin
None
end))))

let short_circuit_typ = (fun head seen_args -> (let short_bin_op_t = (fun f _38_15 -> (match (_38_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _38_1916)::[] -> begin
(f fst)
end
| _38_1920 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_t = (fun t -> (let _103_1143 = (unlabel t)
in (FStar_All.pipe_right _103_1143 (fun _103_1142 -> FStar_Tc_Rel.NonTrivial (_103_1142)))))
in (let op_or_t = (fun t -> (let _103_1148 = (let _103_1146 = (unlabel t)
in (FStar_All.pipe_right _103_1146 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _103_1148 (fun _103_1147 -> FStar_Tc_Rel.NonTrivial (_103_1147)))))
in (let op_imp_t = (fun t -> (let _103_1152 = (unlabel t)
in (FStar_All.pipe_right _103_1152 (fun _103_1151 -> FStar_Tc_Rel.NonTrivial (_103_1151)))))
in (let short_op_ite = (fun _38_16 -> (match (_38_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _38_1932)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _38_1938)::[] -> begin
(let _103_1156 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _103_1156 (fun _103_1155 -> FStar_Tc_Rel.NonTrivial (_103_1155))))
end
| _38_1943 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _38_1951) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _38_1961; FStar_Absyn_Syntax.pos = _38_1959; FStar_Absyn_Syntax.fvs = _38_1957; FStar_Absyn_Syntax.uvs = _38_1955}) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _38_1969 -> (match (_38_1969) with
| (x, mk) -> begin
if (FStar_Absyn_Syntax.lid_equals x lid) then begin
(let _103_1183 = (mk seen_args)
in Some (_103_1183))
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
| _38_1974 -> begin
FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _103_1197 = (let _103_1196 = (let _103_1195 = (let _103_1194 = (let _103_1193 = (let _103_1192 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _103_1192))
in (_103_1193)::[])
in (ens, _103_1194))
in (FStar_Absyn_Syntax.mk_Typ_app _103_1195 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _103_1196))
in (FStar_Absyn_Syntax.mk_Typ_refine _103_1197 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_38_1984) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _38_1999)::(FStar_Util.Inl (ens), _38_1993)::_38_1989 -> begin
(let _103_1203 = (let _103_1200 = (norm req)
in Some (_103_1200))
in (let _103_1202 = (let _103_1201 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _103_1201))
in (_103_1203, _103_1202)))
end
| _38_2003 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_38_2006) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _38_2021)::(FStar_Util.Inl (wlp), _38_2015)::_38_2011 -> begin
(let _38_2033 = (match ((let _103_1205 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _103_1204 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_103_1205, _103_1204)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _38_2030 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_38_2033) with
| (as_req, as_ens) -> begin
(let req = (let _103_1209 = (let _103_1208 = (let _103_1207 = (let _103_1206 = (FStar_Absyn_Syntax.targ wp)
in (_103_1206)::[])
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), Some (FStar_Absyn_Syntax.Implicit)))::_103_1207)
in (as_req, _103_1208))
in (FStar_Absyn_Syntax.mk_Typ_app _103_1209 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let ens = (let _103_1213 = (let _103_1212 = (let _103_1211 = (let _103_1210 = (FStar_Absyn_Syntax.targ wlp)
in (_103_1210)::[])
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), Some (FStar_Absyn_Syntax.Implicit)))::_103_1211)
in (as_ens, _103_1212))
in (FStar_Absyn_Syntax.mk_Typ_app _103_1213 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _103_1217 = (let _103_1214 = (norm req)
in Some (_103_1214))
in (let _103_1216 = (let _103_1215 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _103_1215))
in (_103_1217, _103_1216)))))
end))
end
| _38_2037 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




