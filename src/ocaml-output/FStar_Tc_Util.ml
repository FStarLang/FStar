
open Prims
let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _154_10 = (FStar_Tc_Env.get_range env)
in (let _154_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _154_10 _154_9))))

let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))

let syn' = (fun env k -> (let _154_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _154_29 k)))

let is_xvar_free : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun x t -> (let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) f.FStar_Absyn_Syntax.fxvs)))

let is_tvar_free : FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun a t -> (let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun) f.FStar_Absyn_Syntax.ftvs)))

let check_and_ascribe : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Tc_Rel.guard_t) = (fun env e t1 t2 -> (let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _154_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _154_52 -> Some (_154_52)) _154_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _154_57 = (let _154_56 = (let _154_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _154_54 = (FStar_Tc_Env.get_range env)
in (_154_55, _154_54)))
in FStar_Absyn_Syntax.Error (_154_56))
in (Prims.raise _154_57))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _154_61 = (let _154_60 = (let _154_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _154_58 = (FStar_Tc_Env.get_range env)
in (_154_59, _154_58)))
in FStar_Absyn_Syntax.Error (_154_60))
in (Prims.raise _154_61))
end
| Some (g) -> begin
(let _52_51 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _154_62))
end else begin
()
end
in (let e = (FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(FStar_Absyn_Syntax.mk_Exp_bvar (FStar_Absyn_Util.bvd_to_bvar_s x.FStar_Absyn_Syntax.v t2) (Some (t2)) e.FStar_Absyn_Syntax.pos)
end
| _52_57 -> begin
(let _52_58 = e
in (let _154_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _52_58.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _154_63; FStar_Absyn_Syntax.pos = _52_58.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _52_58.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _52_58.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))

let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

let as_uvar_e = (fun _52_1 -> (match (_52_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _52_73); FStar_Absyn_Syntax.tk = _52_70; FStar_Absyn_Syntax.pos = _52_68; FStar_Absyn_Syntax.fvs = _52_66; FStar_Absyn_Syntax.uvs = _52_64} -> begin
uv
end
| _52_78 -> begin
(FStar_All.failwith "Impossible")
end))

let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _52_90); FStar_Absyn_Syntax.tk = _52_87; FStar_Absyn_Syntax.pos = _52_85; FStar_Absyn_Syntax.fvs = _52_83; FStar_Absyn_Syntax.uvs = _52_81} -> begin
uv
end
| _52_95 -> begin
(FStar_All.failwith "Impossible")
end))

let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _154_73 = (let _154_72 = (FStar_Tc_Env.get_range env)
in (let _154_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _154_72 _154_71)))
in (FStar_All.pipe_right _154_73 Prims.fst)))

let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _154_80 = (let _154_79 = (FStar_Tc_Env.get_range env)
in (let _154_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _154_79 _154_78 k)))
in (FStar_All.pipe_right _154_80 Prims.fst)))

let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _154_87 = (let _154_86 = (FStar_Tc_Env.get_range env)
in (let _154_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _154_86 _154_85 t)))
in (FStar_All.pipe_right _154_87 Prims.fst)))

let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (let _52_105 = (let _154_93 = (FStar_Tc_Env.get_range env)
in (let _154_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _154_93 _154_92 k)))
in (match (_52_105) with
| (t, u) -> begin
(let _154_95 = (let _154_94 = (as_uvar_t u)
in (_154_94, u.FStar_Absyn_Syntax.pos))
in (t, _154_95))
end)))

let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (let _52_110 = (let _154_101 = (FStar_Tc_Env.get_range env)
in (let _154_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _154_101 _154_100 t)))
in (match (_52_110) with
| (e, u) -> begin
(let _154_103 = (let _154_102 = (as_uvar_e u)
in (_154_102, u.FStar_Absyn_Syntax.pos))
in (e, _154_103))
end)))

let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _154_106 = (let _154_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _154_105))
in (FStar_All.failwith _154_106))
end
| Some (tk) -> begin
tk
end))

let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _52_2 -> (match (_52_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _154_111 = (let _154_110 = (force_tk t)
in FStar_Util.Inl (_154_110))
in (_154_111, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _154_113 = (let _154_112 = (force_tk v)
in FStar_Util.Inr (_154_112))
in (_154_113, imp))
end)))))

let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _52_3 -> (match (_52_3) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _52_129 -> begin
false
end))

let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (let ktop = (let _154_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _154_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (FStar_Tc_Env.get_range env)
in (let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(let imp_follows = (match (args) with
| (_52_145, qual)::_52_143 -> begin
(is_implicit qual)
end
| _52_150 -> begin
false
end)
in (let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _154_136 = (let _154_134 = (let _154_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _154_133))
in (FStar_All.pipe_right _154_134 Prims.fst))
in (FStar_All.pipe_right _154_136 (fun x -> (FStar_Util.Inl (x), (FStar_Absyn_Syntax.as_implicit true)))))
end
| FStar_Util.Inr (x) -> begin
(let _154_140 = (let _154_138 = (let _154_137 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _154_137))
in (FStar_All.pipe_right _154_138 Prims.fst))
in (FStar_All.pipe_right _154_140 (fun x -> (FStar_Util.Inr (x), (FStar_Absyn_Syntax.as_implicit true)))))
end)
in (let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _154_141 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_154_141)::subst)
end
in (let _52_169 = (mk_implicits vars subst brest)
in (match (_52_169) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _154_142 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _154_142))
end
end
| _52_171 -> begin
(let _154_143 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _154_143))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(let _52_174 = (let _154_144 = (FStar_Tc_Env.binders env)
in (mk_implicits _154_144 [] bs))
in (match (_52_174) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_52_176, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_52_181) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _154_145 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _154_145 Prims.fst))
in (let bs = (let _154_146 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _154_146))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _52_188 = (let _154_147 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _154_147))
in ([], bs, kres)))))))
end
| _52_191 -> begin
(let _154_150 = (let _154_149 = (let _154_148 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_154_148, r))
in FStar_Absyn_Syntax.Error (_154_149))
in (Prims.raise _154_150))
end))
in (aux ktop)))))

let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _52_4 -> (match (_52_4) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _52_196 -> begin
false
end))

let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (let pvar_eq = (fun x y -> (match ((x, y)) with
| (FStar_Tc_Env.Binding_var (x, _52_205), FStar_Tc_Env.Binding_var (y, _52_210)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _52_216), FStar_Tc_Env.Binding_typ (y, _52_221)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _52_226 -> begin
false
end))
in (let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _52_5 -> (match (_52_5) with
| FStar_Tc_Env.Binding_var (x, _52_232) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _52_237) -> begin
FStar_Util.Inl (x)
end
| _52_241 -> begin
(FStar_All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _52_248) -> begin
(let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (let _52_254 = (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p [] t)
in (match (_52_254) with
| (e, u) -> begin
(let p = (let _52_255 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _52_255.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_255.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _52_260) -> begin
(let k = (new_kvar env)
in (let _52_266 = (let _154_172 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _154_172 k))
in (match (_52_266) with
| (t, u) -> begin
(let p = (let _52_267 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _52_267.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_267.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inl (t), p))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in ([], [], [], env, FStar_Util.Inr (e), p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _154_174 = (let _154_173 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _154_173))
in FStar_Tc_Env.Binding_var (_154_174))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let b = (let _154_176 = (let _154_175 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _154_175))
in FStar_Tc_Env.Binding_var (_154_176))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _154_178 = (let _154_177 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _154_177))
in FStar_Tc_Env.Binding_typ (_154_178))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _154_180 = (let _154_179 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _154_179))
in FStar_Tc_Env.Binding_typ (_154_180))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _52_326 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _52_304 _52_307 -> (match ((_52_304, _52_307)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _52_314 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_52_314) with
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
in (match (_52_326) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _154_188 = (let _154_187 = (let _154_186 = (let _154_185 = (let _154_184 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _154_183 = (FStar_All.pipe_right args FStar_List.rev)
in (_154_184, _154_183)))
in (FStar_Absyn_Syntax.mk_Exp_app' _154_185 None p.FStar_Absyn_Syntax.p))
in (_154_186, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_154_187))
in (FStar_Absyn_Syntax.mk_Exp_meta _154_188))
in (let _154_191 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _154_190 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _154_189 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_154_191, _154_190, _154_189, env, FStar_Util.Inr (e), (let _52_328 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _52_328.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_328.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_52_331) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let pats = (FStar_List.map (fun _52_343 -> (match (_52_343) with
| (p, imp) -> begin
(let _154_197 = (elaborate_pat env p)
in (_154_197, imp))
end)) pats)
in (let t = (FStar_Tc_Env.lookup_datacon env fv.FStar_Absyn_Syntax.v)
in (let pats = (match ((FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _52_349 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end)
end
| Some (f, _52_352) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _52_365::_52_363) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end
| (_52_371::_52_369, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(let a = (let _154_203 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _154_203 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), (as_imp imp))
end else begin
((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), (as_imp imp))
end)
end
| (FStar_Util.Inr (_52_382), Some (FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in ((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), true))
end
| _52_389 -> begin
(let _154_207 = (let _154_206 = (let _154_205 = (let _154_204 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _154_204))
in (_154_205, (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_154_206))
in (Prims.raise _154_207))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _154_208 = (aux formals' pats')
in ((p, (as_imp imp)))::_154_208)
end
| ((FStar_Util.Inl (_52_417), imp), FStar_Absyn_Syntax.Pat_dot_typ (_52_422)) when allow_implicits -> begin
(let _154_209 = (aux formals' pats')
in ((p, (as_imp imp)))::_154_209)
end
| ((FStar_Util.Inl (_52_426), imp), _52_431) -> begin
(let a = (let _154_210 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _154_210 FStar_Absyn_Syntax.kun))
in (let p1 = if allow_implicits then begin
(FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
end else begin
(FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
end
in (let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_52_436) -> begin
pats'
end
| _52_439 -> begin
pats
end)
in (let _154_211 = (aux formals' pats')
in ((p1, (as_imp imp)))::_154_211))))
end
| ((FStar_Util.Inr (_52_442), Some (FStar_Absyn_Syntax.Implicit)), _52_448) when p_imp -> begin
(let _154_212 = (aux formals' pats')
in ((p, true))::_154_212)
end
| ((FStar_Util.Inr (_52_451), Some (FStar_Absyn_Syntax.Implicit)), _52_457) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let p = (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
in (let _154_213 = (aux formals' pats)
in ((p, true))::_154_213)))
end
| ((FStar_Util.Inr (_52_462), imp), _52_467) -> begin
(let _154_214 = (aux formals' pats')
in ((p, (as_imp imp)))::_154_214)
end)
end))
in (aux f pats))
end)
in (let _52_470 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _52_470.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_470.FStar_Absyn_Syntax.p}))))
end
| _52_473 -> begin
p
end))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _52_485 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_52_485) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _52_488)) -> begin
(let _154_223 = (let _154_222 = (let _154_221 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_154_221, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_154_222))
in (Prims.raise _154_223))
end
| Some (FStar_Tc_Env.Binding_typ (x, _52_494)) -> begin
(let _154_226 = (let _154_225 = (let _154_224 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_154_224, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_154_225))
in (Prims.raise _154_226))
end
| _52_499 -> begin
(b, a, w, arg, p)
end)
end))))
in (let as_arg = (fun _52_6 -> (match (_52_6) with
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
(let _52_521 = (one_pat false env q)
in (match (_52_521) with
| (b, a, _52_518, te, q) -> begin
(let _52_536 = (FStar_List.fold_right (fun p _52_526 -> (match (_52_526) with
| (w, args, pats) -> begin
(let _52_532 = (one_pat false env p)
in (match (_52_532) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _154_240 = (let _154_239 = (let _154_238 = (let _154_236 = (vars_of_bindings a)
in (let _154_235 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _154_236 _154_235)))
in (let _154_237 = (FStar_Tc_Env.get_range env)
in (_154_238, _154_237)))
in FStar_Absyn_Syntax.Error (_154_239))
in (Prims.raise _154_240))
end else begin
(let _154_242 = (let _154_241 = (as_arg arg)
in (_154_241)::args)
in ((FStar_List.append w' w), _154_242, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_52_536) with
| (w, args, pats) -> begin
(let _154_244 = (let _154_243 = (as_arg te)
in (_154_243)::args)
in ((FStar_List.append b w), _154_244, (let _52_537 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _52_537.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_537.FStar_Absyn_Syntax.p})))
end))
end))
end
| _52_540 -> begin
(let _52_548 = (one_pat true env p)
in (match (_52_548) with
| (b, _52_543, _52_545, arg, p) -> begin
(let _154_246 = (let _154_245 = (as_arg arg)
in (_154_245)::[])
in (b, _154_246, p))
end))
end))
in (let _52_552 = (top_level_pat_as_args env p)
in (match (_52_552) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map (fun _52_7 -> (match (_52_7) with
| (FStar_Util.Inl (_52_555), _52_558) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _52_563) -> begin
e
end))))
in (b, exps, p))
end))))))))))

let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (let _154_265 = (FStar_All.pipe_left (fun _154_264 -> Some (_154_264)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _154_265 p.FStar_Absyn_Syntax.p)))
in (let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_52_579), FStar_Absyn_Syntax.Exp_constant (_52_582)) -> begin
(let _154_266 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _154_266))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _52_590 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _154_269 = (let _154_268 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _154_267 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_268 _154_267)))
in (FStar_All.failwith _154_269))
end else begin
()
end
in (let _52_592 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _154_271 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _154_270 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _154_271 _154_270)))
end else begin
()
end
in (let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (let x = (let _52_595 = x
in {FStar_Absyn_Syntax.v = _52_595.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _52_595.FStar_Absyn_Syntax.p})
in (let _154_272 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _154_272))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _52_603 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _154_275 = (let _154_274 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _154_273 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_274 _154_273)))
in (FStar_All.failwith _154_275))
end else begin
()
end
in (let x = (let _52_605 = x
in (let _154_276 = (force_tk e)
in {FStar_Absyn_Syntax.v = _52_605.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _154_276; FStar_Absyn_Syntax.p = _52_605.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _52_610), _52_614) -> begin
(let x = (let _52_616 = x
in (let _154_277 = (force_tk e)
in {FStar_Absyn_Syntax.v = _52_616.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _154_277; FStar_Absyn_Syntax.p = _52_616.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _52_626)) -> begin
(let _52_630 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _154_278 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _154_278))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _52_647); FStar_Absyn_Syntax.tk = _52_644; FStar_Absyn_Syntax.pos = _52_642; FStar_Absyn_Syntax.fvs = _52_640; FStar_Absyn_Syntax.uvs = _52_638}, args)) -> begin
(let _52_655 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _154_279 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _154_279))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _154_286 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _154_286))
end
| (arg::args, (argpat, _52_671)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)), FStar_Absyn_Syntax.Pat_dot_typ (_52_681)) -> begin
(let x = (let _154_287 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _154_287))
in (let q = (let _154_289 = (FStar_All.pipe_left (fun _154_288 -> Some (_154_288)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _154_289 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit)), FStar_Absyn_Syntax.Pat_dot_term (_52_692)) -> begin
(let x = (let _154_290 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _154_290))
in (let q = (let _154_292 = (FStar_All.pipe_left (fun _154_291 -> Some (_154_291)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _154_292 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _52_702) -> begin
(let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _52_710) -> begin
(let pat = (let _154_293 = (aux argpat e)
in (_154_293, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _52_714 -> begin
(let _154_296 = (let _154_295 = (FStar_Absyn_Print.pat_to_string p)
in (let _154_294 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _154_295 _154_294)))
in (FStar_All.failwith _154_296))
end))
in (match_args [] args argpats))))
end
| _52_716 -> begin
(let _154_301 = (let _154_300 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _154_299 = (FStar_Absyn_Print.pat_to_string qq)
in (let _154_298 = (let _154_297 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _154_297 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _154_300 _154_299 _154_298))))
in (FStar_All.failwith _154_301))
end))))
and aux_t = (fun p t0 -> (let pkg = (fun q k -> (let _154_309 = (FStar_All.pipe_left (fun _154_308 -> Some (_154_308)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _154_309 p.FStar_Absyn_Syntax.p)))
in (let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _52_728 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _154_312 = (let _154_311 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _154_310 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_311 _154_310)))
in (FStar_All.failwith _154_312))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _52_735 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _154_315 = (let _154_314 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _154_313 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_314 _154_313)))
in (FStar_All.failwith _154_315))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _52_739), _52_743) -> begin
(let k0 = (force_tk t0)
in (let a = (let _52_746 = a
in {FStar_Absyn_Syntax.v = _52_746.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _52_746.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _52_750 -> begin
(let _154_319 = (let _154_318 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _154_317 = (FStar_Absyn_Print.pat_to_string p)
in (let _154_316 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _154_318 _154_317 _154_316))))
in (FStar_All.failwith _154_319))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _52_754) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (let _154_321 = (FStar_All.pipe_left (fun _154_320 -> Some (_154_320)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _154_321 p.FStar_Absyn_Syntax.p)))
end
| (_52_758, e::[]) -> begin
(aux p e)
end
| _52_763 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.exp) = (fun pat -> (let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _52_770 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun _52_777 -> (match (_52_777) with
| (p, i) -> begin
(let _52_780 = (decorated_pattern_as_either p)
in (match (_52_780) with
| (vars, te) -> begin
(vars, (te, (FStar_Absyn_Syntax.as_implicit i)))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_52_782) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _154_342 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _154_342))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _154_345 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _154_345))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _52_796 = (let _154_346 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _154_346 FStar_List.unzip))
in (match (_52_796) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _154_352 = (let _154_351 = (let _154_350 = (let _154_349 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_154_349, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _154_350))
in (FStar_All.pipe_right _154_351 pkg))
in (vars, _154_352)))
end))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(FStar_All.failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.typ) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (a)) | (FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _154_354 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _154_354))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _52_820 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _52_833 = (decorated_pattern_as_typ p)
in (match (_52_833) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _52_835 -> begin
(let _52_838 = (decorated_pattern_as_exp p)
in (match (_52_838) with
| (vars, e) -> begin
(vars, FStar_Util.Inr (e))
end))
end))

let mk_basic_dtuple_type : FStar_Tc_Env.env  ->  Prims.int  ->  FStar_Absyn_Syntax.typ = (fun env n -> (let r = (FStar_Tc_Env.get_range env)
in (let l = (FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (FStar_Absyn_Util.ftv l k)
in (let vars = (FStar_Tc_Env.binders env)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _52_854; FStar_Absyn_Syntax.pos = _52_852; FStar_Absyn_Syntax.fvs = _52_850; FStar_Absyn_Syntax.uvs = _52_848}) -> begin
(let _52_884 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _52_861 _52_865 -> (match ((_52_861, _52_865)) with
| ((out, subst), (b, _52_864)) -> begin
(match (b) with
| FStar_Util.Inr (_52_867) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _154_362 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_362 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _154_365 = (let _154_364 = (let _154_363 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_363 Prims.fst))
in (bs, _154_364))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_365 (Some (k)) r))
end
| _52_878 -> begin
(FStar_All.failwith "Impossible")
end)
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (((FStar_Absyn_Syntax.targ arg))::out, subst))))
end)
end)) ([], [])))
in (match (_52_884) with
| (args, _52_883) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _52_886 -> begin
(FStar_All.failwith "Impossible")
end)))))))

let extract_lb_annotation : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * Prims.bool) = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _154_376 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _154_376 Prims.fst))
in ((let _52_897 = a
in {FStar_Absyn_Syntax.v = _52_897.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _52_897.FStar_Absyn_Syntax.p}), false))
end
| _52_900 -> begin
(a, true)
end))
in (let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _154_381 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_381 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _52_909) -> begin
(x, false)
end
| _52_912 -> begin
(FStar_All.failwith "impos")
end))
end
| _52_914 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _52_918) -> begin
(x, true)
end
| _52_921 -> begin
(FStar_All.failwith "impos")
end)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _52_927)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _52_934) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _52_963 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _52_944 b -> (match (_52_944) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _52_950 = (mk_t_binder scope a)
in (match (_52_950) with
| (tb, c) -> begin
(let b = (FStar_Util.Inl (tb), (Prims.snd b))
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _52_958 = (mk_v_binder scope x)
in (match (_52_958) with
| (vb, c) -> begin
(let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_52_963) with
| (scope, bs, check) -> begin
(let _52_967 = (aux scope body)
in (match (_52_967) with
| (body, res, check_res) -> begin
(let c = (FStar_Absyn_Util.ml_comp res r)
in (let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (let _52_970 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _154_389 = (FStar_Range.string_of_range r)
in (let _154_388 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _154_389 _154_388)))
end else begin
()
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _52_974 -> begin
(let _154_391 = (let _154_390 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_390 Prims.fst))
in (e, _154_391, false))
end))
in (let _154_392 = (FStar_Tc_Env.t_binders env)
in (aux _154_392 e))))))
end
| _52_976 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (let _52_993 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _52_986)::(FStar_Util.Inl (wlp), _52_981)::[] -> begin
(wp, wlp)
end
| _52_990 -> begin
(let _154_397 = (let _154_396 = (let _154_395 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _154_395 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _154_396))
in (FStar_All.failwith _154_397))
end)
in (match (_52_993) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (let _52_1001 = (destruct_comp c)
in (match (_52_1001) with
| (_52_998, wp, wlp) -> begin
(let _154_419 = (let _154_418 = (let _154_414 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _154_414))
in (let _154_417 = (let _154_416 = (let _154_415 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _154_415))
in (_154_416)::[])
in (_154_418)::_154_417))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _154_419; FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_52_1009, c) -> begin
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
(let _52_1023 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.lident = (fun env l1 l2 -> (let _52_1034 = (let _154_433 = (norm_eff_name env l1)
in (let _154_432 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _154_433 _154_432)))
in (match (_52_1034) with
| (m, _52_1031, _52_1033) -> begin
m
end)))

let join_lcomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Ident.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Ident.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)

let lift_and_destruct : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  ((FStar_Absyn_Syntax.eff_decl * FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ)) = (fun env c1 c2 -> (let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _52_1046 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_52_1046) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_Tc_Env.get_effect_decl env m)
in (let _52_1052 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_52_1052) with
| (a, kwp) -> begin
(let _154_447 = (destruct_comp m1)
in (let _154_446 = (destruct_comp m2)
in ((md, a, kwp), _154_447, _154_446)))
end)))))
end)))))

let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun md result wp wlp flags -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = ((FStar_Absyn_Syntax.targ wp))::((FStar_Absyn_Syntax.targ wlp))::[]; FStar_Absyn_Syntax.flags = flags}))

let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _52_1066 -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (let _52_1069 = lc
in (let _154_475 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _52_1069.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _154_475; FStar_Absyn_Syntax.cflags = _52_1069.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _52_1071 -> (match (()) with
| () -> begin
(let _154_474 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _154_474))
end))})))

let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _154_478 = (FStar_Absyn_Util.compress_typ t)
in _154_478.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_52_1074) -> begin
true
end
| _52_1077 -> begin
false
end))

let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp = (fun env t v -> (let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _52_1086 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_52_1086) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _154_485 = (FStar_Absyn_Syntax.mk_Typ_app (m.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.varg v))::[]) (Some (k)) v.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _154_485))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _52_1091 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _154_488 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _154_487 = (FStar_Absyn_Print.exp_to_string v)
in (let _154_486 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _154_488 _154_487 _154_486))))
end else begin
()
end
in c)))

let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _52_1098 -> (match (_52_1098) with
| (b, lc2) -> begin
(let _52_1109 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _52_1102)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _52_1107 -> begin
"??"
end)
in (let _154_498 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _154_497 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _154_498 bstr _154_497))))
end else begin
()
end
in (let bind_it = (fun _52_1112 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun _52_1116 -> (match (()) with
| () -> begin
(let aux = (fun _52_1118 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_52_1121)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_52_1125)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _52_1129 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _52_1134))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _154_506 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _154_505 -> Some (_154_505)) _154_506))
end else begin
(aux ())
end
end
| _52_1140 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _52_1158 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _154_510 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _52_1146)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _52_1152)) -> begin
(FStar_Absyn_Print.sli l)
end
| _52_1157 -> begin
"Something else"
end)
in (let _154_509 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _154_508 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _154_507 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _154_510 _154_509 _154_508 _154_507)))))
end else begin
()
end
in c)
end
| None -> begin
(let _52_1173 = (lift_and_destruct env c1 c2)
in (match (_52_1173) with
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
| _52_1186 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (let wp_args = (let _154_521 = (let _154_520 = (let _154_519 = (let _154_518 = (let _154_517 = (let _154_513 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _154_513))
in (let _154_516 = (let _154_515 = (let _154_514 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _154_514))
in (_154_515)::[])
in (_154_517)::_154_516))
in ((FStar_Absyn_Syntax.targ wlp1))::_154_518)
in ((FStar_Absyn_Syntax.targ wp1))::_154_519)
in ((FStar_Absyn_Syntax.targ t2))::_154_520)
in ((FStar_Absyn_Syntax.targ t1))::_154_521)
in (let wlp_args = (let _154_526 = (let _154_525 = (let _154_524 = (let _154_523 = (let _154_522 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _154_522))
in (_154_523)::[])
in ((FStar_Absyn_Syntax.targ wlp1))::_154_524)
in ((FStar_Absyn_Syntax.targ t2))::_154_525)
in ((FStar_Absyn_Syntax.targ t1))::_154_526)
in (let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wp, wp_args) None t2.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _154_527 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _154_527; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let _52_1204 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_52_1204) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (mk_wp, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (mk_wlp, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.FStar_Absyn_Syntax.pos)
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))

let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (let refresh = (fun _52_1213 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_52_1216) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _52_1220 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _154_549 = (let _154_548 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _154_548))
in (FStar_Util.print1 "Refreshing label at %s\n" _154_549))
end else begin
()
end
in (let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_1223 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _154_552 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _154_551 = (let _154_550 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _154_550))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _154_552 _154_551)))
end else begin
()
end
in (let _52_1228 = (destruct_comp c')
in (match (_52_1228) with
| (t, wp, wlp) -> begin
(let wp = (let _154_555 = (let _154_554 = (let _154_553 = (FStar_Tc_Env.get_range env)
in (wp, Some (b), _154_553))
in FStar_Absyn_Syntax.Meta_refresh_label (_154_554))
in (FStar_Absyn_Syntax.mk_Typ_meta _154_555))
in (let wlp = (let _154_558 = (let _154_557 = (let _154_556 = (FStar_Tc_Env.get_range env)
in (wlp, Some (b), _154_556))
in FStar_Absyn_Syntax.Meta_refresh_label (_154_557))
in (FStar_Absyn_Syntax.mk_Typ_meta _154_558))
in (FStar_Absyn_Syntax.mk_Comp (let _52_1231 = c'
in {FStar_Absyn_Syntax.effect_name = _52_1231.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _52_1231.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = ((FStar_Absyn_Syntax.targ wp))::((FStar_Absyn_Syntax.targ wlp))::[]; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))))
end)))))
end)
end)
end))
in (let _52_1233 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1233.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1233.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _52_1233.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _154_582 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _154_582)) then begin
f
end else begin
(let _154_583 = (reason ())
in (label _154_583 r f))
end
end))

let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _154_590 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_154_590))
end))

let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _52_1260 -> begin
g2
end))

let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (let weaken = (fun _52_1265 -> (match (()) with
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
in (let _52_1274 = (destruct_comp c)
in (match (_52_1274) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (let _52_1278 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1278.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1278.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _52_1278.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _52_8 -> (match (_52_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _52_1289 -> begin
[]
end))))
in (let strengthen = (fun _52_1292 -> (match (()) with
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
in (let xret = (let _154_624 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _154_624))
in (let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (let lc = (let _154_627 = (lcomp_of_comp c)
in (let _154_626 = (let _154_625 = (lcomp_of_comp xret)
in (Some (xbinding), _154_625))
in (bind env (Some (e)) _154_627 _154_626)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_1307 = (destruct_comp c)
in (match (_52_1307) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (let _154_633 = (let _154_632 = (let _154_631 = (let _154_630 = (let _154_629 = (let _154_628 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _154_628 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_629))
in (_154_630)::((FStar_Absyn_Syntax.targ wp))::[])
in ((FStar_Absyn_Syntax.targ res_t))::_154_631)
in (md.FStar_Absyn_Syntax.assert_p, _154_632))
in (FStar_Absyn_Syntax.mk_Typ_app _154_633 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _154_637 = (let _52_1312 = lc
in (let _154_636 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _154_635 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _154_634 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _154_634))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _154_636; FStar_Absyn_Syntax.res_typ = _52_1312.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _154_635; FStar_Absyn_Syntax.comp = strengthen})))
in (_154_637, (let _52_1314 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _52_1314.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_1314.FStar_Tc_Rel.implicits})))))
end)

let add_equality_to_post_condition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env comp res_t -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let y = (FStar_Absyn_Util.gen_bvar res_t)
in (let _52_1324 = (let _154_645 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _154_644 = (FStar_Absyn_Util.bvar_to_exp y)
in (_154_645, _154_644)))
in (match (_52_1324) with
| (xexp, yexp) -> begin
(let yret = (FStar_Absyn_Syntax.mk_Typ_app (md_pure.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.varg yexp))::[]) None res_t.FStar_Absyn_Syntax.pos)
in (let x_eq_y_yret = (let _154_652 = (let _154_651 = (let _154_650 = (let _154_649 = (let _154_646 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_646))
in (let _154_648 = (let _154_647 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_154_647)::[])
in (_154_649)::_154_648))
in ((FStar_Absyn_Syntax.targ res_t))::_154_650)
in (md_pure.FStar_Absyn_Syntax.assume_p, _154_651))
in (FStar_Absyn_Syntax.mk_Typ_app _154_652 None res_t.FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _154_658 = (let _154_657 = (let _154_656 = (let _154_655 = (let _154_654 = (let _154_653 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder y))::[], x_eq_y_yret) None res_t.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_653))
in (_154_654)::[])
in ((FStar_Absyn_Syntax.targ res_t))::_154_655)
in ((FStar_Absyn_Syntax.targ res_t))::_154_656)
in (md_pure.FStar_Absyn_Syntax.close_wp, _154_657))
in (FStar_Absyn_Syntax.mk_Typ_app _154_658 None res_t.FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _154_661 = (lcomp_of_comp comp)
in (let _154_660 = (let _154_659 = (lcomp_of_comp lc2)
in (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), _154_659))
in (bind env None _154_661 _154_660)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _52_1335 -> (match (()) with
| () -> begin
(let _52_1351 = (let _154_673 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _154_672 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _154_673 _154_672)))
in (match (_52_1351) with
| ((md, _52_1338, _52_1340), (res_t, wp_then, wlp_then), (_52_1347, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _154_684 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.if_then_else, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ g))::((FStar_Absyn_Syntax.targ wp_t))::((FStar_Absyn_Syntax.targ wp_e))::[]) None _154_684)))
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
in (let _154_685 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _154_685; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))

let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _52_1374 -> (match (_52_1374) with
| (_52_1372, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun _52_1377 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _154_706 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.if_then_else, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ g))::((FStar_Absyn_Syntax.targ wp_t))::((FStar_Absyn_Syntax.targ wp_e))::[]) None _154_706)))
in (let default_case = (let post_k = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_v_binder res_t))::[], FStar_Absyn_Syntax.ktype) res_t.FStar_Absyn_Syntax.pos)
in (let kwp = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder post_k))::[], FStar_Absyn_Syntax.ktype) res_t.FStar_Absyn_Syntax.pos)
in (let post = (let _154_707 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _154_707 post_k))
in (let wp = (let _154_712 = (let _154_711 = (let _154_710 = (let _154_708 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _154_708))
in (let _154_709 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _154_710 _154_709)))
in (((FStar_Absyn_Syntax.t_binder post))::[], _154_711))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_712 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let wlp = (let _154_714 = (let _154_713 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (((FStar_Absyn_Syntax.t_binder post))::[], _154_713))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_714 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _52_1393 celse -> (match (_52_1393) with
| (g, cthen) -> begin
(let _52_1411 = (let _154_717 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _154_717 celse))
in (match (_52_1411) with
| ((md, _52_1397, _52_1399), (_52_1402, wp_then, wlp_then), (_52_1407, wp_else, wlp_else)) -> begin
(let _154_719 = (ifthenelse md res_t g wp_then wp_else)
in (let _154_718 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _154_719 _154_718 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (let _52_1419 = (destruct_comp comp)
in (match (_52_1419) with
| (_52_1416, wp, wlp) -> begin
(let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wlp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (let close = (fun _52_1426 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bindings wp0 -> (FStar_List.fold_right (fun b wp -> (match (b) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let bs = (let _154_738 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_154_738)::[])
in (let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.close_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ wp))::[]) None wp0.FStar_Absyn_Syntax.pos)))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let bs = (let _154_739 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_154_739)::[])
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
in (let _52_1457 = (destruct_comp c)
in (match (_52_1457) with
| (t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.FStar_Absyn_Syntax.result_typ wp wlp c.FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (let _52_1461 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1461.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1461.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _52_1461.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (let refine = (fun _52_1467 -> (match (()) with
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
in (let ret = (let _154_748 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _154_748))
in (let eq_ret = (let _154_750 = (let _154_749 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_154_749))
in (weaken_precondition env ret _154_750))
in (let _154_753 = (let _154_752 = (let _154_751 = (lcomp_of_comp c)
in (bind env None _154_751 (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_154_752.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _154_753 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
end
end)
end))
in (let flags = if (((not ((FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.FStar_Absyn_Syntax.cflags
end else begin
lc.FStar_Absyn_Syntax.cflags
end
in (let _52_1477 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1477.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1477.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _154_765 = (let _154_764 = (let _154_763 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _154_762 = (FStar_Tc_Env.get_range env)
in (_154_763, _154_762)))
in FStar_Absyn_Syntax.Error (_154_764))
in (Prims.raise _154_765))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_instantiate_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.implicits) = (fun env t k -> (let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(t, k, [])
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let rec aux = (fun subst _52_9 -> (match (_52_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1507 = (new_implicit_tvar env k)
in (match (_52_1507) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _52_1513 = (aux subst rest)
in (match (_52_1513) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inl (u))::us)
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1524 = (new_implicit_evar env t)
in (match (_52_1524) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _52_1530 = (aux subst rest)
in (match (_52_1530) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inr (v), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _52_1536 = (aux [] bs)
in (match (_52_1536) with
| (args, bs, subst, implicits) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _154_776 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_154_776, k, implicits))))
end)))
end
| _52_1540 -> begin
(t, k, [])
end)
end))

let maybe_instantiate : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.implicits) = (fun env e t -> (let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let rec aux = (fun subst _52_10 -> (match (_52_10) with
| (FStar_Util.Inl (a), _52_1556)::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1562 = (new_implicit_tvar env k)
in (match (_52_1562) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _52_1568 = (aux subst rest)
in (match (_52_1568) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inl (u))::us)
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1579 = (new_implicit_evar env t)
in (match (_52_1579) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _52_1585 = (aux subst rest)
in (match (_52_1585) with
| (args, bs, subst, us) -> begin
(((FStar_Util.Inr (v), Some (FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (FStar_Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _52_1591 = (aux [] bs)
in (match (_52_1591) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _52_1598 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _154_793 = (mk_exp_app e args (Some (t)))
in (_154_793, t, implicits)))
end else begin
(e, t, [])
end
end
| _52_1602 -> begin
(let t = (let _154_794 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _154_794 (FStar_Absyn_Util.subst_typ subst)))
in (let _154_795 = (mk_exp_app e args (Some (t)))
in (_154_795, t, implicits)))
end))
end)))
end
| _52_1605 -> begin
(e, t, [])
end)
end))

let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _154_804 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_154_804, false))
end else begin
(let _154_805 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_154_805, true))
end
in (match (gopt) with
| (None, _52_1613) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(let lc = (let _52_1621 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1621.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _52_1621.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _52_1621.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _52_1626 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _52_1626.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_1626.FStar_Tc_Rel.implicits})
in (let strengthen = (fun _52_1630 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let _52_1632 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _154_809 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _154_808 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _154_809 _154_808)))
end else begin
()
end
in (let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_1637 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_52_1637) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (let x = (FStar_Absyn_Util.new_bvd None)
in (let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.varg xexp))::[]) (Some (k)) xexp.FStar_Absyn_Syntax.pos)
in (let cret = (let _154_810 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _154_810))
in (let guard = if apply_guard then begin
(FStar_Absyn_Syntax.mk_Typ_app (f, ((FStar_Absyn_Syntax.varg xexp))::[]) (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos)
end else begin
f
end
in (let _52_1647 = (let _154_818 = (FStar_All.pipe_left (fun _154_815 -> Some (_154_815)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _154_817 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _154_816 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _154_818 _154_817 e cret _154_816))))
in (match (_52_1647) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _154_820 = (let _154_819 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _154_819))
in (bind env (Some (e)) _154_820 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.FStar_Absyn_Syntax.comp ())
in (let _52_1650 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _154_821 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _154_821))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _52_11 -> (match (_52_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _52_1656 -> begin
[]
end))))
in (let lc = (let _52_1658 = lc
in (let _154_823 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _154_823; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(let ue = (let _154_828 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _154_828))
in (let ut = (let _154_829 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _154_829))
in (let uk = (let _154_830 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _154_830))
in (let union = (FStar_String.concat "," (FStar_List.append (FStar_List.append ue ut) uk))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _52_1670 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _52_1672 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _52_1674 = (let _154_832 = (let _154_831 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _154_831))
in (FStar_Tc_Errors.report r _154_832))
in (let _52_1676 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))

let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _154_840 = (FStar_Util.for_all (fun _52_1684 -> (match (_52_1684) with
| (_52_1682, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _154_840)) then begin
None
end else begin
(let norm = (fun c -> (let _52_1687 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _154_843 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _154_843))
end else begin
()
end
in (let steps = (FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
in (let c = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::[]) env c)
end
in (let _52_1691 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _154_844 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _154_844))
end else begin
()
end
in c)))))
in (let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _154_847 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _154_847 FStar_Util.set_elements)))
in (let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _52_1700) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _52_12 -> (match (_52_12) with
| (FStar_Util.Inl (_52_1705), _52_1708) -> begin
true
end
| _52_1711 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _52_1713 -> begin
true
end))
in (let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _52_1716 -> (match (_52_1716) with
| (e, c) -> begin
(let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _154_852 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _154_852)) then begin
([], e, c)
end else begin
(let c = (norm c)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.FStar_Absyn_Syntax.result_typ
in (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.FStar_Absyn_Syntax.uvars_t)
in (let _52_1732 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _154_853 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _154_853))) then begin
(let _52_1728 = (destruct_comp ct)
in (match (_52_1728) with
| (_52_1724, wp, _52_1727) -> begin
(let binder = ((FStar_Absyn_Syntax.null_v_binder t))::[]
in (let post = (let _154_857 = (let _154_854 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _154_854))
in (let _154_856 = (let _154_855 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_154_855))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_857 _154_856 t.FStar_Absyn_Syntax.pos)))
in (let vc = (let _154_860 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) (FStar_Absyn_Syntax.mk_Typ_app (wp, ((FStar_Absyn_Syntax.targ post))::[])))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _154_860))
in (let _154_861 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _154_861)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _52_1738 -> (match (_52_1738) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _52_1741 -> (match (_52_1741) with
| (u, k) -> begin
(let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_52_1779) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _52_1782 -> begin
(let a = (let _154_866 = (let _154_865 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _154_864 -> Some (_154_864)) _154_865))
in (FStar_Absyn_Util.new_bvd _154_866))
in (let t = (let _154_867 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _154_867 k))
in (let _52_1785 = (FStar_Absyn_Util.unchecked_unify u t)
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
| _52_1796 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _52_1800 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _154_868 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _154_868)))))
end))))
in Some (ecs)))))))
end)

let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (let _52_1812 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _154_877 = (let _154_876 = (FStar_List.map (fun _52_1811 -> (match (_52_1811) with
| (lb, _52_1808, _52_1810) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _154_876 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _154_877))
end else begin
()
end
in (match ((let _154_879 = (FStar_All.pipe_right lecs (FStar_List.map (fun _52_1818 -> (match (_52_1818) with
| (_52_1815, e, c) -> begin
(e, c)
end))))
in (gen verify env _154_879))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _52_1827 _52_1830 -> (match ((_52_1827, _52_1830)) with
| ((l, _52_1824, _52_1826), (e, c)) -> begin
(let _52_1831 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _154_884 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _154_883 = (FStar_Absyn_Print.lbname_to_string l)
in (let _154_882 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _154_884 _154_883 _154_882))))
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
| _52_1836 -> begin
false
end))

let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (let discharge = (fun g -> (let _52_1842 = (FStar_Tc_Rel.try_discharge_guard env g)
in (let _52_1860 = (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _52_13 -> (match (_52_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _52_1849) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_52_1853, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _52_1859 -> begin
()
end)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _154_896 = (discharge g)
in (let _154_895 = (lc.FStar_Absyn_Syntax.comp ())
in (_154_896, _154_895)))
end else begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _154_897 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _154_897 FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let _52_1871 = (destruct_comp c)
in (match (_52_1871) with
| (t, wp, _52_1870) -> begin
(let vc = (let _154_898 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.trivial, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ wp))::[]) (Some (FStar_Absyn_Syntax.ktype)) _154_898))
in (let g = (let _154_899 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _154_899))
in (let _154_901 = (discharge g)
in (let _154_900 = (FStar_Absyn_Syntax.mk_Comp c)
in (_154_901, _154_900)))))
end))))))
end)))

let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (let short_bin_op_e = (fun f _52_14 -> (match (_52_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _52_1883)::[] -> begin
(let _154_920 = (f fst)
in (FStar_All.pipe_right _154_920 (fun _154_919 -> Some (_154_919))))
end
| _52_1887 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let table = (let op_and_e = (fun e -> (let _154_926 = (FStar_Absyn_Util.b2t e)
in (_154_926, FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun e -> (let _154_930 = (let _154_929 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _154_929))
in (_154_930, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _52_1895) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _52_1901 -> (match (_52_1901) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _154_948 = (mk seen_args)
in Some (_154_948))
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
| _52_1906 -> begin
None
end))))

let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (let short_bin_op_t = (fun f _52_15 -> (match (_52_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _52_1916)::[] -> begin
(f fst)
end
| _52_1920 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_t = (fun t -> (let _154_969 = (unlabel t)
in (FStar_All.pipe_right _154_969 (fun _154_968 -> FStar_Tc_Rel.NonTrivial (_154_968)))))
in (let op_or_t = (fun t -> (let _154_974 = (let _154_972 = (unlabel t)
in (FStar_All.pipe_right _154_972 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _154_974 (fun _154_973 -> FStar_Tc_Rel.NonTrivial (_154_973)))))
in (let op_imp_t = (fun t -> (let _154_978 = (unlabel t)
in (FStar_All.pipe_right _154_978 (fun _154_977 -> FStar_Tc_Rel.NonTrivial (_154_977)))))
in (let short_op_ite = (fun _52_16 -> (match (_52_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _52_1932)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _52_1938)::[] -> begin
(let _154_982 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _154_982 (fun _154_981 -> FStar_Tc_Rel.NonTrivial (_154_981))))
end
| _52_1943 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _52_1951) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _52_1961; FStar_Absyn_Syntax.pos = _52_1959; FStar_Absyn_Syntax.fvs = _52_1957; FStar_Absyn_Syntax.uvs = _52_1955}) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _52_1969 -> (match (_52_1969) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _154_1009 = (mk seen_args)
in Some (_154_1009))
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
| _52_1974 -> begin
FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _154_1023 = (let _154_1022 = (let _154_1021 = (let _154_1020 = (let _154_1019 = (let _154_1018 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _154_1018))
in (_154_1019)::[])
in (ens, _154_1020))
in (FStar_Absyn_Syntax.mk_Typ_app _154_1021 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _154_1022))
in (FStar_Absyn_Syntax.mk_Typ_refine _154_1023 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_52_1984) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _52_1999)::(FStar_Util.Inl (ens), _52_1993)::_52_1989 -> begin
(let _154_1029 = (let _154_1026 = (norm req)
in Some (_154_1026))
in (let _154_1028 = (let _154_1027 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _154_1027))
in (_154_1029, _154_1028)))
end
| _52_2003 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_52_2006) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _52_2021)::(FStar_Util.Inl (wlp), _52_2015)::_52_2011 -> begin
(let _52_2033 = (match ((let _154_1031 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _154_1030 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_154_1031, _154_1030)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _52_2030 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_52_2033) with
| (as_req, as_ens) -> begin
(let req = (FStar_Absyn_Syntax.mk_Typ_app (as_req, ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Absyn_Syntax.targ wp))::[]) (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let ens = (FStar_Absyn_Syntax.mk_Typ_app (as_ens, ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Absyn_Syntax.targ wlp))::[]) None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let _154_1035 = (let _154_1032 = (norm req)
in Some (_154_1032))
in (let _154_1034 = (let _154_1033 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _154_1033))
in (_154_1035, _154_1034)))))
end))
end
| _52_2037 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




