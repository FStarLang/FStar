
open Prims
# 35 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

# 36 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _154_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report (FStar_Tc_Env.get_range env) _154_9)))

# 40 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

# 42 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))

# 45 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let syn' = (fun env k -> (FStar_Absyn_Syntax.syn (FStar_Tc_Env.get_range env) k))

# 47 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let is_xvar_free : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun x t -> (let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) f.FStar_Absyn_Syntax.fxvs)))

# 51 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let is_tvar_free : FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun a t -> (let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun) f.FStar_Absyn_Syntax.ftvs)))

# 55 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let check_and_ascribe : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Tc_Rel.guard_t) = (fun env e t1 t2 -> (let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _154_51 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _154_50 -> Some (_154_50)) _154_51))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _154_54 = (let _154_53 = (let _154_52 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (_154_52, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_154_53))
in (Prims.raise _154_54))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _154_57 = (let _154_56 = (let _154_55 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (_154_55, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_154_56))
in (Prims.raise _154_57))
end
| Some (g) -> begin
(let _52_51 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_58 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _154_58))
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
in (let _154_59 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _52_58.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _154_59; FStar_Absyn_Syntax.pos = _52_58.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _52_58.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _52_58.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))

# 79 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let env_binders : FStar_Tc_Env.env  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, FStar_Absyn_Syntax.bvvar) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

# 84 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let as_uvar_e = (fun _52_1 -> (match (_52_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _52_73); FStar_Absyn_Syntax.tk = _52_70; FStar_Absyn_Syntax.pos = _52_68; FStar_Absyn_Syntax.fvs = _52_66; FStar_Absyn_Syntax.uvs = _52_64} -> begin
uv
end
| _52_78 -> begin
(FStar_All.failwith "Impossible")
end))

# 87 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _52_90); FStar_Absyn_Syntax.tk = _52_87; FStar_Absyn_Syntax.pos = _52_85; FStar_Absyn_Syntax.fvs = _52_83; FStar_Absyn_Syntax.uvs = _52_81} -> begin
uv
end
| _52_95 -> begin
(FStar_All.failwith "Impossible")
end))

# 90 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let new_kvar : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env -> (let _154_68 = (let _154_67 = (env_binders env)
in (FStar_Tc_Rel.new_kvar (FStar_Tc_Env.get_range env) _154_67))
in (FStar_All.pipe_right _154_68 Prims.fst)))

# 91 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env k -> (let _154_74 = (let _154_73 = (env_binders env)
in (FStar_Tc_Rel.new_tvar (FStar_Tc_Env.get_range env) _154_73 k))
in (FStar_All.pipe_right _154_74 Prims.fst)))

# 92 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _154_80 = (let _154_79 = (env_binders env)
in (FStar_Tc_Rel.new_evar (FStar_Tc_Env.get_range env) _154_79 t))
in (FStar_All.pipe_right _154_80 Prims.fst)))

# 93 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (let _52_105 = (let _154_85 = (env_binders env)
in (FStar_Tc_Rel.new_tvar (FStar_Tc_Env.get_range env) _154_85 k))
in (match (_52_105) with
| (t, u) -> begin
(let _154_87 = (let _154_86 = (as_uvar_t u)
in (_154_86, u.FStar_Absyn_Syntax.pos))
in (t, _154_87))
end)))

# 96 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (let _52_110 = (let _154_92 = (env_binders env)
in (FStar_Tc_Rel.new_evar (FStar_Tc_Env.get_range env) _154_92 t))
in (match (_52_110) with
| (e, u) -> begin
(let _154_94 = (let _154_93 = (as_uvar_e u)
in (_154_93, u.FStar_Absyn_Syntax.pos))
in (e, _154_94))
end)))

# 99 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _154_97 = (let _154_96 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _154_96))
in (FStar_All.failwith _154_97))
end
| Some (tk) -> begin
tk
end))

# 102 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let tks_of_args : FStar_Absyn_Syntax.args  ->  (((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _52_2 -> (match (_52_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _154_102 = (let _154_101 = (force_tk t)
in FStar_Util.Inl (_154_101))
in (_154_102, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _154_104 = (let _154_103 = (force_tk v)
in FStar_Util.Inr (_154_103))
in (_154_104, imp))
end)))))

# 107 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _52_3 -> (match (_52_3) with
| Some (FStar_Absyn_Syntax.Implicit (_52_127)) -> begin
true
end
| _52_131 -> begin
false
end))

# 108 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.args  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (let ktop = (let _154_115 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _154_115 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (FStar_Tc_Env.get_range env)
in (let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(let imp_follows = (match (args) with
| (_52_147, qual)::_52_145 -> begin
(is_implicit qual)
end
| _52_152 -> begin
false
end)
in (let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _154_127 = (let _154_125 = (let _154_124 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _154_124))
in (FStar_All.pipe_right _154_125 Prims.fst))
in (FStar_All.pipe_right _154_127 (fun x -> (FStar_Util.Inl (x), (FStar_Absyn_Syntax.as_implicit true)))))
end
| FStar_Util.Inr (x) -> begin
(let _154_131 = (let _154_129 = (let _154_128 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _154_128))
in (FStar_All.pipe_right _154_129 Prims.fst))
in (FStar_All.pipe_right _154_131 (fun x -> (FStar_Util.Inr (x), (FStar_Absyn_Syntax.as_implicit true)))))
end)
in (let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _154_132 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_154_132)::subst)
end
in (let _52_171 = (mk_implicits vars subst brest)
in (match (_52_171) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _154_133 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _154_133))
end
end
| _52_173 -> begin
(let _154_134 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _154_134))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(let _52_176 = (let _154_135 = (FStar_Tc_Env.binders env)
in (mk_implicits _154_135 [] bs))
in (match (_52_176) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_52_178, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_52_183) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _154_136 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _154_136 Prims.fst))
in (let bs = (let _154_137 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _154_137))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _52_190 = (let _154_138 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _154_138))
in ([], bs, kres)))))))
end
| _52_193 -> begin
(let _154_141 = (let _154_140 = (let _154_139 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_154_139, r))
in FStar_Absyn_Syntax.Error (_154_140))
in (Prims.raise _154_141))
end))
in (aux ktop)))))

# 147 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _52_4 -> (match (_52_4) with
| Some (FStar_Absyn_Syntax.Implicit (_52_196)) -> begin
true
end
| _52_200 -> begin
false
end))

# 153 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (let pvar_eq = (fun x y -> (match ((x, y)) with
| (FStar_Tc_Env.Binding_var (x, _52_209), FStar_Tc_Env.Binding_var (y, _52_214)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _52_220), FStar_Tc_Env.Binding_typ (y, _52_225)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _52_230 -> begin
false
end))
in (let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _52_5 -> (match (_52_5) with
| FStar_Tc_Env.Binding_var (x, _52_236) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _52_241) -> begin
FStar_Util.Inl (x)
end
| _52_245 -> begin
(FStar_All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _52_252) -> begin
(let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (let _52_258 = (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p [] t)
in (match (_52_258) with
| (e, u) -> begin
(let p = (let _52_259 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _52_259.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_259.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _52_264) -> begin
(let k = (new_kvar env)
in (let _52_270 = (let _154_163 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _154_163 k))
in (match (_52_270) with
| (t, u) -> begin
(let p = (let _52_271 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _52_271.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_271.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inl (t), p))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in ([], [], [], env, FStar_Util.Inr (e), p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _154_165 = (let _154_164 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _154_164))
in FStar_Tc_Env.Binding_var (_154_165))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let b = (let _154_167 = (let _154_166 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _154_166))
in FStar_Tc_Env.Binding_var (_154_167))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _154_169 = (let _154_168 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _154_168))
in FStar_Tc_Env.Binding_typ (_154_169))
in (let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _154_171 = (let _154_170 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _154_170))
in FStar_Tc_Env.Binding_typ (_154_171))
in (let env = (FStar_Tc_Env.push_local_binding env b)
in (let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _52_330 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _52_308 _52_311 -> (match ((_52_308, _52_311)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _52_318 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_52_318) with
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
in (match (_52_330) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _154_179 = (let _154_178 = (let _154_177 = (let _154_176 = (let _154_175 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _154_174 = (FStar_All.pipe_right args FStar_List.rev)
in (_154_175, _154_174)))
in (FStar_Absyn_Syntax.mk_Exp_app' _154_176 None p.FStar_Absyn_Syntax.p))
in (_154_177, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_154_178))
in (FStar_Absyn_Syntax.mk_Exp_meta _154_179))
in (let _154_182 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _154_181 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _154_180 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_154_182, _154_181, _154_180, env, FStar_Util.Inr (e), (let _52_332 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _52_332.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_332.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_52_335) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let pats = (FStar_List.map (fun _52_347 -> (match (_52_347) with
| (p, imp) -> begin
(let _154_188 = (elaborate_pat env p)
in (_154_188, imp))
end)) pats)
in (let t = (FStar_Tc_Env.lookup_datacon env fv.FStar_Absyn_Syntax.v)
in (let pats = (match ((FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _52_353 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end)
end
| Some (f, _52_356) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _52_369::_52_367) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end
| (_52_375::_52_373, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(let a = (let _154_194 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _154_194 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), (as_imp imp))
end else begin
((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), (as_imp imp))
end)
end
| (FStar_Util.Inr (_52_386), Some (FStar_Absyn_Syntax.Implicit (_52_389))) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in ((FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)), true))
end
| _52_395 -> begin
(let _154_198 = (let _154_197 = (let _154_196 = (let _154_195 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _154_195))
in (_154_196, (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_154_197))
in (Prims.raise _154_198))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _154_199 = (aux formals' pats')
in ((p, (as_imp imp)))::_154_199)
end
| ((FStar_Util.Inl (_52_423), imp), FStar_Absyn_Syntax.Pat_dot_typ (_52_428)) when allow_implicits -> begin
(let _154_200 = (aux formals' pats')
in ((p, (as_imp imp)))::_154_200)
end
| ((FStar_Util.Inl (_52_432), imp), _52_437) -> begin
(let a = (let _154_201 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _154_201 FStar_Absyn_Syntax.kun))
in (let p1 = if allow_implicits then begin
(FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
end else begin
(FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
end
in (let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_52_442) -> begin
pats'
end
| _52_445 -> begin
pats
end)
in (let _154_202 = (aux formals' pats')
in ((p1, (as_imp imp)))::_154_202))))
end
| ((FStar_Util.Inr (_52_448), Some (FStar_Absyn_Syntax.Implicit (_52_451))), _52_456) when p_imp -> begin
(let _154_203 = (aux formals' pats')
in ((p, true))::_154_203)
end
| ((FStar_Util.Inr (_52_459), Some (FStar_Absyn_Syntax.Implicit (_52_462))), _52_467) -> begin
(let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let p = (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v))
in (let _154_204 = (aux formals' pats)
in ((p, true))::_154_204)))
end
| ((FStar_Util.Inr (_52_472), imp), _52_477) -> begin
(let _154_205 = (aux formals' pats')
in ((p, (as_imp imp)))::_154_205)
end)
end))
in (aux f pats))
end)
in (let _52_480 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _52_480.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_480.FStar_Absyn_Syntax.p}))))
end
| _52_483 -> begin
p
end))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _52_495 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_52_495) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _52_498)) -> begin
(let _154_214 = (let _154_213 = (let _154_212 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_154_212, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_154_213))
in (Prims.raise _154_214))
end
| Some (FStar_Tc_Env.Binding_typ (x, _52_504)) -> begin
(let _154_217 = (let _154_216 = (let _154_215 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_154_215, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_154_216))
in (Prims.raise _154_217))
end
| _52_509 -> begin
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
(let _52_531 = (one_pat false env q)
in (match (_52_531) with
| (b, a, _52_528, te, q) -> begin
(let _52_546 = (FStar_List.fold_right (fun p _52_536 -> (match (_52_536) with
| (w, args, pats) -> begin
(let _52_542 = (one_pat false env p)
in (match (_52_542) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _154_230 = (let _154_229 = (let _154_228 = (let _154_227 = (vars_of_bindings a)
in (let _154_226 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _154_227 _154_226)))
in (_154_228, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_154_229))
in (Prims.raise _154_230))
end else begin
(let _154_232 = (let _154_231 = (as_arg arg)
in (_154_231)::args)
in ((FStar_List.append w' w), _154_232, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_52_546) with
| (w, args, pats) -> begin
(let _154_234 = (let _154_233 = (as_arg te)
in (_154_233)::args)
in ((FStar_List.append b w), _154_234, (let _52_547 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _52_547.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _52_547.FStar_Absyn_Syntax.p})))
end))
end))
end
| _52_550 -> begin
(let _52_558 = (one_pat true env p)
in (match (_52_558) with
| (b, _52_553, _52_555, arg, p) -> begin
(let _154_236 = (let _154_235 = (as_arg arg)
in (_154_235)::[])
in (b, _154_236, p))
end))
end))
in (let _52_562 = (top_level_pat_as_args env p)
in (match (_52_562) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map (fun _52_7 -> (match (_52_7) with
| (FStar_Util.Inl (_52_565), _52_568) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _52_573) -> begin
e
end))))
in (b, exps, p))
end))))))))))

# 335 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let decorate_pattern : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.pat', ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either Prims.option) FStar_Absyn_Syntax.withinfo_t = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (let _154_255 = (FStar_All.pipe_left (fun _154_254 -> Some (_154_254)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _154_255 p.FStar_Absyn_Syntax.p)))
in (let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_52_589), FStar_Absyn_Syntax.Exp_constant (_52_592)) -> begin
(let _154_256 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _154_256))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _52_600 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _154_259 = (let _154_258 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _154_257 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_258 _154_257)))
in (FStar_All.failwith _154_259))
end else begin
()
end
in (let _52_602 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _154_261 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _154_260 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _154_261 _154_260)))
end else begin
()
end
in (let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (let x = (let _52_605 = x
in {FStar_Absyn_Syntax.v = _52_605.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _52_605.FStar_Absyn_Syntax.p})
in (let _154_262 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _154_262))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _52_613 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _154_265 = (let _154_264 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _154_263 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_264 _154_263)))
in (FStar_All.failwith _154_265))
end else begin
()
end
in (let x = (let _52_615 = x
in (let _154_266 = (force_tk e)
in {FStar_Absyn_Syntax.v = _52_615.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _154_266; FStar_Absyn_Syntax.p = _52_615.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _52_620), _52_624) -> begin
(let x = (let _52_626 = x
in (let _154_267 = (force_tk e)
in {FStar_Absyn_Syntax.v = _52_626.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _154_267; FStar_Absyn_Syntax.p = _52_626.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _52_636)) -> begin
(let _52_640 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _154_268 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _154_268))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _52_657); FStar_Absyn_Syntax.tk = _52_654; FStar_Absyn_Syntax.pos = _52_652; FStar_Absyn_Syntax.fvs = _52_650; FStar_Absyn_Syntax.uvs = _52_648}, args)) -> begin
(let _52_665 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _154_269 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _154_269))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _154_276 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _154_276))
end
| (arg::args, (argpat, _52_681)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_52_688))), FStar_Absyn_Syntax.Pat_dot_typ (_52_693)) -> begin
(let x = (let _154_277 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _154_277))
in (let q = (let _154_279 = (FStar_All.pipe_left (fun _154_278 -> Some (_154_278)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _154_279 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_52_701))), FStar_Absyn_Syntax.Pat_dot_term (_52_706)) -> begin
(let x = (let _154_280 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _154_280))
in (let q = (let _154_282 = (FStar_All.pipe_left (fun _154_281 -> Some (_154_281)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _154_282 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _52_716) -> begin
(let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _52_724) -> begin
(let pat = (let _154_283 = (aux argpat e)
in (_154_283, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _52_728 -> begin
(let _154_286 = (let _154_285 = (FStar_Absyn_Print.pat_to_string p)
in (let _154_284 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _154_285 _154_284)))
in (FStar_All.failwith _154_286))
end))
in (match_args [] args argpats))))
end
| _52_730 -> begin
(let _154_291 = (let _154_290 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _154_289 = (FStar_Absyn_Print.pat_to_string qq)
in (let _154_288 = (let _154_287 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _154_287 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _154_290 _154_289 _154_288))))
in (FStar_All.failwith _154_291))
end))))
and aux_t = (fun p t0 -> (let pkg = (fun q k -> (let _154_299 = (FStar_All.pipe_left (fun _154_298 -> Some (_154_298)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _154_299 p.FStar_Absyn_Syntax.p)))
in (let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _52_742 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _154_302 = (let _154_301 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _154_300 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_301 _154_300)))
in (FStar_All.failwith _154_302))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _52_749 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _154_305 = (let _154_304 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _154_303 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_304 _154_303)))
in (FStar_All.failwith _154_305))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _52_753), _52_757) -> begin
(let k0 = (force_tk t0)
in (let a = (let _52_760 = a
in {FStar_Absyn_Syntax.v = _52_760.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _52_760.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _52_764 -> begin
(let _154_309 = (let _154_308 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _154_307 = (FStar_Absyn_Print.pat_to_string p)
in (let _154_306 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _154_308 _154_307 _154_306))))
in (FStar_All.failwith _154_309))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _52_768) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (let _154_311 = (FStar_All.pipe_left (fun _154_310 -> Some (_154_310)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _154_311 p.FStar_Absyn_Syntax.p)))
end
| (_52_772, e::[]) -> begin
(aux p e)
end
| _52_777 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 433 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let rec decorated_pattern_as_exp : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.exp) = (fun pat -> (let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _52_784 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun _52_791 -> (match (_52_791) with
| (p, i) -> begin
(let _52_794 = (decorated_pattern_as_either p)
in (match (_52_794) with
| (vars, te) -> begin
(vars, (te, (FStar_Absyn_Syntax.as_implicit i)))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_52_796) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _154_332 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _154_332))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _154_335 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _154_335))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _52_810 = (let _154_336 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _154_336 FStar_List.unzip))
in (match (_52_810) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _154_342 = (let _154_341 = (let _154_340 = (let _154_339 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_154_339, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _154_340))
in (FStar_All.pipe_right _154_341 pkg))
in (vars, _154_342)))
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
(let _154_344 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _154_344))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _52_834 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _52_847 = (decorated_pattern_as_typ p)
in (match (_52_847) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _52_849 -> begin
(let _52_852 = (decorated_pattern_as_exp p)
in (match (_52_852) with
| (vars, e) -> begin
(vars, FStar_Util.Inr (e))
end))
end))

# 492 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let mk_basic_dtuple_type : FStar_Tc_Env.env  ->  Prims.int  ->  FStar_Absyn_Syntax.typ = (fun env n -> (let r = (FStar_Tc_Env.get_range env)
in (let l = (FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (FStar_Absyn_Util.ftv l k)
in (let vars = (FStar_Tc_Env.binders env)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _52_868; FStar_Absyn_Syntax.pos = _52_866; FStar_Absyn_Syntax.fvs = _52_864; FStar_Absyn_Syntax.uvs = _52_862}) -> begin
(let _52_898 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _52_875 _52_879 -> (match ((_52_875, _52_879)) with
| ((out, subst), (b, _52_878)) -> begin
(match (b) with
| FStar_Util.Inr (_52_881) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _154_352 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_352 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _154_355 = (let _154_354 = (let _154_353 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_353 Prims.fst))
in (bs, _154_354))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_355 (Some (k)) r))
end
| _52_892 -> begin
(FStar_All.failwith "Impossible")
end)
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (((FStar_Absyn_Syntax.targ arg))::out, subst))))
end)
end)) ([], [])))
in (match (_52_898) with
| (args, _52_897) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _52_900 -> begin
(FStar_All.failwith "Impossible")
end)))))))

# 516 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let extract_lb_annotation : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * Prims.bool) = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _154_366 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _154_366 Prims.fst))
in ((let _52_911 = a
in {FStar_Absyn_Syntax.v = _52_911.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _52_911.FStar_Absyn_Syntax.p}), false))
end
| _52_914 -> begin
(a, true)
end))
in (let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _154_371 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_371 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _52_923) -> begin
(x, false)
end
| _52_926 -> begin
(FStar_All.failwith "impos")
end))
end
| _52_928 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _52_932) -> begin
(x, true)
end
| _52_935 -> begin
(FStar_All.failwith "impos")
end)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _52_941)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _52_948) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _52_977 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _52_958 b -> (match (_52_958) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _52_964 = (mk_t_binder scope a)
in (match (_52_964) with
| (tb, c) -> begin
(let b = (FStar_Util.Inl (tb), (Prims.snd b))
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _52_972 = (mk_v_binder scope x)
in (match (_52_972) with
| (vb, c) -> begin
(let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_52_977) with
| (scope, bs, check) -> begin
(let _52_981 = (aux scope body)
in (match (_52_981) with
| (body, res, check_res) -> begin
(let c = (FStar_Absyn_Util.ml_comp res r)
in (let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (let _52_984 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _154_379 = (FStar_Range.string_of_range r)
in (let _154_378 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _154_379 _154_378)))
end else begin
()
end
in (let e = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _52_988 -> begin
(let _154_381 = (let _154_380 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _154_380 Prims.fst))
in (e, _154_381, false))
end))
in (let _154_382 = (FStar_Tc_Env.t_binders env)
in (aux _154_382 e))))))
end
| _52_990 -> begin
(e, t, false)
end))

# 573 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

# 575 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (let _52_1007 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _52_1000)::(FStar_Util.Inl (wlp), _52_995)::[] -> begin
(wp, wlp)
end
| _52_1004 -> begin
(let _154_387 = (let _154_386 = (let _154_385 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _154_385 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _154_386))
in (FStar_All.failwith _154_387))
end)
in (match (_52_1007) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

# 582 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (let _52_1015 = (destruct_comp c)
in (match (_52_1015) with
| (_52_1012, wp, wlp) -> begin
(let _154_409 = (let _154_408 = (let _154_404 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _154_404))
in (let _154_407 = (let _154_406 = (let _154_405 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _154_405))
in (_154_406)::[])
in (_154_408)::_154_407))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _154_409; FStar_Absyn_Syntax.flags = []})
end)))

# 589 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_52_1023, c) -> begin
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
(let _52_1037 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 611 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (let _52_1048 = (let _154_431 = (norm_eff_name env l1)
in (let _154_430 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _154_431 _154_430)))
in (match (_52_1048) with
| (m, _52_1045, _52_1047) -> begin
m
end)))

# 614 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let join_lcomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Ident.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Ident.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)

# 620 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let lift_and_destruct : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  ((FStar_Absyn_Syntax.eff_decl * ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ)) = (fun env c1 c2 -> (let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _52_1060 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_52_1060) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_Tc_Env.get_effect_decl env m)
in (let _52_1066 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_52_1066) with
| (a, kwp) -> begin
(let _154_461 = (destruct_comp m1)
in (let _154_460 = (destruct_comp m2)
in ((md, a, kwp), _154_461, _154_460)))
end)))))
end)))))

# 630 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))

# 634 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))

# 639 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun md result wp wlp flags -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = ((FStar_Absyn_Syntax.targ wp))::((FStar_Absyn_Syntax.targ wlp))::[]; FStar_Absyn_Syntax.flags = flags}))

# 645 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _52_1080 -> (match (()) with
| () -> begin
c0
end))}))

# 652 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let subst_lcomp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (let _52_1083 = lc
in (let _154_489 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _52_1083.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _154_489; FStar_Absyn_Syntax.cflags = _52_1083.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _52_1085 -> (match (()) with
| () -> begin
(let _154_488 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _154_488))
end))})))

# 656 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _154_492 = (FStar_Absyn_Util.compress_typ t)
in _154_492.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_52_1088) -> begin
true
end
| _52_1091 -> begin
false
end))

# 660 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env t v -> (let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _52_1100 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_52_1100) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _154_499 = (FStar_Absyn_Syntax.mk_Typ_app (m.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.varg v))::[]) (Some (k)) v.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _154_499))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _52_1105 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _154_502 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _154_501 = (FStar_Absyn_Print.exp_to_string v)
in (let _154_500 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _154_502 _154_501 _154_500))))
end else begin
()
end
in c)))

# 674 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let bind : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _52_1112 -> (match (_52_1112) with
| (b, lc2) -> begin
(let _52_1123 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _52_1116)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _52_1121 -> begin
"??"
end)
in (let _154_512 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _154_511 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _154_512 bstr _154_511))))
end else begin
()
end
in (let bind_it = (fun _52_1126 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun _52_1130 -> (match (()) with
| () -> begin
(let aux = (fun _52_1132 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_52_1135)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_52_1139)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _52_1143 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _52_1148))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _154_520 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _154_519 -> Some (_154_519)) _154_520))
end else begin
(aux ())
end
end
| _52_1154 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _52_1172 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _154_524 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _52_1160)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _52_1166)) -> begin
(FStar_Absyn_Print.sli l)
end
| _52_1171 -> begin
"Something else"
end)
in (let _154_523 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _154_522 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _154_521 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _154_524 _154_523 _154_522 _154_521)))))
end else begin
()
end
in c)
end
| None -> begin
(let _52_1187 = (lift_and_destruct env c1 c2)
in (match (_52_1187) with
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
| _52_1200 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (let wp_args = (let _154_535 = (let _154_534 = (let _154_533 = (let _154_532 = (let _154_531 = (let _154_527 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _154_527))
in (let _154_530 = (let _154_529 = (let _154_528 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _154_528))
in (_154_529)::[])
in (_154_531)::_154_530))
in ((FStar_Absyn_Syntax.targ wlp1))::_154_532)
in ((FStar_Absyn_Syntax.targ wp1))::_154_533)
in ((FStar_Absyn_Syntax.targ t2))::_154_534)
in ((FStar_Absyn_Syntax.targ t1))::_154_535)
in (let wlp_args = (let _154_540 = (let _154_539 = (let _154_538 = (let _154_537 = (let _154_536 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _154_536))
in (_154_537)::[])
in ((FStar_Absyn_Syntax.targ wlp1))::_154_538)
in ((FStar_Absyn_Syntax.targ t2))::_154_539)
in ((FStar_Absyn_Syntax.targ t1))::_154_540)
in (let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wp, wp_args) None t2.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _154_541 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _154_541; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

# 736 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let _52_1218 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_52_1218) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (mk_wp, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (mk_wlp, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ f))::[]) (Some (k)) f.FStar_Absyn_Syntax.pos)
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

# 744 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))

# 746 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (let refresh = (fun _52_1227 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_52_1230) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _52_1234 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _154_562 = (FStar_All.pipe_left FStar_Range.string_of_range (FStar_Tc_Env.get_range env))
in (FStar_Util.print1 "Refreshing label at %s\n" _154_562))
end else begin
()
end
in (let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_1237 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _154_565 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _154_564 = (let _154_563 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _154_563))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _154_565 _154_564)))
end else begin
()
end
in (let _52_1242 = (destruct_comp c')
in (match (_52_1242) with
| (t, wp, wlp) -> begin
(let wp = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((wp, Some (b), (FStar_Tc_Env.get_range env)))))
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((wlp, Some (b), (FStar_Tc_Env.get_range env)))))
in (FStar_Absyn_Syntax.mk_Comp (let _52_1245 = c'
in {FStar_Absyn_Syntax.effect_name = _52_1245.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _52_1245.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = ((FStar_Absyn_Syntax.targ wp))::((FStar_Absyn_Syntax.targ wlp))::[]; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))))
end)))))
end)
end)
end))
in (let _52_1247 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1247.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1247.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _52_1247.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

# 764 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

# 766 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _154_589 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _154_589)) then begin
f
end else begin
(let _154_590 = (reason ())
in (label _154_590 r f))
end
end))

# 773 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _154_597 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_154_597))
end))

# 777 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _52_1274 -> begin
g2
end))

# 783 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (let weaken = (fun _52_1279 -> (match (()) with
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
in (let _52_1288 = (destruct_comp c)
in (match (_52_1288) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (let _52_1292 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1292.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1292.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _52_1292.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

# 799 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _52_8 -> (match (_52_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _52_1303 -> begin
[]
end))))
in (let strengthen = (fun _52_1306 -> (match (()) with
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
in (let xret = (let _154_631 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _154_631))
in (let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (let lc = (bind env (Some (e)) (lcomp_of_comp c) (Some (xbinding), (lcomp_of_comp xret)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_1321 = (destruct_comp c)
in (match (_52_1321) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (let _154_636 = (let _154_635 = (let _154_634 = (let _154_633 = (let _154_632 = (label_opt env reason (FStar_Tc_Env.get_range env) f)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_632))
in (_154_633)::((FStar_Absyn_Syntax.targ wp))::[])
in ((FStar_Absyn_Syntax.targ res_t))::_154_634)
in (md.FStar_Absyn_Syntax.assert_p, _154_635))
in (FStar_Absyn_Syntax.mk_Typ_app _154_636 None wp.FStar_Absyn_Syntax.pos))
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.assume_p, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ f))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _154_640 = (let _52_1326 = lc
in (let _154_639 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _154_638 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _154_637 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _154_637))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _154_639; FStar_Absyn_Syntax.res_typ = _52_1326.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _154_638; FStar_Absyn_Syntax.comp = strengthen})))
in (_154_640, (let _52_1328 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _52_1328.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_1328.FStar_Tc_Rel.implicits})))))
end)

# 831 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let add_equality_to_post_condition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env comp res_t -> (let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let y = (FStar_Absyn_Util.gen_bvar res_t)
in (let _52_1338 = (let _154_648 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _154_647 = (FStar_Absyn_Util.bvar_to_exp y)
in (_154_648, _154_647)))
in (match (_52_1338) with
| (xexp, yexp) -> begin
(let yret = (FStar_Absyn_Syntax.mk_Typ_app (md_pure.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.varg yexp))::[]) None res_t.FStar_Absyn_Syntax.pos)
in (let x_eq_y_yret = (let _154_655 = (let _154_654 = (let _154_653 = (let _154_652 = (let _154_649 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_649))
in (let _154_651 = (let _154_650 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_154_650)::[])
in (_154_652)::_154_651))
in ((FStar_Absyn_Syntax.targ res_t))::_154_653)
in (md_pure.FStar_Absyn_Syntax.assume_p, _154_654))
in (FStar_Absyn_Syntax.mk_Typ_app _154_655 None res_t.FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _154_661 = (let _154_660 = (let _154_659 = (let _154_658 = (let _154_657 = (let _154_656 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder y))::[], x_eq_y_yret) None res_t.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_656))
in (_154_657)::[])
in ((FStar_Absyn_Syntax.targ res_t))::_154_658)
in ((FStar_Absyn_Syntax.targ res_t))::_154_659)
in (md_pure.FStar_Absyn_Syntax.close_wp, _154_660))
in (FStar_Absyn_Syntax.mk_Typ_app _154_661 None res_t.FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (bind env None (lcomp_of_comp comp) (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), (lcomp_of_comp lc2)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

# 843 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _52_1349 -> (match (()) with
| () -> begin
(let _52_1365 = (let _154_673 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _154_672 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _154_673 _154_672)))
in (match (_52_1365) with
| ((md, _52_1352, _52_1354), (res_t, wp_then, wlp_then), (_52_1361, wp_else, wlp_else)) -> begin
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

# 860 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _52_1388 -> (match (_52_1388) with
| (_52_1386, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun _52_1391 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _154_706 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.if_then_else, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ g))::((FStar_Absyn_Syntax.targ wp_t))::((FStar_Absyn_Syntax.targ wp_e))::[]) None _154_706)))
in (let default_case = (let post_k = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_v_binder res_t))::[], FStar_Absyn_Syntax.ktype) res_t.FStar_Absyn_Syntax.pos)
in (let kwp = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder post_k))::[], FStar_Absyn_Syntax.ktype) res_t.FStar_Absyn_Syntax.pos)
in (let post = (let _154_707 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _154_707 post_k))
in (let wp = (let _154_710 = (let _154_709 = (let _154_708 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (label FStar_Tc_Errors.exhaustiveness_check (FStar_Tc_Env.get_range env)) _154_708))
in (((FStar_Absyn_Syntax.t_binder post))::[], _154_709))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_710 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let wlp = (let _154_712 = (let _154_711 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (((FStar_Absyn_Syntax.t_binder post))::[], _154_711))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_712 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _52_1407 celse -> (match (_52_1407) with
| (g, cthen) -> begin
(let _52_1425 = (let _154_715 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _154_715 celse))
in (match (_52_1425) with
| ((md, _52_1411, _52_1413), (_52_1416, wp_then, wlp_then), (_52_1421, wp_else, wlp_else)) -> begin
(let _154_717 = (ifthenelse md res_t g wp_then wp_else)
in (let _154_716 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _154_717 _154_716 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (let _52_1433 = (destruct_comp comp)
in (match (_52_1433) with
| (_52_1430, wp, wlp) -> begin
(let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::((FStar_Absyn_Syntax.targ wp))::[]) None wp.FStar_Absyn_Syntax.pos)
in (let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ite_wlp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ wlp))::[]) None wlp.FStar_Absyn_Syntax.pos)
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

# 890 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (let close = (fun _52_1440 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bindings wp0 -> (FStar_List.fold_right (fun b wp -> (match (b) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let bs = (let _154_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_154_736)::[])
in (let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.close_wp, ((FStar_Absyn_Syntax.targ res_t))::((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ wp))::[]) None wp0.FStar_Absyn_Syntax.pos)))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let bs = (let _154_737 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_154_737)::[])
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
in (let _52_1471 = (destruct_comp c)
in (match (_52_1471) with
| (t, wp, wlp) -> begin
(let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.FStar_Absyn_Syntax.result_typ wp wlp c.FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (let _52_1475 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1475.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1475.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _52_1475.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

# 920 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (let refine = (fun _52_1481 -> (match (()) with
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
in (let ret = (let _154_746 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _154_746))
in (let eq_ret = (let _154_748 = (let _154_747 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_154_747))
in (weaken_precondition env ret _154_748))
in (let _154_750 = (let _154_749 = (bind env None (lcomp_of_comp c) (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret))
in (_154_749.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _154_750 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
end
end)
end))
in (let flags = if (((not ((FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.FStar_Absyn_Syntax.cflags
end else begin
lc.FStar_Absyn_Syntax.cflags
end
in (let _52_1491 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1491.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _52_1491.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

# 943 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _154_761 = (let _154_760 = (let _154_759 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (_154_759, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_154_760))
in (Prims.raise _154_761))
end
| Some (g) -> begin
(e, c', g)
end))

# 949 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let maybe_instantiate_typ : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * ((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list) = (fun env t k -> (let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(t, k, [])
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let rec aux = (fun subst _52_9 -> (match (_52_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_52_1515)))::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1523 = (new_implicit_tvar env k)
in (match (_52_1523) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _52_1529 = (aux subst rest)
in (match (_52_1529) with
| (args, bs, subst, us) -> begin
(let _154_775 = (let _154_774 = (let _154_773 = (FStar_All.pipe_left (fun _154_772 -> Some (_154_772)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _154_773))
in (_154_774)::args)
in (_154_775, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_52_1534)))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1542 = (new_implicit_evar env t)
in (match (_52_1542) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _52_1548 = (aux subst rest)
in (match (_52_1548) with
| (args, bs, subst, us) -> begin
(let _154_779 = (let _154_778 = (let _154_777 = (FStar_All.pipe_left (fun _154_776 -> Some (_154_776)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _154_777))
in (_154_778)::args)
in (_154_779, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _52_1554 = (aux [] bs)
in (match (_52_1554) with
| (args, bs, subst, implicits) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _154_780 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_154_780, k, implicits))))
end)))
end
| _52_1558 -> begin
(t, k, [])
end)
end))

# 977 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let maybe_instantiate : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * ((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list) = (fun env e t -> (let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let rec aux = (fun subst _52_10 -> (match (_52_10) with
| (FStar_Util.Inl (a), _52_1574)::rest -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1580 = (new_implicit_tvar env k)
in (match (_52_1580) with
| (t, u) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _52_1586 = (aux subst rest)
in (match (_52_1586) with
| (args, bs, subst, us) -> begin
(let _154_794 = (let _154_793 = (let _154_792 = (FStar_All.pipe_left (fun _154_791 -> Some (_154_791)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _154_792))
in (_154_793)::args)
in (_154_794, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_52_1591)))::rest -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1599 = (new_implicit_evar env t)
in (match (_52_1599) with
| (v, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (let _52_1605 = (aux subst rest)
in (match (_52_1605) with
| (args, bs, subst, us) -> begin
(let _154_798 = (let _154_797 = (let _154_796 = (FStar_All.pipe_left (fun _154_795 -> Some (_154_795)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _154_796))
in (_154_797)::args)
in (_154_798, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _52_1611 = (aux [] bs)
in (match (_52_1611) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _52_1618 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _154_805 = (mk_exp_app e args (Some (t)))
in (_154_805, t, implicits)))
end else begin
(e, t, [])
end
end
| _52_1622 -> begin
(let t = (let _154_806 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _154_806 (FStar_Absyn_Util.subst_typ subst)))
in (let _154_807 = (mk_exp_app e args (Some (t)))
in (_154_807, t, implicits)))
end))
end)))
end
| _52_1625 -> begin
(e, t, [])
end)
end))

# 1015 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _154_816 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_154_816, false))
end else begin
(let _154_817 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_154_817, true))
end
in (match (gopt) with
| (None, _52_1633) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(let lc = (let _52_1641 = lc
in {FStar_Absyn_Syntax.eff_name = _52_1641.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _52_1641.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _52_1641.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _52_1646 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _52_1646.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_1646.FStar_Tc_Rel.implicits})
in (let strengthen = (fun _52_1650 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let _52_1652 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _154_821 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _154_820 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _154_821 _154_820)))
end else begin
()
end
in (let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_1657 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_52_1657) with
| (a, kwp) -> begin
(let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (let x = (FStar_Absyn_Util.new_bvd None)
in (let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.ret, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.varg xexp))::[]) (Some (k)) xexp.FStar_Absyn_Syntax.pos)
in (let cret = (let _154_822 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _154_822))
in (let guard = if apply_guard then begin
(FStar_Absyn_Syntax.mk_Typ_app (f, ((FStar_Absyn_Syntax.varg xexp))::[]) (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos)
end else begin
f
end
in (let _52_1667 = (let _154_829 = (FStar_All.pipe_left (fun _154_827 -> Some (_154_827)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _154_828 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _154_829 (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos) e cret _154_828)))
in (match (_52_1667) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _154_831 = (let _154_830 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _154_830))
in (bind env (Some (e)) _154_831 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.FStar_Absyn_Syntax.comp ())
in (let _52_1670 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _154_832 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _154_832))
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
| _52_1676 -> begin
[]
end))))
in (let lc = (let _52_1678 = lc
in (let _154_834 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _154_834; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

# 1065 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let check_uvars : FStar_Range.range  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.unit = (fun r t -> (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(let ue = (let _154_839 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _154_839))
in (let ut = (let _154_840 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _154_840))
in (let uk = (let _154_841 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _154_841))
in (let union = (FStar_String.concat "," (FStar_List.append (FStar_List.append ue ut) uk))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _52_1690 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _52_1692 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _52_1694 = (let _154_843 = (let _154_842 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _154_842))
in (FStar_Tc_Errors.report r _154_843))
in (let _52_1696 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))

# 1086 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _154_851 = (FStar_Util.for_all (fun _52_1704 -> (match (_52_1704) with
| (_52_1702, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _154_851)) then begin
None
end else begin
(let norm = (fun c -> (let _52_1707 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _154_854 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _154_854))
end else begin
()
end
in (let steps = (FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
in (let c = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::[]) env c)
end
in (let _52_1711 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _154_855 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _154_855))
end else begin
()
end
in c)))))
in (let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _154_858 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _154_858 FStar_Util.set_elements)))
in (let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _52_1720) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _52_12 -> (match (_52_12) with
| (FStar_Util.Inl (_52_1725), _52_1728) -> begin
true
end
| _52_1731 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _52_1733 -> begin
true
end))
in (let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _52_1736 -> (match (_52_1736) with
| (e, c) -> begin
(let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _154_863 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _154_863)) then begin
([], e, c)
end else begin
(let c = (norm c)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.FStar_Absyn_Syntax.result_typ
in (let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.FStar_Absyn_Syntax.uvars_t)
in (let _52_1752 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _154_864 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _154_864))) then begin
(let _52_1748 = (destruct_comp ct)
in (match (_52_1748) with
| (_52_1744, wp, _52_1747) -> begin
(let binder = ((FStar_Absyn_Syntax.null_v_binder t))::[]
in (let post = (let _154_868 = (let _154_865 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _154_865))
in (let _154_867 = (let _154_866 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_154_866))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_868 _154_867 t.FStar_Absyn_Syntax.pos)))
in (let vc = (let _154_871 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) (FStar_Absyn_Syntax.mk_Typ_app (wp, ((FStar_Absyn_Syntax.targ post))::[])))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _154_871))
in (let _154_872 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _154_872)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _52_1758 -> (match (_52_1758) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _52_1761 -> (match (_52_1761) with
| (u, k) -> begin
(let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_52_1799) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _52_1802 -> begin
(let a = (let _154_876 = (FStar_All.pipe_left (fun _154_875 -> Some (_154_875)) (FStar_Tc_Env.get_range env))
in (FStar_Absyn_Util.new_bvd _154_876))
in (let t = (let _154_877 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _154_877 k))
in (let _52_1805 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _154_879 = (FStar_All.pipe_left (fun _154_878 -> Some (_154_878)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (a), _154_879)))
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
| _52_1816 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _52_1820 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _154_880 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _154_880)))))
end))))
in Some (ecs)))))))
end)

# 1153 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (let _52_1832 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _154_889 = (let _154_888 = (FStar_List.map (fun _52_1831 -> (match (_52_1831) with
| (lb, _52_1828, _52_1830) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _154_888 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _154_889))
end else begin
()
end
in (match ((let _154_891 = (FStar_All.pipe_right lecs (FStar_List.map (fun _52_1838 -> (match (_52_1838) with
| (_52_1835, e, c) -> begin
(e, c)
end))))
in (gen verify env _154_891))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _52_1847 _52_1850 -> (match ((_52_1847, _52_1850)) with
| ((l, _52_1844, _52_1846), (e, c)) -> begin
(let _52_1851 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _154_896 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _154_895 = (FStar_Absyn_Print.lbname_to_string l)
in (let _154_894 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _154_896 _154_895 _154_894))))
end else begin
()
end
in (l, e, c))
end)) lecs ecs)
end)))

# 1162 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Uvar -> begin
true
end
| _52_1856 -> begin
false
end))

# 1166 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (let discharge = (fun g -> (let _52_1862 = (FStar_Tc_Rel.try_discharge_guard env g)
in (let _52_1880 = (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _52_13 -> (match (_52_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _52_1869) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_52_1873, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _52_1879 -> begin
()
end)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _154_908 = (discharge g)
in (let _154_907 = (lc.FStar_Absyn_Syntax.comp ())
in (_154_908, _154_907)))
end else begin
(let c = (lc.FStar_Absyn_Syntax.comp ())
in (let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _154_909 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _154_909 FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (let _52_1891 = (destruct_comp c)
in (match (_52_1891) with
| (t, wp, _52_1890) -> begin
(let vc = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.trivial, ((FStar_Absyn_Syntax.targ t))::((FStar_Absyn_Syntax.targ wp))::[]) (Some (FStar_Absyn_Syntax.ktype)) (FStar_Tc_Env.get_range env))
in (let g = (let _154_910 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _154_910))
in (let _154_912 = (discharge g)
in (let _154_911 = (FStar_Absyn_Syntax.mk_Comp c)
in (_154_912, _154_911)))))
end))))))
end)))

# 1189 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (let short_bin_op_e = (fun f _52_14 -> (match (_52_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _52_1903)::[] -> begin
(let _154_931 = (f fst)
in (FStar_All.pipe_right _154_931 (fun _154_930 -> Some (_154_930))))
end
| _52_1907 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let table = (let op_and_e = (fun e -> (let _154_937 = (FStar_Absyn_Util.b2t e)
in (_154_937, FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun e -> (let _154_941 = (let _154_940 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _154_940))
in (_154_941, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _52_1915) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _52_1921 -> (match (_52_1921) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _154_959 = (mk seen_args)
in Some (_154_959))
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
| _52_1926 -> begin
None
end))))

# 1214 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (let short_bin_op_t = (fun f _52_15 -> (match (_52_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _52_1936)::[] -> begin
(f fst)
end
| _52_1940 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_t = (fun t -> (let _154_980 = (unlabel t)
in (FStar_All.pipe_right _154_980 (fun _154_979 -> FStar_Tc_Rel.NonTrivial (_154_979)))))
in (let op_or_t = (fun t -> (let _154_985 = (let _154_983 = (unlabel t)
in (FStar_All.pipe_right _154_983 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _154_985 (fun _154_984 -> FStar_Tc_Rel.NonTrivial (_154_984)))))
in (let op_imp_t = (fun t -> (let _154_989 = (unlabel t)
in (FStar_All.pipe_right _154_989 (fun _154_988 -> FStar_Tc_Rel.NonTrivial (_154_988)))))
in (let short_op_ite = (fun _52_16 -> (match (_52_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _52_1952)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _52_1958)::[] -> begin
(let _154_993 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _154_993 (fun _154_992 -> FStar_Tc_Rel.NonTrivial (_154_992))))
end
| _52_1963 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _52_1971) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _52_1981; FStar_Absyn_Syntax.pos = _52_1979; FStar_Absyn_Syntax.fvs = _52_1977; FStar_Absyn_Syntax.uvs = _52_1975}) -> begin
(let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _52_1989 -> (match (_52_1989) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _154_1020 = (mk seen_args)
in Some (_154_1020))
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
| _52_1994 -> begin
FStar_Tc_Rel.Trivial
end))))))))

# 1248 "D:\\workspace\\universes\\FStar\\src\\tc\\tcutil.fs"

let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _154_1034 = (let _154_1033 = (let _154_1032 = (let _154_1031 = (let _154_1030 = (let _154_1029 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _154_1029))
in (_154_1030)::[])
in (ens, _154_1031))
in (FStar_Absyn_Syntax.mk_Typ_app _154_1032 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _154_1033))
in (FStar_Absyn_Syntax.mk_Typ_refine _154_1034 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_52_2004) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _52_2019)::(FStar_Util.Inl (ens), _52_2013)::_52_2009 -> begin
(let _154_1040 = (let _154_1037 = (norm req)
in Some (_154_1037))
in (let _154_1039 = (let _154_1038 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _154_1038))
in (_154_1040, _154_1039)))
end
| _52_2023 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_52_2026) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _52_2041)::(FStar_Util.Inl (wlp), _52_2035)::_52_2031 -> begin
(let _52_2053 = (match ((let _154_1042 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _154_1041 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_154_1042, _154_1041)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _52_2050 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_52_2053) with
| (as_req, as_ens) -> begin
(let req = (let _154_1047 = (let _154_1046 = (let _154_1045 = (let _154_1044 = (FStar_All.pipe_left (fun _154_1043 -> Some (_154_1043)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _154_1044))
in (_154_1045)::((FStar_Absyn_Syntax.targ wp))::[])
in (as_req, _154_1046))
in (FStar_Absyn_Syntax.mk_Typ_app _154_1047 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let ens = (let _154_1052 = (let _154_1051 = (let _154_1050 = (let _154_1049 = (FStar_All.pipe_left (fun _154_1048 -> Some (_154_1048)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _154_1049))
in (_154_1050)::((FStar_Absyn_Syntax.targ wlp))::[])
in (as_ens, _154_1051))
in (FStar_Absyn_Syntax.mk_Typ_app _154_1052 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _154_1056 = (let _154_1053 = (norm req)
in Some (_154_1053))
in (let _154_1055 = (let _154_1054 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _154_1054))
in (_154_1056, _154_1055)))))
end))
end
| _52_2057 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




