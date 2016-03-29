
open Prims
# 30 "FStar.Tc.Util.fst"
type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

# 80 "FStar.Tc.Util.fst"
let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

# 85 "FStar.Tc.Util.fst"
let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _114_10 = (FStar_Tc_Env.get_range env)
in (let _114_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _114_10 _114_9))))

# 88 "FStar.Tc.Util.fst"
let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

# 90 "FStar.Tc.Util.fst"
let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))

# 92 "FStar.Tc.Util.fst"
let syn' = (fun env k -> (let _114_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _114_29 k)))

# 95 "FStar.Tc.Util.fst"
let is_xvar_free : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun x t -> (
# 98 "FStar.Tc.Util.fst"
let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) f.FStar_Absyn_Syntax.fxvs)))

# 99 "FStar.Tc.Util.fst"
let is_tvar_free : FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun a t -> (
# 102 "FStar.Tc.Util.fst"
let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun) f.FStar_Absyn_Syntax.ftvs)))

# 103 "FStar.Tc.Util.fst"
let check_and_ascribe : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Tc_Rel.guard_t) = (fun env e t1 t2 -> (
# 106 "FStar.Tc.Util.fst"
let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (
# 107 "FStar.Tc.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _114_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _114_52 -> Some (_114_52)) _114_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _114_57 = (let _114_56 = (let _114_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _114_54 = (FStar_Tc_Env.get_range env)
in (_114_55, _114_54)))
in FStar_Absyn_Syntax.Error (_114_56))
in (Prims.raise _114_57))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _114_61 = (let _114_60 = (let _114_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _114_58 = (FStar_Tc_Env.get_range env)
in (_114_59, _114_58)))
in FStar_Absyn_Syntax.Error (_114_60))
in (Prims.raise _114_61))
end
| Some (g) -> begin
(
# 121 "FStar.Tc.Util.fst"
let _35_53 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _114_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _114_62))
end else begin
()
end
in (
# 123 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Util.compress_exp e)
in (
# 124 "FStar.Tc.Util.fst"
let e = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(FStar_Absyn_Syntax.mk_Exp_bvar (FStar_Absyn_Util.bvd_to_bvar_s x.FStar_Absyn_Syntax.v t2) (Some (t2)) e.FStar_Absyn_Syntax.pos)
end
| _35_59 -> begin
(
# 126 "FStar.Tc.Util.fst"
let _35_60 = e
in (let _114_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _35_60.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _114_63; FStar_Absyn_Syntax.pos = _35_60.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _35_60.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _35_60.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))

# 127 "FStar.Tc.Util.fst"
let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

# 132 "FStar.Tc.Util.fst"
let as_uvar_e = (fun _35_1 -> (match (_35_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _35_75); FStar_Absyn_Syntax.tk = _35_72; FStar_Absyn_Syntax.pos = _35_70; FStar_Absyn_Syntax.fvs = _35_68; FStar_Absyn_Syntax.uvs = _35_66} -> begin
uv
end
| _35_80 -> begin
(FStar_All.failwith "Impossible")
end))

# 136 "FStar.Tc.Util.fst"
let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _35_92); FStar_Absyn_Syntax.tk = _35_89; FStar_Absyn_Syntax.pos = _35_87; FStar_Absyn_Syntax.fvs = _35_85; FStar_Absyn_Syntax.uvs = _35_83} -> begin
uv
end
| _35_97 -> begin
(FStar_All.failwith "Impossible")
end))

# 139 "FStar.Tc.Util.fst"
let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _114_73 = (let _114_72 = (FStar_Tc_Env.get_range env)
in (let _114_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _114_72 _114_71)))
in (FStar_All.pipe_right _114_73 Prims.fst)))

# 140 "FStar.Tc.Util.fst"
let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _114_80 = (let _114_79 = (FStar_Tc_Env.get_range env)
in (let _114_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _114_79 _114_78 k)))
in (FStar_All.pipe_right _114_80 Prims.fst)))

# 141 "FStar.Tc.Util.fst"
let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _114_87 = (let _114_86 = (FStar_Tc_Env.get_range env)
in (let _114_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _114_86 _114_85 t)))
in (FStar_All.pipe_right _114_87 Prims.fst)))

# 142 "FStar.Tc.Util.fst"
let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (
# 144 "FStar.Tc.Util.fst"
let _35_107 = (let _114_93 = (FStar_Tc_Env.get_range env)
in (let _114_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _114_93 _114_92 k)))
in (match (_35_107) with
| (t, u) -> begin
(let _114_95 = (let _114_94 = (as_uvar_t u)
in (_114_94, u.FStar_Absyn_Syntax.pos))
in (t, _114_95))
end)))

# 145 "FStar.Tc.Util.fst"
let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (
# 147 "FStar.Tc.Util.fst"
let _35_112 = (let _114_101 = (FStar_Tc_Env.get_range env)
in (let _114_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _114_101 _114_100 t)))
in (match (_35_112) with
| (e, u) -> begin
(let _114_103 = (let _114_102 = (as_uvar_e u)
in (_114_102, u.FStar_Absyn_Syntax.pos))
in (e, _114_103))
end)))

# 148 "FStar.Tc.Util.fst"
let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _114_106 = (let _114_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _114_105))
in (FStar_All.failwith _114_106))
end
| Some (tk) -> begin
tk
end))

# 151 "FStar.Tc.Util.fst"
let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _35_2 -> (match (_35_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _114_111 = (let _114_110 = (force_tk t)
in FStar_Util.Inl (_114_110))
in (_114_111, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _114_113 = (let _114_112 = (force_tk v)
in FStar_Util.Inr (_114_112))
in (_114_113, imp))
end)))))

# 155 "FStar.Tc.Util.fst"
let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _35_3 -> (match (_35_3) with
| Some (FStar_Absyn_Syntax.Implicit (_35_129)) -> begin
true
end
| _35_133 -> begin
false
end))

# 157 "FStar.Tc.Util.fst"
let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (
# 159 "FStar.Tc.Util.fst"
let ktop = (let _114_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _114_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (
# 160 "FStar.Tc.Util.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 161 "FStar.Tc.Util.fst"
let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(
# 163 "FStar.Tc.Util.fst"
let imp_follows = (match (args) with
| (_35_149, qual)::_35_147 -> begin
(is_implicit qual)
end
| _35_154 -> begin
false
end)
in (
# 166 "FStar.Tc.Util.fst"
let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(
# 169 "FStar.Tc.Util.fst"
let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _114_137 = (let _114_134 = (let _114_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _114_133))
in (FStar_All.pipe_right _114_134 Prims.fst))
in (FStar_All.pipe_right _114_137 (fun x -> (let _114_136 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (x), _114_136)))))
end
| FStar_Util.Inr (x) -> begin
(let _114_142 = (let _114_139 = (let _114_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _114_138))
in (FStar_All.pipe_right _114_139 Prims.fst))
in (FStar_All.pipe_right _114_142 (fun x -> (let _114_141 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (x), _114_141)))))
end)
in (
# 172 "FStar.Tc.Util.fst"
let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _114_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_114_143)::subst)
end
in (
# 173 "FStar.Tc.Util.fst"
let _35_173 = (mk_implicits vars subst brest)
in (match (_35_173) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _114_144 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _114_144))
end
end
| _35_175 -> begin
(let _114_145 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _114_145))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(
# 179 "FStar.Tc.Util.fst"
let _35_178 = (let _114_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _114_146 [] bs))
in (match (_35_178) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_35_180, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_35_185) -> begin
(
# 185 "FStar.Tc.Util.fst"
let fvs = (FStar_Absyn_Util.freevars_kind k)
in (
# 186 "FStar.Tc.Util.fst"
let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (
# 187 "FStar.Tc.Util.fst"
let kres = (let _114_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _114_147 Prims.fst))
in (
# 188 "FStar.Tc.Util.fst"
let bs = (let _114_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _114_148))
in (
# 189 "FStar.Tc.Util.fst"
let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (
# 190 "FStar.Tc.Util.fst"
let _35_192 = (let _114_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _114_149))
in ([], bs, kres)))))))
end
| _35_195 -> begin
(let _114_152 = (let _114_151 = (let _114_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_114_150, r))
in FStar_Absyn_Syntax.Error (_114_151))
in (Prims.raise _114_152))
end))
in (aux ktop)))))

# 195 "FStar.Tc.Util.fst"
let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _35_4 -> (match (_35_4) with
| Some (FStar_Absyn_Syntax.Implicit (_35_198)) -> begin
true
end
| _35_202 -> begin
false
end))

# 199 "FStar.Tc.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (
# 207 "FStar.Tc.Util.fst"
let pvar_eq = (fun x y -> (match ((x, y)) with
| (FStar_Tc_Env.Binding_var (x, _35_211), FStar_Tc_Env.Binding_var (y, _35_216)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _35_222), FStar_Tc_Env.Binding_typ (y, _35_227)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _35_232 -> begin
false
end))
in (
# 212 "FStar.Tc.Util.fst"
let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _35_5 -> (match (_35_5) with
| FStar_Tc_Env.Binding_var (x, _35_238) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _35_243) -> begin
FStar_Util.Inl (x)
end
| _35_247 -> begin
(FStar_All.failwith "impos")
end)))))
in (
# 219 "FStar.Tc.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _35_254) -> begin
(
# 228 "FStar.Tc.Util.fst"
let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (
# 229 "FStar.Tc.Util.fst"
let _35_260 = (let _114_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p _114_174 t))
in (match (_35_260) with
| (e, u) -> begin
(
# 230 "FStar.Tc.Util.fst"
let p = (
# 230 "FStar.Tc.Util.fst"
let _35_261 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _35_261.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _35_261.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _35_266) -> begin
(
# 234 "FStar.Tc.Util.fst"
let k = (new_kvar env)
in (
# 235 "FStar.Tc.Util.fst"
let _35_272 = (let _114_175 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _114_175 k))
in (match (_35_272) with
| (t, u) -> begin
(
# 236 "FStar.Tc.Util.fst"
let p = (
# 236 "FStar.Tc.Util.fst"
let _35_273 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _35_273.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _35_273.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inl (t), p))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(
# 240 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in ([], [], [], env, FStar_Util.Inr (e), p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(
# 244 "FStar.Tc.Util.fst"
let w = (let _114_177 = (let _114_176 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _114_176))
in FStar_Tc_Env.Binding_var (_114_177))
in (
# 245 "FStar.Tc.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (
# 246 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(
# 250 "FStar.Tc.Util.fst"
let b = (let _114_179 = (let _114_178 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _114_178))
in FStar_Tc_Env.Binding_var (_114_179))
in (
# 251 "FStar.Tc.Util.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in (
# 252 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(
# 256 "FStar.Tc.Util.fst"
let w = (let _114_181 = (let _114_180 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _114_180))
in FStar_Tc_Env.Binding_typ (_114_181))
in (
# 257 "FStar.Tc.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (
# 258 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(
# 262 "FStar.Tc.Util.fst"
let b = (let _114_183 = (let _114_182 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _114_182))
in FStar_Tc_Env.Binding_typ (_114_183))
in (
# 263 "FStar.Tc.Util.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in (
# 264 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 269 "FStar.Tc.Util.fst"
let _35_332 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_310 _35_313 -> (match ((_35_310, _35_313)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 270 "FStar.Tc.Util.fst"
let _35_320 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_320) with
| (b', a', w', env, te, pat) -> begin
(
# 271 "FStar.Tc.Util.fst"
let arg = (match (te) with
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
in (match (_35_332) with
| (b, a, w, env, args, pats) -> begin
(
# 275 "FStar.Tc.Util.fst"
let e = (let _114_191 = (let _114_190 = (let _114_189 = (let _114_188 = (let _114_187 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _114_186 = (FStar_All.pipe_right args FStar_List.rev)
in (_114_187, _114_186)))
in (FStar_Absyn_Syntax.mk_Exp_app' _114_188 None p.FStar_Absyn_Syntax.p))
in (_114_189, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_114_190))
in (FStar_Absyn_Syntax.mk_Exp_meta _114_191))
in (let _114_194 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _114_193 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _114_192 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_114_194, _114_193, _114_192, env, FStar_Util.Inr (e), (
# 281 "FStar.Tc.Util.fst"
let _35_334 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _35_334.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _35_334.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_35_337) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 284 "FStar.Tc.Util.fst"
let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 287 "FStar.Tc.Util.fst"
let pats = (FStar_List.map (fun _35_349 -> (match (_35_349) with
| (p, imp) -> begin
(let _114_200 = (elaborate_pat env p)
in (_114_200, imp))
end)) pats)
in (
# 288 "FStar.Tc.Util.fst"
let t = (FStar_Tc_Env.lookup_datacon env fv.FStar_Absyn_Syntax.v)
in (
# 289 "FStar.Tc.Util.fst"
let pats = (match ((FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _35_355 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end)
end
| Some (f, _35_358) -> begin
(
# 296 "FStar.Tc.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _35_371::_35_369) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end
| (_35_377::_35_375, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(
# 302 "FStar.Tc.Util.fst"
let a = (let _114_206 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _114_206 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _114_208 = (let _114_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _114_207))
in (_114_208, (as_imp imp)))
end else begin
(let _114_210 = (let _114_209 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _114_209))
in (_114_210, (as_imp imp)))
end)
end
| (FStar_Util.Inr (_35_388), Some (FStar_Absyn_Syntax.Implicit (dot))) -> begin
(
# 308 "FStar.Tc.Util.fst"
let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in if (allow_implicits && dot) then begin
(let _114_215 = (let _114_214 = (let _114_212 = (let _114_211 = (FStar_Absyn_Util.bvar_to_exp a)
in (a, _114_211))
in FStar_Absyn_Syntax.Pat_dot_term (_114_212))
in (let _114_213 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _114_214 None _114_213)))
in (_114_215, true))
end else begin
(let _114_217 = (let _114_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _114_216))
in (_114_217, true))
end)
end
| _35_396 -> begin
(let _114_221 = (let _114_220 = (let _114_219 = (let _114_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _114_218))
in (_114_219, (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_114_220))
in (Prims.raise _114_221))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _114_222 = (aux formals' pats')
in ((p, (as_imp imp)))::_114_222)
end
| ((FStar_Util.Inl (_35_424), imp), FStar_Absyn_Syntax.Pat_dot_typ (_35_429)) when allow_implicits -> begin
(let _114_223 = (aux formals' pats')
in ((p, (as_imp imp)))::_114_223)
end
| ((FStar_Util.Inl (_35_433), imp), _35_438) -> begin
(
# 321 "FStar.Tc.Util.fst"
let a = (let _114_224 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _114_224 FStar_Absyn_Syntax.kun))
in (
# 322 "FStar.Tc.Util.fst"
let p1 = if allow_implicits then begin
(let _114_225 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _114_225))
end else begin
(let _114_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _114_226))
end
in (
# 326 "FStar.Tc.Util.fst"
let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_35_443) -> begin
pats'
end
| _35_446 -> begin
pats
end)
in (let _114_227 = (aux formals' pats')
in ((p1, (as_imp imp)))::_114_227))))
end
| ((FStar_Util.Inr (_35_449), Some (FStar_Absyn_Syntax.Implicit (false))), _35_456) when p_imp -> begin
(let _114_228 = (aux formals' pats')
in ((p, true))::_114_228)
end
| ((FStar_Util.Inr (_35_459), Some (FStar_Absyn_Syntax.Implicit (dot))), _35_466) -> begin
(
# 333 "FStar.Tc.Util.fst"
let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 334 "FStar.Tc.Util.fst"
let p = if (allow_implicits && dot) then begin
(let _114_232 = (let _114_230 = (let _114_229 = (FStar_Absyn_Util.bvar_to_exp a)
in (a, _114_229))
in FStar_Absyn_Syntax.Pat_dot_term (_114_230))
in (let _114_231 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _114_232 None _114_231)))
end else begin
(let _114_233 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _114_233))
end
in (let _114_234 = (aux formals' pats)
in ((p, true))::_114_234)))
end
| ((FStar_Util.Inr (_35_471), imp), _35_476) -> begin
(let _114_235 = (aux formals' pats')
in ((p, (as_imp imp)))::_114_235)
end)
end))
in (aux f pats))
end)
in (
# 343 "FStar.Tc.Util.fst"
let _35_479 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _35_479.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _35_479.FStar_Absyn_Syntax.p}))))
end
| _35_482 -> begin
p
end))
in (
# 347 "FStar.Tc.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 348 "FStar.Tc.Util.fst"
let p = (elaborate_pat env p)
in (
# 354 "FStar.Tc.Util.fst"
let _35_494 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_35_494) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _35_497)) -> begin
(let _114_244 = (let _114_243 = (let _114_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_114_242, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_114_243))
in (Prims.raise _114_244))
end
| Some (FStar_Tc_Env.Binding_typ (x, _35_503)) -> begin
(let _114_247 = (let _114_246 = (let _114_245 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_114_245, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_114_246))
in (Prims.raise _114_247))
end
| _35_508 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 361 "FStar.Tc.Util.fst"
let as_arg = (fun _35_6 -> (match (_35_6) with
| FStar_Util.Inl (t) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Util.Inr (e) -> begin
(FStar_Absyn_Syntax.varg e)
end))
in (
# 364 "FStar.Tc.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(
# 371 "FStar.Tc.Util.fst"
let _35_530 = (one_pat false env q)
in (match (_35_530) with
| (b, a, _35_527, te, q) -> begin
(
# 372 "FStar.Tc.Util.fst"
let _35_545 = (FStar_List.fold_right (fun p _35_535 -> (match (_35_535) with
| (w, args, pats) -> begin
(
# 373 "FStar.Tc.Util.fst"
let _35_541 = (one_pat false env p)
in (match (_35_541) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _114_261 = (let _114_260 = (let _114_259 = (let _114_257 = (vars_of_bindings a)
in (let _114_256 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _114_257 _114_256)))
in (let _114_258 = (FStar_Tc_Env.get_range env)
in (_114_259, _114_258)))
in FStar_Absyn_Syntax.Error (_114_260))
in (Prims.raise _114_261))
end else begin
(let _114_263 = (let _114_262 = (as_arg arg)
in (_114_262)::args)
in ((FStar_List.append w' w), _114_263, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_35_545) with
| (w, args, pats) -> begin
(let _114_265 = (let _114_264 = (as_arg te)
in (_114_264)::args)
in ((FStar_List.append b w), _114_265, (
# 378 "FStar.Tc.Util.fst"
let _35_546 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _35_546.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _35_546.FStar_Absyn_Syntax.p})))
end))
end))
end
| _35_549 -> begin
(
# 381 "FStar.Tc.Util.fst"
let _35_557 = (one_pat true env p)
in (match (_35_557) with
| (b, _35_552, _35_554, arg, p) -> begin
(let _114_267 = (let _114_266 = (as_arg arg)
in (_114_266)::[])
in (b, _114_267, p))
end))
end))
in (
# 384 "FStar.Tc.Util.fst"
let _35_561 = (top_level_pat_as_args env p)
in (match (_35_561) with
| (b, args, p) -> begin
(
# 385 "FStar.Tc.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map (fun _35_7 -> (match (_35_7) with
| (FStar_Util.Inl (_35_564), _35_567) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _35_572) -> begin
e
end))))
in (b, exps, p))
end))))))))))

# 388 "FStar.Tc.Util.fst"
let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (
# 391 "FStar.Tc.Util.fst"
let qq = p
in (
# 392 "FStar.Tc.Util.fst"
let rec aux = (fun p e -> (
# 393 "FStar.Tc.Util.fst"
let pkg = (fun q t -> (let _114_286 = (FStar_All.pipe_left (fun _114_285 -> Some (_114_285)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _114_286 p.FStar_Absyn_Syntax.p)))
in (
# 394 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_35_588), FStar_Absyn_Syntax.Exp_constant (_35_591)) -> begin
(let _114_287 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _114_287))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(
# 399 "FStar.Tc.Util.fst"
let _35_599 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _114_290 = (let _114_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _114_288 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _114_289 _114_288)))
in (FStar_All.failwith _114_290))
end else begin
()
end
in (
# 401 "FStar.Tc.Util.fst"
let _35_601 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _114_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _114_291 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _114_292 _114_291)))
end else begin
()
end
in (
# 403 "FStar.Tc.Util.fst"
let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (
# 404 "FStar.Tc.Util.fst"
let x = (
# 404 "FStar.Tc.Util.fst"
let _35_604 = x
in {FStar_Absyn_Syntax.v = _35_604.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _35_604.FStar_Absyn_Syntax.p})
in (let _114_293 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _114_293))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(
# 408 "FStar.Tc.Util.fst"
let _35_612 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _114_296 = (let _114_295 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _114_294 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _114_295 _114_294)))
in (FStar_All.failwith _114_296))
end else begin
()
end
in (
# 410 "FStar.Tc.Util.fst"
let x = (
# 410 "FStar.Tc.Util.fst"
let _35_614 = x
in (let _114_297 = (force_tk e)
in {FStar_Absyn_Syntax.v = _35_614.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _114_297; FStar_Absyn_Syntax.p = _35_614.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _35_619), _35_623) -> begin
(
# 414 "FStar.Tc.Util.fst"
let x = (
# 414 "FStar.Tc.Util.fst"
let _35_625 = x
in (let _114_298 = (force_tk e)
in {FStar_Absyn_Syntax.v = _35_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _114_298; FStar_Absyn_Syntax.p = _35_625.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _35_635)) -> begin
(
# 418 "FStar.Tc.Util.fst"
let _35_639 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _114_299 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _114_299))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _35_656); FStar_Absyn_Syntax.tk = _35_653; FStar_Absyn_Syntax.pos = _35_651; FStar_Absyn_Syntax.fvs = _35_649; FStar_Absyn_Syntax.uvs = _35_647}, args)) -> begin
(
# 423 "FStar.Tc.Util.fst"
let _35_664 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _114_300 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _114_300))
end else begin
()
end
in (
# 425 "FStar.Tc.Util.fst"
let fv = fv'
in (
# 427 "FStar.Tc.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _114_307 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _114_307))
end
| (arg::args, (argpat, _35_680)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_35_687))), FStar_Absyn_Syntax.Pat_dot_typ (_35_692)) -> begin
(
# 432 "FStar.Tc.Util.fst"
let x = (let _114_308 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _114_308))
in (
# 433 "FStar.Tc.Util.fst"
let q = (let _114_310 = (FStar_All.pipe_left (fun _114_309 -> Some (_114_309)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _114_310 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_35_700))), FStar_Absyn_Syntax.Pat_dot_term (_35_705)) -> begin
(
# 437 "FStar.Tc.Util.fst"
let x = (let _114_311 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _114_311))
in (
# 438 "FStar.Tc.Util.fst"
let q = (let _114_313 = (FStar_All.pipe_left (fun _114_312 -> Some (_114_312)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _114_313 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _35_715) -> begin
(
# 442 "FStar.Tc.Util.fst"
let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _35_723) -> begin
(
# 446 "FStar.Tc.Util.fst"
let pat = (let _114_314 = (aux argpat e)
in (_114_314, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _35_727 -> begin
(let _114_317 = (let _114_316 = (FStar_Absyn_Print.pat_to_string p)
in (let _114_315 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _114_316 _114_315)))
in (FStar_All.failwith _114_317))
end))
in (match_args [] args argpats))))
end
| _35_729 -> begin
(let _114_322 = (let _114_321 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _114_320 = (FStar_Absyn_Print.pat_to_string qq)
in (let _114_319 = (let _114_318 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _114_318 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _114_321 _114_320 _114_319))))
in (FStar_All.failwith _114_322))
end))))
and aux_t = (fun p t0 -> (
# 458 "FStar.Tc.Util.fst"
let pkg = (fun q k -> (let _114_330 = (FStar_All.pipe_left (fun _114_329 -> Some (_114_329)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _114_330 p.FStar_Absyn_Syntax.p)))
in (
# 459 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(
# 462 "FStar.Tc.Util.fst"
let _35_741 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _114_333 = (let _114_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _114_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _114_332 _114_331)))
in (FStar_All.failwith _114_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(
# 467 "FStar.Tc.Util.fst"
let _35_748 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _114_336 = (let _114_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _114_334 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _114_335 _114_334)))
in (FStar_All.failwith _114_336))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _35_752), _35_756) -> begin
(
# 472 "FStar.Tc.Util.fst"
let k0 = (force_tk t0)
in (
# 473 "FStar.Tc.Util.fst"
let a = (
# 473 "FStar.Tc.Util.fst"
let _35_759 = a
in {FStar_Absyn_Syntax.v = _35_759.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _35_759.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _35_763 -> begin
(let _114_340 = (let _114_339 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _114_338 = (FStar_Absyn_Print.pat_to_string p)
in (let _114_337 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _114_339 _114_338 _114_337))))
in (FStar_All.failwith _114_340))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _35_767) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 480 "FStar.Tc.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (let _114_342 = (FStar_All.pipe_left (fun _114_341 -> Some (_114_341)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _114_342 p.FStar_Absyn_Syntax.p)))
end
| (_35_771, e::[]) -> begin
(aux p e)
end
| _35_776 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 486 "FStar.Tc.Util.fst"
let rec decorated_pattern_as_exp : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.exp) = (fun pat -> (
# 489 "FStar.Tc.Util.fst"
let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _35_783 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (
# 494 "FStar.Tc.Util.fst"
let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (
# 496 "FStar.Tc.Util.fst"
let pat_as_arg = (fun _35_790 -> (match (_35_790) with
| (p, i) -> begin
(
# 497 "FStar.Tc.Util.fst"
let _35_793 = (decorated_pattern_as_either p)
in (match (_35_793) with
| (vars, te) -> begin
(let _114_362 = (let _114_361 = (FStar_Absyn_Syntax.as_implicit i)
in (te, _114_361))
in (vars, _114_362))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_35_795) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _114_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _114_365))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _114_368 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _114_368))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 511 "FStar.Tc.Util.fst"
let _35_809 = (let _114_369 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _114_369 FStar_List.unzip))
in (match (_35_809) with
| (vars, args) -> begin
(
# 512 "FStar.Tc.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _114_375 = (let _114_374 = (let _114_373 = (let _114_372 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_114_372, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _114_373))
in (FStar_All.pipe_right _114_374 pkg))
in (vars, _114_375)))
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
(let _114_377 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _114_377))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _35_833 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(
# 537 "FStar.Tc.Util.fst"
let _35_846 = (decorated_pattern_as_typ p)
in (match (_35_846) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _35_848 -> begin
(
# 541 "FStar.Tc.Util.fst"
let _35_851 = (decorated_pattern_as_exp p)
in (match (_35_851) with
| (vars, e) -> begin
(vars, FStar_Util.Inr (e))
end))
end))

# 542 "FStar.Tc.Util.fst"
let mk_basic_dtuple_type : FStar_Tc_Env.env  ->  Prims.int  ->  FStar_Absyn_Syntax.typ = (fun env n -> (
# 548 "FStar.Tc.Util.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 549 "FStar.Tc.Util.fst"
let l = (FStar_Absyn_Util.mk_dtuple_lid n r)
in (
# 550 "FStar.Tc.Util.fst"
let k = (FStar_Tc_Env.lookup_typ_lid env l)
in (
# 551 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.ftv l k)
in (
# 552 "FStar.Tc.Util.fst"
let vars = (FStar_Tc_Env.binders env)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _35_867; FStar_Absyn_Syntax.pos = _35_865; FStar_Absyn_Syntax.fvs = _35_863; FStar_Absyn_Syntax.uvs = _35_861}) -> begin
(
# 555 "FStar.Tc.Util.fst"
let _35_897 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _35_874 _35_878 -> (match ((_35_874, _35_878)) with
| ((out, subst), (b, _35_877)) -> begin
(match (b) with
| FStar_Util.Inr (_35_880) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(
# 558 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 559 "FStar.Tc.Util.fst"
let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _114_385 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _114_385 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _114_388 = (let _114_387 = (let _114_386 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _114_386 Prims.fst))
in (bs, _114_387))
in (FStar_Absyn_Syntax.mk_Typ_lam _114_388 (Some (k)) r))
end
| _35_891 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 565 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (let _114_390 = (let _114_389 = (FStar_Absyn_Syntax.targ arg)
in (_114_389)::out)
in (_114_390, subst)))))
end)
end)) ([], [])))
in (match (_35_897) with
| (args, _35_896) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _35_899 -> begin
(FStar_All.failwith "Impossible")
end)))))))

# 569 "FStar.Tc.Util.fst"
let extract_lb_annotation : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * Prims.bool) = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(
# 573 "FStar.Tc.Util.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 574 "FStar.Tc.Util.fst"
let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(
# 576 "FStar.Tc.Util.fst"
let k = (let _114_401 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _114_401 Prims.fst))
in ((
# 577 "FStar.Tc.Util.fst"
let _35_910 = a
in {FStar_Absyn_Syntax.v = _35_910.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _35_910.FStar_Absyn_Syntax.p}), false))
end
| _35_913 -> begin
(a, true)
end))
in (
# 580 "FStar.Tc.Util.fst"
let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(
# 582 "FStar.Tc.Util.fst"
let t = (let _114_406 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _114_406 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _35_922) -> begin
(x, false)
end
| _35_925 -> begin
(FStar_All.failwith "impos")
end))
end
| _35_927 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _35_931) -> begin
(x, true)
end
| _35_934 -> begin
(FStar_All.failwith "impos")
end)
end))
in (
# 595 "FStar.Tc.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _35_940)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _35_947) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 600 "FStar.Tc.Util.fst"
let _35_976 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _35_957 b -> (match (_35_957) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(
# 602 "FStar.Tc.Util.fst"
let _35_963 = (mk_t_binder scope a)
in (match (_35_963) with
| (tb, c) -> begin
(
# 603 "FStar.Tc.Util.fst"
let b = (FStar_Util.Inl (tb), (Prims.snd b))
in (
# 604 "FStar.Tc.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 605 "FStar.Tc.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| FStar_Util.Inr (x) -> begin
(
# 608 "FStar.Tc.Util.fst"
let _35_971 = (mk_v_binder scope x)
in (match (_35_971) with
| (vb, c) -> begin
(
# 609 "FStar.Tc.Util.fst"
let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_35_976) with
| (scope, bs, check) -> begin
(
# 612 "FStar.Tc.Util.fst"
let _35_980 = (aux scope body)
in (match (_35_980) with
| (body, res, check_res) -> begin
(
# 613 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Util.ml_comp res r)
in (
# 614 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (
# 615 "FStar.Tc.Util.fst"
let _35_983 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _114_414 = (FStar_Range.string_of_range r)
in (let _114_413 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _114_414 _114_413)))
end else begin
()
end
in (
# 616 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _35_987 -> begin
(let _114_416 = (let _114_415 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _114_415 Prims.fst))
in (e, _114_416, false))
end))
in (let _114_417 = (FStar_Tc_Env.t_binders env)
in (aux _114_417 e))))))
end
| _35_989 -> begin
(e, t, false)
end))

# 623 "FStar.Tc.Util.fst"
let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (
# 629 "FStar.Tc.Util.fst"
let _35_1006 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _35_999)::(FStar_Util.Inl (wlp), _35_994)::[] -> begin
(wp, wlp)
end
| _35_1003 -> begin
(let _114_422 = (let _114_421 = (let _114_420 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _114_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _114_421))
in (FStar_All.failwith _114_422))
end)
in (match (_35_1006) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

# 633 "FStar.Tc.Util.fst"
let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (
# 636 "FStar.Tc.Util.fst"
let _35_1014 = (destruct_comp c)
in (match (_35_1014) with
| (_35_1011, wp, wlp) -> begin
(let _114_444 = (let _114_443 = (let _114_439 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _114_439))
in (let _114_442 = (let _114_441 = (let _114_440 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _114_440))
in (_114_441)::[])
in (_114_443)::_114_442))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _114_444; FStar_Absyn_Syntax.flags = []})
end)))

# 640 "FStar.Tc.Util.fst"
let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 643 "FStar.Tc.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 645 "FStar.Tc.Util.fst"
let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_35_1022, c) -> begin
(
# 649 "FStar.Tc.Util.fst"
let l = (FStar_Absyn_Util.comp_to_comp_typ c).FStar_Absyn_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (
# 653 "FStar.Tc.Util.fst"
let res = (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(
# 658 "FStar.Tc.Util.fst"
let _35_1036 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 661 "FStar.Tc.Util.fst"
let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 665 "FStar.Tc.Util.fst"
let _35_1047 = (let _114_458 = (norm_eff_name env l1)
in (let _114_457 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _114_458 _114_457)))
in (match (_35_1047) with
| (m, _35_1044, _35_1046) -> begin
m
end)))

# 666 "FStar.Tc.Util.fst"
let join_lcomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lident = (fun env c1 c2 -> if ((FStar_Ident.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Ident.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)

# 671 "FStar.Tc.Util.fst"
let lift_and_destruct : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  ((FStar_Absyn_Syntax.eff_decl * FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ)) = (fun env c1 c2 -> (
# 674 "FStar.Tc.Util.fst"
let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (
# 675 "FStar.Tc.Util.fst"
let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (
# 676 "FStar.Tc.Util.fst"
let _35_1059 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_35_1059) with
| (m, lift1, lift2) -> begin
(
# 677 "FStar.Tc.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 678 "FStar.Tc.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 679 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env m)
in (
# 680 "FStar.Tc.Util.fst"
let _35_1065 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_35_1065) with
| (a, kwp) -> begin
(let _114_472 = (destruct_comp m1)
in (let _114_471 = (destruct_comp m2)
in ((md, a, kwp), _114_472, _114_471)))
end)))))
end)))))

# 681 "FStar.Tc.Util.fst"
let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 684 "FStar.Tc.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))

# 685 "FStar.Tc.Util.fst"
let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 688 "FStar.Tc.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))

# 690 "FStar.Tc.Util.fst"
let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun md result wp wlp flags -> (let _114_495 = (let _114_494 = (let _114_493 = (FStar_Absyn_Syntax.targ wp)
in (let _114_492 = (let _114_491 = (FStar_Absyn_Syntax.targ wlp)
in (_114_491)::[])
in (_114_493)::_114_492))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _114_494; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _114_495)))

# 696 "FStar.Tc.Util.fst"
let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (
# 699 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _35_1079 -> (match (()) with
| () -> begin
c0
end))}))

# 703 "FStar.Tc.Util.fst"
let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (
# 706 "FStar.Tc.Util.fst"
let _35_1082 = lc
in (let _114_505 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _35_1082.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _114_505; FStar_Absyn_Syntax.cflags = _35_1082.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _35_1084 -> (match (()) with
| () -> begin
(let _114_504 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _114_504))
end))})))

# 707 "FStar.Tc.Util.fst"
let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _114_508 = (FStar_Absyn_Util.compress_typ t)
in _114_508.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_35_1087) -> begin
true
end
| _35_1090 -> begin
false
end))

# 711 "FStar.Tc.Util.fst"
let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp = (fun env t v -> (
# 715 "FStar.Tc.Util.fst"
let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(
# 718 "FStar.Tc.Util.fst"
let _35_1099 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_35_1099) with
| (a, kwp) -> begin
(
# 719 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (
# 720 "FStar.Tc.Util.fst"
let wp = (let _114_520 = (let _114_519 = (let _114_518 = (let _114_517 = (FStar_Absyn_Syntax.targ t)
in (let _114_516 = (let _114_515 = (FStar_Absyn_Syntax.varg v)
in (_114_515)::[])
in (_114_517)::_114_516))
in (m.FStar_Absyn_Syntax.ret, _114_518))
in (FStar_Absyn_Syntax.mk_Typ_app _114_519 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _114_520))
in (
# 721 "FStar.Tc.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (
# 723 "FStar.Tc.Util.fst"
let _35_1104 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _114_523 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _114_522 = (FStar_Absyn_Print.exp_to_string v)
in (let _114_521 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _114_523 _114_522 _114_521))))
end else begin
()
end
in c)))

# 725 "FStar.Tc.Util.fst"
let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _35_1111 -> (match (_35_1111) with
| (b, lc2) -> begin
(
# 728 "FStar.Tc.Util.fst"
let _35_1122 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(
# 730 "FStar.Tc.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _35_1115)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _35_1120 -> begin
"??"
end)
in (let _114_533 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _114_532 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _114_533 bstr _114_532))))
end else begin
()
end
in (
# 735 "FStar.Tc.Util.fst"
let bind_it = (fun _35_1125 -> (match (()) with
| () -> begin
(
# 736 "FStar.Tc.Util.fst"
let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (
# 737 "FStar.Tc.Util.fst"
let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (
# 738 "FStar.Tc.Util.fst"
let try_simplify = (fun _35_1129 -> (match (()) with
| () -> begin
(
# 739 "FStar.Tc.Util.fst"
let aux = (fun _35_1131 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_35_1134)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_35_1138)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _35_1142 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _35_1147))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _114_541 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _114_540 -> Some (_114_540)) _114_541))
end else begin
(aux ())
end
end
| _35_1153 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(
# 760 "FStar.Tc.Util.fst"
let _35_1171 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _114_545 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _35_1159)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _35_1165)) -> begin
(FStar_Absyn_Print.sli l)
end
| _35_1170 -> begin
"Something else"
end)
in (let _114_544 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _114_543 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _114_542 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _114_545 _114_544 _114_543 _114_542)))))
end else begin
()
end
in c)
end
| None -> begin
(
# 770 "FStar.Tc.Util.fst"
let _35_1186 = (lift_and_destruct env c1 c2)
in (match (_35_1186) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 771 "FStar.Tc.Util.fst"
let bs = (match (b) with
| None -> begin
(let _114_546 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_114_546)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _114_547 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_114_547)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _114_548 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_114_548)::[])
end
| _35_1199 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (
# 776 "FStar.Tc.Util.fst"
let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (
# 777 "FStar.Tc.Util.fst"
let wp_args = (let _114_563 = (FStar_Absyn_Syntax.targ t1)
in (let _114_562 = (let _114_561 = (FStar_Absyn_Syntax.targ t2)
in (let _114_560 = (let _114_559 = (FStar_Absyn_Syntax.targ wp1)
in (let _114_558 = (let _114_557 = (FStar_Absyn_Syntax.targ wlp1)
in (let _114_556 = (let _114_555 = (let _114_551 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _114_551))
in (let _114_554 = (let _114_553 = (let _114_552 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _114_552))
in (_114_553)::[])
in (_114_555)::_114_554))
in (_114_557)::_114_556))
in (_114_559)::_114_558))
in (_114_561)::_114_560))
in (_114_563)::_114_562))
in (
# 778 "FStar.Tc.Util.fst"
let wlp_args = (let _114_571 = (FStar_Absyn_Syntax.targ t1)
in (let _114_570 = (let _114_569 = (FStar_Absyn_Syntax.targ t2)
in (let _114_568 = (let _114_567 = (FStar_Absyn_Syntax.targ wlp1)
in (let _114_566 = (let _114_565 = (let _114_564 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _114_564))
in (_114_565)::[])
in (_114_567)::_114_566))
in (_114_569)::_114_568))
in (_114_571)::_114_570))
in (
# 779 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (
# 780 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wp, wp_args) None t2.FStar_Absyn_Syntax.pos)
in (
# 781 "FStar.Tc.Util.fst"
let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.FStar_Absyn_Syntax.pos)
in (
# 782 "FStar.Tc.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _114_572 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _114_572; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

# 787 "FStar.Tc.Util.fst"
let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 790 "FStar.Tc.Util.fst"
let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (
# 791 "FStar.Tc.Util.fst"
let _35_1217 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_35_1217) with
| (a, kwp) -> begin
(
# 792 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (
# 793 "FStar.Tc.Util.fst"
let wp = (let _114_587 = (let _114_586 = (let _114_585 = (FStar_Absyn_Syntax.targ t)
in (let _114_584 = (let _114_583 = (FStar_Absyn_Syntax.targ f)
in (_114_583)::[])
in (_114_585)::_114_584))
in (mk_wp, _114_586))
in (FStar_Absyn_Syntax.mk_Typ_app _114_587 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (
# 794 "FStar.Tc.Util.fst"
let wlp = (let _114_592 = (let _114_591 = (let _114_590 = (FStar_Absyn_Syntax.targ t)
in (let _114_589 = (let _114_588 = (FStar_Absyn_Syntax.targ f)
in (_114_588)::[])
in (_114_590)::_114_589))
in (mk_wlp, _114_591))
in (FStar_Absyn_Syntax.mk_Typ_app _114_592 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

# 795 "FStar.Tc.Util.fst"
let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))

# 797 "FStar.Tc.Util.fst"
let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (
# 800 "FStar.Tc.Util.fst"
let refresh = (fun _35_1226 -> (match (()) with
| () -> begin
(
# 801 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_35_1229) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 806 "FStar.Tc.Util.fst"
let _35_1233 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _114_604 = (let _114_603 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _114_603))
in (FStar_Util.print1 "Refreshing label at %s\n" _114_604))
end else begin
()
end
in (
# 808 "FStar.Tc.Util.fst"
let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 809 "FStar.Tc.Util.fst"
let _35_1236 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _114_607 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _114_606 = (let _114_605 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _114_605))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _114_607 _114_606)))
end else begin
()
end
in (
# 811 "FStar.Tc.Util.fst"
let _35_1241 = (destruct_comp c')
in (match (_35_1241) with
| (t, wp, wlp) -> begin
(
# 812 "FStar.Tc.Util.fst"
let wp = (let _114_610 = (let _114_609 = (let _114_608 = (FStar_Tc_Env.get_range env)
in (wp, Some (b), _114_608))
in FStar_Absyn_Syntax.Meta_refresh_label (_114_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _114_610))
in (
# 813 "FStar.Tc.Util.fst"
let wlp = (let _114_613 = (let _114_612 = (let _114_611 = (FStar_Tc_Env.get_range env)
in (wlp, Some (b), _114_611))
in FStar_Absyn_Syntax.Meta_refresh_label (_114_612))
in (FStar_Absyn_Syntax.mk_Typ_meta _114_613))
in (let _114_618 = (
# 814 "FStar.Tc.Util.fst"
let _35_1244 = c'
in (let _114_617 = (let _114_616 = (FStar_Absyn_Syntax.targ wp)
in (let _114_615 = (let _114_614 = (FStar_Absyn_Syntax.targ wlp)
in (_114_614)::[])
in (_114_616)::_114_615))
in {FStar_Absyn_Syntax.effect_name = _35_1244.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _35_1244.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _114_617; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _114_618))))
end)))))
end)
end)
end))
in (
# 815 "FStar.Tc.Util.fst"
let _35_1246 = lc
in {FStar_Absyn_Syntax.eff_name = _35_1246.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _35_1246.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _35_1246.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

# 815 "FStar.Tc.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

# 818 "FStar.Tc.Util.fst"
let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _114_642 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _114_642)) then begin
f
end else begin
(let _114_643 = (reason ())
in (label _114_643 r f))
end
end))

# 824 "FStar.Tc.Util.fst"
let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _114_650 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_114_650))
end))

# 828 "FStar.Tc.Util.fst"
let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(
# 832 "FStar.Tc.Util.fst"
let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _35_1273 -> begin
g2
end))

# 834 "FStar.Tc.Util.fst"
let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (
# 837 "FStar.Tc.Util.fst"
let weaken = (fun _35_1278 -> (match (()) with
| () -> begin
(
# 838 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (match (f) with
| FStar_Tc_Rel.Trivial -> begin
c
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(
# 844 "FStar.Tc.Util.fst"
let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 845 "FStar.Tc.Util.fst"
let _35_1287 = (destruct_comp c)
in (match (_35_1287) with
| (res_t, wp, wlp) -> begin
(
# 846 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 847 "FStar.Tc.Util.fst"
let wp = (let _114_669 = (let _114_668 = (let _114_667 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_666 = (let _114_665 = (FStar_Absyn_Syntax.targ f)
in (let _114_664 = (let _114_663 = (FStar_Absyn_Syntax.targ wp)
in (_114_663)::[])
in (_114_665)::_114_664))
in (_114_667)::_114_666))
in (md.FStar_Absyn_Syntax.assume_p, _114_668))
in (FStar_Absyn_Syntax.mk_Typ_app _114_669 None wp.FStar_Absyn_Syntax.pos))
in (
# 848 "FStar.Tc.Util.fst"
let wlp = (let _114_676 = (let _114_675 = (let _114_674 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_673 = (let _114_672 = (FStar_Absyn_Syntax.targ f)
in (let _114_671 = (let _114_670 = (FStar_Absyn_Syntax.targ wlp)
in (_114_670)::[])
in (_114_672)::_114_671))
in (_114_674)::_114_673))
in (md.FStar_Absyn_Syntax.assume_p, _114_675))
in (FStar_Absyn_Syntax.mk_Typ_app _114_676 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (
# 850 "FStar.Tc.Util.fst"
let _35_1291 = lc
in {FStar_Absyn_Syntax.eff_name = _35_1291.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _35_1291.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _35_1291.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

# 850 "FStar.Tc.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 855 "FStar.Tc.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _35_8 -> (match (_35_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _35_1302 -> begin
[]
end))))
in (
# 856 "FStar.Tc.Util.fst"
let strengthen = (fun _35_1305 -> (match (()) with
| () -> begin
(
# 857 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 858 "FStar.Tc.Util.fst"
let g0 = (FStar_Tc_Rel.simplify_guard env g0)
in (match ((FStar_Tc_Rel.guard_form g0)) with
| FStar_Tc_Rel.Trivial -> begin
c
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(
# 862 "FStar.Tc.Util.fst"
let c = if (((FStar_Absyn_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Absyn_Util.comp_result c))))) && (not ((FStar_Absyn_Util.is_partial_return c)))) then begin
(
# 866 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar (FStar_Absyn_Util.comp_result c))
in (
# 867 "FStar.Tc.Util.fst"
let xret = (let _114_698 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _114_698))
in (
# 868 "FStar.Tc.Util.fst"
let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (
# 869 "FStar.Tc.Util.fst"
let lc = (let _114_701 = (lcomp_of_comp c)
in (let _114_700 = (let _114_699 = (lcomp_of_comp xret)
in (Some (xbinding), _114_699))
in (bind env (Some (e)) _114_701 _114_700)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (
# 872 "FStar.Tc.Util.fst"
let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 873 "FStar.Tc.Util.fst"
let _35_1320 = (destruct_comp c)
in (match (_35_1320) with
| (res_t, wp, wlp) -> begin
(
# 874 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 875 "FStar.Tc.Util.fst"
let wp = (let _114_710 = (let _114_709 = (let _114_708 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_707 = (let _114_706 = (let _114_703 = (let _114_702 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _114_702 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _114_703))
in (let _114_705 = (let _114_704 = (FStar_Absyn_Syntax.targ wp)
in (_114_704)::[])
in (_114_706)::_114_705))
in (_114_708)::_114_707))
in (md.FStar_Absyn_Syntax.assert_p, _114_709))
in (FStar_Absyn_Syntax.mk_Typ_app _114_710 None wp.FStar_Absyn_Syntax.pos))
in (
# 876 "FStar.Tc.Util.fst"
let wlp = (let _114_717 = (let _114_716 = (let _114_715 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_714 = (let _114_713 = (FStar_Absyn_Syntax.targ f)
in (let _114_712 = (let _114_711 = (FStar_Absyn_Syntax.targ wlp)
in (_114_711)::[])
in (_114_713)::_114_712))
in (_114_715)::_114_714))
in (md.FStar_Absyn_Syntax.assume_p, _114_716))
in (FStar_Absyn_Syntax.mk_Typ_app _114_717 None wlp.FStar_Absyn_Syntax.pos))
in (
# 877 "FStar.Tc.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _114_721 = (
# 879 "FStar.Tc.Util.fst"
let _35_1325 = lc
in (let _114_720 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _114_719 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _114_718 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _114_718))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _114_720; FStar_Absyn_Syntax.res_typ = _35_1325.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _114_719; FStar_Absyn_Syntax.comp = strengthen})))
in (_114_721, (
# 882 "FStar.Tc.Util.fst"
let _35_1327 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _35_1327.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _35_1327.FStar_Tc_Rel.implicits})))))
end)

# 882 "FStar.Tc.Util.fst"
let add_equality_to_post_condition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env comp res_t -> (
# 885 "FStar.Tc.Util.fst"
let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (
# 886 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar res_t)
in (
# 887 "FStar.Tc.Util.fst"
let y = (FStar_Absyn_Util.gen_bvar res_t)
in (
# 888 "FStar.Tc.Util.fst"
let _35_1337 = (let _114_729 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _114_728 = (FStar_Absyn_Util.bvar_to_exp y)
in (_114_729, _114_728)))
in (match (_35_1337) with
| (xexp, yexp) -> begin
(
# 889 "FStar.Tc.Util.fst"
let yret = (let _114_734 = (let _114_733 = (let _114_732 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_731 = (let _114_730 = (FStar_Absyn_Syntax.varg yexp)
in (_114_730)::[])
in (_114_732)::_114_731))
in (md_pure.FStar_Absyn_Syntax.ret, _114_733))
in (FStar_Absyn_Syntax.mk_Typ_app _114_734 None res_t.FStar_Absyn_Syntax.pos))
in (
# 890 "FStar.Tc.Util.fst"
let x_eq_y_yret = (let _114_742 = (let _114_741 = (let _114_740 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_739 = (let _114_738 = (let _114_735 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _114_735))
in (let _114_737 = (let _114_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_114_736)::[])
in (_114_738)::_114_737))
in (_114_740)::_114_739))
in (md_pure.FStar_Absyn_Syntax.assume_p, _114_741))
in (FStar_Absyn_Syntax.mk_Typ_app _114_742 None res_t.FStar_Absyn_Syntax.pos))
in (
# 891 "FStar.Tc.Util.fst"
let forall_y_x_eq_y_yret = (let _114_753 = (let _114_752 = (let _114_751 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_750 = (let _114_749 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_748 = (let _114_747 = (let _114_746 = (let _114_745 = (let _114_744 = (let _114_743 = (FStar_Absyn_Syntax.v_binder y)
in (_114_743)::[])
in (_114_744, x_eq_y_yret))
in (FStar_Absyn_Syntax.mk_Typ_lam _114_745 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _114_746))
in (_114_747)::[])
in (_114_749)::_114_748))
in (_114_751)::_114_750))
in (md_pure.FStar_Absyn_Syntax.close_wp, _114_752))
in (FStar_Absyn_Syntax.mk_Typ_app _114_753 None res_t.FStar_Absyn_Syntax.pos))
in (
# 892 "FStar.Tc.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (
# 893 "FStar.Tc.Util.fst"
let lc = (let _114_756 = (lcomp_of_comp comp)
in (let _114_755 = (let _114_754 = (lcomp_of_comp lc2)
in (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), _114_754))
in (bind env None _114_756 _114_755)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

# 894 "FStar.Tc.Util.fst"
let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 897 "FStar.Tc.Util.fst"
let comp = (fun _35_1348 -> (match (()) with
| () -> begin
(
# 898 "FStar.Tc.Util.fst"
let _35_1364 = (let _114_768 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _114_767 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _114_768 _114_767)))
in (match (_35_1364) with
| ((md, _35_1351, _35_1353), (res_t, wp_then, wlp_then), (_35_1360, wp_else, wlp_else)) -> begin
(
# 899 "FStar.Tc.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _114_788 = (let _114_786 = (let _114_785 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_784 = (let _114_783 = (FStar_Absyn_Syntax.targ g)
in (let _114_782 = (let _114_781 = (FStar_Absyn_Syntax.targ wp_t)
in (let _114_780 = (let _114_779 = (FStar_Absyn_Syntax.targ wp_e)
in (_114_779)::[])
in (_114_781)::_114_780))
in (_114_783)::_114_782))
in (_114_785)::_114_784))
in (md.FStar_Absyn_Syntax.if_then_else, _114_786))
in (let _114_787 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _114_788 None _114_787))))
in (
# 900 "FStar.Tc.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 901 "FStar.Tc.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 903 "FStar.Tc.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 905 "FStar.Tc.Util.fst"
let wp = (let _114_795 = (let _114_794 = (let _114_793 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_792 = (let _114_791 = (FStar_Absyn_Syntax.targ wlp)
in (let _114_790 = (let _114_789 = (FStar_Absyn_Syntax.targ wp)
in (_114_789)::[])
in (_114_791)::_114_790))
in (_114_793)::_114_792))
in (md.FStar_Absyn_Syntax.ite_wp, _114_794))
in (FStar_Absyn_Syntax.mk_Typ_app _114_795 None wp.FStar_Absyn_Syntax.pos))
in (
# 906 "FStar.Tc.Util.fst"
let wlp = (let _114_800 = (let _114_799 = (let _114_798 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_797 = (let _114_796 = (FStar_Absyn_Syntax.targ wlp)
in (_114_796)::[])
in (_114_798)::_114_797))
in (md.FStar_Absyn_Syntax.ite_wlp, _114_799))
in (FStar_Absyn_Syntax.mk_Typ_app _114_800 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _114_801 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _114_801; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))

# 911 "FStar.Tc.Util.fst"
let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (
# 914 "FStar.Tc.Util.fst"
let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _35_1387 -> (match (_35_1387) with
| (_35_1385, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (
# 917 "FStar.Tc.Util.fst"
let bind_cases = (fun _35_1390 -> (match (()) with
| () -> begin
(
# 918 "FStar.Tc.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _114_831 = (let _114_829 = (let _114_828 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_827 = (let _114_826 = (FStar_Absyn_Syntax.targ g)
in (let _114_825 = (let _114_824 = (FStar_Absyn_Syntax.targ wp_t)
in (let _114_823 = (let _114_822 = (FStar_Absyn_Syntax.targ wp_e)
in (_114_822)::[])
in (_114_824)::_114_823))
in (_114_826)::_114_825))
in (_114_828)::_114_827))
in (md.FStar_Absyn_Syntax.if_then_else, _114_829))
in (let _114_830 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _114_831 None _114_830))))
in (
# 919 "FStar.Tc.Util.fst"
let default_case = (
# 920 "FStar.Tc.Util.fst"
let post_k = (let _114_834 = (let _114_833 = (let _114_832 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_114_832)::[])
in (_114_833, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _114_834 res_t.FStar_Absyn_Syntax.pos))
in (
# 921 "FStar.Tc.Util.fst"
let kwp = (let _114_837 = (let _114_836 = (let _114_835 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_114_835)::[])
in (_114_836, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _114_837 res_t.FStar_Absyn_Syntax.pos))
in (
# 922 "FStar.Tc.Util.fst"
let post = (let _114_838 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _114_838 post_k))
in (
# 923 "FStar.Tc.Util.fst"
let wp = (let _114_845 = (let _114_844 = (let _114_839 = (FStar_Absyn_Syntax.t_binder post)
in (_114_839)::[])
in (let _114_843 = (let _114_842 = (let _114_840 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _114_840))
in (let _114_841 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _114_842 _114_841)))
in (_114_844, _114_843)))
in (FStar_Absyn_Syntax.mk_Typ_lam _114_845 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (
# 924 "FStar.Tc.Util.fst"
let wlp = (let _114_849 = (let _114_848 = (let _114_846 = (FStar_Absyn_Syntax.t_binder post)
in (_114_846)::[])
in (let _114_847 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_114_848, _114_847)))
in (FStar_Absyn_Syntax.mk_Typ_lam _114_849 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (
# 925 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 927 "FStar.Tc.Util.fst"
let comp = (FStar_List.fold_right (fun _35_1406 celse -> (match (_35_1406) with
| (g, cthen) -> begin
(
# 928 "FStar.Tc.Util.fst"
let _35_1424 = (let _114_852 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _114_852 celse))
in (match (_35_1424) with
| ((md, _35_1410, _35_1412), (_35_1415, wp_then, wlp_then), (_35_1420, wp_else, wlp_else)) -> begin
(let _114_854 = (ifthenelse md res_t g wp_then wp_else)
in (let _114_853 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _114_854 _114_853 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 932 "FStar.Tc.Util.fst"
let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (
# 933 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (
# 934 "FStar.Tc.Util.fst"
let _35_1432 = (destruct_comp comp)
in (match (_35_1432) with
| (_35_1429, wp, wlp) -> begin
(
# 935 "FStar.Tc.Util.fst"
let wp = (let _114_861 = (let _114_860 = (let _114_859 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_858 = (let _114_857 = (FStar_Absyn_Syntax.targ wlp)
in (let _114_856 = (let _114_855 = (FStar_Absyn_Syntax.targ wp)
in (_114_855)::[])
in (_114_857)::_114_856))
in (_114_859)::_114_858))
in (md.FStar_Absyn_Syntax.ite_wp, _114_860))
in (FStar_Absyn_Syntax.mk_Typ_app _114_861 None wp.FStar_Absyn_Syntax.pos))
in (
# 936 "FStar.Tc.Util.fst"
let wlp = (let _114_866 = (let _114_865 = (let _114_864 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_863 = (let _114_862 = (FStar_Absyn_Syntax.targ wlp)
in (_114_862)::[])
in (_114_864)::_114_863))
in (md.FStar_Absyn_Syntax.ite_wlp, _114_865))
in (FStar_Absyn_Syntax.mk_Typ_app _114_866 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

# 941 "FStar.Tc.Util.fst"
let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (
# 944 "FStar.Tc.Util.fst"
let close = (fun _35_1439 -> (match (()) with
| () -> begin
(
# 945 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(
# 948 "FStar.Tc.Util.fst"
let close_wp = (fun md res_t bindings wp0 -> (FStar_List.fold_right (fun b wp -> (match (b) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(
# 951 "FStar.Tc.Util.fst"
let bs = (let _114_885 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_114_885)::[])
in (
# 952 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _114_892 = (let _114_891 = (let _114_890 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_889 = (let _114_888 = (FStar_Absyn_Syntax.targ t)
in (let _114_887 = (let _114_886 = (FStar_Absyn_Syntax.targ wp)
in (_114_886)::[])
in (_114_888)::_114_887))
in (_114_890)::_114_889))
in (md.FStar_Absyn_Syntax.close_wp, _114_891))
in (FStar_Absyn_Syntax.mk_Typ_app _114_892 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(
# 956 "FStar.Tc.Util.fst"
let bs = (let _114_893 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_114_893)::[])
in (
# 957 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _114_898 = (let _114_897 = (let _114_896 = (FStar_Absyn_Syntax.targ res_t)
in (let _114_895 = (let _114_894 = (FStar_Absyn_Syntax.targ wp)
in (_114_894)::[])
in (_114_896)::_114_895))
in (md.FStar_Absyn_Syntax.close_wp_t, _114_897))
in (FStar_Absyn_Syntax.mk_Typ_app _114_898 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_lid (l, t) -> begin
wp
end
| FStar_Tc_Env.Binding_sig (s) -> begin
(FStar_All.failwith "impos")
end)) bindings wp0))
in (
# 965 "FStar.Tc.Util.fst"
let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 966 "FStar.Tc.Util.fst"
let _35_1470 = (destruct_comp c)
in (match (_35_1470) with
| (t, wp, wlp) -> begin
(
# 967 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 968 "FStar.Tc.Util.fst"
let wp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wp)
in (
# 969 "FStar.Tc.Util.fst"
let wlp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.FStar_Absyn_Syntax.result_typ wp wlp c.FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (
# 971 "FStar.Tc.Util.fst"
let _35_1474 = lc
in {FStar_Absyn_Syntax.eff_name = _35_1474.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _35_1474.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _35_1474.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

# 971 "FStar.Tc.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (
# 974 "FStar.Tc.Util.fst"
let refine = (fun _35_1480 -> (match (()) with
| () -> begin
(
# 975 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Absyn_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Absyn_Util.is_partial_return c) then begin
c
end else begin
(
# 980 "FStar.Tc.Util.fst"
let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 981 "FStar.Tc.Util.fst"
let t = c.FStar_Absyn_Syntax.result_typ
in (
# 982 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Syntax.mk_Comp c)
in (
# 983 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.new_bvd None)
in (
# 984 "FStar.Tc.Util.fst"
let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (
# 985 "FStar.Tc.Util.fst"
let ret = (let _114_907 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _114_907))
in (
# 986 "FStar.Tc.Util.fst"
let eq_ret = (let _114_909 = (let _114_908 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_114_908))
in (weaken_precondition env ret _114_909))
in (let _114_912 = (let _114_911 = (let _114_910 = (lcomp_of_comp c)
in (bind env None _114_910 (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_114_911.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _114_912 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
end
end)
end))
in (
# 988 "FStar.Tc.Util.fst"
let flags = if (((not ((FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.FStar_Absyn_Syntax.cflags
end else begin
lc.FStar_Absyn_Syntax.cflags
end
in (
# 994 "FStar.Tc.Util.fst"
let _35_1490 = lc
in {FStar_Absyn_Syntax.eff_name = _35_1490.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _35_1490.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

# 994 "FStar.Tc.Util.fst"
let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _114_924 = (let _114_923 = (let _114_922 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _114_921 = (FStar_Tc_Env.get_range env)
in (_114_922, _114_921)))
in FStar_Absyn_Syntax.Error (_114_923))
in (Prims.raise _114_924))
end
| Some (g) -> begin
(e, c', g)
end))

# 1000 "FStar.Tc.Util.fst"
let maybe_instantiate_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.implicits) = (fun env t k -> (
# 1003 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(t, k, [])
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 1007 "FStar.Tc.Util.fst"
let rec aux = (fun subst _35_9 -> (match (_35_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_35_1514)))::rest -> begin
(
# 1009 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1010 "FStar.Tc.Util.fst"
let _35_1522 = (new_implicit_tvar env k)
in (match (_35_1522) with
| (t, u) -> begin
(
# 1011 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (
# 1012 "FStar.Tc.Util.fst"
let _35_1528 = (aux subst rest)
in (match (_35_1528) with
| (args, bs, subst, us) -> begin
(let _114_938 = (let _114_937 = (let _114_936 = (FStar_All.pipe_left (fun _114_935 -> Some (_114_935)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _114_936))
in (_114_937)::args)
in (_114_938, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_35_1533)))::rest -> begin
(
# 1016 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1017 "FStar.Tc.Util.fst"
let _35_1541 = (new_implicit_evar env t)
in (match (_35_1541) with
| (v, u) -> begin
(
# 1018 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (
# 1019 "FStar.Tc.Util.fst"
let _35_1547 = (aux subst rest)
in (match (_35_1547) with
| (args, bs, subst, us) -> begin
(let _114_942 = (let _114_941 = (let _114_940 = (FStar_All.pipe_left (fun _114_939 -> Some (_114_939)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _114_940))
in (_114_941)::args)
in (_114_942, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (
# 1023 "FStar.Tc.Util.fst"
let _35_1553 = (aux [] bs)
in (match (_35_1553) with
| (args, bs, subst, implicits) -> begin
(
# 1024 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (
# 1025 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _114_943 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_114_943, k, implicits))))
end)))
end
| _35_1557 -> begin
(t, k, [])
end)
end))

# 1028 "FStar.Tc.Util.fst"
let maybe_instantiate : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.implicits) = (fun env e t -> (
# 1031 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 1035 "FStar.Tc.Util.fst"
let rec aux = (fun subst _35_10 -> (match (_35_10) with
| (FStar_Util.Inl (a), _35_1573)::rest -> begin
(
# 1037 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1038 "FStar.Tc.Util.fst"
let _35_1579 = (new_implicit_tvar env k)
in (match (_35_1579) with
| (t, u) -> begin
(
# 1039 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (
# 1040 "FStar.Tc.Util.fst"
let _35_1585 = (aux subst rest)
in (match (_35_1585) with
| (args, bs, subst, us) -> begin
(let _114_957 = (let _114_956 = (let _114_955 = (FStar_All.pipe_left (fun _114_954 -> Some (_114_954)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _114_955))
in (_114_956)::args)
in (_114_957, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_35_1590)))::rest -> begin
(
# 1044 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1045 "FStar.Tc.Util.fst"
let _35_1598 = (new_implicit_evar env t)
in (match (_35_1598) with
| (v, u) -> begin
(
# 1046 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (
# 1047 "FStar.Tc.Util.fst"
let _35_1604 = (aux subst rest)
in (match (_35_1604) with
| (args, bs, subst, us) -> begin
(let _114_961 = (let _114_960 = (let _114_959 = (FStar_All.pipe_left (fun _114_958 -> Some (_114_958)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _114_959))
in (_114_960)::args)
in (_114_961, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (
# 1051 "FStar.Tc.Util.fst"
let _35_1610 = (aux [] bs)
in (match (_35_1610) with
| (args, bs, subst, implicits) -> begin
(
# 1052 "FStar.Tc.Util.fst"
let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _35_1617 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(
# 1058 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _114_968 = (mk_exp_app e args (Some (t)))
in (_114_968, t, implicits)))
end else begin
(e, t, [])
end
end
| _35_1621 -> begin
(
# 1062 "FStar.Tc.Util.fst"
let t = (let _114_969 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _114_969 (FStar_Absyn_Util.subst_typ subst)))
in (let _114_970 = (mk_exp_app e args (Some (t)))
in (_114_970, t, implicits)))
end))
end)))
end
| _35_1624 -> begin
(e, t, [])
end)
end))

# 1066 "FStar.Tc.Util.fst"
let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (
# 1069 "FStar.Tc.Util.fst"
let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _114_979 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_114_979, false))
end else begin
(let _114_980 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_114_980, true))
end
in (match (gopt) with
| (None, _35_1632) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(
# 1076 "FStar.Tc.Util.fst"
let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(
# 1079 "FStar.Tc.Util.fst"
let lc = (
# 1079 "FStar.Tc.Util.fst"
let _35_1640 = lc
in {FStar_Absyn_Syntax.eff_name = _35_1640.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _35_1640.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _35_1640.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(
# 1082 "FStar.Tc.Util.fst"
let g = (
# 1082 "FStar.Tc.Util.fst"
let _35_1645 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _35_1645.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _35_1645.FStar_Tc_Rel.implicits})
in (
# 1083 "FStar.Tc.Util.fst"
let strengthen = (fun _35_1649 -> (match (()) with
| () -> begin
(
# 1084 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 1086 "FStar.Tc.Util.fst"
let _35_1651 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _114_984 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _114_983 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _114_984 _114_983)))
end else begin
()
end
in (
# 1089 "FStar.Tc.Util.fst"
let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 1090 "FStar.Tc.Util.fst"
let _35_1656 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_35_1656) with
| (a, kwp) -> begin
(
# 1091 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (
# 1092 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (
# 1093 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.new_bvd None)
in (
# 1094 "FStar.Tc.Util.fst"
let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (
# 1095 "FStar.Tc.Util.fst"
let wp = (let _114_989 = (let _114_988 = (let _114_987 = (FStar_Absyn_Syntax.targ t)
in (let _114_986 = (let _114_985 = (FStar_Absyn_Syntax.varg xexp)
in (_114_985)::[])
in (_114_987)::_114_986))
in (md.FStar_Absyn_Syntax.ret, _114_988))
in (FStar_Absyn_Syntax.mk_Typ_app _114_989 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (
# 1096 "FStar.Tc.Util.fst"
let cret = (let _114_990 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _114_990))
in (
# 1097 "FStar.Tc.Util.fst"
let guard = if apply_guard then begin
(let _114_993 = (let _114_992 = (let _114_991 = (FStar_Absyn_Syntax.varg xexp)
in (_114_991)::[])
in (f, _114_992))
in (FStar_Absyn_Syntax.mk_Typ_app _114_993 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (
# 1098 "FStar.Tc.Util.fst"
let _35_1666 = (let _114_1001 = (FStar_All.pipe_left (fun _114_998 -> Some (_114_998)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _114_1000 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _114_999 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _114_1001 _114_1000 e cret _114_999))))
in (match (_35_1666) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 1105 "FStar.Tc.Util.fst"
let c = (let _114_1003 = (let _114_1002 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _114_1002))
in (bind env (Some (e)) _114_1003 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (
# 1106 "FStar.Tc.Util.fst"
let c = (c.FStar_Absyn_Syntax.comp ())
in (
# 1107 "FStar.Tc.Util.fst"
let _35_1669 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _114_1004 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _114_1004))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (
# 1110 "FStar.Tc.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _35_11 -> (match (_35_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _35_1675 -> begin
[]
end))))
in (
# 1111 "FStar.Tc.Util.fst"
let lc = (
# 1111 "FStar.Tc.Util.fst"
let _35_1677 = lc
in (let _114_1006 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _114_1006; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

# 1112 "FStar.Tc.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 1119 "FStar.Tc.Util.fst"
let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(
# 1124 "FStar.Tc.Util.fst"
let ue = (let _114_1011 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _114_1011))
in (
# 1125 "FStar.Tc.Util.fst"
let ut = (let _114_1012 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _114_1012))
in (
# 1126 "FStar.Tc.Util.fst"
let uk = (let _114_1013 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _114_1013))
in (
# 1127 "FStar.Tc.Util.fst"
let union = (FStar_String.concat "," (FStar_List.append (FStar_List.append ue ut) uk))
in (
# 1129 "FStar.Tc.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 1130 "FStar.Tc.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 1131 "FStar.Tc.Util.fst"
let _35_1689 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 1132 "FStar.Tc.Util.fst"
let _35_1691 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 1133 "FStar.Tc.Util.fst"
let _35_1693 = (let _114_1015 = (let _114_1014 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _114_1014))
in (FStar_Tc_Errors.report r _114_1015))
in (
# 1136 "FStar.Tc.Util.fst"
let _35_1695 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))

# 1137 "FStar.Tc.Util.fst"
let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _114_1023 = (FStar_Util.for_all (fun _35_1703 -> (match (_35_1703) with
| (_35_1701, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _114_1023)) then begin
None
end else begin
(
# 1143 "FStar.Tc.Util.fst"
let norm = (fun c -> (
# 1144 "FStar.Tc.Util.fst"
let _35_1706 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _114_1026 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _114_1026))
end else begin
()
end
in (
# 1145 "FStar.Tc.Util.fst"
let steps = (FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
in (
# 1146 "FStar.Tc.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::[]) env c)
end
in (
# 1150 "FStar.Tc.Util.fst"
let _35_1710 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _114_1027 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _114_1027))
end else begin
()
end
in c)))))
in (
# 1152 "FStar.Tc.Util.fst"
let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (
# 1153 "FStar.Tc.Util.fst"
let gen_uvars = (fun uvs -> (let _114_1030 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _114_1030 FStar_Util.set_elements)))
in (
# 1154 "FStar.Tc.Util.fst"
let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _35_1719) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _35_12 -> (match (_35_12) with
| (FStar_Util.Inl (_35_1724), _35_1727) -> begin
true
end
| _35_1730 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _35_1732 -> begin
true
end))
in (
# 1161 "FStar.Tc.Util.fst"
let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _35_1735 -> (match (_35_1735) with
| (e, c) -> begin
(
# 1162 "FStar.Tc.Util.fst"
let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _114_1035 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _114_1035)) then begin
([], e, c)
end else begin
(
# 1165 "FStar.Tc.Util.fst"
let c = (norm c)
in (
# 1166 "FStar.Tc.Util.fst"
let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (
# 1167 "FStar.Tc.Util.fst"
let t = ct.FStar_Absyn_Syntax.result_typ
in (
# 1168 "FStar.Tc.Util.fst"
let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in (
# 1169 "FStar.Tc.Util.fst"
let uvs = (gen_uvars uvt.FStar_Absyn_Syntax.uvars_t)
in (
# 1170 "FStar.Tc.Util.fst"
let _35_1751 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _114_1036 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _114_1036))) then begin
(
# 1174 "FStar.Tc.Util.fst"
let _35_1747 = (destruct_comp ct)
in (match (_35_1747) with
| (_35_1743, wp, _35_1746) -> begin
(
# 1175 "FStar.Tc.Util.fst"
let binder = (let _114_1037 = (FStar_Absyn_Syntax.null_v_binder t)
in (_114_1037)::[])
in (
# 1176 "FStar.Tc.Util.fst"
let post = (let _114_1041 = (let _114_1038 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _114_1038))
in (let _114_1040 = (let _114_1039 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_114_1039))
in (FStar_Absyn_Syntax.mk_Typ_lam _114_1041 _114_1040 t.FStar_Absyn_Syntax.pos)))
in (
# 1177 "FStar.Tc.Util.fst"
let vc = (let _114_1048 = (let _114_1047 = (let _114_1046 = (let _114_1045 = (let _114_1044 = (FStar_Absyn_Syntax.targ post)
in (_114_1044)::[])
in (wp, _114_1045))
in (FStar_Absyn_Syntax.mk_Typ_app _114_1046))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _114_1047))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _114_1048))
in (let _114_1049 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _114_1049)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (
# 1182 "FStar.Tc.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _35_1757 -> (match (_35_1757) with
| (uvs, e, c) -> begin
(
# 1183 "FStar.Tc.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _35_1760 -> (match (_35_1760) with
| (u, k) -> begin
(
# 1184 "FStar.Tc.Util.fst"
let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_35_1798) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _35_1801 -> begin
(
# 1189 "FStar.Tc.Util.fst"
let a = (let _114_1054 = (let _114_1053 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _114_1052 -> Some (_114_1052)) _114_1053))
in (FStar_Absyn_Util.new_bvd _114_1054))
in (
# 1190 "FStar.Tc.Util.fst"
let t = (let _114_1055 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _114_1055 k))
in (
# 1192 "FStar.Tc.Util.fst"
let _35_1804 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _114_1057 = (FStar_All.pipe_left (fun _114_1056 -> Some (_114_1056)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (a), _114_1057)))
end))))
in (
# 1196 "FStar.Tc.Util.fst"
let t = (match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.function_formals)) with
| Some (bs, cod) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.append tvars bs), cod) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(FStar_Absyn_Util.comp_result c)
end
| _35_1815 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (
# 1200 "FStar.Tc.Util.fst"
let e = (match (tvars) with
| [] -> begin
e
end
| _35_1819 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _114_1058 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _114_1058)))))
end))))
in Some (ecs)))))))
end)

# 1204 "FStar.Tc.Util.fst"
let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (
# 1207 "FStar.Tc.Util.fst"
let _35_1831 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _114_1067 = (let _114_1066 = (FStar_List.map (fun _35_1830 -> (match (_35_1830) with
| (lb, _35_1827, _35_1829) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _114_1066 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _114_1067))
end else begin
()
end
in (match ((let _114_1069 = (FStar_All.pipe_right lecs (FStar_List.map (fun _35_1837 -> (match (_35_1837) with
| (_35_1834, e, c) -> begin
(e, c)
end))))
in (gen verify env _114_1069))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _35_1846 _35_1849 -> (match ((_35_1846, _35_1849)) with
| ((l, _35_1843, _35_1845), (e, c)) -> begin
(
# 1212 "FStar.Tc.Util.fst"
let _35_1850 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _114_1074 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _114_1073 = (FStar_Absyn_Print.lbname_to_string l)
in (let _114_1072 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _114_1074 _114_1073 _114_1072))))
end else begin
()
end
in (l, e, c))
end)) lecs ecs)
end)))

# 1213 "FStar.Tc.Util.fst"
let check_unresolved_implicits : FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun g -> (
# 1216 "FStar.Tc.Util.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Uvar -> begin
true
end
| _35_1857 -> begin
false
end))
in (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _35_13 -> (match (_35_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _35_1863) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_35_1867, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _35_1873 -> begin
()
end)))

# 1221 "FStar.Tc.Util.fst"
let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (
# 1224 "FStar.Tc.Util.fst"
let discharge = (fun g -> (
# 1225 "FStar.Tc.Util.fst"
let _35_1879 = (FStar_Tc_Rel.try_discharge_guard env g)
in (
# 1226 "FStar.Tc.Util.fst"
let _35_1881 = (check_unresolved_implicits g)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (
# 1228 "FStar.Tc.Util.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _114_1089 = (discharge g)
in (let _114_1088 = (lc.FStar_Absyn_Syntax.comp ())
in (_114_1089, _114_1088)))
end else begin
(
# 1231 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 1232 "FStar.Tc.Util.fst"
let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (
# 1233 "FStar.Tc.Util.fst"
let c = (let _114_1090 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _114_1090 FStar_Absyn_Util.comp_to_comp_typ))
in (
# 1234 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 1235 "FStar.Tc.Util.fst"
let _35_1892 = (destruct_comp c)
in (match (_35_1892) with
| (t, wp, _35_1891) -> begin
(
# 1236 "FStar.Tc.Util.fst"
let vc = (let _114_1096 = (let _114_1094 = (let _114_1093 = (FStar_Absyn_Syntax.targ t)
in (let _114_1092 = (let _114_1091 = (FStar_Absyn_Syntax.targ wp)
in (_114_1091)::[])
in (_114_1093)::_114_1092))
in (md.FStar_Absyn_Syntax.trivial, _114_1094))
in (let _114_1095 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _114_1096 (Some (FStar_Absyn_Syntax.ktype)) _114_1095)))
in (
# 1237 "FStar.Tc.Util.fst"
let g = (let _114_1097 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _114_1097))
in (let _114_1099 = (discharge g)
in (let _114_1098 = (FStar_Absyn_Syntax.mk_Comp c)
in (_114_1099, _114_1098)))))
end))))))
end)))

# 1238 "FStar.Tc.Util.fst"
let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (
# 1244 "FStar.Tc.Util.fst"
let short_bin_op_e = (fun f _35_14 -> (match (_35_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _35_1904)::[] -> begin
(let _114_1118 = (f fst)
in (FStar_All.pipe_right _114_1118 (fun _114_1117 -> Some (_114_1117))))
end
| _35_1908 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1249 "FStar.Tc.Util.fst"
let table = (
# 1250 "FStar.Tc.Util.fst"
let op_and_e = (fun e -> (let _114_1124 = (FStar_Absyn_Util.b2t e)
in (_114_1124, FStar_Absyn_Const.exp_false_bool)))
in (
# 1251 "FStar.Tc.Util.fst"
let op_or_e = (fun e -> (let _114_1128 = (let _114_1127 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _114_1127))
in (_114_1128, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _35_1916) -> begin
(
# 1257 "FStar.Tc.Util.fst"
let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _35_1922 -> (match (_35_1922) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _114_1146 = (mk seen_args)
in Some (_114_1146))
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
| _35_1927 -> begin
None
end))))

# 1262 "FStar.Tc.Util.fst"
let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (
# 1269 "FStar.Tc.Util.fst"
let short_bin_op_t = (fun f _35_15 -> (match (_35_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _35_1937)::[] -> begin
(f fst)
end
| _35_1941 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1274 "FStar.Tc.Util.fst"
let op_and_t = (fun t -> (let _114_1167 = (unlabel t)
in (FStar_All.pipe_right _114_1167 (fun _114_1166 -> FStar_Tc_Rel.NonTrivial (_114_1166)))))
in (
# 1275 "FStar.Tc.Util.fst"
let op_or_t = (fun t -> (let _114_1172 = (let _114_1170 = (unlabel t)
in (FStar_All.pipe_right _114_1170 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _114_1172 (fun _114_1171 -> FStar_Tc_Rel.NonTrivial (_114_1171)))))
in (
# 1276 "FStar.Tc.Util.fst"
let op_imp_t = (fun t -> (let _114_1176 = (unlabel t)
in (FStar_All.pipe_right _114_1176 (fun _114_1175 -> FStar_Tc_Rel.NonTrivial (_114_1175)))))
in (
# 1277 "FStar.Tc.Util.fst"
let short_op_ite = (fun _35_16 -> (match (_35_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _35_1953)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _35_1959)::[] -> begin
(let _114_1180 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _114_1180 (fun _114_1179 -> FStar_Tc_Rel.NonTrivial (_114_1179))))
end
| _35_1964 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1282 "FStar.Tc.Util.fst"
let table = ((FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _35_1972) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _35_1982; FStar_Absyn_Syntax.pos = _35_1980; FStar_Absyn_Syntax.fvs = _35_1978; FStar_Absyn_Syntax.uvs = _35_1976}) -> begin
(
# 1295 "FStar.Tc.Util.fst"
let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _35_1990 -> (match (_35_1990) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _114_1207 = (mk seen_args)
in Some (_114_1207))
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
| _35_1995 -> begin
FStar_Tc_Rel.Trivial
end))))))))

# 1300 "FStar.Tc.Util.fst"
let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (
# 1303 "FStar.Tc.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 1304 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _114_1221 = (let _114_1220 = (let _114_1219 = (let _114_1218 = (let _114_1217 = (let _114_1216 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _114_1216))
in (_114_1217)::[])
in (ens, _114_1218))
in (FStar_Absyn_Syntax.mk_Typ_app _114_1219 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _114_1220))
in (FStar_Absyn_Syntax.mk_Typ_refine _114_1221 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (
# 1306 "FStar.Tc.Util.fst"
let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_35_2005) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _35_2020)::(FStar_Util.Inl (ens), _35_2014)::_35_2010 -> begin
(let _114_1227 = (let _114_1224 = (norm req)
in Some (_114_1224))
in (let _114_1226 = (let _114_1225 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _114_1225))
in (_114_1227, _114_1226)))
end
| _35_2024 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1319 "FStar.Tc.Util.fst"
let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_35_2027) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _35_2042)::(FStar_Util.Inl (wlp), _35_2036)::_35_2032 -> begin
(
# 1325 "FStar.Tc.Util.fst"
let _35_2054 = (match ((let _114_1229 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _114_1228 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_114_1229, _114_1228)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _35_2051 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_35_2054) with
| (as_req, as_ens) -> begin
(
# 1328 "FStar.Tc.Util.fst"
let req = (let _114_1236 = (let _114_1235 = (let _114_1234 = (let _114_1231 = (FStar_All.pipe_left (fun _114_1230 -> Some (_114_1230)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _114_1231))
in (let _114_1233 = (let _114_1232 = (FStar_Absyn_Syntax.targ wp)
in (_114_1232)::[])
in (_114_1234)::_114_1233))
in (as_req, _114_1235))
in (FStar_Absyn_Syntax.mk_Typ_app _114_1236 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (
# 1329 "FStar.Tc.Util.fst"
let ens = (let _114_1243 = (let _114_1242 = (let _114_1241 = (let _114_1238 = (FStar_All.pipe_left (fun _114_1237 -> Some (_114_1237)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _114_1238))
in (let _114_1240 = (let _114_1239 = (FStar_Absyn_Syntax.targ wlp)
in (_114_1239)::[])
in (_114_1241)::_114_1240))
in (as_ens, _114_1242))
in (FStar_Absyn_Syntax.mk_Typ_app _114_1243 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _114_1247 = (let _114_1244 = (norm req)
in Some (_114_1244))
in (let _114_1246 = (let _114_1245 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _114_1245))
in (_114_1247, _114_1246)))))
end))
end
| _35_2058 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




