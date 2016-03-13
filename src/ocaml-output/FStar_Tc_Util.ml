
open Prims
# 31 "FStar.Tc.Util.fst"
type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

# 85 "FStar.Tc.Util.fst"
let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

# 86 "FStar.Tc.Util.fst"
let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _123_10 = (FStar_Tc_Env.get_range env)
in (let _123_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _123_10 _123_9))))

# 90 "FStar.Tc.Util.fst"
let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

# 92 "FStar.Tc.Util.fst"
let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))

# 95 "FStar.Tc.Util.fst"
let syn' = (fun env k -> (let _123_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _123_29 k)))

# 97 "FStar.Tc.Util.fst"
let is_xvar_free : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun x t -> (
# 98 "FStar.Tc.Util.fst"
let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) f.FStar_Absyn_Syntax.fxvs)))

# 101 "FStar.Tc.Util.fst"
let is_tvar_free : FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun a t -> (
# 102 "FStar.Tc.Util.fst"
let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun) f.FStar_Absyn_Syntax.ftvs)))

# 105 "FStar.Tc.Util.fst"
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
(let _123_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _123_52 -> Some (_123_52)) _123_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _123_57 = (let _123_56 = (let _123_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _123_54 = (FStar_Tc_Env.get_range env)
in (_123_55, _123_54)))
in FStar_Absyn_Syntax.Error (_123_56))
in (Prims.raise _123_57))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _123_61 = (let _123_60 = (let _123_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _123_58 = (FStar_Tc_Env.get_range env)
in (_123_59, _123_58)))
in FStar_Absyn_Syntax.Error (_123_60))
in (Prims.raise _123_61))
end
| Some (g) -> begin
(
# 121 "FStar.Tc.Util.fst"
let _41_53 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _123_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _123_62))
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
| _41_59 -> begin
(
# 126 "FStar.Tc.Util.fst"
let _41_60 = e
in (let _123_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _41_60.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _123_63; FStar_Absyn_Syntax.pos = _41_60.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _41_60.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _41_60.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))

# 129 "FStar.Tc.Util.fst"
let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

# 134 "FStar.Tc.Util.fst"
let as_uvar_e = (fun _41_1 -> (match (_41_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _41_75); FStar_Absyn_Syntax.tk = _41_72; FStar_Absyn_Syntax.pos = _41_70; FStar_Absyn_Syntax.fvs = _41_68; FStar_Absyn_Syntax.uvs = _41_66} -> begin
uv
end
| _41_80 -> begin
(FStar_All.failwith "Impossible")
end))

# 137 "FStar.Tc.Util.fst"
let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _41_92); FStar_Absyn_Syntax.tk = _41_89; FStar_Absyn_Syntax.pos = _41_87; FStar_Absyn_Syntax.fvs = _41_85; FStar_Absyn_Syntax.uvs = _41_83} -> begin
uv
end
| _41_97 -> begin
(FStar_All.failwith "Impossible")
end))

# 140 "FStar.Tc.Util.fst"
let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _123_73 = (let _123_72 = (FStar_Tc_Env.get_range env)
in (let _123_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _123_72 _123_71)))
in (FStar_All.pipe_right _123_73 Prims.fst)))

# 141 "FStar.Tc.Util.fst"
let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _123_80 = (let _123_79 = (FStar_Tc_Env.get_range env)
in (let _123_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _123_79 _123_78 k)))
in (FStar_All.pipe_right _123_80 Prims.fst)))

# 142 "FStar.Tc.Util.fst"
let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _123_87 = (let _123_86 = (FStar_Tc_Env.get_range env)
in (let _123_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _123_86 _123_85 t)))
in (FStar_All.pipe_right _123_87 Prims.fst)))

# 143 "FStar.Tc.Util.fst"
let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (
# 144 "FStar.Tc.Util.fst"
let _41_107 = (let _123_93 = (FStar_Tc_Env.get_range env)
in (let _123_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _123_93 _123_92 k)))
in (match (_41_107) with
| (t, u) -> begin
(let _123_95 = (let _123_94 = (as_uvar_t u)
in (_123_94, u.FStar_Absyn_Syntax.pos))
in (t, _123_95))
end)))

# 146 "FStar.Tc.Util.fst"
let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (
# 147 "FStar.Tc.Util.fst"
let _41_112 = (let _123_101 = (FStar_Tc_Env.get_range env)
in (let _123_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _123_101 _123_100 t)))
in (match (_41_112) with
| (e, u) -> begin
(let _123_103 = (let _123_102 = (as_uvar_e u)
in (_123_102, u.FStar_Absyn_Syntax.pos))
in (e, _123_103))
end)))

# 149 "FStar.Tc.Util.fst"
let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _123_106 = (let _123_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _123_105))
in (FStar_All.failwith _123_106))
end
| Some (tk) -> begin
tk
end))

# 152 "FStar.Tc.Util.fst"
let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _41_2 -> (match (_41_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _123_111 = (let _123_110 = (force_tk t)
in FStar_Util.Inl (_123_110))
in (_123_111, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _123_113 = (let _123_112 = (force_tk v)
in FStar_Util.Inr (_123_112))
in (_123_113, imp))
end)))))

# 157 "FStar.Tc.Util.fst"
let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _41_3 -> (match (_41_3) with
| Some (FStar_Absyn_Syntax.Implicit (_41_129)) -> begin
true
end
| _41_133 -> begin
false
end))

# 158 "FStar.Tc.Util.fst"
let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (
# 159 "FStar.Tc.Util.fst"
let ktop = (let _123_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _123_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
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
| (_41_149, qual)::_41_147 -> begin
(is_implicit qual)
end
| _41_154 -> begin
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
(let _123_137 = (let _123_134 = (let _123_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _123_133))
in (FStar_All.pipe_right _123_134 Prims.fst))
in (FStar_All.pipe_right _123_137 (fun x -> (let _123_136 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (x), _123_136)))))
end
| FStar_Util.Inr (x) -> begin
(let _123_142 = (let _123_139 = (let _123_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _123_138))
in (FStar_All.pipe_right _123_139 Prims.fst))
in (FStar_All.pipe_right _123_142 (fun x -> (let _123_141 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (x), _123_141)))))
end)
in (
# 172 "FStar.Tc.Util.fst"
let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _123_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_123_143)::subst)
end
in (
# 173 "FStar.Tc.Util.fst"
let _41_173 = (mk_implicits vars subst brest)
in (match (_41_173) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _123_144 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _123_144))
end
end
| _41_175 -> begin
(let _123_145 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _123_145))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(
# 179 "FStar.Tc.Util.fst"
let _41_178 = (let _123_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _123_146 [] bs))
in (match (_41_178) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_41_180, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_41_185) -> begin
(
# 185 "FStar.Tc.Util.fst"
let fvs = (FStar_Absyn_Util.freevars_kind k)
in (
# 186 "FStar.Tc.Util.fst"
let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (
# 187 "FStar.Tc.Util.fst"
let kres = (let _123_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _123_147 Prims.fst))
in (
# 188 "FStar.Tc.Util.fst"
let bs = (let _123_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _123_148))
in (
# 189 "FStar.Tc.Util.fst"
let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (
# 190 "FStar.Tc.Util.fst"
let _41_192 = (let _123_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _123_149))
in ([], bs, kres)))))))
end
| _41_195 -> begin
(let _123_152 = (let _123_151 = (let _123_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_123_150, r))
in FStar_Absyn_Syntax.Error (_123_151))
in (Prims.raise _123_152))
end))
in (aux ktop)))))

# 197 "FStar.Tc.Util.fst"
let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _41_4 -> (match (_41_4) with
| Some (FStar_Absyn_Syntax.Implicit (_41_198)) -> begin
true
end
| _41_202 -> begin
false
end))

# 203 "FStar.Tc.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (
# 207 "FStar.Tc.Util.fst"
let pvar_eq = (fun x y -> (match ((x, y)) with
| (FStar_Tc_Env.Binding_var (x, _41_211), FStar_Tc_Env.Binding_var (y, _41_216)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _41_222), FStar_Tc_Env.Binding_typ (y, _41_227)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _41_232 -> begin
false
end))
in (
# 212 "FStar.Tc.Util.fst"
let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _41_5 -> (match (_41_5) with
| FStar_Tc_Env.Binding_var (x, _41_238) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _41_243) -> begin
FStar_Util.Inl (x)
end
| _41_247 -> begin
(FStar_All.failwith "impos")
end)))))
in (
# 219 "FStar.Tc.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _41_254) -> begin
(
# 228 "FStar.Tc.Util.fst"
let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (
# 229 "FStar.Tc.Util.fst"
let _41_260 = (let _123_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p _123_174 t))
in (match (_41_260) with
| (e, u) -> begin
(
# 230 "FStar.Tc.Util.fst"
let p = (
# 230 "FStar.Tc.Util.fst"
let _41_261 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _41_261.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _41_261.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _41_266) -> begin
(
# 234 "FStar.Tc.Util.fst"
let k = (new_kvar env)
in (
# 235 "FStar.Tc.Util.fst"
let _41_272 = (let _123_175 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _123_175 k))
in (match (_41_272) with
| (t, u) -> begin
(
# 236 "FStar.Tc.Util.fst"
let p = (
# 236 "FStar.Tc.Util.fst"
let _41_273 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _41_273.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _41_273.FStar_Absyn_Syntax.p})
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
let w = (let _123_177 = (let _123_176 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _123_176))
in FStar_Tc_Env.Binding_var (_123_177))
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
let b = (let _123_179 = (let _123_178 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _123_178))
in FStar_Tc_Env.Binding_var (_123_179))
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
let w = (let _123_181 = (let _123_180 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _123_180))
in FStar_Tc_Env.Binding_typ (_123_181))
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
let b = (let _123_183 = (let _123_182 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _123_182))
in FStar_Tc_Env.Binding_typ (_123_183))
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
let _41_332 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _41_310 _41_313 -> (match ((_41_310, _41_313)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 270 "FStar.Tc.Util.fst"
let _41_320 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_41_320) with
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
in (match (_41_332) with
| (b, a, w, env, args, pats) -> begin
(
# 275 "FStar.Tc.Util.fst"
let e = (let _123_191 = (let _123_190 = (let _123_189 = (let _123_188 = (let _123_187 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _123_186 = (FStar_All.pipe_right args FStar_List.rev)
in (_123_187, _123_186)))
in (FStar_Absyn_Syntax.mk_Exp_app' _123_188 None p.FStar_Absyn_Syntax.p))
in (_123_189, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_123_190))
in (FStar_Absyn_Syntax.mk_Exp_meta _123_191))
in (let _123_194 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _123_193 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _123_192 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_123_194, _123_193, _123_192, env, FStar_Util.Inr (e), (
# 281 "FStar.Tc.Util.fst"
let _41_334 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _41_334.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _41_334.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_41_337) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 284 "FStar.Tc.Util.fst"
let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 287 "FStar.Tc.Util.fst"
let pats = (FStar_List.map (fun _41_349 -> (match (_41_349) with
| (p, imp) -> begin
(let _123_200 = (elaborate_pat env p)
in (_123_200, imp))
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
| _41_355 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end)
end
| Some (f, _41_358) -> begin
(
# 296 "FStar.Tc.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _41_371::_41_369) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end
| (_41_377::_41_375, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(
# 302 "FStar.Tc.Util.fst"
let a = (let _123_206 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _123_206 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _123_208 = (let _123_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _123_207))
in (_123_208, (as_imp imp)))
end else begin
(let _123_210 = (let _123_209 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _123_209))
in (_123_210, (as_imp imp)))
end)
end
| (FStar_Util.Inr (_41_388), Some (FStar_Absyn_Syntax.Implicit (dot))) -> begin
(
# 308 "FStar.Tc.Util.fst"
let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in if (allow_implicits && dot) then begin
(let _123_215 = (let _123_214 = (let _123_212 = (let _123_211 = (FStar_Absyn_Util.bvar_to_exp a)
in (a, _123_211))
in FStar_Absyn_Syntax.Pat_dot_term (_123_212))
in (let _123_213 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _123_214 None _123_213)))
in (_123_215, true))
end else begin
(let _123_217 = (let _123_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _123_216))
in (_123_217, true))
end)
end
| _41_396 -> begin
(let _123_221 = (let _123_220 = (let _123_219 = (let _123_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _123_218))
in (_123_219, (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_123_220))
in (Prims.raise _123_221))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _123_222 = (aux formals' pats')
in ((p, (as_imp imp)))::_123_222)
end
| ((FStar_Util.Inl (_41_424), imp), FStar_Absyn_Syntax.Pat_dot_typ (_41_429)) when allow_implicits -> begin
(let _123_223 = (aux formals' pats')
in ((p, (as_imp imp)))::_123_223)
end
| ((FStar_Util.Inl (_41_433), imp), _41_438) -> begin
(
# 321 "FStar.Tc.Util.fst"
let a = (let _123_224 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _123_224 FStar_Absyn_Syntax.kun))
in (
# 322 "FStar.Tc.Util.fst"
let p1 = if allow_implicits then begin
(let _123_225 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _123_225))
end else begin
(let _123_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _123_226))
end
in (
# 326 "FStar.Tc.Util.fst"
let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_41_443) -> begin
pats'
end
| _41_446 -> begin
pats
end)
in (let _123_227 = (aux formals' pats')
in ((p1, (as_imp imp)))::_123_227))))
end
| ((FStar_Util.Inr (_41_449), Some (FStar_Absyn_Syntax.Implicit (false))), _41_456) when p_imp -> begin
(let _123_228 = (aux formals' pats')
in ((p, true))::_123_228)
end
| ((FStar_Util.Inr (_41_459), Some (FStar_Absyn_Syntax.Implicit (dot))), _41_466) -> begin
(
# 333 "FStar.Tc.Util.fst"
let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 334 "FStar.Tc.Util.fst"
let p = if (allow_implicits && dot) then begin
(let _123_232 = (let _123_230 = (let _123_229 = (FStar_Absyn_Util.bvar_to_exp a)
in (a, _123_229))
in FStar_Absyn_Syntax.Pat_dot_term (_123_230))
in (let _123_231 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _123_232 None _123_231)))
end else begin
(let _123_233 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _123_233))
end
in (let _123_234 = (aux formals' pats)
in ((p, true))::_123_234)))
end
| ((FStar_Util.Inr (_41_471), imp), _41_476) -> begin
(let _123_235 = (aux formals' pats')
in ((p, (as_imp imp)))::_123_235)
end)
end))
in (aux f pats))
end)
in (
# 343 "FStar.Tc.Util.fst"
let _41_479 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _41_479.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _41_479.FStar_Absyn_Syntax.p}))))
end
| _41_482 -> begin
p
end))
in (
# 347 "FStar.Tc.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 348 "FStar.Tc.Util.fst"
let p = (elaborate_pat env p)
in (
# 354 "FStar.Tc.Util.fst"
let _41_494 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_41_494) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _41_497)) -> begin
(let _123_244 = (let _123_243 = (let _123_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_123_242, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_123_243))
in (Prims.raise _123_244))
end
| Some (FStar_Tc_Env.Binding_typ (x, _41_503)) -> begin
(let _123_247 = (let _123_246 = (let _123_245 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_123_245, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_123_246))
in (Prims.raise _123_247))
end
| _41_508 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 361 "FStar.Tc.Util.fst"
let as_arg = (fun _41_6 -> (match (_41_6) with
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
let _41_530 = (one_pat false env q)
in (match (_41_530) with
| (b, a, _41_527, te, q) -> begin
(
# 372 "FStar.Tc.Util.fst"
let _41_545 = (FStar_List.fold_right (fun p _41_535 -> (match (_41_535) with
| (w, args, pats) -> begin
(
# 373 "FStar.Tc.Util.fst"
let _41_541 = (one_pat false env p)
in (match (_41_541) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _123_261 = (let _123_260 = (let _123_259 = (let _123_257 = (vars_of_bindings a)
in (let _123_256 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _123_257 _123_256)))
in (let _123_258 = (FStar_Tc_Env.get_range env)
in (_123_259, _123_258)))
in FStar_Absyn_Syntax.Error (_123_260))
in (Prims.raise _123_261))
end else begin
(let _123_263 = (let _123_262 = (as_arg arg)
in (_123_262)::args)
in ((FStar_List.append w' w), _123_263, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_41_545) with
| (w, args, pats) -> begin
(let _123_265 = (let _123_264 = (as_arg te)
in (_123_264)::args)
in ((FStar_List.append b w), _123_265, (
# 378 "FStar.Tc.Util.fst"
let _41_546 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _41_546.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _41_546.FStar_Absyn_Syntax.p})))
end))
end))
end
| _41_549 -> begin
(
# 381 "FStar.Tc.Util.fst"
let _41_557 = (one_pat true env p)
in (match (_41_557) with
| (b, _41_552, _41_554, arg, p) -> begin
(let _123_267 = (let _123_266 = (as_arg arg)
in (_123_266)::[])
in (b, _123_267, p))
end))
end))
in (
# 384 "FStar.Tc.Util.fst"
let _41_561 = (top_level_pat_as_args env p)
in (match (_41_561) with
| (b, args, p) -> begin
(
# 385 "FStar.Tc.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map (fun _41_7 -> (match (_41_7) with
| (FStar_Util.Inl (_41_564), _41_567) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _41_572) -> begin
e
end))))
in (b, exps, p))
end))))))))))

# 390 "FStar.Tc.Util.fst"
let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (
# 391 "FStar.Tc.Util.fst"
let qq = p
in (
# 392 "FStar.Tc.Util.fst"
let rec aux = (fun p e -> (
# 393 "FStar.Tc.Util.fst"
let pkg = (fun q t -> (let _123_286 = (FStar_All.pipe_left (fun _123_285 -> Some (_123_285)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _123_286 p.FStar_Absyn_Syntax.p)))
in (
# 394 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_41_588), FStar_Absyn_Syntax.Exp_constant (_41_591)) -> begin
(let _123_287 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _123_287))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(
# 399 "FStar.Tc.Util.fst"
let _41_599 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _123_290 = (let _123_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _123_288 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _123_289 _123_288)))
in (FStar_All.failwith _123_290))
end else begin
()
end
in (
# 401 "FStar.Tc.Util.fst"
let _41_601 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _123_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _123_291 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _123_292 _123_291)))
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
let _41_604 = x
in {FStar_Absyn_Syntax.v = _41_604.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _41_604.FStar_Absyn_Syntax.p})
in (let _123_293 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _123_293))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(
# 408 "FStar.Tc.Util.fst"
let _41_612 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _123_296 = (let _123_295 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _123_294 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _123_295 _123_294)))
in (FStar_All.failwith _123_296))
end else begin
()
end
in (
# 410 "FStar.Tc.Util.fst"
let x = (
# 410 "FStar.Tc.Util.fst"
let _41_614 = x
in (let _123_297 = (force_tk e)
in {FStar_Absyn_Syntax.v = _41_614.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _123_297; FStar_Absyn_Syntax.p = _41_614.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _41_619), _41_623) -> begin
(
# 414 "FStar.Tc.Util.fst"
let x = (
# 414 "FStar.Tc.Util.fst"
let _41_625 = x
in (let _123_298 = (force_tk e)
in {FStar_Absyn_Syntax.v = _41_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _123_298; FStar_Absyn_Syntax.p = _41_625.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _41_635)) -> begin
(
# 418 "FStar.Tc.Util.fst"
let _41_639 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _123_299 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _123_299))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _41_656); FStar_Absyn_Syntax.tk = _41_653; FStar_Absyn_Syntax.pos = _41_651; FStar_Absyn_Syntax.fvs = _41_649; FStar_Absyn_Syntax.uvs = _41_647}, args)) -> begin
(
# 423 "FStar.Tc.Util.fst"
let _41_664 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _123_300 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _123_300))
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
(let _123_307 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _123_307))
end
| (arg::args, (argpat, _41_680)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_41_687))), FStar_Absyn_Syntax.Pat_dot_typ (_41_692)) -> begin
(
# 432 "FStar.Tc.Util.fst"
let x = (let _123_308 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _123_308))
in (
# 433 "FStar.Tc.Util.fst"
let q = (let _123_310 = (FStar_All.pipe_left (fun _123_309 -> Some (_123_309)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _123_310 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_41_700))), FStar_Absyn_Syntax.Pat_dot_term (_41_705)) -> begin
(
# 437 "FStar.Tc.Util.fst"
let x = (let _123_311 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _123_311))
in (
# 438 "FStar.Tc.Util.fst"
let q = (let _123_313 = (FStar_All.pipe_left (fun _123_312 -> Some (_123_312)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _123_313 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _41_715) -> begin
(
# 442 "FStar.Tc.Util.fst"
let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _41_723) -> begin
(
# 446 "FStar.Tc.Util.fst"
let pat = (let _123_314 = (aux argpat e)
in (_123_314, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _41_727 -> begin
(let _123_317 = (let _123_316 = (FStar_Absyn_Print.pat_to_string p)
in (let _123_315 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _123_316 _123_315)))
in (FStar_All.failwith _123_317))
end))
in (match_args [] args argpats))))
end
| _41_729 -> begin
(let _123_322 = (let _123_321 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _123_320 = (FStar_Absyn_Print.pat_to_string qq)
in (let _123_319 = (let _123_318 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _123_318 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _123_321 _123_320 _123_319))))
in (FStar_All.failwith _123_322))
end))))
and aux_t = (fun p t0 -> (
# 458 "FStar.Tc.Util.fst"
let pkg = (fun q k -> (let _123_330 = (FStar_All.pipe_left (fun _123_329 -> Some (_123_329)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _123_330 p.FStar_Absyn_Syntax.p)))
in (
# 459 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(
# 462 "FStar.Tc.Util.fst"
let _41_741 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _123_333 = (let _123_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _123_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _123_332 _123_331)))
in (FStar_All.failwith _123_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(
# 467 "FStar.Tc.Util.fst"
let _41_748 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _123_336 = (let _123_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _123_334 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _123_335 _123_334)))
in (FStar_All.failwith _123_336))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _41_752), _41_756) -> begin
(
# 472 "FStar.Tc.Util.fst"
let k0 = (force_tk t0)
in (
# 473 "FStar.Tc.Util.fst"
let a = (
# 473 "FStar.Tc.Util.fst"
let _41_759 = a
in {FStar_Absyn_Syntax.v = _41_759.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _41_759.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _41_763 -> begin
(let _123_340 = (let _123_339 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _123_338 = (FStar_Absyn_Print.pat_to_string p)
in (let _123_337 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _123_339 _123_338 _123_337))))
in (FStar_All.failwith _123_340))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _41_767) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 480 "FStar.Tc.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (let _123_342 = (FStar_All.pipe_left (fun _123_341 -> Some (_123_341)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _123_342 p.FStar_Absyn_Syntax.p)))
end
| (_41_771, e::[]) -> begin
(aux p e)
end
| _41_776 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 488 "FStar.Tc.Util.fst"
let rec decorated_pattern_as_exp : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.exp) = (fun pat -> (
# 489 "FStar.Tc.Util.fst"
let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _41_783 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (
# 494 "FStar.Tc.Util.fst"
let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (
# 496 "FStar.Tc.Util.fst"
let pat_as_arg = (fun _41_790 -> (match (_41_790) with
| (p, i) -> begin
(
# 497 "FStar.Tc.Util.fst"
let _41_793 = (decorated_pattern_as_either p)
in (match (_41_793) with
| (vars, te) -> begin
(let _123_362 = (let _123_361 = (FStar_Absyn_Syntax.as_implicit i)
in (te, _123_361))
in (vars, _123_362))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_41_795) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _123_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _123_365))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _123_368 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _123_368))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 511 "FStar.Tc.Util.fst"
let _41_809 = (let _123_369 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _123_369 FStar_List.unzip))
in (match (_41_809) with
| (vars, args) -> begin
(
# 512 "FStar.Tc.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _123_375 = (let _123_374 = (let _123_373 = (let _123_372 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_123_372, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _123_373))
in (FStar_All.pipe_right _123_374 pkg))
in (vars, _123_375)))
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
(let _123_377 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _123_377))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _41_833 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(
# 537 "FStar.Tc.Util.fst"
let _41_846 = (decorated_pattern_as_typ p)
in (match (_41_846) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _41_848 -> begin
(
# 541 "FStar.Tc.Util.fst"
let _41_851 = (decorated_pattern_as_exp p)
in (match (_41_851) with
| (vars, e) -> begin
(vars, FStar_Util.Inr (e))
end))
end))

# 547 "FStar.Tc.Util.fst"
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
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _41_867; FStar_Absyn_Syntax.pos = _41_865; FStar_Absyn_Syntax.fvs = _41_863; FStar_Absyn_Syntax.uvs = _41_861}) -> begin
(
# 555 "FStar.Tc.Util.fst"
let _41_897 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _41_874 _41_878 -> (match ((_41_874, _41_878)) with
| ((out, subst), (b, _41_877)) -> begin
(match (b) with
| FStar_Util.Inr (_41_880) -> begin
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
(let _123_385 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _123_385 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _123_388 = (let _123_387 = (let _123_386 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _123_386 Prims.fst))
in (bs, _123_387))
in (FStar_Absyn_Syntax.mk_Typ_lam _123_388 (Some (k)) r))
end
| _41_891 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 565 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (let _123_390 = (let _123_389 = (FStar_Absyn_Syntax.targ arg)
in (_123_389)::out)
in (_123_390, subst)))))
end)
end)) ([], [])))
in (match (_41_897) with
| (args, _41_896) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _41_899 -> begin
(FStar_All.failwith "Impossible")
end)))))))

# 571 "FStar.Tc.Util.fst"
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
let k = (let _123_401 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _123_401 Prims.fst))
in ((
# 577 "FStar.Tc.Util.fst"
let _41_910 = a
in {FStar_Absyn_Syntax.v = _41_910.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _41_910.FStar_Absyn_Syntax.p}), false))
end
| _41_913 -> begin
(a, true)
end))
in (
# 580 "FStar.Tc.Util.fst"
let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(
# 582 "FStar.Tc.Util.fst"
let t = (let _123_406 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _123_406 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _41_922) -> begin
(x, false)
end
| _41_925 -> begin
(FStar_All.failwith "impos")
end))
end
| _41_927 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _41_931) -> begin
(x, true)
end
| _41_934 -> begin
(FStar_All.failwith "impos")
end)
end))
in (
# 595 "FStar.Tc.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _41_940)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _41_947) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 600 "FStar.Tc.Util.fst"
let _41_976 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _41_957 b -> (match (_41_957) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(
# 602 "FStar.Tc.Util.fst"
let _41_963 = (mk_t_binder scope a)
in (match (_41_963) with
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
let _41_971 = (mk_v_binder scope x)
in (match (_41_971) with
| (vb, c) -> begin
(
# 609 "FStar.Tc.Util.fst"
let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_41_976) with
| (scope, bs, check) -> begin
(
# 612 "FStar.Tc.Util.fst"
let _41_980 = (aux scope body)
in (match (_41_980) with
| (body, res, check_res) -> begin
(
# 613 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Util.ml_comp res r)
in (
# 614 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (
# 615 "FStar.Tc.Util.fst"
let _41_983 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _123_414 = (FStar_Range.string_of_range r)
in (let _123_413 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _123_414 _123_413)))
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
| _41_987 -> begin
(let _123_416 = (let _123_415 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _123_415 Prims.fst))
in (e, _123_416, false))
end))
in (let _123_417 = (FStar_Tc_Env.t_binders env)
in (aux _123_417 e))))))
end
| _41_989 -> begin
(e, t, false)
end))

# 628 "FStar.Tc.Util.fst"
let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (
# 629 "FStar.Tc.Util.fst"
let _41_1006 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _41_999)::(FStar_Util.Inl (wlp), _41_994)::[] -> begin
(wp, wlp)
end
| _41_1003 -> begin
(let _123_422 = (let _123_421 = (let _123_420 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _123_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _123_421))
in (FStar_All.failwith _123_422))
end)
in (match (_41_1006) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

# 635 "FStar.Tc.Util.fst"
let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (
# 636 "FStar.Tc.Util.fst"
let _41_1014 = (destruct_comp c)
in (match (_41_1014) with
| (_41_1011, wp, wlp) -> begin
(let _123_444 = (let _123_443 = (let _123_439 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _123_439))
in (let _123_442 = (let _123_441 = (let _123_440 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _123_440))
in (_123_441)::[])
in (_123_443)::_123_442))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _123_444; FStar_Absyn_Syntax.flags = []})
end)))

# 642 "FStar.Tc.Util.fst"
let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 643 "FStar.Tc.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 645 "FStar.Tc.Util.fst"
let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_41_1022, c) -> begin
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
let _41_1036 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 664 "FStar.Tc.Util.fst"
let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 665 "FStar.Tc.Util.fst"
let _41_1047 = (let _123_458 = (norm_eff_name env l1)
in (let _123_457 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _123_458 _123_457)))
in (match (_41_1047) with
| (m, _41_1044, _41_1046) -> begin
m
end)))

# 667 "FStar.Tc.Util.fst"
let join_lcomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lident = (fun env c1 c2 -> if ((FStar_Ident.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Ident.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)

# 673 "FStar.Tc.Util.fst"
let lift_and_destruct : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  ((FStar_Absyn_Syntax.eff_decl * FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ)) = (fun env c1 c2 -> (
# 674 "FStar.Tc.Util.fst"
let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (
# 675 "FStar.Tc.Util.fst"
let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (
# 676 "FStar.Tc.Util.fst"
let _41_1059 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_41_1059) with
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
let _41_1065 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_41_1065) with
| (a, kwp) -> begin
(let _123_472 = (destruct_comp m1)
in (let _123_471 = (destruct_comp m2)
in ((md, a, kwp), _123_472, _123_471)))
end)))))
end)))))

# 683 "FStar.Tc.Util.fst"
let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 684 "FStar.Tc.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))

# 687 "FStar.Tc.Util.fst"
let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 688 "FStar.Tc.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))

# 692 "FStar.Tc.Util.fst"
let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun md result wp wlp flags -> (let _123_495 = (let _123_494 = (let _123_493 = (FStar_Absyn_Syntax.targ wp)
in (let _123_492 = (let _123_491 = (FStar_Absyn_Syntax.targ wlp)
in (_123_491)::[])
in (_123_493)::_123_492))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _123_494; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _123_495)))

# 698 "FStar.Tc.Util.fst"
let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (
# 699 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _41_1079 -> (match (()) with
| () -> begin
c0
end))}))

# 705 "FStar.Tc.Util.fst"
let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (
# 706 "FStar.Tc.Util.fst"
let _41_1082 = lc
in (let _123_505 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _41_1082.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _123_505; FStar_Absyn_Syntax.cflags = _41_1082.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _41_1084 -> (match (()) with
| () -> begin
(let _123_504 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _123_504))
end))})))

# 709 "FStar.Tc.Util.fst"
let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _123_508 = (FStar_Absyn_Util.compress_typ t)
in _123_508.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_41_1087) -> begin
true
end
| _41_1090 -> begin
false
end))

# 713 "FStar.Tc.Util.fst"
let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp = (fun env t v -> (
# 715 "FStar.Tc.Util.fst"
let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(
# 718 "FStar.Tc.Util.fst"
let _41_1099 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_41_1099) with
| (a, kwp) -> begin
(
# 719 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (
# 720 "FStar.Tc.Util.fst"
let wp = (let _123_520 = (let _123_519 = (let _123_518 = (let _123_517 = (FStar_Absyn_Syntax.targ t)
in (let _123_516 = (let _123_515 = (FStar_Absyn_Syntax.varg v)
in (_123_515)::[])
in (_123_517)::_123_516))
in (m.FStar_Absyn_Syntax.ret, _123_518))
in (FStar_Absyn_Syntax.mk_Typ_app _123_519 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _123_520))
in (
# 721 "FStar.Tc.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (
# 723 "FStar.Tc.Util.fst"
let _41_1104 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _123_523 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _123_522 = (FStar_Absyn_Print.exp_to_string v)
in (let _123_521 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _123_523 _123_522 _123_521))))
end else begin
()
end
in c)))

# 727 "FStar.Tc.Util.fst"
let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _41_1111 -> (match (_41_1111) with
| (b, lc2) -> begin
(
# 728 "FStar.Tc.Util.fst"
let _41_1122 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(
# 730 "FStar.Tc.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _41_1115)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _41_1120 -> begin
"??"
end)
in (let _123_533 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _123_532 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _123_533 bstr _123_532))))
end else begin
()
end
in (
# 735 "FStar.Tc.Util.fst"
let bind_it = (fun _41_1125 -> (match (()) with
| () -> begin
(
# 736 "FStar.Tc.Util.fst"
let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (
# 737 "FStar.Tc.Util.fst"
let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (
# 738 "FStar.Tc.Util.fst"
let try_simplify = (fun _41_1129 -> (match (()) with
| () -> begin
(
# 739 "FStar.Tc.Util.fst"
let aux = (fun _41_1131 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_41_1134)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_41_1138)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _41_1142 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _41_1147))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _123_541 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _123_540 -> Some (_123_540)) _123_541))
end else begin
(aux ())
end
end
| _41_1153 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(
# 760 "FStar.Tc.Util.fst"
let _41_1171 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _123_545 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _41_1159)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _41_1165)) -> begin
(FStar_Absyn_Print.sli l)
end
| _41_1170 -> begin
"Something else"
end)
in (let _123_544 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _123_543 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _123_542 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _123_545 _123_544 _123_543 _123_542)))))
end else begin
()
end
in c)
end
| None -> begin
(
# 770 "FStar.Tc.Util.fst"
let _41_1186 = (lift_and_destruct env c1 c2)
in (match (_41_1186) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 771 "FStar.Tc.Util.fst"
let bs = (match (b) with
| None -> begin
(let _123_546 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_123_546)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _123_547 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_123_547)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _123_548 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_123_548)::[])
end
| _41_1199 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (
# 776 "FStar.Tc.Util.fst"
let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (
# 777 "FStar.Tc.Util.fst"
let wp_args = (let _123_563 = (FStar_Absyn_Syntax.targ t1)
in (let _123_562 = (let _123_561 = (FStar_Absyn_Syntax.targ t2)
in (let _123_560 = (let _123_559 = (FStar_Absyn_Syntax.targ wp1)
in (let _123_558 = (let _123_557 = (FStar_Absyn_Syntax.targ wlp1)
in (let _123_556 = (let _123_555 = (let _123_551 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _123_551))
in (let _123_554 = (let _123_553 = (let _123_552 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _123_552))
in (_123_553)::[])
in (_123_555)::_123_554))
in (_123_557)::_123_556))
in (_123_559)::_123_558))
in (_123_561)::_123_560))
in (_123_563)::_123_562))
in (
# 778 "FStar.Tc.Util.fst"
let wlp_args = (let _123_571 = (FStar_Absyn_Syntax.targ t1)
in (let _123_570 = (let _123_569 = (FStar_Absyn_Syntax.targ t2)
in (let _123_568 = (let _123_567 = (FStar_Absyn_Syntax.targ wlp1)
in (let _123_566 = (let _123_565 = (let _123_564 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _123_564))
in (_123_565)::[])
in (_123_567)::_123_566))
in (_123_569)::_123_568))
in (_123_571)::_123_570))
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
in (let _123_572 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _123_572; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

# 789 "FStar.Tc.Util.fst"
let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 790 "FStar.Tc.Util.fst"
let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (
# 791 "FStar.Tc.Util.fst"
let _41_1217 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_41_1217) with
| (a, kwp) -> begin
(
# 792 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (
# 793 "FStar.Tc.Util.fst"
let wp = (let _123_587 = (let _123_586 = (let _123_585 = (FStar_Absyn_Syntax.targ t)
in (let _123_584 = (let _123_583 = (FStar_Absyn_Syntax.targ f)
in (_123_583)::[])
in (_123_585)::_123_584))
in (mk_wp, _123_586))
in (FStar_Absyn_Syntax.mk_Typ_app _123_587 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (
# 794 "FStar.Tc.Util.fst"
let wlp = (let _123_592 = (let _123_591 = (let _123_590 = (FStar_Absyn_Syntax.targ t)
in (let _123_589 = (let _123_588 = (FStar_Absyn_Syntax.targ f)
in (_123_588)::[])
in (_123_590)::_123_589))
in (mk_wlp, _123_591))
in (FStar_Absyn_Syntax.mk_Typ_app _123_592 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

# 797 "FStar.Tc.Util.fst"
let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))

# 799 "FStar.Tc.Util.fst"
let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (
# 800 "FStar.Tc.Util.fst"
let refresh = (fun _41_1226 -> (match (()) with
| () -> begin
(
# 801 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_41_1229) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 806 "FStar.Tc.Util.fst"
let _41_1233 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _123_604 = (let _123_603 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _123_603))
in (FStar_Util.print1 "Refreshing label at %s\n" _123_604))
end else begin
()
end
in (
# 808 "FStar.Tc.Util.fst"
let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 809 "FStar.Tc.Util.fst"
let _41_1236 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _123_607 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _123_606 = (let _123_605 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _123_605))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _123_607 _123_606)))
end else begin
()
end
in (
# 811 "FStar.Tc.Util.fst"
let _41_1241 = (destruct_comp c')
in (match (_41_1241) with
| (t, wp, wlp) -> begin
(
# 812 "FStar.Tc.Util.fst"
let wp = (let _123_610 = (let _123_609 = (let _123_608 = (FStar_Tc_Env.get_range env)
in (wp, Some (b), _123_608))
in FStar_Absyn_Syntax.Meta_refresh_label (_123_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _123_610))
in (
# 813 "FStar.Tc.Util.fst"
let wlp = (let _123_613 = (let _123_612 = (let _123_611 = (FStar_Tc_Env.get_range env)
in (wlp, Some (b), _123_611))
in FStar_Absyn_Syntax.Meta_refresh_label (_123_612))
in (FStar_Absyn_Syntax.mk_Typ_meta _123_613))
in (let _123_618 = (
# 814 "FStar.Tc.Util.fst"
let _41_1244 = c'
in (let _123_617 = (let _123_616 = (FStar_Absyn_Syntax.targ wp)
in (let _123_615 = (let _123_614 = (FStar_Absyn_Syntax.targ wlp)
in (_123_614)::[])
in (_123_616)::_123_615))
in {FStar_Absyn_Syntax.effect_name = _41_1244.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _41_1244.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _123_617; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _123_618))))
end)))))
end)
end)
end))
in (
# 815 "FStar.Tc.Util.fst"
let _41_1246 = lc
in {FStar_Absyn_Syntax.eff_name = _41_1246.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _41_1246.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _41_1246.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

# 817 "FStar.Tc.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

# 819 "FStar.Tc.Util.fst"
let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _123_642 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _123_642)) then begin
f
end else begin
(let _123_643 = (reason ())
in (label _123_643 r f))
end
end))

# 826 "FStar.Tc.Util.fst"
let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _123_650 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_123_650))
end))

# 830 "FStar.Tc.Util.fst"
let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(
# 832 "FStar.Tc.Util.fst"
let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _41_1273 -> begin
g2
end))

# 836 "FStar.Tc.Util.fst"
let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (
# 837 "FStar.Tc.Util.fst"
let weaken = (fun _41_1278 -> (match (()) with
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
let _41_1287 = (destruct_comp c)
in (match (_41_1287) with
| (res_t, wp, wlp) -> begin
(
# 846 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 847 "FStar.Tc.Util.fst"
let wp = (let _123_669 = (let _123_668 = (let _123_667 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_666 = (let _123_665 = (FStar_Absyn_Syntax.targ f)
in (let _123_664 = (let _123_663 = (FStar_Absyn_Syntax.targ wp)
in (_123_663)::[])
in (_123_665)::_123_664))
in (_123_667)::_123_666))
in (md.FStar_Absyn_Syntax.assume_p, _123_668))
in (FStar_Absyn_Syntax.mk_Typ_app _123_669 None wp.FStar_Absyn_Syntax.pos))
in (
# 848 "FStar.Tc.Util.fst"
let wlp = (let _123_676 = (let _123_675 = (let _123_674 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_673 = (let _123_672 = (FStar_Absyn_Syntax.targ f)
in (let _123_671 = (let _123_670 = (FStar_Absyn_Syntax.targ wlp)
in (_123_670)::[])
in (_123_672)::_123_671))
in (_123_674)::_123_673))
in (md.FStar_Absyn_Syntax.assume_p, _123_675))
in (FStar_Absyn_Syntax.mk_Typ_app _123_676 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (
# 850 "FStar.Tc.Util.fst"
let _41_1291 = lc
in {FStar_Absyn_Syntax.eff_name = _41_1291.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _41_1291.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _41_1291.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

# 852 "FStar.Tc.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 855 "FStar.Tc.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _41_8 -> (match (_41_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _41_1302 -> begin
[]
end))))
in (
# 856 "FStar.Tc.Util.fst"
let strengthen = (fun _41_1305 -> (match (()) with
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
let xret = (let _123_698 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _123_698))
in (
# 868 "FStar.Tc.Util.fst"
let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (
# 869 "FStar.Tc.Util.fst"
let lc = (let _123_701 = (lcomp_of_comp c)
in (let _123_700 = (let _123_699 = (lcomp_of_comp xret)
in (Some (xbinding), _123_699))
in (bind env (Some (e)) _123_701 _123_700)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (
# 872 "FStar.Tc.Util.fst"
let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 873 "FStar.Tc.Util.fst"
let _41_1320 = (destruct_comp c)
in (match (_41_1320) with
| (res_t, wp, wlp) -> begin
(
# 874 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 875 "FStar.Tc.Util.fst"
let wp = (let _123_710 = (let _123_709 = (let _123_708 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_707 = (let _123_706 = (let _123_703 = (let _123_702 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _123_702 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _123_703))
in (let _123_705 = (let _123_704 = (FStar_Absyn_Syntax.targ wp)
in (_123_704)::[])
in (_123_706)::_123_705))
in (_123_708)::_123_707))
in (md.FStar_Absyn_Syntax.assert_p, _123_709))
in (FStar_Absyn_Syntax.mk_Typ_app _123_710 None wp.FStar_Absyn_Syntax.pos))
in (
# 876 "FStar.Tc.Util.fst"
let wlp = (let _123_717 = (let _123_716 = (let _123_715 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_714 = (let _123_713 = (FStar_Absyn_Syntax.targ f)
in (let _123_712 = (let _123_711 = (FStar_Absyn_Syntax.targ wlp)
in (_123_711)::[])
in (_123_713)::_123_712))
in (_123_715)::_123_714))
in (md.FStar_Absyn_Syntax.assume_p, _123_716))
in (FStar_Absyn_Syntax.mk_Typ_app _123_717 None wlp.FStar_Absyn_Syntax.pos))
in (
# 877 "FStar.Tc.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _123_721 = (
# 879 "FStar.Tc.Util.fst"
let _41_1325 = lc
in (let _123_720 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _123_719 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _123_718 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _123_718))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _123_720; FStar_Absyn_Syntax.res_typ = _41_1325.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _123_719; FStar_Absyn_Syntax.comp = strengthen})))
in (_123_721, (
# 882 "FStar.Tc.Util.fst"
let _41_1327 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _41_1327.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _41_1327.FStar_Tc_Rel.implicits})))))
end)

# 884 "FStar.Tc.Util.fst"
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
let _41_1337 = (let _123_729 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _123_728 = (FStar_Absyn_Util.bvar_to_exp y)
in (_123_729, _123_728)))
in (match (_41_1337) with
| (xexp, yexp) -> begin
(
# 889 "FStar.Tc.Util.fst"
let yret = (let _123_734 = (let _123_733 = (let _123_732 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_731 = (let _123_730 = (FStar_Absyn_Syntax.varg yexp)
in (_123_730)::[])
in (_123_732)::_123_731))
in (md_pure.FStar_Absyn_Syntax.ret, _123_733))
in (FStar_Absyn_Syntax.mk_Typ_app _123_734 None res_t.FStar_Absyn_Syntax.pos))
in (
# 890 "FStar.Tc.Util.fst"
let x_eq_y_yret = (let _123_742 = (let _123_741 = (let _123_740 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_739 = (let _123_738 = (let _123_735 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _123_735))
in (let _123_737 = (let _123_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_123_736)::[])
in (_123_738)::_123_737))
in (_123_740)::_123_739))
in (md_pure.FStar_Absyn_Syntax.assume_p, _123_741))
in (FStar_Absyn_Syntax.mk_Typ_app _123_742 None res_t.FStar_Absyn_Syntax.pos))
in (
# 891 "FStar.Tc.Util.fst"
let forall_y_x_eq_y_yret = (let _123_753 = (let _123_752 = (let _123_751 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_750 = (let _123_749 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_748 = (let _123_747 = (let _123_746 = (let _123_745 = (let _123_744 = (let _123_743 = (FStar_Absyn_Syntax.v_binder y)
in (_123_743)::[])
in (_123_744, x_eq_y_yret))
in (FStar_Absyn_Syntax.mk_Typ_lam _123_745 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _123_746))
in (_123_747)::[])
in (_123_749)::_123_748))
in (_123_751)::_123_750))
in (md_pure.FStar_Absyn_Syntax.close_wp, _123_752))
in (FStar_Absyn_Syntax.mk_Typ_app _123_753 None res_t.FStar_Absyn_Syntax.pos))
in (
# 892 "FStar.Tc.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (
# 893 "FStar.Tc.Util.fst"
let lc = (let _123_756 = (lcomp_of_comp comp)
in (let _123_755 = (let _123_754 = (lcomp_of_comp lc2)
in (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), _123_754))
in (bind env None _123_756 _123_755)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

# 896 "FStar.Tc.Util.fst"
let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 897 "FStar.Tc.Util.fst"
let comp = (fun _41_1348 -> (match (()) with
| () -> begin
(
# 898 "FStar.Tc.Util.fst"
let _41_1364 = (let _123_768 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _123_767 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _123_768 _123_767)))
in (match (_41_1364) with
| ((md, _41_1351, _41_1353), (res_t, wp_then, wlp_then), (_41_1360, wp_else, wlp_else)) -> begin
(
# 899 "FStar.Tc.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _123_788 = (let _123_786 = (let _123_785 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_784 = (let _123_783 = (FStar_Absyn_Syntax.targ g)
in (let _123_782 = (let _123_781 = (FStar_Absyn_Syntax.targ wp_t)
in (let _123_780 = (let _123_779 = (FStar_Absyn_Syntax.targ wp_e)
in (_123_779)::[])
in (_123_781)::_123_780))
in (_123_783)::_123_782))
in (_123_785)::_123_784))
in (md.FStar_Absyn_Syntax.if_then_else, _123_786))
in (let _123_787 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _123_788 None _123_787))))
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
let wp = (let _123_795 = (let _123_794 = (let _123_793 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_792 = (let _123_791 = (FStar_Absyn_Syntax.targ wlp)
in (let _123_790 = (let _123_789 = (FStar_Absyn_Syntax.targ wp)
in (_123_789)::[])
in (_123_791)::_123_790))
in (_123_793)::_123_792))
in (md.FStar_Absyn_Syntax.ite_wp, _123_794))
in (FStar_Absyn_Syntax.mk_Typ_app _123_795 None wp.FStar_Absyn_Syntax.pos))
in (
# 906 "FStar.Tc.Util.fst"
let wlp = (let _123_800 = (let _123_799 = (let _123_798 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_797 = (let _123_796 = (FStar_Absyn_Syntax.targ wlp)
in (_123_796)::[])
in (_123_798)::_123_797))
in (md.FStar_Absyn_Syntax.ite_wlp, _123_799))
in (FStar_Absyn_Syntax.mk_Typ_app _123_800 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _123_801 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _123_801; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))

# 913 "FStar.Tc.Util.fst"
let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (
# 914 "FStar.Tc.Util.fst"
let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _41_1387 -> (match (_41_1387) with
| (_41_1385, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (
# 917 "FStar.Tc.Util.fst"
let bind_cases = (fun _41_1390 -> (match (()) with
| () -> begin
(
# 918 "FStar.Tc.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _123_831 = (let _123_829 = (let _123_828 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_827 = (let _123_826 = (FStar_Absyn_Syntax.targ g)
in (let _123_825 = (let _123_824 = (FStar_Absyn_Syntax.targ wp_t)
in (let _123_823 = (let _123_822 = (FStar_Absyn_Syntax.targ wp_e)
in (_123_822)::[])
in (_123_824)::_123_823))
in (_123_826)::_123_825))
in (_123_828)::_123_827))
in (md.FStar_Absyn_Syntax.if_then_else, _123_829))
in (let _123_830 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _123_831 None _123_830))))
in (
# 919 "FStar.Tc.Util.fst"
let default_case = (
# 920 "FStar.Tc.Util.fst"
let post_k = (let _123_834 = (let _123_833 = (let _123_832 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_123_832)::[])
in (_123_833, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _123_834 res_t.FStar_Absyn_Syntax.pos))
in (
# 921 "FStar.Tc.Util.fst"
let kwp = (let _123_837 = (let _123_836 = (let _123_835 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_123_835)::[])
in (_123_836, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _123_837 res_t.FStar_Absyn_Syntax.pos))
in (
# 922 "FStar.Tc.Util.fst"
let post = (let _123_838 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _123_838 post_k))
in (
# 923 "FStar.Tc.Util.fst"
let wp = (let _123_845 = (let _123_844 = (let _123_839 = (FStar_Absyn_Syntax.t_binder post)
in (_123_839)::[])
in (let _123_843 = (let _123_842 = (let _123_840 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _123_840))
in (let _123_841 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _123_842 _123_841)))
in (_123_844, _123_843)))
in (FStar_Absyn_Syntax.mk_Typ_lam _123_845 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (
# 924 "FStar.Tc.Util.fst"
let wlp = (let _123_849 = (let _123_848 = (let _123_846 = (FStar_Absyn_Syntax.t_binder post)
in (_123_846)::[])
in (let _123_847 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_123_848, _123_847)))
in (FStar_Absyn_Syntax.mk_Typ_lam _123_849 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (
# 925 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 927 "FStar.Tc.Util.fst"
let comp = (FStar_List.fold_right (fun _41_1406 celse -> (match (_41_1406) with
| (g, cthen) -> begin
(
# 928 "FStar.Tc.Util.fst"
let _41_1424 = (let _123_852 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _123_852 celse))
in (match (_41_1424) with
| ((md, _41_1410, _41_1412), (_41_1415, wp_then, wlp_then), (_41_1420, wp_else, wlp_else)) -> begin
(let _123_854 = (ifthenelse md res_t g wp_then wp_else)
in (let _123_853 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _123_854 _123_853 [])))
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
let _41_1432 = (destruct_comp comp)
in (match (_41_1432) with
| (_41_1429, wp, wlp) -> begin
(
# 935 "FStar.Tc.Util.fst"
let wp = (let _123_861 = (let _123_860 = (let _123_859 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_858 = (let _123_857 = (FStar_Absyn_Syntax.targ wlp)
in (let _123_856 = (let _123_855 = (FStar_Absyn_Syntax.targ wp)
in (_123_855)::[])
in (_123_857)::_123_856))
in (_123_859)::_123_858))
in (md.FStar_Absyn_Syntax.ite_wp, _123_860))
in (FStar_Absyn_Syntax.mk_Typ_app _123_861 None wp.FStar_Absyn_Syntax.pos))
in (
# 936 "FStar.Tc.Util.fst"
let wlp = (let _123_866 = (let _123_865 = (let _123_864 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_863 = (let _123_862 = (FStar_Absyn_Syntax.targ wlp)
in (_123_862)::[])
in (_123_864)::_123_863))
in (md.FStar_Absyn_Syntax.ite_wlp, _123_865))
in (FStar_Absyn_Syntax.mk_Typ_app _123_866 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

# 943 "FStar.Tc.Util.fst"
let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (
# 944 "FStar.Tc.Util.fst"
let close = (fun _41_1439 -> (match (()) with
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
let bs = (let _123_885 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_123_885)::[])
in (
# 952 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _123_892 = (let _123_891 = (let _123_890 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_889 = (let _123_888 = (FStar_Absyn_Syntax.targ t)
in (let _123_887 = (let _123_886 = (FStar_Absyn_Syntax.targ wp)
in (_123_886)::[])
in (_123_888)::_123_887))
in (_123_890)::_123_889))
in (md.FStar_Absyn_Syntax.close_wp, _123_891))
in (FStar_Absyn_Syntax.mk_Typ_app _123_892 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(
# 956 "FStar.Tc.Util.fst"
let bs = (let _123_893 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_123_893)::[])
in (
# 957 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _123_898 = (let _123_897 = (let _123_896 = (FStar_Absyn_Syntax.targ res_t)
in (let _123_895 = (let _123_894 = (FStar_Absyn_Syntax.targ wp)
in (_123_894)::[])
in (_123_896)::_123_895))
in (md.FStar_Absyn_Syntax.close_wp_t, _123_897))
in (FStar_Absyn_Syntax.mk_Typ_app _123_898 None wp0.FStar_Absyn_Syntax.pos))))
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
let _41_1470 = (destruct_comp c)
in (match (_41_1470) with
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
let _41_1474 = lc
in {FStar_Absyn_Syntax.eff_name = _41_1474.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _41_1474.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _41_1474.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

# 973 "FStar.Tc.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (
# 974 "FStar.Tc.Util.fst"
let refine = (fun _41_1480 -> (match (()) with
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
let ret = (let _123_907 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _123_907))
in (
# 986 "FStar.Tc.Util.fst"
let eq_ret = (let _123_909 = (let _123_908 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_123_908))
in (weaken_precondition env ret _123_909))
in (let _123_912 = (let _123_911 = (let _123_910 = (lcomp_of_comp c)
in (bind env None _123_910 (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_123_911.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _123_912 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
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
let _41_1490 = lc
in {FStar_Absyn_Syntax.eff_name = _41_1490.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _41_1490.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

# 996 "FStar.Tc.Util.fst"
let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _123_924 = (let _123_923 = (let _123_922 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _123_921 = (FStar_Tc_Env.get_range env)
in (_123_922, _123_921)))
in FStar_Absyn_Syntax.Error (_123_923))
in (Prims.raise _123_924))
end
| Some (g) -> begin
(e, c', g)
end))

# 1002 "FStar.Tc.Util.fst"
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
let rec aux = (fun subst _41_9 -> (match (_41_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_41_1514)))::rest -> begin
(
# 1009 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1010 "FStar.Tc.Util.fst"
let _41_1522 = (new_implicit_tvar env k)
in (match (_41_1522) with
| (t, u) -> begin
(
# 1011 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (
# 1012 "FStar.Tc.Util.fst"
let _41_1528 = (aux subst rest)
in (match (_41_1528) with
| (args, bs, subst, us) -> begin
(let _123_938 = (let _123_937 = (let _123_936 = (FStar_All.pipe_left (fun _123_935 -> Some (_123_935)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _123_936))
in (_123_937)::args)
in (_123_938, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_41_1533)))::rest -> begin
(
# 1016 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1017 "FStar.Tc.Util.fst"
let _41_1541 = (new_implicit_evar env t)
in (match (_41_1541) with
| (v, u) -> begin
(
# 1018 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (
# 1019 "FStar.Tc.Util.fst"
let _41_1547 = (aux subst rest)
in (match (_41_1547) with
| (args, bs, subst, us) -> begin
(let _123_942 = (let _123_941 = (let _123_940 = (FStar_All.pipe_left (fun _123_939 -> Some (_123_939)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _123_940))
in (_123_941)::args)
in (_123_942, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (
# 1023 "FStar.Tc.Util.fst"
let _41_1553 = (aux [] bs)
in (match (_41_1553) with
| (args, bs, subst, implicits) -> begin
(
# 1024 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (
# 1025 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _123_943 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_123_943, k, implicits))))
end)))
end
| _41_1557 -> begin
(t, k, [])
end)
end))

# 1030 "FStar.Tc.Util.fst"
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
let rec aux = (fun subst _41_10 -> (match (_41_10) with
| (FStar_Util.Inl (a), _41_1573)::rest -> begin
(
# 1037 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1038 "FStar.Tc.Util.fst"
let _41_1579 = (new_implicit_tvar env k)
in (match (_41_1579) with
| (t, u) -> begin
(
# 1039 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (
# 1040 "FStar.Tc.Util.fst"
let _41_1585 = (aux subst rest)
in (match (_41_1585) with
| (args, bs, subst, us) -> begin
(let _123_957 = (let _123_956 = (let _123_955 = (FStar_All.pipe_left (fun _123_954 -> Some (_123_954)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _123_955))
in (_123_956)::args)
in (_123_957, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_41_1590)))::rest -> begin
(
# 1044 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1045 "FStar.Tc.Util.fst"
let _41_1598 = (new_implicit_evar env t)
in (match (_41_1598) with
| (v, u) -> begin
(
# 1046 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (
# 1047 "FStar.Tc.Util.fst"
let _41_1604 = (aux subst rest)
in (match (_41_1604) with
| (args, bs, subst, us) -> begin
(let _123_961 = (let _123_960 = (let _123_959 = (FStar_All.pipe_left (fun _123_958 -> Some (_123_958)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _123_959))
in (_123_960)::args)
in (_123_961, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (
# 1051 "FStar.Tc.Util.fst"
let _41_1610 = (aux [] bs)
in (match (_41_1610) with
| (args, bs, subst, implicits) -> begin
(
# 1052 "FStar.Tc.Util.fst"
let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _41_1617 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(
# 1058 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _123_968 = (mk_exp_app e args (Some (t)))
in (_123_968, t, implicits)))
end else begin
(e, t, [])
end
end
| _41_1621 -> begin
(
# 1062 "FStar.Tc.Util.fst"
let t = (let _123_969 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _123_969 (FStar_Absyn_Util.subst_typ subst)))
in (let _123_970 = (mk_exp_app e args (Some (t)))
in (_123_970, t, implicits)))
end))
end)))
end
| _41_1624 -> begin
(e, t, [])
end)
end))

# 1068 "FStar.Tc.Util.fst"
let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (
# 1069 "FStar.Tc.Util.fst"
let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _123_979 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_123_979, false))
end else begin
(let _123_980 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_123_980, true))
end
in (match (gopt) with
| (None, _41_1632) -> begin
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
let _41_1640 = lc
in {FStar_Absyn_Syntax.eff_name = _41_1640.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _41_1640.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _41_1640.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(
# 1082 "FStar.Tc.Util.fst"
let g = (
# 1082 "FStar.Tc.Util.fst"
let _41_1645 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _41_1645.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _41_1645.FStar_Tc_Rel.implicits})
in (
# 1083 "FStar.Tc.Util.fst"
let strengthen = (fun _41_1649 -> (match (()) with
| () -> begin
(
# 1084 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 1086 "FStar.Tc.Util.fst"
let _41_1651 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _123_984 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _123_983 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _123_984 _123_983)))
end else begin
()
end
in (
# 1089 "FStar.Tc.Util.fst"
let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 1090 "FStar.Tc.Util.fst"
let _41_1656 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_41_1656) with
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
let wp = (let _123_989 = (let _123_988 = (let _123_987 = (FStar_Absyn_Syntax.targ t)
in (let _123_986 = (let _123_985 = (FStar_Absyn_Syntax.varg xexp)
in (_123_985)::[])
in (_123_987)::_123_986))
in (md.FStar_Absyn_Syntax.ret, _123_988))
in (FStar_Absyn_Syntax.mk_Typ_app _123_989 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (
# 1096 "FStar.Tc.Util.fst"
let cret = (let _123_990 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _123_990))
in (
# 1097 "FStar.Tc.Util.fst"
let guard = if apply_guard then begin
(let _123_993 = (let _123_992 = (let _123_991 = (FStar_Absyn_Syntax.varg xexp)
in (_123_991)::[])
in (f, _123_992))
in (FStar_Absyn_Syntax.mk_Typ_app _123_993 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (
# 1098 "FStar.Tc.Util.fst"
let _41_1666 = (let _123_1001 = (FStar_All.pipe_left (fun _123_998 -> Some (_123_998)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _123_1000 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _123_999 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _123_1001 _123_1000 e cret _123_999))))
in (match (_41_1666) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 1105 "FStar.Tc.Util.fst"
let c = (let _123_1003 = (let _123_1002 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _123_1002))
in (bind env (Some (e)) _123_1003 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (
# 1106 "FStar.Tc.Util.fst"
let c = (c.FStar_Absyn_Syntax.comp ())
in (
# 1107 "FStar.Tc.Util.fst"
let _41_1669 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _123_1004 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _123_1004))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (
# 1110 "FStar.Tc.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _41_11 -> (match (_41_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _41_1675 -> begin
[]
end))))
in (
# 1111 "FStar.Tc.Util.fst"
let lc = (
# 1111 "FStar.Tc.Util.fst"
let _41_1677 = lc
in (let _123_1006 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _123_1006; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

# 1118 "FStar.Tc.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 1119 "FStar.Tc.Util.fst"
let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(
# 1124 "FStar.Tc.Util.fst"
let ue = (let _123_1011 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _123_1011))
in (
# 1125 "FStar.Tc.Util.fst"
let ut = (let _123_1012 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _123_1012))
in (
# 1126 "FStar.Tc.Util.fst"
let uk = (let _123_1013 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _123_1013))
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
let _41_1689 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 1132 "FStar.Tc.Util.fst"
let _41_1691 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 1133 "FStar.Tc.Util.fst"
let _41_1693 = (let _123_1015 = (let _123_1014 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _123_1014))
in (FStar_Tc_Errors.report r _123_1015))
in (
# 1136 "FStar.Tc.Util.fst"
let _41_1695 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))

# 1139 "FStar.Tc.Util.fst"
let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _123_1023 = (FStar_Util.for_all (fun _41_1703 -> (match (_41_1703) with
| (_41_1701, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _123_1023)) then begin
None
end else begin
(
# 1143 "FStar.Tc.Util.fst"
let norm = (fun c -> (
# 1144 "FStar.Tc.Util.fst"
let _41_1706 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _123_1026 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _123_1026))
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
let _41_1710 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _123_1027 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _123_1027))
end else begin
()
end
in c)))))
in (
# 1152 "FStar.Tc.Util.fst"
let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (
# 1153 "FStar.Tc.Util.fst"
let gen_uvars = (fun uvs -> (let _123_1030 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _123_1030 FStar_Util.set_elements)))
in (
# 1154 "FStar.Tc.Util.fst"
let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _41_1719) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _41_12 -> (match (_41_12) with
| (FStar_Util.Inl (_41_1724), _41_1727) -> begin
true
end
| _41_1730 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _41_1732 -> begin
true
end))
in (
# 1161 "FStar.Tc.Util.fst"
let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _41_1735 -> (match (_41_1735) with
| (e, c) -> begin
(
# 1162 "FStar.Tc.Util.fst"
let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _123_1035 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _123_1035)) then begin
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
let _41_1751 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _123_1036 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _123_1036))) then begin
(
# 1174 "FStar.Tc.Util.fst"
let _41_1747 = (destruct_comp ct)
in (match (_41_1747) with
| (_41_1743, wp, _41_1746) -> begin
(
# 1175 "FStar.Tc.Util.fst"
let binder = (let _123_1037 = (FStar_Absyn_Syntax.null_v_binder t)
in (_123_1037)::[])
in (
# 1176 "FStar.Tc.Util.fst"
let post = (let _123_1041 = (let _123_1038 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _123_1038))
in (let _123_1040 = (let _123_1039 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_123_1039))
in (FStar_Absyn_Syntax.mk_Typ_lam _123_1041 _123_1040 t.FStar_Absyn_Syntax.pos)))
in (
# 1177 "FStar.Tc.Util.fst"
let vc = (let _123_1048 = (let _123_1047 = (let _123_1046 = (let _123_1045 = (let _123_1044 = (FStar_Absyn_Syntax.targ post)
in (_123_1044)::[])
in (wp, _123_1045))
in (FStar_Absyn_Syntax.mk_Typ_app _123_1046))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _123_1047))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _123_1048))
in (let _123_1049 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _123_1049)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (
# 1182 "FStar.Tc.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _41_1757 -> (match (_41_1757) with
| (uvs, e, c) -> begin
(
# 1183 "FStar.Tc.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _41_1760 -> (match (_41_1760) with
| (u, k) -> begin
(
# 1184 "FStar.Tc.Util.fst"
let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_41_1798) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _41_1801 -> begin
(
# 1189 "FStar.Tc.Util.fst"
let a = (let _123_1054 = (let _123_1053 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _123_1052 -> Some (_123_1052)) _123_1053))
in (FStar_Absyn_Util.new_bvd _123_1054))
in (
# 1190 "FStar.Tc.Util.fst"
let t = (let _123_1055 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _123_1055 k))
in (
# 1192 "FStar.Tc.Util.fst"
let _41_1804 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _123_1057 = (FStar_All.pipe_left (fun _123_1056 -> Some (_123_1056)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (a), _123_1057)))
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
| _41_1815 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (
# 1200 "FStar.Tc.Util.fst"
let e = (match (tvars) with
| [] -> begin
e
end
| _41_1819 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _123_1058 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _123_1058)))))
end))))
in Some (ecs)))))))
end)

# 1206 "FStar.Tc.Util.fst"
let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (
# 1207 "FStar.Tc.Util.fst"
let _41_1831 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _123_1067 = (let _123_1066 = (FStar_List.map (fun _41_1830 -> (match (_41_1830) with
| (lb, _41_1827, _41_1829) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _123_1066 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _123_1067))
end else begin
()
end
in (match ((let _123_1069 = (FStar_All.pipe_right lecs (FStar_List.map (fun _41_1837 -> (match (_41_1837) with
| (_41_1834, e, c) -> begin
(e, c)
end))))
in (gen verify env _123_1069))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _41_1846 _41_1849 -> (match ((_41_1846, _41_1849)) with
| ((l, _41_1843, _41_1845), (e, c)) -> begin
(
# 1212 "FStar.Tc.Util.fst"
let _41_1850 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _123_1074 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _123_1073 = (FStar_Absyn_Print.lbname_to_string l)
in (let _123_1072 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _123_1074 _123_1073 _123_1072))))
end else begin
()
end
in (l, e, c))
end)) lecs ecs)
end)))

# 1215 "FStar.Tc.Util.fst"
let check_unresolved_implicits : FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun g -> (
# 1216 "FStar.Tc.Util.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Uvar -> begin
true
end
| _41_1857 -> begin
false
end))
in (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _41_13 -> (match (_41_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _41_1863) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_41_1867, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _41_1873 -> begin
()
end)))

# 1223 "FStar.Tc.Util.fst"
let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (
# 1224 "FStar.Tc.Util.fst"
let discharge = (fun g -> (
# 1225 "FStar.Tc.Util.fst"
let _41_1879 = (FStar_Tc_Rel.try_discharge_guard env g)
in (
# 1226 "FStar.Tc.Util.fst"
let _41_1881 = (check_unresolved_implicits g)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (
# 1228 "FStar.Tc.Util.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _123_1089 = (discharge g)
in (let _123_1088 = (lc.FStar_Absyn_Syntax.comp ())
in (_123_1089, _123_1088)))
end else begin
(
# 1231 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 1232 "FStar.Tc.Util.fst"
let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (
# 1233 "FStar.Tc.Util.fst"
let c = (let _123_1090 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _123_1090 FStar_Absyn_Util.comp_to_comp_typ))
in (
# 1234 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 1235 "FStar.Tc.Util.fst"
let _41_1892 = (destruct_comp c)
in (match (_41_1892) with
| (t, wp, _41_1891) -> begin
(
# 1236 "FStar.Tc.Util.fst"
let vc = (let _123_1096 = (let _123_1094 = (let _123_1093 = (FStar_Absyn_Syntax.targ t)
in (let _123_1092 = (let _123_1091 = (FStar_Absyn_Syntax.targ wp)
in (_123_1091)::[])
in (_123_1093)::_123_1092))
in (md.FStar_Absyn_Syntax.trivial, _123_1094))
in (let _123_1095 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _123_1096 (Some (FStar_Absyn_Syntax.ktype)) _123_1095)))
in (
# 1237 "FStar.Tc.Util.fst"
let g = (let _123_1097 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _123_1097))
in (let _123_1099 = (discharge g)
in (let _123_1098 = (FStar_Absyn_Syntax.mk_Comp c)
in (_123_1099, _123_1098)))))
end))))))
end)))

# 1243 "FStar.Tc.Util.fst"
let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (
# 1244 "FStar.Tc.Util.fst"
let short_bin_op_e = (fun f _41_14 -> (match (_41_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _41_1904)::[] -> begin
(let _123_1118 = (f fst)
in (FStar_All.pipe_right _123_1118 (fun _123_1117 -> Some (_123_1117))))
end
| _41_1908 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1249 "FStar.Tc.Util.fst"
let table = (
# 1250 "FStar.Tc.Util.fst"
let op_and_e = (fun e -> (let _123_1124 = (FStar_Absyn_Util.b2t e)
in (_123_1124, FStar_Absyn_Const.exp_false_bool)))
in (
# 1251 "FStar.Tc.Util.fst"
let op_or_e = (fun e -> (let _123_1128 = (let _123_1127 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _123_1127))
in (_123_1128, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _41_1916) -> begin
(
# 1257 "FStar.Tc.Util.fst"
let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _41_1922 -> (match (_41_1922) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _123_1146 = (mk seen_args)
in Some (_123_1146))
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
| _41_1927 -> begin
None
end))))

# 1268 "FStar.Tc.Util.fst"
let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (
# 1269 "FStar.Tc.Util.fst"
let short_bin_op_t = (fun f _41_15 -> (match (_41_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _41_1937)::[] -> begin
(f fst)
end
| _41_1941 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1274 "FStar.Tc.Util.fst"
let op_and_t = (fun t -> (let _123_1167 = (unlabel t)
in (FStar_All.pipe_right _123_1167 (fun _123_1166 -> FStar_Tc_Rel.NonTrivial (_123_1166)))))
in (
# 1275 "FStar.Tc.Util.fst"
let op_or_t = (fun t -> (let _123_1172 = (let _123_1170 = (unlabel t)
in (FStar_All.pipe_right _123_1170 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _123_1172 (fun _123_1171 -> FStar_Tc_Rel.NonTrivial (_123_1171)))))
in (
# 1276 "FStar.Tc.Util.fst"
let op_imp_t = (fun t -> (let _123_1176 = (unlabel t)
in (FStar_All.pipe_right _123_1176 (fun _123_1175 -> FStar_Tc_Rel.NonTrivial (_123_1175)))))
in (
# 1277 "FStar.Tc.Util.fst"
let short_op_ite = (fun _41_16 -> (match (_41_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _41_1953)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _41_1959)::[] -> begin
(let _123_1180 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _123_1180 (fun _123_1179 -> FStar_Tc_Rel.NonTrivial (_123_1179))))
end
| _41_1964 -> begin
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
| Some (g, _41_1972) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _41_1982; FStar_Absyn_Syntax.pos = _41_1980; FStar_Absyn_Syntax.fvs = _41_1978; FStar_Absyn_Syntax.uvs = _41_1976}) -> begin
(
# 1295 "FStar.Tc.Util.fst"
let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _41_1990 -> (match (_41_1990) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _123_1207 = (mk seen_args)
in Some (_123_1207))
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
| _41_1995 -> begin
FStar_Tc_Rel.Trivial
end))))))))

# 1302 "FStar.Tc.Util.fst"
let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (
# 1303 "FStar.Tc.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 1304 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _123_1221 = (let _123_1220 = (let _123_1219 = (let _123_1218 = (let _123_1217 = (let _123_1216 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _123_1216))
in (_123_1217)::[])
in (ens, _123_1218))
in (FStar_Absyn_Syntax.mk_Typ_app _123_1219 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _123_1220))
in (FStar_Absyn_Syntax.mk_Typ_refine _123_1221 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (
# 1306 "FStar.Tc.Util.fst"
let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_41_2005) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _41_2020)::(FStar_Util.Inl (ens), _41_2014)::_41_2010 -> begin
(let _123_1227 = (let _123_1224 = (norm req)
in Some (_123_1224))
in (let _123_1226 = (let _123_1225 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _123_1225))
in (_123_1227, _123_1226)))
end
| _41_2024 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1319 "FStar.Tc.Util.fst"
let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_41_2027) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _41_2042)::(FStar_Util.Inl (wlp), _41_2036)::_41_2032 -> begin
(
# 1325 "FStar.Tc.Util.fst"
let _41_2054 = (match ((let _123_1229 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _123_1228 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_123_1229, _123_1228)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _41_2051 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_41_2054) with
| (as_req, as_ens) -> begin
(
# 1328 "FStar.Tc.Util.fst"
let req = (let _123_1236 = (let _123_1235 = (let _123_1234 = (let _123_1231 = (FStar_All.pipe_left (fun _123_1230 -> Some (_123_1230)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _123_1231))
in (let _123_1233 = (let _123_1232 = (FStar_Absyn_Syntax.targ wp)
in (_123_1232)::[])
in (_123_1234)::_123_1233))
in (as_req, _123_1235))
in (FStar_Absyn_Syntax.mk_Typ_app _123_1236 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (
# 1329 "FStar.Tc.Util.fst"
let ens = (let _123_1243 = (let _123_1242 = (let _123_1241 = (let _123_1238 = (FStar_All.pipe_left (fun _123_1237 -> Some (_123_1237)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _123_1238))
in (let _123_1240 = (let _123_1239 = (FStar_Absyn_Syntax.targ wlp)
in (_123_1239)::[])
in (_123_1241)::_123_1240))
in (as_ens, _123_1242))
in (FStar_Absyn_Syntax.mk_Typ_app _123_1243 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _123_1247 = (let _123_1244 = (norm req)
in Some (_123_1244))
in (let _123_1246 = (let _123_1245 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _123_1245))
in (_123_1247, _123_1246)))))
end))
end
| _41_2058 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




