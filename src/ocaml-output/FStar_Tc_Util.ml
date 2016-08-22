
open Prims
# 30 "FStar.Tc.Util.fst"
type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)

# 80 "FStar.Tc.Util.fst"
let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))

# 85 "FStar.Tc.Util.fst"
let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _137_10 = (FStar_Tc_Env.get_range env)
in (let _137_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _137_10 _137_9))))

# 88 "FStar.Tc.Util.fst"
let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))

# 90 "FStar.Tc.Util.fst"
let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))

# 92 "FStar.Tc.Util.fst"
let syn' = (fun env k -> (let _137_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _137_29 k)))

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
(let _137_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _137_52 -> Some (_137_52)) _137_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _137_57 = (let _137_56 = (let _137_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _137_54 = (FStar_Tc_Env.get_range env)
in ((_137_55), (_137_54))))
in FStar_Absyn_Syntax.Error (_137_56))
in (Prims.raise _137_57))
end
| Some (g) -> begin
((e), (g))
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _137_61 = (let _137_60 = (let _137_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _137_58 = (FStar_Tc_Env.get_range env)
in ((_137_59), (_137_58))))
in FStar_Absyn_Syntax.Error (_137_60))
in (Prims.raise _137_61))
end
| Some (g) -> begin
(
# 121 "FStar.Tc.Util.fst"
let _45_53 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _137_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _137_62))
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
| _45_59 -> begin
(
# 126 "FStar.Tc.Util.fst"
let _45_60 = e
in (let _137_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _45_60.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _137_63; FStar_Absyn_Syntax.pos = _45_60.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _45_60.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _45_60.FStar_Absyn_Syntax.uvs}))
end)
in ((e), (g)))))
end)
end)))

# 127 "FStar.Tc.Util.fst"
let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_Options.full_context_dependency ()) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)

# 132 "FStar.Tc.Util.fst"
let as_uvar_e = (fun _45_1 -> (match (_45_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _45_75); FStar_Absyn_Syntax.tk = _45_72; FStar_Absyn_Syntax.pos = _45_70; FStar_Absyn_Syntax.fvs = _45_68; FStar_Absyn_Syntax.uvs = _45_66} -> begin
uv
end
| _45_80 -> begin
(FStar_All.failwith "Impossible")
end))

# 136 "FStar.Tc.Util.fst"
let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _45_92); FStar_Absyn_Syntax.tk = _45_89; FStar_Absyn_Syntax.pos = _45_87; FStar_Absyn_Syntax.fvs = _45_85; FStar_Absyn_Syntax.uvs = _45_83} -> begin
uv
end
| _45_97 -> begin
(FStar_All.failwith "Impossible")
end))

# 139 "FStar.Tc.Util.fst"
let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _137_73 = (let _137_72 = (FStar_Tc_Env.get_range env)
in (let _137_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _137_72 _137_71)))
in (FStar_All.pipe_right _137_73 Prims.fst)))

# 140 "FStar.Tc.Util.fst"
let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _137_80 = (let _137_79 = (FStar_Tc_Env.get_range env)
in (let _137_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _137_79 _137_78 k)))
in (FStar_All.pipe_right _137_80 Prims.fst)))

# 141 "FStar.Tc.Util.fst"
let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _137_87 = (let _137_86 = (FStar_Tc_Env.get_range env)
in (let _137_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _137_86 _137_85 t)))
in (FStar_All.pipe_right _137_87 Prims.fst)))

# 142 "FStar.Tc.Util.fst"
let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (
# 144 "FStar.Tc.Util.fst"
let _45_107 = (let _137_93 = (FStar_Tc_Env.get_range env)
in (let _137_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _137_93 _137_92 k)))
in (match (_45_107) with
| (t, u) -> begin
(let _137_95 = (let _137_94 = (as_uvar_t u)
in ((_137_94), (u.FStar_Absyn_Syntax.pos)))
in ((t), (_137_95)))
end)))

# 145 "FStar.Tc.Util.fst"
let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (
# 147 "FStar.Tc.Util.fst"
let _45_112 = (let _137_101 = (FStar_Tc_Env.get_range env)
in (let _137_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _137_101 _137_100 t)))
in (match (_45_112) with
| (e, u) -> begin
(let _137_103 = (let _137_102 = (as_uvar_e u)
in ((_137_102), (u.FStar_Absyn_Syntax.pos)))
in ((e), (_137_103)))
end)))

# 148 "FStar.Tc.Util.fst"
let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _137_106 = (let _137_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _137_105))
in (FStar_All.failwith _137_106))
end
| Some (tk) -> begin
tk
end))

# 151 "FStar.Tc.Util.fst"
let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _45_2 -> (match (_45_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _137_111 = (let _137_110 = (force_tk t)
in FStar_Util.Inl (_137_110))
in ((_137_111), (imp)))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _137_113 = (let _137_112 = (force_tk v)
in FStar_Util.Inr (_137_112))
in ((_137_113), (imp)))
end)))))

# 155 "FStar.Tc.Util.fst"
let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _45_3 -> (match (_45_3) with
| Some (FStar_Absyn_Syntax.Implicit (_45_129)) -> begin
true
end
| _45_133 -> begin
false
end))

# 157 "FStar.Tc.Util.fst"
let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (
# 159 "FStar.Tc.Util.fst"
let ktop = (let _137_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _137_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
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
| ((_45_149, qual))::_45_147 -> begin
(is_implicit qual)
end
| _45_154 -> begin
false
end)
in (
# 166 "FStar.Tc.Util.fst"
let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| (b)::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(
# 169 "FStar.Tc.Util.fst"
let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _137_137 = (let _137_134 = (let _137_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _137_133))
in (FStar_All.pipe_right _137_134 Prims.fst))
in (FStar_All.pipe_right _137_137 (fun x -> (let _137_136 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inl (x)), (_137_136))))))
end
| FStar_Util.Inr (x) -> begin
(let _137_142 = (let _137_139 = (let _137_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _137_138))
in (FStar_All.pipe_right _137_139 Prims.fst))
in (FStar_All.pipe_right _137_142 (fun x -> (let _137_141 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inr (x)), (_137_141))))))
end)
in (
# 172 "FStar.Tc.Util.fst"
let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _137_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_137_143)::subst)
end
in (
# 173 "FStar.Tc.Util.fst"
let _45_173 = (mk_implicits vars subst brest)
in (match (_45_173) with
| (imp_args, bs) -> begin
(((imp_arg)::imp_args), (bs))
end))))
end else begin
(let _137_144 = (FStar_Absyn_Util.subst_binders subst bs)
in (([]), (_137_144)))
end
end
| _45_175 -> begin
(let _137_145 = (FStar_Absyn_Util.subst_binders subst bs)
in (([]), (_137_145)))
end))
in if imp_follows then begin
(([]), (bs), (k'))
end else begin
(
# 179 "FStar.Tc.Util.fst"
let _45_178 = (let _137_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _137_146 [] bs))
in (match (_45_178) with
| (imps, bs) -> begin
((imps), (bs), (k'))
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_45_180, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_45_185) -> begin
(
# 185 "FStar.Tc.Util.fst"
let fvs = (FStar_Absyn_Util.freevars_kind k)
in (
# 186 "FStar.Tc.Util.fst"
let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (
# 187 "FStar.Tc.Util.fst"
let kres = (let _137_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _137_147 Prims.fst))
in (
# 188 "FStar.Tc.Util.fst"
let bs = (let _137_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _137_148))
in (
# 189 "FStar.Tc.Util.fst"
let kar = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (kres)) r)
in (
# 190 "FStar.Tc.Util.fst"
let _45_192 = (let _137_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _137_149))
in (([]), (bs), (kres))))))))
end
| _45_195 -> begin
(let _137_152 = (let _137_151 = (let _137_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in ((_137_150), (r)))
in FStar_Absyn_Syntax.Error (_137_151))
in (Prims.raise _137_152))
end))
in (aux ktop)))))

# 195 "FStar.Tc.Util.fst"
let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _45_4 -> (match (_45_4) with
| Some (FStar_Absyn_Syntax.Implicit (_45_198)) -> begin
true
end
| _45_202 -> begin
false
end))

# 199 "FStar.Tc.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (
# 207 "FStar.Tc.Util.fst"
let pvar_eq = (fun x y -> (match (((x), (y))) with
| (FStar_Tc_Env.Binding_var (x, _45_211), FStar_Tc_Env.Binding_var (y, _45_216)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _45_222), FStar_Tc_Env.Binding_typ (y, _45_227)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _45_232 -> begin
false
end))
in (
# 212 "FStar.Tc.Util.fst"
let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _45_5 -> (match (_45_5) with
| FStar_Tc_Env.Binding_var (x, _45_238) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _45_243) -> begin
FStar_Util.Inl (x)
end
| _45_247 -> begin
(FStar_All.failwith "impos")
end)))))
in (
# 219 "FStar.Tc.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _45_254) -> begin
(
# 228 "FStar.Tc.Util.fst"
let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (
# 229 "FStar.Tc.Util.fst"
let _45_260 = (let _137_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p _137_174 t))
in (match (_45_260) with
| (e, u) -> begin
(
# 230 "FStar.Tc.Util.fst"
let p = (
# 230 "FStar.Tc.Util.fst"
let _45_261 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term (((x), (e))); FStar_Absyn_Syntax.sort = _45_261.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_261.FStar_Absyn_Syntax.p})
in (([]), ([]), ([]), (env), (FStar_Util.Inr (e)), (p)))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _45_266) -> begin
(
# 234 "FStar.Tc.Util.fst"
let k = (new_kvar env)
in (
# 235 "FStar.Tc.Util.fst"
let _45_272 = (let _137_175 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _137_175 k))
in (match (_45_272) with
| (t, u) -> begin
(
# 236 "FStar.Tc.Util.fst"
let p = (
# 236 "FStar.Tc.Util.fst"
let _45_273 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ (((a), (t))); FStar_Absyn_Syntax.sort = _45_273.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_273.FStar_Absyn_Syntax.p})
in (([]), ([]), ([]), (env), (FStar_Util.Inl (t)), (p)))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(
# 240 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in (([]), ([]), ([]), (env), (FStar_Util.Inr (e)), (p)))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(
# 244 "FStar.Tc.Util.fst"
let w = (let _137_177 = (let _137_176 = (new_tvar env FStar_Absyn_Syntax.ktype)
in ((x.FStar_Absyn_Syntax.v), (_137_176)))
in FStar_Tc_Env.Binding_var (_137_177))
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
in (((w)::[]), ([]), ((w)::[]), (env), (FStar_Util.Inr (e)), (p)))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(
# 250 "FStar.Tc.Util.fst"
let b = (let _137_179 = (let _137_178 = (new_tvar env FStar_Absyn_Syntax.ktype)
in ((x.FStar_Absyn_Syntax.v), (_137_178)))
in FStar_Tc_Env.Binding_var (_137_179))
in (
# 251 "FStar.Tc.Util.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in (
# 252 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in (((b)::[]), ((b)::[]), ([]), (env), (FStar_Util.Inr (e)), (p)))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(
# 256 "FStar.Tc.Util.fst"
let w = (let _137_181 = (let _137_180 = (new_kvar env)
in ((a.FStar_Absyn_Syntax.v), (_137_180)))
in FStar_Tc_Env.Binding_typ (_137_181))
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
in (((w)::[]), ([]), ((w)::[]), (env), (FStar_Util.Inl (t)), (p)))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(
# 262 "FStar.Tc.Util.fst"
let b = (let _137_183 = (let _137_182 = (new_kvar env)
in ((a.FStar_Absyn_Syntax.v), (_137_182)))
in FStar_Tc_Env.Binding_typ (_137_183))
in (
# 263 "FStar.Tc.Util.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in (
# 264 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in (((b)::[]), ((b)::[]), ([]), (env), (FStar_Util.Inl (t)), (p)))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 269 "FStar.Tc.Util.fst"
let _45_332 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _45_310 _45_313 -> (match (((_45_310), (_45_313))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 270 "FStar.Tc.Util.fst"
let _45_320 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_45_320) with
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
in (((b')::b), ((a')::a), ((w')::w), (env), ((arg)::args), ((((pat), (imp)))::pats)))
end))
end)) (([]), ([]), ([]), (env), ([]), ([]))))
in (match (_45_332) with
| (b, a, w, env, args, pats) -> begin
(
# 275 "FStar.Tc.Util.fst"
let e = (let _137_191 = (let _137_190 = (let _137_189 = (let _137_188 = (let _137_187 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _137_186 = (FStar_All.pipe_right args FStar_List.rev)
in ((_137_187), (_137_186))))
in (FStar_Absyn_Syntax.mk_Exp_app' _137_188 None p.FStar_Absyn_Syntax.p))
in ((_137_189), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_137_190))
in (FStar_Absyn_Syntax.mk_Exp_meta _137_191))
in (let _137_194 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _137_193 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _137_192 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_137_194), (_137_193), (_137_192), (env), (FStar_Util.Inr (e)), ((
# 281 "FStar.Tc.Util.fst"
let _45_334 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons (((fv), (q), ((FStar_List.rev pats)))); FStar_Absyn_Syntax.sort = _45_334.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_334.FStar_Absyn_Syntax.p})))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_45_337) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 284 "FStar.Tc.Util.fst"
let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 287 "FStar.Tc.Util.fst"
let pats = (FStar_List.map (fun _45_349 -> (match (_45_349) with
| (p, imp) -> begin
(let _137_200 = (elaborate_pat env p)
in ((_137_200), (imp)))
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
| _45_355 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))))
end)
end
| Some (f, _45_358) -> begin
(
# 296 "FStar.Tc.Util.fst"
let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_45_371)::_45_369) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))))
end
| ((_45_377)::_45_375, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(
# 302 "FStar.Tc.Util.fst"
let a = (let _137_206 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _137_206 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _137_208 = (let _137_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((a), (FStar_Absyn_Syntax.tun)))) None _137_207))
in ((_137_208), ((as_imp imp))))
end else begin
(let _137_210 = (let _137_209 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _137_209))
in ((_137_210), ((as_imp imp))))
end)
end
| (FStar_Util.Inr (_45_388), Some (FStar_Absyn_Syntax.Implicit (dot))) -> begin
(
# 308 "FStar.Tc.Util.fst"
let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in if (allow_implicits && dot) then begin
(let _137_215 = (let _137_214 = (let _137_212 = (let _137_211 = (FStar_Absyn_Util.bvar_to_exp a)
in ((a), (_137_211)))
in FStar_Absyn_Syntax.Pat_dot_term (_137_212))
in (let _137_213 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _137_214 None _137_213)))
in ((_137_215), (true)))
end else begin
(let _137_217 = (let _137_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _137_216))
in ((_137_217), (true)))
end)
end
| _45_396 -> begin
(let _137_221 = (let _137_220 = (let _137_219 = (let _137_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _137_218))
in ((_137_219), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))
in FStar_Absyn_Syntax.Error (_137_220))
in (Prims.raise _137_221))
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (((f), (p.FStar_Absyn_Syntax.v))) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _137_222 = (aux formals' pats')
in (((p), ((as_imp imp))))::_137_222)
end
| ((FStar_Util.Inl (_45_424), imp), FStar_Absyn_Syntax.Pat_dot_typ (_45_429)) when allow_implicits -> begin
(let _137_223 = (aux formals' pats')
in (((p), ((as_imp imp))))::_137_223)
end
| ((FStar_Util.Inl (_45_433), imp), _45_438) -> begin
(
# 321 "FStar.Tc.Util.fst"
let a = (let _137_224 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _137_224 FStar_Absyn_Syntax.kun))
in (
# 322 "FStar.Tc.Util.fst"
let p1 = if allow_implicits then begin
(let _137_225 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((a), (FStar_Absyn_Syntax.tun)))) None _137_225))
end else begin
(let _137_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _137_226))
end
in (
# 326 "FStar.Tc.Util.fst"
let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_45_443) -> begin
pats'
end
| _45_446 -> begin
pats
end)
in (let _137_227 = (aux formals' pats')
in (((p1), ((as_imp imp))))::_137_227))))
end
| ((FStar_Util.Inr (_45_449), Some (FStar_Absyn_Syntax.Implicit (false))), _45_456) when p_imp -> begin
(let _137_228 = (aux formals' pats')
in (((p), (true)))::_137_228)
end
| ((FStar_Util.Inr (_45_459), Some (FStar_Absyn_Syntax.Implicit (dot))), _45_466) -> begin
(
# 333 "FStar.Tc.Util.fst"
let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 334 "FStar.Tc.Util.fst"
let p = if (allow_implicits && dot) then begin
(let _137_232 = (let _137_230 = (let _137_229 = (FStar_Absyn_Util.bvar_to_exp a)
in ((a), (_137_229)))
in FStar_Absyn_Syntax.Pat_dot_term (_137_230))
in (let _137_231 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _137_232 None _137_231)))
end else begin
(let _137_233 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _137_233))
end
in (let _137_234 = (aux formals' pats)
in (((p), (true)))::_137_234)))
end
| ((FStar_Util.Inr (_45_471), imp), _45_476) -> begin
(let _137_235 = (aux formals' pats')
in (((p), ((as_imp imp))))::_137_235)
end)
end))
in (aux f pats))
end)
in (
# 343 "FStar.Tc.Util.fst"
let _45_479 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons (((fv), (q), (pats))); FStar_Absyn_Syntax.sort = _45_479.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_479.FStar_Absyn_Syntax.p}))))
end
| _45_482 -> begin
p
end))
in (
# 347 "FStar.Tc.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 348 "FStar.Tc.Util.fst"
let p = (elaborate_pat env p)
in (
# 354 "FStar.Tc.Util.fst"
let _45_494 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_45_494) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _45_497)) -> begin
(let _137_244 = (let _137_243 = (let _137_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in ((_137_242), (p.FStar_Absyn_Syntax.p)))
in FStar_Absyn_Syntax.Error (_137_243))
in (Prims.raise _137_244))
end
| Some (FStar_Tc_Env.Binding_typ (x, _45_503)) -> begin
(let _137_247 = (let _137_246 = (let _137_245 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in ((_137_245), (p.FStar_Absyn_Syntax.p)))
in FStar_Absyn_Syntax.Error (_137_246))
in (Prims.raise _137_247))
end
| _45_508 -> begin
((b), (a), (w), (arg), (p))
end)
end))))
in (
# 361 "FStar.Tc.Util.fst"
let as_arg = (fun _45_6 -> (match (_45_6) with
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
| FStar_Absyn_Syntax.Pat_disj ((q)::pats) -> begin
(
# 371 "FStar.Tc.Util.fst"
let _45_530 = (one_pat false env q)
in (match (_45_530) with
| (b, a, _45_527, te, q) -> begin
(
# 372 "FStar.Tc.Util.fst"
let _45_545 = (FStar_List.fold_right (fun p _45_535 -> (match (_45_535) with
| (w, args, pats) -> begin
(
# 373 "FStar.Tc.Util.fst"
let _45_541 = (one_pat false env p)
in (match (_45_541) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _137_261 = (let _137_260 = (let _137_259 = (let _137_257 = (vars_of_bindings a)
in (let _137_256 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _137_257 _137_256)))
in (let _137_258 = (FStar_Tc_Env.get_range env)
in ((_137_259), (_137_258))))
in FStar_Absyn_Syntax.Error (_137_260))
in (Prims.raise _137_261))
end else begin
(let _137_263 = (let _137_262 = (as_arg arg)
in (_137_262)::args)
in (((FStar_List.append w' w)), (_137_263), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_45_545) with
| (w, args, pats) -> begin
(let _137_265 = (let _137_264 = (as_arg te)
in (_137_264)::args)
in (((FStar_List.append b w)), (_137_265), ((
# 378 "FStar.Tc.Util.fst"
let _45_546 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _45_546.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_546.FStar_Absyn_Syntax.p}))))
end))
end))
end
| _45_549 -> begin
(
# 381 "FStar.Tc.Util.fst"
let _45_557 = (one_pat true env p)
in (match (_45_557) with
| (b, _45_552, _45_554, arg, p) -> begin
(let _137_267 = (let _137_266 = (as_arg arg)
in (_137_266)::[])
in ((b), (_137_267), (p)))
end))
end))
in (
# 384 "FStar.Tc.Util.fst"
let _45_561 = (top_level_pat_as_args env p)
in (match (_45_561) with
| (b, args, p) -> begin
(
# 385 "FStar.Tc.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map (fun _45_7 -> (match (_45_7) with
| (FStar_Util.Inl (_45_564), _45_567) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _45_572) -> begin
e
end))))
in ((b), (exps), (p)))
end))))))))))

# 388 "FStar.Tc.Util.fst"
let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (
# 391 "FStar.Tc.Util.fst"
let qq = p
in (
# 392 "FStar.Tc.Util.fst"
let rec aux = (fun p e -> (
# 393 "FStar.Tc.Util.fst"
let pkg = (fun q t -> (let _137_286 = (FStar_All.pipe_left (fun _137_285 -> Some (_137_285)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _137_286 p.FStar_Absyn_Syntax.p)))
in (
# 394 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Util.unmeta_exp e)
in (match (((p.FStar_Absyn_Syntax.v), (e.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Pat_constant (_45_588), FStar_Absyn_Syntax.Exp_constant (_45_591)) -> begin
(let _137_287 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _137_287))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(
# 399 "FStar.Tc.Util.fst"
let _45_599 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _137_290 = (let _137_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _137_288 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _137_289 _137_288)))
in (FStar_All.failwith _137_290))
end else begin
()
end
in (
# 401 "FStar.Tc.Util.fst"
let _45_601 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _137_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _137_291 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _137_292 _137_291)))
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
let _45_604 = x
in {FStar_Absyn_Syntax.v = _45_604.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _45_604.FStar_Absyn_Syntax.p})
in (let _137_293 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _137_293))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(
# 408 "FStar.Tc.Util.fst"
let _45_612 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _137_296 = (let _137_295 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _137_294 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _137_295 _137_294)))
in (FStar_All.failwith _137_296))
end else begin
()
end
in (
# 410 "FStar.Tc.Util.fst"
let x = (
# 410 "FStar.Tc.Util.fst"
let _45_614 = x
in (let _137_297 = (force_tk e)
in {FStar_Absyn_Syntax.v = _45_614.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _137_297; FStar_Absyn_Syntax.p = _45_614.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _45_619), _45_623) -> begin
(
# 414 "FStar.Tc.Util.fst"
let x = (
# 414 "FStar.Tc.Util.fst"
let _45_625 = x
in (let _137_298 = (force_tk e)
in {FStar_Absyn_Syntax.v = _45_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _137_298; FStar_Absyn_Syntax.p = _45_625.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _45_635)) -> begin
(
# 418 "FStar.Tc.Util.fst"
let _45_639 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _137_299 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _137_299))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons (((fv'), (q), ([])))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _45_656); FStar_Absyn_Syntax.tk = _45_653; FStar_Absyn_Syntax.pos = _45_651; FStar_Absyn_Syntax.fvs = _45_649; FStar_Absyn_Syntax.uvs = _45_647}, args)) -> begin
(
# 423 "FStar.Tc.Util.fst"
let _45_664 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _137_300 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _137_300))
end else begin
()
end
in (
# 425 "FStar.Tc.Util.fst"
let fv = fv'
in (
# 427 "FStar.Tc.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _137_307 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons (((fv), (q), ((FStar_List.rev matched_pats))))) _137_307))
end
| ((arg)::args, ((argpat, _45_680))::argpats) -> begin
(match (((arg), (argpat.FStar_Absyn_Syntax.v))) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_45_687))), FStar_Absyn_Syntax.Pat_dot_typ (_45_692)) -> begin
(
# 432 "FStar.Tc.Util.fst"
let x = (let _137_308 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _137_308))
in (
# 433 "FStar.Tc.Util.fst"
let q = (let _137_310 = (FStar_All.pipe_left (fun _137_309 -> Some (_137_309)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((x), (t)))) _137_310 p.FStar_Absyn_Syntax.p))
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_45_700))), FStar_Absyn_Syntax.Pat_dot_term (_45_705)) -> begin
(
# 437 "FStar.Tc.Util.fst"
let x = (let _137_311 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _137_311))
in (
# 438 "FStar.Tc.Util.fst"
let q = (let _137_313 = (FStar_All.pipe_left (fun _137_312 -> Some (_137_312)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term (((x), (e)))) _137_313 p.FStar_Absyn_Syntax.p))
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _45_715) -> begin
(
# 442 "FStar.Tc.Util.fst"
let pat = (aux_t argpat t)
in (match_args ((((pat), ((as_imp imp))))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _45_723) -> begin
(
# 446 "FStar.Tc.Util.fst"
let pat = (let _137_314 = (aux argpat e)
in ((_137_314), ((as_imp imp))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _45_727 -> begin
(let _137_317 = (let _137_316 = (FStar_Absyn_Print.pat_to_string p)
in (let _137_315 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _137_316 _137_315)))
in (FStar_All.failwith _137_317))
end))
in (match_args [] args argpats))))
end
| _45_729 -> begin
(let _137_322 = (let _137_321 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _137_320 = (FStar_Absyn_Print.pat_to_string qq)
in (let _137_319 = (let _137_318 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _137_318 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _137_321 _137_320 _137_319))))
in (FStar_All.failwith _137_322))
end))))
and aux_t = (fun p t0 -> (
# 458 "FStar.Tc.Util.fst"
let pkg = (fun q k -> (let _137_330 = (FStar_All.pipe_left (fun _137_329 -> Some (_137_329)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _137_330 p.FStar_Absyn_Syntax.p)))
in (
# 459 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.compress_typ t0)
in (match (((p.FStar_Absyn_Syntax.v), (t.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(
# 462 "FStar.Tc.Util.fst"
let _45_741 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _137_333 = (let _137_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _137_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _137_332 _137_331)))
in (FStar_All.failwith _137_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(
# 467 "FStar.Tc.Util.fst"
let _45_748 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _137_336 = (let _137_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _137_334 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _137_335 _137_334)))
in (FStar_All.failwith _137_336))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _45_752), _45_756) -> begin
(
# 472 "FStar.Tc.Util.fst"
let k0 = (force_tk t0)
in (
# 473 "FStar.Tc.Util.fst"
let a = (
# 473 "FStar.Tc.Util.fst"
let _45_759 = a
in {FStar_Absyn_Syntax.v = _45_759.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _45_759.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ (((a), (t)))) a.FStar_Absyn_Syntax.sort)))
end
| _45_763 -> begin
(let _137_340 = (let _137_339 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _137_338 = (FStar_Absyn_Print.pat_to_string p)
in (let _137_337 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _137_339 _137_338 _137_337))))
in (FStar_All.failwith _137_340))
end))))
in (match (((p.FStar_Absyn_Syntax.v), (exps))) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _45_767) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 480 "FStar.Tc.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (let _137_342 = (FStar_All.pipe_left (fun _137_341 -> Some (_137_341)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _137_342 p.FStar_Absyn_Syntax.p)))
end
| (_45_771, (e)::[]) -> begin
(aux p e)
end
| _45_776 -> begin
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
| _45_783 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (
# 494 "FStar.Tc.Util.fst"
let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (
# 496 "FStar.Tc.Util.fst"
let pat_as_arg = (fun _45_790 -> (match (_45_790) with
| (p, i) -> begin
(
# 497 "FStar.Tc.Util.fst"
let _45_793 = (decorated_pattern_as_either p)
in (match (_45_793) with
| (vars, te) -> begin
(let _137_362 = (let _137_361 = (FStar_Absyn_Syntax.as_implicit i)
in ((te), (_137_361)))
in ((vars), (_137_362)))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_45_795) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _137_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in (([]), (_137_365)))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _137_368 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in (((FStar_Util.Inr (x))::[]), (_137_368)))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(
# 511 "FStar.Tc.Util.fst"
let _45_809 = (let _137_369 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _137_369 FStar_List.unzip))
in (match (_45_809) with
| (vars, args) -> begin
(
# 512 "FStar.Tc.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _137_375 = (let _137_374 = (let _137_373 = (let _137_372 = (FStar_Absyn_Syntax.mk_Exp_fvar ((fv), (q)) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in ((_137_372), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app' _137_373))
in (FStar_All.pipe_right _137_374 pkg))
in ((vars), (_137_375))))
end))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(FStar_All.failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.typ) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (a)) | (FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _137_377 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in (((FStar_Util.Inl (a))::[]), (_137_377)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(([]), (t))
end
| _45_833 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(
# 537 "FStar.Tc.Util.fst"
let _45_846 = (decorated_pattern_as_typ p)
in (match (_45_846) with
| (vars, t) -> begin
((vars), (FStar_Util.Inl (t)))
end))
end
| _45_848 -> begin
(
# 541 "FStar.Tc.Util.fst"
let _45_851 = (decorated_pattern_as_exp p)
in (match (_45_851) with
| (vars, e) -> begin
((vars), (FStar_Util.Inr (e)))
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
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _45_867; FStar_Absyn_Syntax.pos = _45_865; FStar_Absyn_Syntax.fvs = _45_863; FStar_Absyn_Syntax.uvs = _45_861}) -> begin
(
# 555 "FStar.Tc.Util.fst"
let _45_897 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _45_874 _45_878 -> (match (((_45_874), (_45_878))) with
| ((out, subst), (b, _45_877)) -> begin
(match (b) with
| FStar_Util.Inr (_45_880) -> begin
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
(let _137_385 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _137_385 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _137_388 = (let _137_387 = (let _137_386 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _137_386 Prims.fst))
in ((bs), (_137_387)))
in (FStar_Absyn_Syntax.mk_Typ_lam _137_388 (Some (k)) r))
end
| _45_891 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 565 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (arg))))::subst
in (let _137_390 = (let _137_389 = (FStar_Absyn_Syntax.targ arg)
in (_137_389)::out)
in ((_137_390), (subst))))))
end)
end)) (([]), ([]))))
in (match (_45_897) with
| (args, _45_896) -> begin
(FStar_Absyn_Syntax.mk_Typ_app ((t), ((FStar_List.rev args))) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _45_899 -> begin
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
let k = (let _137_401 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _137_401 Prims.fst))
in (((
# 577 "FStar.Tc.Util.fst"
let _45_910 = a
in {FStar_Absyn_Syntax.v = _45_910.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _45_910.FStar_Absyn_Syntax.p})), (false)))
end
| _45_913 -> begin
((a), (true))
end))
in (
# 580 "FStar.Tc.Util.fst"
let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(
# 582 "FStar.Tc.Util.fst"
let t = (let _137_406 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _137_406 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _45_922) -> begin
((x), (false))
end
| _45_925 -> begin
(FStar_All.failwith "impos")
end))
end
| _45_927 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _45_931) -> begin
((x), (true))
end
| _45_934 -> begin
(FStar_All.failwith "impos")
end)
end))
in (
# 595 "FStar.Tc.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _45_940)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _45_947) -> begin
((e), (t), (true))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 600 "FStar.Tc.Util.fst"
let _45_976 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _45_957 b -> (match (_45_957) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(
# 602 "FStar.Tc.Util.fst"
let _45_963 = (mk_t_binder scope a)
in (match (_45_963) with
| (tb, c) -> begin
(
# 603 "FStar.Tc.Util.fst"
let b = ((FStar_Util.Inl (tb)), ((Prims.snd b)))
in (
# 604 "FStar.Tc.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 605 "FStar.Tc.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in ((scope), (bs), ((c || check))))))
end))
end
| FStar_Util.Inr (x) -> begin
(
# 608 "FStar.Tc.Util.fst"
let _45_971 = (mk_v_binder scope x)
in (match (_45_971) with
| (vb, c) -> begin
(
# 609 "FStar.Tc.Util.fst"
let b = ((FStar_Util.Inr (vb)), ((Prims.snd b)))
in ((scope), ((FStar_List.append bs ((b)::[]))), ((c || check))))
end))
end)
end)) ((vars), ([]), (false))))
in (match (_45_976) with
| (scope, bs, check) -> begin
(
# 612 "FStar.Tc.Util.fst"
let _45_980 = (aux scope body)
in (match (_45_980) with
| (body, res, check_res) -> begin
(
# 613 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Util.ml_comp res r)
in (
# 614 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (
# 615 "FStar.Tc.Util.fst"
let _45_983 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _137_414 = (FStar_Range.string_of_range r)
in (let _137_413 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _137_414 _137_413)))
end else begin
()
end
in (
# 616 "FStar.Tc.Util.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) None e.FStar_Absyn_Syntax.pos)
in ((e), (t), ((check_res || check)))))))
end))
end))
end
| _45_987 -> begin
(let _137_416 = (let _137_415 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _137_415 Prims.fst))
in ((e), (_137_416), (false)))
end))
in (let _137_417 = (FStar_Tc_Env.t_binders env)
in (aux _137_417 e))))))
end
| _45_989 -> begin
((e), (t), (false))
end))

# 623 "FStar.Tc.Util.fst"
let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (
# 629 "FStar.Tc.Util.fst"
let _45_1006 = (match (c.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp), _45_999))::((FStar_Util.Inl (wlp), _45_994))::[] -> begin
((wp), (wlp))
end
| _45_1003 -> begin
(let _137_422 = (let _137_421 = (let _137_420 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _137_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _137_421))
in (FStar_All.failwith _137_422))
end)
in (match (_45_1006) with
| (wp, wlp) -> begin
((c.FStar_Absyn_Syntax.result_typ), (wp), (wlp))
end)))

# 633 "FStar.Tc.Util.fst"
let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (
# 636 "FStar.Tc.Util.fst"
let _45_1014 = (destruct_comp c)
in (match (_45_1014) with
| (_45_1011, wp, wlp) -> begin
(let _137_444 = (let _137_443 = (let _137_439 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _137_439))
in (let _137_442 = (let _137_441 = (let _137_440 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _137_440))
in (_137_441)::[])
in (_137_443)::_137_442))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _137_444; FStar_Absyn_Syntax.flags = []})
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
| Some (_45_1022, c) -> begin
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
let _45_1036 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 661 "FStar.Tc.Util.fst"
let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 665 "FStar.Tc.Util.fst"
let _45_1047 = (let _137_458 = (norm_eff_name env l1)
in (let _137_457 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _137_458 _137_457)))
in (match (_45_1047) with
| (m, _45_1044, _45_1046) -> begin
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
let _45_1059 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_45_1059) with
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
let _45_1065 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_45_1065) with
| (a, kwp) -> begin
(let _137_472 = (destruct_comp m1)
in (let _137_471 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_137_472), (_137_471))))
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
let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun md result wp wlp flags -> (let _137_495 = (let _137_494 = (let _137_493 = (FStar_Absyn_Syntax.targ wp)
in (let _137_492 = (let _137_491 = (FStar_Absyn_Syntax.targ wlp)
in (_137_491)::[])
in (_137_493)::_137_492))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _137_494; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _137_495)))

# 696 "FStar.Tc.Util.fst"
let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (
# 699 "FStar.Tc.Util.fst"
let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _45_1079 -> (match (()) with
| () -> begin
c0
end))}))

# 703 "FStar.Tc.Util.fst"
let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (
# 706 "FStar.Tc.Util.fst"
let _45_1082 = lc
in (let _137_505 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _45_1082.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _137_505; FStar_Absyn_Syntax.cflags = _45_1082.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _45_1084 -> (match (()) with
| () -> begin
(let _137_504 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _137_504))
end))})))

# 707 "FStar.Tc.Util.fst"
let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _137_508 = (FStar_Absyn_Util.compress_typ t)
in _137_508.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_45_1087) -> begin
true
end
| _45_1090 -> begin
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
let _45_1099 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_45_1099) with
| (a, kwp) -> begin
(
# 719 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (
# 720 "FStar.Tc.Util.fst"
let wp = (let _137_520 = (let _137_519 = (let _137_518 = (let _137_517 = (FStar_Absyn_Syntax.targ t)
in (let _137_516 = (let _137_515 = (FStar_Absyn_Syntax.varg v)
in (_137_515)::[])
in (_137_517)::_137_516))
in ((m.FStar_Absyn_Syntax.ret), (_137_518)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_519 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _137_520))
in (
# 721 "FStar.Tc.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (
# 723 "FStar.Tc.Util.fst"
let _45_1104 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _137_523 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _137_522 = (FStar_Absyn_Print.exp_to_string v)
in (let _137_521 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _137_523 _137_522 _137_521))))
end else begin
()
end
in c)))

# 725 "FStar.Tc.Util.fst"
let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _45_1111 -> (match (_45_1111) with
| (b, lc2) -> begin
(
# 728 "FStar.Tc.Util.fst"
let _45_1122 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(
# 730 "FStar.Tc.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _45_1115)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _45_1120 -> begin
"??"
end)
in (let _137_533 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _137_532 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _137_533 bstr _137_532))))
end else begin
()
end
in (
# 735 "FStar.Tc.Util.fst"
let bind_it = (fun _45_1125 -> (match (()) with
| () -> begin
(
# 736 "FStar.Tc.Util.fst"
let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (
# 737 "FStar.Tc.Util.fst"
let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (
# 738 "FStar.Tc.Util.fst"
let try_simplify = (fun _45_1129 -> (match (()) with
| () -> begin
(
# 739 "FStar.Tc.Util.fst"
let aux = (fun _45_1131 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_45_1134)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_45_1138)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _45_1142 -> begin
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
in (match (((e1opt), (b))) with
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _45_1147))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _137_541 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr (((x), (e))))::[]) c2)
in (FStar_All.pipe_left (fun _137_540 -> Some (_137_540)) _137_541))
end else begin
(aux ())
end
end
| _45_1153 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(
# 760 "FStar.Tc.Util.fst"
let _45_1171 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _137_545 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _45_1159)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _45_1165)) -> begin
(FStar_Absyn_Print.sli l)
end
| _45_1170 -> begin
"Something else"
end)
in (let _137_544 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _137_543 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _137_542 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _137_545 _137_544 _137_543 _137_542)))))
end else begin
()
end
in c)
end
| None -> begin
(
# 770 "FStar.Tc.Util.fst"
let _45_1186 = (lift_and_destruct env c1 c2)
in (match (_45_1186) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 771 "FStar.Tc.Util.fst"
let bs = (match (b) with
| None -> begin
(let _137_546 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_137_546)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _137_547 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_137_547)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _137_548 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_137_548)::[])
end
| _45_1199 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (
# 776 "FStar.Tc.Util.fst"
let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos))
in (
# 777 "FStar.Tc.Util.fst"
let wp_args = (let _137_563 = (FStar_Absyn_Syntax.targ t1)
in (let _137_562 = (let _137_561 = (FStar_Absyn_Syntax.targ t2)
in (let _137_560 = (let _137_559 = (FStar_Absyn_Syntax.targ wp1)
in (let _137_558 = (let _137_557 = (FStar_Absyn_Syntax.targ wlp1)
in (let _137_556 = (let _137_555 = (let _137_551 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _137_551))
in (let _137_554 = (let _137_553 = (let _137_552 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _137_552))
in (_137_553)::[])
in (_137_555)::_137_554))
in (_137_557)::_137_556))
in (_137_559)::_137_558))
in (_137_561)::_137_560))
in (_137_563)::_137_562))
in (
# 778 "FStar.Tc.Util.fst"
let wlp_args = (let _137_571 = (FStar_Absyn_Syntax.targ t1)
in (let _137_570 = (let _137_569 = (FStar_Absyn_Syntax.targ t2)
in (let _137_568 = (let _137_567 = (FStar_Absyn_Syntax.targ wlp1)
in (let _137_566 = (let _137_565 = (let _137_564 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _137_564))
in (_137_565)::[])
in (_137_567)::_137_566))
in (_137_569)::_137_568))
in (_137_571)::_137_570))
in (
# 779 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t2))))::[]) kwp)
in (
# 780 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_app ((md.FStar_Absyn_Syntax.bind_wp), (wp_args)) None t2.FStar_Absyn_Syntax.pos)
in (
# 781 "FStar.Tc.Util.fst"
let wlp = (FStar_Absyn_Syntax.mk_Typ_app ((md.FStar_Absyn_Syntax.bind_wlp), (wlp_args)) None t2.FStar_Absyn_Syntax.pos)
in (
# 782 "FStar.Tc.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _137_572 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _137_572; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))

# 787 "FStar.Tc.Util.fst"
let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 790 "FStar.Tc.Util.fst"
let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (
# 791 "FStar.Tc.Util.fst"
let _45_1217 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_45_1217) with
| (a, kwp) -> begin
(
# 792 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (
# 793 "FStar.Tc.Util.fst"
let wp = (let _137_587 = (let _137_586 = (let _137_585 = (FStar_Absyn_Syntax.targ t)
in (let _137_584 = (let _137_583 = (FStar_Absyn_Syntax.targ f)
in (_137_583)::[])
in (_137_585)::_137_584))
in ((mk_wp), (_137_586)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_587 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (
# 794 "FStar.Tc.Util.fst"
let wlp = (let _137_592 = (let _137_591 = (let _137_590 = (FStar_Absyn_Syntax.targ t)
in (let _137_589 = (let _137_588 = (FStar_Absyn_Syntax.targ f)
in (_137_588)::[])
in (_137_590)::_137_589))
in ((mk_wlp), (_137_591)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_592 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

# 795 "FStar.Tc.Util.fst"
let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (((t), (None), (t.FStar_Absyn_Syntax.pos))))))

# 797 "FStar.Tc.Util.fst"
let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (
# 800 "FStar.Tc.Util.fst"
let refresh = (fun _45_1226 -> (match (()) with
| () -> begin
(
# 801 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_45_1229) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 806 "FStar.Tc.Util.fst"
let _45_1233 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _137_604 = (let _137_603 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _137_603))
in (FStar_Util.print1 "Refreshing label at %s\n" _137_604))
end else begin
()
end
in (
# 808 "FStar.Tc.Util.fst"
let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 809 "FStar.Tc.Util.fst"
let _45_1236 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _137_607 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _137_606 = (let _137_605 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _137_605))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _137_607 _137_606)))
end else begin
()
end
in (
# 811 "FStar.Tc.Util.fst"
let _45_1241 = (destruct_comp c')
in (match (_45_1241) with
| (t, wp, wlp) -> begin
(
# 812 "FStar.Tc.Util.fst"
let wp = (let _137_610 = (let _137_609 = (let _137_608 = (FStar_Tc_Env.get_range env)
in ((wp), (Some (b)), (_137_608)))
in FStar_Absyn_Syntax.Meta_refresh_label (_137_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _137_610))
in (
# 813 "FStar.Tc.Util.fst"
let wlp = (let _137_613 = (let _137_612 = (let _137_611 = (FStar_Tc_Env.get_range env)
in ((wlp), (Some (b)), (_137_611)))
in FStar_Absyn_Syntax.Meta_refresh_label (_137_612))
in (FStar_Absyn_Syntax.mk_Typ_meta _137_613))
in (let _137_618 = (
# 814 "FStar.Tc.Util.fst"
let _45_1244 = c'
in (let _137_617 = (let _137_616 = (FStar_Absyn_Syntax.targ wp)
in (let _137_615 = (let _137_614 = (FStar_Absyn_Syntax.targ wlp)
in (_137_614)::[])
in (_137_616)::_137_615))
in {FStar_Absyn_Syntax.effect_name = _45_1244.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _45_1244.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _137_617; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _137_618))))
end)))))
end)
end)
end))
in (
# 815 "FStar.Tc.Util.fst"
let _45_1246 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1246.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1246.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _45_1246.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))

# 815 "FStar.Tc.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (reason), (r), (true))))))

# 818 "FStar.Tc.Util.fst"
let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _137_642 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _137_642)) then begin
f
end else begin
(let _137_643 = (reason ())
in (label _137_643 r f))
end
end))

# 824 "FStar.Tc.Util.fst"
let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _137_650 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_137_650))
end))

# 828 "FStar.Tc.Util.fst"
let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(
# 832 "FStar.Tc.Util.fst"
let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _45_1273 -> begin
g2
end))

# 834 "FStar.Tc.Util.fst"
let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (
# 837 "FStar.Tc.Util.fst"
let weaken = (fun _45_1278 -> (match (()) with
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
let _45_1287 = (destruct_comp c)
in (match (_45_1287) with
| (res_t, wp, wlp) -> begin
(
# 846 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 847 "FStar.Tc.Util.fst"
let wp = (let _137_669 = (let _137_668 = (let _137_667 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_666 = (let _137_665 = (FStar_Absyn_Syntax.targ f)
in (let _137_664 = (let _137_663 = (FStar_Absyn_Syntax.targ wp)
in (_137_663)::[])
in (_137_665)::_137_664))
in (_137_667)::_137_666))
in ((md.FStar_Absyn_Syntax.assume_p), (_137_668)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_669 None wp.FStar_Absyn_Syntax.pos))
in (
# 848 "FStar.Tc.Util.fst"
let wlp = (let _137_676 = (let _137_675 = (let _137_674 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_673 = (let _137_672 = (FStar_Absyn_Syntax.targ f)
in (let _137_671 = (let _137_670 = (FStar_Absyn_Syntax.targ wlp)
in (_137_670)::[])
in (_137_672)::_137_671))
in (_137_674)::_137_673))
in ((md.FStar_Absyn_Syntax.assume_p), (_137_675)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_676 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (
# 850 "FStar.Tc.Util.fst"
let _45_1291 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1291.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1291.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _45_1291.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))

# 850 "FStar.Tc.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(
# 855 "FStar.Tc.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _45_8 -> (match (_45_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _45_1302 -> begin
[]
end))))
in (
# 856 "FStar.Tc.Util.fst"
let strengthen = (fun _45_1305 -> (match (()) with
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
let xret = (let _137_698 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _137_698))
in (
# 868 "FStar.Tc.Util.fst"
let xbinding = FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))
in (
# 869 "FStar.Tc.Util.fst"
let lc = (let _137_701 = (lcomp_of_comp c)
in (let _137_700 = (let _137_699 = (lcomp_of_comp xret)
in ((Some (xbinding)), (_137_699)))
in (bind env (Some (e)) _137_701 _137_700)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (
# 872 "FStar.Tc.Util.fst"
let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 873 "FStar.Tc.Util.fst"
let _45_1320 = (destruct_comp c)
in (match (_45_1320) with
| (res_t, wp, wlp) -> begin
(
# 874 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 875 "FStar.Tc.Util.fst"
let wp = (let _137_710 = (let _137_709 = (let _137_708 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_707 = (let _137_706 = (let _137_703 = (let _137_702 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _137_702 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _137_703))
in (let _137_705 = (let _137_704 = (FStar_Absyn_Syntax.targ wp)
in (_137_704)::[])
in (_137_706)::_137_705))
in (_137_708)::_137_707))
in ((md.FStar_Absyn_Syntax.assert_p), (_137_709)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_710 None wp.FStar_Absyn_Syntax.pos))
in (
# 876 "FStar.Tc.Util.fst"
let wlp = (let _137_717 = (let _137_716 = (let _137_715 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_714 = (let _137_713 = (FStar_Absyn_Syntax.targ f)
in (let _137_712 = (let _137_711 = (FStar_Absyn_Syntax.targ wlp)
in (_137_711)::[])
in (_137_713)::_137_712))
in (_137_715)::_137_714))
in ((md.FStar_Absyn_Syntax.assume_p), (_137_716)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_717 None wlp.FStar_Absyn_Syntax.pos))
in (
# 877 "FStar.Tc.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _137_721 = (
# 879 "FStar.Tc.Util.fst"
let _45_1325 = lc
in (let _137_720 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _137_719 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _137_718 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _137_718))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _137_720; FStar_Absyn_Syntax.res_typ = _45_1325.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _137_719; FStar_Absyn_Syntax.comp = strengthen})))
in ((_137_721), ((
# 882 "FStar.Tc.Util.fst"
let _45_1327 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _45_1327.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _45_1327.FStar_Tc_Rel.implicits}))))))
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
let _45_1337 = (let _137_729 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _137_728 = (FStar_Absyn_Util.bvar_to_exp y)
in ((_137_729), (_137_728))))
in (match (_45_1337) with
| (xexp, yexp) -> begin
(
# 889 "FStar.Tc.Util.fst"
let yret = (let _137_734 = (let _137_733 = (let _137_732 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_731 = (let _137_730 = (FStar_Absyn_Syntax.varg yexp)
in (_137_730)::[])
in (_137_732)::_137_731))
in ((md_pure.FStar_Absyn_Syntax.ret), (_137_733)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_734 None res_t.FStar_Absyn_Syntax.pos))
in (
# 890 "FStar.Tc.Util.fst"
let x_eq_y_yret = (let _137_742 = (let _137_741 = (let _137_740 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_739 = (let _137_738 = (let _137_735 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _137_735))
in (let _137_737 = (let _137_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_137_736)::[])
in (_137_738)::_137_737))
in (_137_740)::_137_739))
in ((md_pure.FStar_Absyn_Syntax.assume_p), (_137_741)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_742 None res_t.FStar_Absyn_Syntax.pos))
in (
# 891 "FStar.Tc.Util.fst"
let forall_y_x_eq_y_yret = (let _137_753 = (let _137_752 = (let _137_751 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_750 = (let _137_749 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_748 = (let _137_747 = (let _137_746 = (let _137_745 = (let _137_744 = (let _137_743 = (FStar_Absyn_Syntax.v_binder y)
in (_137_743)::[])
in ((_137_744), (x_eq_y_yret)))
in (FStar_Absyn_Syntax.mk_Typ_lam _137_745 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _137_746))
in (_137_747)::[])
in (_137_749)::_137_748))
in (_137_751)::_137_750))
in ((md_pure.FStar_Absyn_Syntax.close_wp), (_137_752)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_753 None res_t.FStar_Absyn_Syntax.pos))
in (
# 892 "FStar.Tc.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (
# 893 "FStar.Tc.Util.fst"
let lc = (let _137_756 = (lcomp_of_comp comp)
in (let _137_755 = (let _137_754 = (lcomp_of_comp lc2)
in ((Some (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort))))), (_137_754)))
in (bind env None _137_756 _137_755)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))

# 894 "FStar.Tc.Util.fst"
let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 897 "FStar.Tc.Util.fst"
let comp = (fun _45_1348 -> (match (()) with
| () -> begin
(
# 898 "FStar.Tc.Util.fst"
let _45_1364 = (let _137_768 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _137_767 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _137_768 _137_767)))
in (match (_45_1364) with
| ((md, _45_1351, _45_1353), (res_t, wp_then, wlp_then), (_45_1360, wp_else, wlp_else)) -> begin
(
# 899 "FStar.Tc.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _137_788 = (let _137_786 = (let _137_785 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_784 = (let _137_783 = (FStar_Absyn_Syntax.targ g)
in (let _137_782 = (let _137_781 = (FStar_Absyn_Syntax.targ wp_t)
in (let _137_780 = (let _137_779 = (FStar_Absyn_Syntax.targ wp_e)
in (_137_779)::[])
in (_137_781)::_137_780))
in (_137_783)::_137_782))
in (_137_785)::_137_784))
in ((md.FStar_Absyn_Syntax.if_then_else), (_137_786)))
in (let _137_787 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _137_788 None _137_787))))
in (
# 900 "FStar.Tc.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 901 "FStar.Tc.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_Options.split_cases ()) > 0) then begin
(
# 903 "FStar.Tc.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 905 "FStar.Tc.Util.fst"
let wp = (let _137_795 = (let _137_794 = (let _137_793 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_792 = (let _137_791 = (FStar_Absyn_Syntax.targ wlp)
in (let _137_790 = (let _137_789 = (FStar_Absyn_Syntax.targ wp)
in (_137_789)::[])
in (_137_791)::_137_790))
in (_137_793)::_137_792))
in ((md.FStar_Absyn_Syntax.ite_wp), (_137_794)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_795 None wp.FStar_Absyn_Syntax.pos))
in (
# 906 "FStar.Tc.Util.fst"
let wlp = (let _137_800 = (let _137_799 = (let _137_798 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_797 = (let _137_796 = (FStar_Absyn_Syntax.targ wlp)
in (_137_796)::[])
in (_137_798)::_137_797))
in ((md.FStar_Absyn_Syntax.ite_wlp), (_137_799)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_800 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _137_801 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _137_801; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))

# 911 "FStar.Tc.Util.fst"
let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (
# 914 "FStar.Tc.Util.fst"
let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun eff _45_1387 -> (match (_45_1387) with
| (_45_1385, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (
# 917 "FStar.Tc.Util.fst"
let bind_cases = (fun _45_1390 -> (match (()) with
| () -> begin
(
# 918 "FStar.Tc.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _137_831 = (let _137_829 = (let _137_828 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_827 = (let _137_826 = (FStar_Absyn_Syntax.targ g)
in (let _137_825 = (let _137_824 = (FStar_Absyn_Syntax.targ wp_t)
in (let _137_823 = (let _137_822 = (FStar_Absyn_Syntax.targ wp_e)
in (_137_822)::[])
in (_137_824)::_137_823))
in (_137_826)::_137_825))
in (_137_828)::_137_827))
in ((md.FStar_Absyn_Syntax.if_then_else), (_137_829)))
in (let _137_830 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _137_831 None _137_830))))
in (
# 919 "FStar.Tc.Util.fst"
let default_case = (
# 920 "FStar.Tc.Util.fst"
let post_k = (let _137_834 = (let _137_833 = (let _137_832 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_137_832)::[])
in ((_137_833), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _137_834 res_t.FStar_Absyn_Syntax.pos))
in (
# 921 "FStar.Tc.Util.fst"
let kwp = (let _137_837 = (let _137_836 = (let _137_835 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_137_835)::[])
in ((_137_836), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _137_837 res_t.FStar_Absyn_Syntax.pos))
in (
# 922 "FStar.Tc.Util.fst"
let post = (let _137_838 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _137_838 post_k))
in (
# 923 "FStar.Tc.Util.fst"
let wp = (let _137_845 = (let _137_844 = (let _137_839 = (FStar_Absyn_Syntax.t_binder post)
in (_137_839)::[])
in (let _137_843 = (let _137_842 = (let _137_840 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _137_840))
in (let _137_841 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _137_842 _137_841)))
in ((_137_844), (_137_843))))
in (FStar_Absyn_Syntax.mk_Typ_lam _137_845 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (
# 924 "FStar.Tc.Util.fst"
let wlp = (let _137_849 = (let _137_848 = (let _137_846 = (FStar_Absyn_Syntax.t_binder post)
in (_137_846)::[])
in (let _137_847 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((_137_848), (_137_847))))
in (FStar_Absyn_Syntax.mk_Typ_lam _137_849 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (
# 925 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 927 "FStar.Tc.Util.fst"
let comp = (FStar_List.fold_right (fun _45_1406 celse -> (match (_45_1406) with
| (g, cthen) -> begin
(
# 928 "FStar.Tc.Util.fst"
let _45_1424 = (let _137_852 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _137_852 celse))
in (match (_45_1424) with
| ((md, _45_1410, _45_1412), (_45_1415, wp_then, wlp_then), (_45_1420, wp_else, wlp_else)) -> begin
(let _137_854 = (ifthenelse md res_t g wp_then wp_else)
in (let _137_853 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _137_854 _137_853 [])))
end))
end)) lcases default_case)
in if ((FStar_Options.split_cases ()) > 0) then begin
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
let _45_1432 = (destruct_comp comp)
in (match (_45_1432) with
| (_45_1429, wp, wlp) -> begin
(
# 935 "FStar.Tc.Util.fst"
let wp = (let _137_861 = (let _137_860 = (let _137_859 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_858 = (let _137_857 = (FStar_Absyn_Syntax.targ wlp)
in (let _137_856 = (let _137_855 = (FStar_Absyn_Syntax.targ wp)
in (_137_855)::[])
in (_137_857)::_137_856))
in (_137_859)::_137_858))
in ((md.FStar_Absyn_Syntax.ite_wp), (_137_860)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_861 None wp.FStar_Absyn_Syntax.pos))
in (
# 936 "FStar.Tc.Util.fst"
let wlp = (let _137_866 = (let _137_865 = (let _137_864 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_863 = (let _137_862 = (FStar_Absyn_Syntax.targ wlp)
in (_137_862)::[])
in (_137_864)::_137_863))
in ((md.FStar_Absyn_Syntax.ite_wlp), (_137_865)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_866 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))

# 941 "FStar.Tc.Util.fst"
let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (
# 944 "FStar.Tc.Util.fst"
let close = (fun _45_1439 -> (match (()) with
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
let bs = (let _137_885 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_137_885)::[])
in (
# 952 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos)
in (let _137_892 = (let _137_891 = (let _137_890 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_889 = (let _137_888 = (FStar_Absyn_Syntax.targ t)
in (let _137_887 = (let _137_886 = (FStar_Absyn_Syntax.targ wp)
in (_137_886)::[])
in (_137_888)::_137_887))
in (_137_890)::_137_889))
in ((md.FStar_Absyn_Syntax.close_wp), (_137_891)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_892 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(
# 956 "FStar.Tc.Util.fst"
let bs = (let _137_893 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_137_893)::[])
in (
# 957 "FStar.Tc.Util.fst"
let wp = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos)
in (let _137_898 = (let _137_897 = (let _137_896 = (FStar_Absyn_Syntax.targ res_t)
in (let _137_895 = (let _137_894 = (FStar_Absyn_Syntax.targ wp)
in (_137_894)::[])
in (_137_896)::_137_895))
in ((md.FStar_Absyn_Syntax.close_wp_t), (_137_897)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_898 None wp0.FStar_Absyn_Syntax.pos))))
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
let _45_1470 = (destruct_comp c)
in (match (_45_1470) with
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
let _45_1474 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1474.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1474.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _45_1474.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))

# 971 "FStar.Tc.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (
# 974 "FStar.Tc.Util.fst"
let refine = (fun _45_1480 -> (match (()) with
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
let ret = (let _137_907 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _137_907))
in (
# 986 "FStar.Tc.Util.fst"
let eq_ret = (let _137_909 = (let _137_908 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_137_908))
in (weaken_precondition env ret _137_909))
in (let _137_912 = (let _137_911 = (let _137_910 = (lcomp_of_comp c)
in (bind env None _137_910 ((Some (FStar_Tc_Env.Binding_var (((x), (t))))), (eq_ret))))
in (_137_911.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _137_912 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
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
let _45_1490 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1490.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1490.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))

# 994 "FStar.Tc.Util.fst"
let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _137_924 = (let _137_923 = (let _137_922 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _137_921 = (FStar_Tc_Env.get_range env)
in ((_137_922), (_137_921))))
in FStar_Absyn_Syntax.Error (_137_923))
in (Prims.raise _137_924))
end
| Some (g) -> begin
((e), (c'), (g))
end))

# 1000 "FStar.Tc.Util.fst"
let maybe_instantiate_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.implicits) = (fun env t k -> (
# 1003 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
((t), (k), ([]))
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 1007 "FStar.Tc.Util.fst"
let rec aux = (fun subst _45_9 -> (match (_45_9) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_45_1514))))::rest -> begin
(
# 1009 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1010 "FStar.Tc.Util.fst"
let _45_1522 = (new_implicit_tvar env k)
in (match (_45_1522) with
| (t, u) -> begin
(
# 1011 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (
# 1012 "FStar.Tc.Util.fst"
let _45_1528 = (aux subst rest)
in (match (_45_1528) with
| (args, bs, subst, us) -> begin
(let _137_938 = (let _137_937 = (let _137_936 = (FStar_All.pipe_left (fun _137_935 -> Some (_137_935)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_137_936)))
in (_137_937)::args)
in ((_137_938), (bs), (subst), ((FStar_Util.Inl (u))::us)))
end)))
end)))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_45_1533))))::rest -> begin
(
# 1016 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1017 "FStar.Tc.Util.fst"
let _45_1541 = (new_implicit_evar env t)
in (match (_45_1541) with
| (v, u) -> begin
(
# 1018 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v))))::subst
in (
# 1019 "FStar.Tc.Util.fst"
let _45_1547 = (aux subst rest)
in (match (_45_1547) with
| (args, bs, subst, us) -> begin
(let _137_942 = (let _137_941 = (let _137_940 = (FStar_All.pipe_left (fun _137_939 -> Some (_137_939)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (v)), (_137_940)))
in (_137_941)::args)
in ((_137_942), (bs), (subst), ((FStar_Util.Inr (u))::us)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), ([]))
end))
in (
# 1023 "FStar.Tc.Util.fst"
let _45_1553 = (aux [] bs)
in (match (_45_1553) with
| (args, bs, subst, implicits) -> begin
(
# 1024 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Syntax.mk_Kind_arrow' ((bs), (k)) t.FStar_Absyn_Syntax.pos)
in (
# 1025 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _137_943 = (FStar_Absyn_Syntax.mk_Typ_app' ((t), (args)) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((_137_943), (k), (implicits)))))
end)))
end
| _45_1557 -> begin
((t), (k), ([]))
end)
end))

# 1028 "FStar.Tc.Util.fst"
let maybe_instantiate : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.implicits) = (fun env e t -> (
# 1031 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
((e), (t), ([]))
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 1035 "FStar.Tc.Util.fst"
let rec aux = (fun subst _45_10 -> (match (_45_10) with
| ((FStar_Util.Inl (a), _45_1573))::rest -> begin
(
# 1037 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1038 "FStar.Tc.Util.fst"
let _45_1579 = (new_implicit_tvar env k)
in (match (_45_1579) with
| (t, u) -> begin
(
# 1039 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (
# 1040 "FStar.Tc.Util.fst"
let _45_1585 = (aux subst rest)
in (match (_45_1585) with
| (args, bs, subst, us) -> begin
(let _137_957 = (let _137_956 = (let _137_955 = (FStar_All.pipe_left (fun _137_954 -> Some (_137_954)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_137_955)))
in (_137_956)::args)
in ((_137_957), (bs), (subst), ((FStar_Util.Inl (u))::us)))
end)))
end)))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_45_1590))))::rest -> begin
(
# 1044 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1045 "FStar.Tc.Util.fst"
let _45_1598 = (new_implicit_evar env t)
in (match (_45_1598) with
| (v, u) -> begin
(
# 1046 "FStar.Tc.Util.fst"
let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v))))::subst
in (
# 1047 "FStar.Tc.Util.fst"
let _45_1604 = (aux subst rest)
in (match (_45_1604) with
| (args, bs, subst, us) -> begin
(let _137_961 = (let _137_960 = (let _137_959 = (FStar_All.pipe_left (fun _137_958 -> Some (_137_958)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (v)), (_137_959)))
in (_137_960)::args)
in ((_137_961), (bs), (subst), ((FStar_Util.Inr (u))::us)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), ([]))
end))
in (
# 1051 "FStar.Tc.Util.fst"
let _45_1610 = (aux [] bs)
in (match (_45_1610) with
| (args, bs, subst, implicits) -> begin
(
# 1052 "FStar.Tc.Util.fst"
let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _45_1617 -> begin
(FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(
# 1058 "FStar.Tc.Util.fst"
let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _137_968 = (mk_exp_app e args (Some (t)))
in ((_137_968), (t), (implicits))))
end else begin
((e), (t), ([]))
end
end
| _45_1621 -> begin
(
# 1062 "FStar.Tc.Util.fst"
let t = (let _137_969 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _137_969 (FStar_Absyn_Util.subst_typ subst)))
in (let _137_970 = (mk_exp_app e args (Some (t)))
in ((_137_970), (t), (implicits))))
end))
end)))
end
| _45_1624 -> begin
((e), (t), ([]))
end)
end))

# 1066 "FStar.Tc.Util.fst"
let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (
# 1069 "FStar.Tc.Util.fst"
let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _137_979 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in ((_137_979), (false)))
end else begin
(let _137_980 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in ((_137_980), (true)))
end
in (match (gopt) with
| (None, _45_1632) -> begin
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
let _45_1640 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1640.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _45_1640.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _45_1640.FStar_Absyn_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(
# 1082 "FStar.Tc.Util.fst"
let g = (
# 1082 "FStar.Tc.Util.fst"
let _45_1645 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _45_1645.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _45_1645.FStar_Tc_Rel.implicits})
in (
# 1083 "FStar.Tc.Util.fst"
let strengthen = (fun _45_1649 -> (match (()) with
| () -> begin
(
# 1084 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 1086 "FStar.Tc.Util.fst"
let _45_1651 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _137_984 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _137_983 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _137_984 _137_983)))
end else begin
()
end
in (
# 1089 "FStar.Tc.Util.fst"
let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 1090 "FStar.Tc.Util.fst"
let _45_1656 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_45_1656) with
| (a, kwp) -> begin
(
# 1091 "FStar.Tc.Util.fst"
let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
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
let wp = (let _137_989 = (let _137_988 = (let _137_987 = (FStar_Absyn_Syntax.targ t)
in (let _137_986 = (let _137_985 = (FStar_Absyn_Syntax.varg xexp)
in (_137_985)::[])
in (_137_987)::_137_986))
in ((md.FStar_Absyn_Syntax.ret), (_137_988)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_989 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (
# 1096 "FStar.Tc.Util.fst"
let cret = (let _137_990 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _137_990))
in (
# 1097 "FStar.Tc.Util.fst"
let guard = if apply_guard then begin
(let _137_993 = (let _137_992 = (let _137_991 = (FStar_Absyn_Syntax.varg xexp)
in (_137_991)::[])
in ((f), (_137_992)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_993 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (
# 1098 "FStar.Tc.Util.fst"
let _45_1666 = (let _137_1001 = (FStar_All.pipe_left (fun _137_998 -> Some (_137_998)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _137_1000 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _137_999 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _137_1001 _137_1000 e cret _137_999))))
in (match (_45_1666) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 1105 "FStar.Tc.Util.fst"
let c = (let _137_1003 = (let _137_1002 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _137_1002))
in (bind env (Some (e)) _137_1003 ((Some (FStar_Tc_Env.Binding_var (((x), (lc.FStar_Absyn_Syntax.res_typ))))), (eq_ret))))
in (
# 1106 "FStar.Tc.Util.fst"
let c = (c.FStar_Absyn_Syntax.comp ())
in (
# 1107 "FStar.Tc.Util.fst"
let _45_1669 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _137_1004 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _137_1004))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (
# 1110 "FStar.Tc.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _45_11 -> (match (_45_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _45_1675 -> begin
[]
end))))
in (
# 1111 "FStar.Tc.Util.fst"
let lc = (
# 1111 "FStar.Tc.Util.fst"
let _45_1677 = lc
in (let _137_1006 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _137_1006; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in ((e), (lc), (g))))))
end))
end)))

# 1112 "FStar.Tc.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 1119 "FStar.Tc.Util.fst"
let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if ((((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t)) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k)) > 0) then begin
(
# 1124 "FStar.Tc.Util.fst"
let ue = (let _137_1011 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _137_1011))
in (
# 1125 "FStar.Tc.Util.fst"
let ut = (let _137_1012 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _137_1012))
in (
# 1126 "FStar.Tc.Util.fst"
let uk = (let _137_1013 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _137_1013))
in (
# 1127 "FStar.Tc.Util.fst"
let union = (FStar_String.concat "," (FStar_List.append ue (FStar_List.append ut uk)))
in (
# 1129 "FStar.Tc.Util.fst"
let hide_uvar_nums_saved = (FStar_Options.hide_uvar_nums ())
in (
# 1130 "FStar.Tc.Util.fst"
let print_implicits_saved = (FStar_Options.print_implicits ())
in (
# 1131 "FStar.Tc.Util.fst"
let _45_1689 = (FStar_Options.push ())
in (
# 1132 "FStar.Tc.Util.fst"
let _45_1691 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (
# 1133 "FStar.Tc.Util.fst"
let _45_1693 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (
# 1134 "FStar.Tc.Util.fst"
let _45_1695 = (let _137_1015 = (let _137_1014 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _137_1014))
in (FStar_Tc_Errors.report r _137_1015))
in (FStar_Options.pop ())))))))))))
end else begin
()
end))

# 1137 "FStar.Tc.Util.fst"
let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _137_1023 = (FStar_Util.for_all (fun _45_1703 -> (match (_45_1703) with
| (_45_1701, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _137_1023)) then begin
None
end else begin
(
# 1143 "FStar.Tc.Util.fst"
let norm = (fun c -> (
# 1144 "FStar.Tc.Util.fst"
let _45_1706 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _137_1026 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _137_1026))
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
let _45_1710 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _137_1027 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _137_1027))
end else begin
()
end
in c)))))
in (
# 1152 "FStar.Tc.Util.fst"
let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (
# 1153 "FStar.Tc.Util.fst"
let gen_uvars = (fun uvs -> (let _137_1030 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _137_1030 FStar_Util.set_elements)))
in (
# 1154 "FStar.Tc.Util.fst"
let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _45_1719) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _45_12 -> (match (_45_12) with
| (FStar_Util.Inl (_45_1724), _45_1727) -> begin
true
end
| _45_1730 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _45_1732 -> begin
true
end))
in (
# 1161 "FStar.Tc.Util.fst"
let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _45_1735 -> (match (_45_1735) with
| (e, c) -> begin
(
# 1162 "FStar.Tc.Util.fst"
let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _137_1035 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _137_1035)) then begin
(([]), (e), (c))
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
let _45_1751 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _137_1036 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _137_1036))) then begin
(
# 1174 "FStar.Tc.Util.fst"
let _45_1747 = (destruct_comp ct)
in (match (_45_1747) with
| (_45_1743, wp, _45_1746) -> begin
(
# 1175 "FStar.Tc.Util.fst"
let binder = (let _137_1037 = (FStar_Absyn_Syntax.null_v_binder t)
in (_137_1037)::[])
in (
# 1176 "FStar.Tc.Util.fst"
let post = (let _137_1041 = (let _137_1038 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((binder), (_137_1038)))
in (let _137_1040 = (let _137_1039 = (FStar_Absyn_Syntax.mk_Kind_arrow ((binder), (FStar_Absyn_Syntax.ktype)) t.FStar_Absyn_Syntax.pos)
in Some (_137_1039))
in (FStar_Absyn_Syntax.mk_Typ_lam _137_1041 _137_1040 t.FStar_Absyn_Syntax.pos)))
in (
# 1177 "FStar.Tc.Util.fst"
let vc = (let _137_1048 = (let _137_1047 = (let _137_1046 = (let _137_1045 = (let _137_1044 = (FStar_Absyn_Syntax.targ post)
in (_137_1044)::[])
in ((wp), (_137_1045)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_1046))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _137_1047))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _137_1048))
in (let _137_1049 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _137_1049)))))
end))
end else begin
()
end
in ((uvs), (e), (c))))))))
end)
end))))
in (
# 1182 "FStar.Tc.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _45_1757 -> (match (_45_1757) with
| (uvs, e, c) -> begin
(
# 1183 "FStar.Tc.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _45_1760 -> (match (_45_1760) with
| (u, k) -> begin
(
# 1184 "FStar.Tc.Util.fst"
let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_45_1798) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _45_1801 -> begin
(
# 1189 "FStar.Tc.Util.fst"
let a = (let _137_1054 = (let _137_1053 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _137_1052 -> Some (_137_1052)) _137_1053))
in (FStar_Absyn_Util.new_bvd _137_1054))
in (
# 1190 "FStar.Tc.Util.fst"
let t = (let _137_1055 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _137_1055 k))
in (
# 1192 "FStar.Tc.Util.fst"
let _45_1804 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _137_1057 = (FStar_All.pipe_left (fun _137_1056 -> Some (_137_1056)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (a)), (_137_1057))))
end))))
in (
# 1196 "FStar.Tc.Util.fst"
let t = (match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.function_formals)) with
| Some (bs, cod) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (((FStar_List.append tvars bs)), (cod)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(FStar_Absyn_Util.comp_result c)
end
| _45_1815 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((tvars), (c)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (
# 1200 "FStar.Tc.Util.fst"
let e = (match (tvars) with
| [] -> begin
e
end
| _45_1819 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' ((tvars), (e)) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _137_1058 = (FStar_Absyn_Syntax.mk_Total t)
in ((e), (_137_1058))))))
end))))
in Some (ecs)))))))
end)

# 1204 "FStar.Tc.Util.fst"
let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (
# 1207 "FStar.Tc.Util.fst"
let _45_1831 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _137_1067 = (let _137_1066 = (FStar_List.map (fun _45_1830 -> (match (_45_1830) with
| (lb, _45_1827, _45_1829) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _137_1066 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _137_1067))
end else begin
()
end
in (match ((let _137_1069 = (FStar_All.pipe_right lecs (FStar_List.map (fun _45_1837 -> (match (_45_1837) with
| (_45_1834, e, c) -> begin
((e), (c))
end))))
in (gen verify env _137_1069))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _45_1846 _45_1849 -> (match (((_45_1846), (_45_1849))) with
| ((l, _45_1843, _45_1845), (e, c)) -> begin
(
# 1212 "FStar.Tc.Util.fst"
let _45_1850 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _137_1074 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _137_1073 = (FStar_Absyn_Print.lbname_to_string l)
in (let _137_1072 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _137_1074 _137_1073 _137_1072))))
end else begin
()
end
in ((l), (e), (c)))
end)) lecs ecs)
end)))

# 1213 "FStar.Tc.Util.fst"
let check_unresolved_implicits : FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun g -> (
# 1216 "FStar.Tc.Util.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Uvar -> begin
true
end
| _45_1857 -> begin
false
end))
in (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _45_13 -> (match (_45_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _45_1863) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_45_1867, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unresolved implicit argument"), (r)))))
end
| _45_1873 -> begin
()
end)))

# 1221 "FStar.Tc.Util.fst"
let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (
# 1224 "FStar.Tc.Util.fst"
let discharge = (fun g -> (
# 1225 "FStar.Tc.Util.fst"
let _45_1879 = (FStar_Tc_Rel.try_discharge_guard env g)
in (
# 1226 "FStar.Tc.Util.fst"
let _45_1881 = (check_unresolved_implicits g)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (
# 1228 "FStar.Tc.Util.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _137_1089 = (discharge g)
in (let _137_1088 = (lc.FStar_Absyn_Syntax.comp ())
in ((_137_1089), (_137_1088))))
end else begin
(
# 1231 "FStar.Tc.Util.fst"
let c = (lc.FStar_Absyn_Syntax.comp ())
in (
# 1232 "FStar.Tc.Util.fst"
let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (
# 1233 "FStar.Tc.Util.fst"
let c = (let _137_1090 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _137_1090 FStar_Absyn_Util.comp_to_comp_typ))
in (
# 1234 "FStar.Tc.Util.fst"
let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (
# 1235 "FStar.Tc.Util.fst"
let _45_1892 = (destruct_comp c)
in (match (_45_1892) with
| (t, wp, _45_1891) -> begin
(
# 1236 "FStar.Tc.Util.fst"
let vc = (let _137_1096 = (let _137_1094 = (let _137_1093 = (FStar_Absyn_Syntax.targ t)
in (let _137_1092 = (let _137_1091 = (FStar_Absyn_Syntax.targ wp)
in (_137_1091)::[])
in (_137_1093)::_137_1092))
in ((md.FStar_Absyn_Syntax.trivial), (_137_1094)))
in (let _137_1095 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _137_1096 (Some (FStar_Absyn_Syntax.ktype)) _137_1095)))
in (
# 1237 "FStar.Tc.Util.fst"
let g = (let _137_1097 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _137_1097))
in (let _137_1099 = (discharge g)
in (let _137_1098 = (FStar_Absyn_Syntax.mk_Comp c)
in ((_137_1099), (_137_1098))))))
end))))))
end)))

# 1238 "FStar.Tc.Util.fst"
let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (
# 1244 "FStar.Tc.Util.fst"
let short_bin_op_e = (fun f _45_14 -> (match (_45_14) with
| [] -> begin
None
end
| ((FStar_Util.Inr (fst), _45_1904))::[] -> begin
(let _137_1118 = (f fst)
in (FStar_All.pipe_right _137_1118 (fun _137_1117 -> Some (_137_1117))))
end
| _45_1908 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1249 "FStar.Tc.Util.fst"
let table = (
# 1250 "FStar.Tc.Util.fst"
let op_and_e = (fun e -> (let _137_1124 = (FStar_Absyn_Util.b2t e)
in ((_137_1124), (FStar_Absyn_Const.exp_false_bool))))
in (
# 1251 "FStar.Tc.Util.fst"
let op_or_e = (fun e -> (let _137_1128 = (let _137_1127 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _137_1127))
in ((_137_1128), (FStar_Absyn_Const.exp_true_bool))))
in (((FStar_Absyn_Const.op_And), ((short_bin_op_e op_and_e))))::(((FStar_Absyn_Const.op_Or), ((short_bin_op_e op_or_e))))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _45_1916) -> begin
(
# 1257 "FStar.Tc.Util.fst"
let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _45_1922 -> (match (_45_1922) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _137_1146 = (mk seen_args)
in Some (_137_1146))
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
| _45_1927 -> begin
None
end))))

# 1262 "FStar.Tc.Util.fst"
let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (
# 1269 "FStar.Tc.Util.fst"
let short_bin_op_t = (fun f _45_15 -> (match (_45_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| ((FStar_Util.Inl (fst), _45_1937))::[] -> begin
(f fst)
end
| _45_1941 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1274 "FStar.Tc.Util.fst"
let op_and_t = (fun t -> (let _137_1167 = (unlabel t)
in (FStar_All.pipe_right _137_1167 (fun _137_1166 -> FStar_Tc_Rel.NonTrivial (_137_1166)))))
in (
# 1275 "FStar.Tc.Util.fst"
let op_or_t = (fun t -> (let _137_1172 = (let _137_1170 = (unlabel t)
in (FStar_All.pipe_right _137_1170 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _137_1172 (fun _137_1171 -> FStar_Tc_Rel.NonTrivial (_137_1171)))))
in (
# 1276 "FStar.Tc.Util.fst"
let op_imp_t = (fun t -> (let _137_1176 = (unlabel t)
in (FStar_All.pipe_right _137_1176 (fun _137_1175 -> FStar_Tc_Rel.NonTrivial (_137_1175)))))
in (
# 1277 "FStar.Tc.Util.fst"
let short_op_ite = (fun _45_16 -> (match (_45_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| ((FStar_Util.Inl (guard), _45_1953))::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| (_then)::((FStar_Util.Inl (guard), _45_1959))::[] -> begin
(let _137_1180 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _137_1180 (fun _137_1179 -> FStar_Tc_Rel.NonTrivial (_137_1179))))
end
| _45_1964 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1282 "FStar.Tc.Util.fst"
let table = (((FStar_Absyn_Const.and_lid), ((short_bin_op_t op_and_t))))::(((FStar_Absyn_Const.or_lid), ((short_bin_op_t op_or_t))))::(((FStar_Absyn_Const.imp_lid), ((short_bin_op_t op_imp_t))))::(((FStar_Absyn_Const.ite_lid), (short_op_ite)))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _45_1972) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _45_1982; FStar_Absyn_Syntax.pos = _45_1980; FStar_Absyn_Syntax.fvs = _45_1978; FStar_Absyn_Syntax.uvs = _45_1976}) -> begin
(
# 1295 "FStar.Tc.Util.fst"
let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _45_1990 -> (match (_45_1990) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _137_1207 = (mk seen_args)
in Some (_137_1207))
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
| _45_1995 -> begin
FStar_Tc_Rel.Trivial
end))))))))

# 1300 "FStar.Tc.Util.fst"
let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (
# 1303 "FStar.Tc.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 1304 "FStar.Tc.Util.fst"
let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _137_1221 = (let _137_1220 = (let _137_1219 = (let _137_1218 = (let _137_1217 = (let _137_1216 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _137_1216))
in (_137_1217)::[])
in ((ens), (_137_1218)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_1219 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in ((x), (_137_1220)))
in (FStar_Absyn_Syntax.mk_Typ_refine _137_1221 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (
# 1306 "FStar.Tc.Util.fst"
let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
((None), ((FStar_Absyn_Util.comp_result comp)))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_45_2005) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (req), _45_2020))::((FStar_Util.Inl (ens), _45_2014))::_45_2010 -> begin
(let _137_1227 = (let _137_1224 = (norm req)
in Some (_137_1224))
in (let _137_1226 = (let _137_1225 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _137_1225))
in ((_137_1227), (_137_1226))))
end
| _45_2024 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1319 "FStar.Tc.Util.fst"
let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_45_2027) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp), _45_2042))::((FStar_Util.Inl (wlp), _45_2036))::_45_2032 -> begin
(
# 1325 "FStar.Tc.Util.fst"
let _45_2054 = (match ((let _137_1229 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _137_1228 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in ((_137_1229), (_137_1228))))) with
| (Some (x), Some (y)) -> begin
((x), (y))
end
| _45_2051 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_45_2054) with
| (as_req, as_ens) -> begin
(
# 1328 "FStar.Tc.Util.fst"
let req = (let _137_1236 = (let _137_1235 = (let _137_1234 = (let _137_1231 = (FStar_All.pipe_left (fun _137_1230 -> Some (_137_1230)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ)), (_137_1231)))
in (let _137_1233 = (let _137_1232 = (FStar_Absyn_Syntax.targ wp)
in (_137_1232)::[])
in (_137_1234)::_137_1233))
in ((as_req), (_137_1235)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_1236 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (
# 1329 "FStar.Tc.Util.fst"
let ens = (let _137_1243 = (let _137_1242 = (let _137_1241 = (let _137_1238 = (FStar_All.pipe_left (fun _137_1237 -> Some (_137_1237)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ)), (_137_1238)))
in (let _137_1240 = (let _137_1239 = (FStar_Absyn_Syntax.targ wlp)
in (_137_1239)::[])
in (_137_1241)::_137_1240))
in ((as_ens), (_137_1242)))
in (FStar_Absyn_Syntax.mk_Typ_app _137_1243 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _137_1247 = (let _137_1244 = (norm req)
in Some (_137_1244))
in (let _137_1246 = (let _137_1245 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _137_1245))
in ((_137_1247), (_137_1246))))))
end))
end
| _45_2058 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




