
open Prims

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)


let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))


let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _134_10 = (FStar_Tc_Env.get_range env)
in (let _134_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _134_10 _134_9))))


let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))


let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))


let syn' = (fun env k -> (let _134_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _134_29 k)))


let is_xvar_free : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun x t -> (

let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) f.FStar_Absyn_Syntax.fxvs)))


let is_tvar_free : FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun a t -> (

let f = (FStar_Absyn_Util.freevars_typ t)
in (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun) f.FStar_Absyn_Syntax.ftvs)))


let check_and_ascribe : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Tc_Rel.guard_t) = (fun env e t1 t2 -> (

let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (

let check = (fun env t1 t2 -> if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _134_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _134_52 -> Some (_134_52)) _134_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _134_57 = (let _134_56 = (let _134_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _134_54 = (FStar_Tc_Env.get_range env)
in (_134_55, _134_54)))
in FStar_Absyn_Syntax.Error (_134_56))
in (Prims.raise _134_57))
end
| Some (g) -> begin
(e, g)
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _134_61 = (let _134_60 = (let _134_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _134_58 = (FStar_Tc_Env.get_range env)
in (_134_59, _134_58)))
in FStar_Absyn_Syntax.Error (_134_60))
in (Prims.raise _134_61))
end
| Some (g) -> begin
(

let _45_53 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _134_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _134_62))
end else begin
()
end
in (

let e = (FStar_Absyn_Util.compress_exp e)
in (

let e = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(FStar_Absyn_Syntax.mk_Exp_bvar (FStar_Absyn_Util.bvd_to_bvar_s x.FStar_Absyn_Syntax.v t2) (Some (t2)) e.FStar_Absyn_Syntax.pos)
end
| _45_59 -> begin
(

let _45_60 = e
in (let _134_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _45_60.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _134_63; FStar_Absyn_Syntax.pos = _45_60.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _45_60.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _45_60.FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end)))


let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)


let as_uvar_e = (fun _45_1 -> (match (_45_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _45_75); FStar_Absyn_Syntax.tk = _45_72; FStar_Absyn_Syntax.pos = _45_70; FStar_Absyn_Syntax.fvs = _45_68; FStar_Absyn_Syntax.uvs = _45_66} -> begin
uv
end
| _45_80 -> begin
(FStar_All.failwith "Impossible")
end))


let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _45_92); FStar_Absyn_Syntax.tk = _45_89; FStar_Absyn_Syntax.pos = _45_87; FStar_Absyn_Syntax.fvs = _45_85; FStar_Absyn_Syntax.uvs = _45_83} -> begin
uv
end
| _45_97 -> begin
(FStar_All.failwith "Impossible")
end))


let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _134_73 = (let _134_72 = (FStar_Tc_Env.get_range env)
in (let _134_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _134_72 _134_71)))
in (FStar_All.pipe_right _134_73 Prims.fst)))


let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _134_80 = (let _134_79 = (FStar_Tc_Env.get_range env)
in (let _134_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _134_79 _134_78 k)))
in (FStar_All.pipe_right _134_80 Prims.fst)))


let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _134_87 = (let _134_86 = (FStar_Tc_Env.get_range env)
in (let _134_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _134_86 _134_85 t)))
in (FStar_All.pipe_right _134_87 Prims.fst)))


let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (

let _45_107 = (let _134_93 = (FStar_Tc_Env.get_range env)
in (let _134_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _134_93 _134_92 k)))
in (match (_45_107) with
| (t, u) -> begin
(let _134_95 = (let _134_94 = (as_uvar_t u)
in (_134_94, u.FStar_Absyn_Syntax.pos))
in (t, _134_95))
end)))


let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (

let _45_112 = (let _134_101 = (FStar_Tc_Env.get_range env)
in (let _134_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _134_101 _134_100 t)))
in (match (_45_112) with
| (e, u) -> begin
(let _134_103 = (let _134_102 = (as_uvar_e u)
in (_134_102, u.FStar_Absyn_Syntax.pos))
in (e, _134_103))
end)))


let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _134_106 = (let _134_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _134_105))
in (FStar_All.failwith _134_106))
end
| Some (tk) -> begin
tk
end))


let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _45_2 -> (match (_45_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _134_111 = (let _134_110 = (force_tk t)
in FStar_Util.Inl (_134_110))
in (_134_111, imp))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _134_113 = (let _134_112 = (force_tk v)
in FStar_Util.Inr (_134_112))
in (_134_113, imp))
end)))))


let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _45_3 -> (match (_45_3) with
| Some (FStar_Absyn_Syntax.Implicit (_45_129)) -> begin
true
end
| _45_133 -> begin
false
end))


let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (

let ktop = (let _134_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _134_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (

let r = (FStar_Tc_Env.get_range env)
in (

let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(

let imp_follows = (match (args) with
| (_45_149, qual)::_45_147 -> begin
(is_implicit qual)
end
| _45_154 -> begin
false
end)
in (

let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| b::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(

let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _134_137 = (let _134_134 = (let _134_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _134_133))
in (FStar_All.pipe_right _134_134 Prims.fst))
in (FStar_All.pipe_right _134_137 (fun x -> (let _134_136 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (x), _134_136)))))
end
| FStar_Util.Inr (x) -> begin
(let _134_142 = (let _134_139 = (let _134_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _134_138))
in (FStar_All.pipe_right _134_139 Prims.fst))
in (FStar_All.pipe_right _134_142 (fun x -> (let _134_141 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (x), _134_141)))))
end)
in (

let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _134_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_134_143)::subst)
end
in (

let _45_173 = (mk_implicits vars subst brest)
in (match (_45_173) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end else begin
(let _134_144 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _134_144))
end
end
| _45_175 -> begin
(let _134_145 = (FStar_Absyn_Util.subst_binders subst bs)
in ([], _134_145))
end))
in if imp_follows then begin
([], bs, k')
end else begin
(

let _45_178 = (let _134_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _134_146 [] bs))
in (match (_45_178) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_45_180, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_45_185) -> begin
(

let fvs = (FStar_Absyn_Util.freevars_kind k)
in (

let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (

let kres = (let _134_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _134_147 Prims.fst))
in (

let bs = (let _134_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _134_148))
in (

let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (

let _45_192 = (let _134_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _134_149))
in ([], bs, kres)))))))
end
| _45_195 -> begin
(let _134_152 = (let _134_151 = (let _134_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_134_150, r))
in FStar_Absyn_Syntax.Error (_134_151))
in (Prims.raise _134_152))
end))
in (aux ktop)))))


let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _45_4 -> (match (_45_4) with
| Some (FStar_Absyn_Syntax.Implicit (_45_198)) -> begin
true
end
| _45_202 -> begin
false
end))


let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (

let pvar_eq = (fun x y -> (match ((x, y)) with
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

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _45_254) -> begin
(

let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (

let _45_260 = (let _134_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p _134_174 t))
in (match (_45_260) with
| (e, u) -> begin
(

let p = (

let _45_261 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term ((x, e)); FStar_Absyn_Syntax.sort = _45_261.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_261.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inr (e), p))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _45_266) -> begin
(

let k = (new_kvar env)
in (

let _45_272 = (let _134_175 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _134_175 k))
in (match (_45_272) with
| (t, u) -> begin
(

let p = (

let _45_273 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); FStar_Absyn_Syntax.sort = _45_273.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_273.FStar_Absyn_Syntax.p})
in ([], [], [], env, FStar_Util.Inl (t), p))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(

let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in ([], [], [], env, FStar_Util.Inr (e), p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(

let w = (let _134_177 = (let _134_176 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _134_176))
in FStar_Tc_Env.Binding_var (_134_177))
in (

let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(

let b = (let _134_179 = (let _134_178 = (new_tvar env FStar_Absyn_Syntax.ktype)
in (x.FStar_Absyn_Syntax.v, _134_178))
in FStar_Tc_Env.Binding_var (_134_179))
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inr (e), p))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(

let w = (let _134_181 = (let _134_180 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _134_180))
in FStar_Tc_Env.Binding_typ (_134_181))
in (

let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (

let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(

let b = (let _134_183 = (let _134_182 = (new_kvar env)
in (a.FStar_Absyn_Syntax.v, _134_182))
in FStar_Tc_Env.Binding_typ (_134_183))
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (

let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, FStar_Util.Inl (t), p))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let _45_332 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _45_310 _45_313 -> (match ((_45_310, _45_313)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _45_320 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_45_320) with
| (b', a', w', env, te, pat) -> begin
(

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
in (match (_45_332) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _134_191 = (let _134_190 = (let _134_189 = (let _134_188 = (let _134_187 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _134_186 = (FStar_All.pipe_right args FStar_List.rev)
in (_134_187, _134_186)))
in (FStar_Absyn_Syntax.mk_Exp_app' _134_188 None p.FStar_Absyn_Syntax.p))
in (_134_189, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_134_190))
in (FStar_Absyn_Syntax.mk_Exp_meta _134_191))
in (let _134_194 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _134_193 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _134_192 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_134_194, _134_193, _134_192, env, FStar_Util.Inr (e), (

let _45_334 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev pats))); FStar_Absyn_Syntax.sort = _45_334.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_334.FStar_Absyn_Syntax.p}))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_45_337) -> begin
(FStar_All.failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let pats = (FStar_List.map (fun _45_349 -> (match (_45_349) with
| (p, imp) -> begin
(let _134_200 = (elaborate_pat env p)
in (_134_200, imp))
end)) pats)
in (

let t = (FStar_Tc_Env.lookup_datacon env fv.FStar_Absyn_Syntax.v)
in (

let pats = (match ((FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _45_355 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end)
end
| Some (f, _45_358) -> begin
(

let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _45_371::_45_369) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))))
end
| (_45_377::_45_375, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(

let a = (let _134_206 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _134_206 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _134_208 = (let _134_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _134_207))
in (_134_208, (as_imp imp)))
end else begin
(let _134_210 = (let _134_209 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _134_209))
in (_134_210, (as_imp imp)))
end)
end
| (FStar_Util.Inr (_45_388), Some (FStar_Absyn_Syntax.Implicit (dot))) -> begin
(

let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in if (allow_implicits && dot) then begin
(let _134_215 = (let _134_214 = (let _134_212 = (let _134_211 = (FStar_Absyn_Util.bvar_to_exp a)
in (a, _134_211))
in FStar_Absyn_Syntax.Pat_dot_term (_134_212))
in (let _134_213 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _134_214 None _134_213)))
in (_134_215, true))
end else begin
(let _134_217 = (let _134_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _134_216))
in (_134_217, true))
end)
end
| _45_396 -> begin
(let _134_221 = (let _134_220 = (let _134_219 = (let _134_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _134_218))
in (_134_219, (FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_134_220))
in (Prims.raise _134_221))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.FStar_Absyn_Syntax.v)) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _134_222 = (aux formals' pats')
in ((p, (as_imp imp)))::_134_222)
end
| ((FStar_Util.Inl (_45_424), imp), FStar_Absyn_Syntax.Pat_dot_typ (_45_429)) when allow_implicits -> begin
(let _134_223 = (aux formals' pats')
in ((p, (as_imp imp)))::_134_223)
end
| ((FStar_Util.Inl (_45_433), imp), _45_438) -> begin
(

let a = (let _134_224 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _134_224 FStar_Absyn_Syntax.kun))
in (

let p1 = if allow_implicits then begin
(let _134_225 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((a, FStar_Absyn_Syntax.tun))) None _134_225))
end else begin
(let _134_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _134_226))
end
in (

let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_45_443) -> begin
pats'
end
| _45_446 -> begin
pats
end)
in (let _134_227 = (aux formals' pats')
in ((p1, (as_imp imp)))::_134_227))))
end
| ((FStar_Util.Inr (_45_449), Some (FStar_Absyn_Syntax.Implicit (false))), _45_456) when p_imp -> begin
(let _134_228 = (aux formals' pats')
in ((p, true))::_134_228)
end
| ((FStar_Util.Inr (_45_459), Some (FStar_Absyn_Syntax.Implicit (dot))), _45_466) -> begin
(

let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let p = if (allow_implicits && dot) then begin
(let _134_232 = (let _134_230 = (let _134_229 = (FStar_Absyn_Util.bvar_to_exp a)
in (a, _134_229))
in FStar_Absyn_Syntax.Pat_dot_term (_134_230))
in (let _134_231 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _134_232 None _134_231)))
end else begin
(let _134_233 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _134_233))
end
in (let _134_234 = (aux formals' pats)
in ((p, true))::_134_234)))
end
| ((FStar_Util.Inr (_45_471), imp), _45_476) -> begin
(let _134_235 = (aux formals' pats')
in ((p, (as_imp imp)))::_134_235)
end)
end))
in (aux f pats))
end)
in (

let _45_479 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); FStar_Absyn_Syntax.sort = _45_479.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_479.FStar_Absyn_Syntax.p}))))
end
| _45_482 -> begin
p
end))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _45_494 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_45_494) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _45_497)) -> begin
(let _134_244 = (let _134_243 = (let _134_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in (_134_242, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_134_243))
in (Prims.raise _134_244))
end
| Some (FStar_Tc_Env.Binding_typ (x, _45_503)) -> begin
(let _134_247 = (let _134_246 = (let _134_245 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in (_134_245, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_134_246))
in (Prims.raise _134_247))
end
| _45_508 -> begin
(b, a, w, arg, p)
end)
end))))
in (

let as_arg = (fun _45_6 -> (match (_45_6) with
| FStar_Util.Inl (t) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Util.Inr (e) -> begin
(FStar_Absyn_Syntax.varg e)
end))
in (

let top_level_pat_as_args = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(

let _45_530 = (one_pat false env q)
in (match (_45_530) with
| (b, a, _45_527, te, q) -> begin
(

let _45_545 = (FStar_List.fold_right (fun p _45_535 -> (match (_45_535) with
| (w, args, pats) -> begin
(

let _45_541 = (one_pat false env p)
in (match (_45_541) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _134_261 = (let _134_260 = (let _134_259 = (let _134_257 = (vars_of_bindings a)
in (let _134_256 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _134_257 _134_256)))
in (let _134_258 = (FStar_Tc_Env.get_range env)
in (_134_259, _134_258)))
in FStar_Absyn_Syntax.Error (_134_260))
in (Prims.raise _134_261))
end else begin
(let _134_263 = (let _134_262 = (as_arg arg)
in (_134_262)::args)
in ((FStar_List.append w' w), _134_263, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_45_545) with
| (w, args, pats) -> begin
(let _134_265 = (let _134_264 = (as_arg te)
in (_134_264)::args)
in ((FStar_List.append b w), _134_265, (

let _45_546 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _45_546.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _45_546.FStar_Absyn_Syntax.p})))
end))
end))
end
| _45_549 -> begin
(

let _45_557 = (one_pat true env p)
in (match (_45_557) with
| (b, _45_552, _45_554, arg, p) -> begin
(let _134_267 = (let _134_266 = (as_arg arg)
in (_134_266)::[])
in (b, _134_267, p))
end))
end))
in (

let _45_561 = (top_level_pat_as_args env p)
in (match (_45_561) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map (fun _45_7 -> (match (_45_7) with
| (FStar_Util.Inl (_45_564), _45_567) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _45_572) -> begin
e
end))))
in (b, exps, p))
end))))))))))


let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (let _134_286 = (FStar_All.pipe_left (fun _134_285 -> Some (_134_285)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _134_286 p.FStar_Absyn_Syntax.p)))
in (

let e = (FStar_Absyn_Util.unmeta_exp e)
in (match ((p.FStar_Absyn_Syntax.v, e.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_constant (_45_588), FStar_Absyn_Syntax.Exp_constant (_45_591)) -> begin
(let _134_287 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _134_287))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(

let _45_599 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _134_290 = (let _134_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _134_288 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _134_289 _134_288)))
in (FStar_All.failwith _134_290))
end else begin
()
end
in (

let _45_601 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _134_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _134_291 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _134_292 _134_291)))
end else begin
()
end
in (

let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (

let x = (

let _45_604 = x
in {FStar_Absyn_Syntax.v = _45_604.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _45_604.FStar_Absyn_Syntax.p})
in (let _134_293 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _134_293))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(

let _45_612 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _134_296 = (let _134_295 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _134_294 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _134_295 _134_294)))
in (FStar_All.failwith _134_296))
end else begin
()
end
in (

let x = (

let _45_614 = x
in (let _134_297 = (force_tk e)
in {FStar_Absyn_Syntax.v = _45_614.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _134_297; FStar_Absyn_Syntax.p = _45_614.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _45_619), _45_623) -> begin
(

let x = (

let _45_625 = x
in (let _134_298 = (force_tk e)
in {FStar_Absyn_Syntax.v = _45_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _134_298; FStar_Absyn_Syntax.p = _45_625.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _45_635)) -> begin
(

let _45_639 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _134_299 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _134_299))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _45_656); FStar_Absyn_Syntax.tk = _45_653; FStar_Absyn_Syntax.pos = _45_651; FStar_Absyn_Syntax.fvs = _45_649; FStar_Absyn_Syntax.uvs = _45_647}, args)) -> begin
(

let _45_664 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _134_300 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _134_300))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _134_307 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons ((fv, q, (FStar_List.rev matched_pats)))) _134_307))
end
| (arg::args, (argpat, _45_680)::argpats) -> begin
(match ((arg, argpat.FStar_Absyn_Syntax.v)) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_45_687))), FStar_Absyn_Syntax.Pat_dot_typ (_45_692)) -> begin
(

let x = (let _134_308 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _134_308))
in (

let q = (let _134_310 = (FStar_All.pipe_left (fun _134_309 -> Some (_134_309)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _134_310 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_45_700))), FStar_Absyn_Syntax.Pat_dot_term (_45_705)) -> begin
(

let x = (let _134_311 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _134_311))
in (

let q = (let _134_313 = (FStar_All.pipe_left (fun _134_312 -> Some (_134_312)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _134_313 p.FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _45_715) -> begin
(

let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _45_723) -> begin
(

let pat = (let _134_314 = (aux argpat e)
in (_134_314, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _45_727 -> begin
(let _134_317 = (let _134_316 = (FStar_Absyn_Print.pat_to_string p)
in (let _134_315 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _134_316 _134_315)))
in (FStar_All.failwith _134_317))
end))
in (match_args [] args argpats))))
end
| _45_729 -> begin
(let _134_322 = (let _134_321 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _134_320 = (FStar_Absyn_Print.pat_to_string qq)
in (let _134_319 = (let _134_318 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _134_318 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _134_321 _134_320 _134_319))))
in (FStar_All.failwith _134_322))
end))))
and aux_t = (fun p t0 -> (

let pkg = (fun q k -> (let _134_330 = (FStar_All.pipe_left (fun _134_329 -> Some (_134_329)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _134_330 p.FStar_Absyn_Syntax.p)))
in (

let t = (FStar_Absyn_Util.compress_typ t0)
in (match ((p.FStar_Absyn_Syntax.v, t.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(

let _45_741 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _134_333 = (let _134_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _134_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _134_332 _134_331)))
in (FStar_All.failwith _134_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(

let _45_748 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _134_336 = (let _134_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _134_334 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _134_335 _134_334)))
in (FStar_All.failwith _134_336))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _45_752), _45_756) -> begin
(

let k0 = (force_tk t0)
in (

let a = (

let _45_759 = a
in {FStar_Absyn_Syntax.v = _45_759.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _45_759.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.FStar_Absyn_Syntax.sort)))
end
| _45_763 -> begin
(let _134_340 = (let _134_339 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _134_338 = (FStar_Absyn_Print.pat_to_string p)
in (let _134_337 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _134_339 _134_338 _134_337))))
in (FStar_All.failwith _134_340))
end))))
in (match ((p.FStar_Absyn_Syntax.v, exps)) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _45_767) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (let _134_342 = (FStar_All.pipe_left (fun _134_341 -> Some (_134_341)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _134_342 p.FStar_Absyn_Syntax.p)))
end
| (_45_771, e::[]) -> begin
(aux p e)
end
| _45_776 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_exp : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.exp) = (fun pat -> (

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

let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (

let pat_as_arg = (fun _45_790 -> (match (_45_790) with
| (p, i) -> begin
(

let _45_793 = (decorated_pattern_as_either p)
in (match (_45_793) with
| (vars, te) -> begin
(let _134_362 = (let _134_361 = (FStar_Absyn_Syntax.as_implicit i)
in (te, _134_361))
in (vars, _134_362))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_45_795) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _134_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _134_365))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _134_368 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((FStar_Util.Inr (x))::[], _134_368))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let _45_809 = (let _134_369 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _134_369 FStar_List.unzip))
in (match (_45_809) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _134_375 = (let _134_374 = (let _134_373 = (let _134_372 = (FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in (_134_372, args))
in (FStar_Absyn_Syntax.mk_Exp_app' _134_373))
in (FStar_All.pipe_right _134_374 pkg))
in (vars, _134_375)))
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
(let _134_377 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in ((FStar_Util.Inl (a))::[], _134_377))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
([], t)
end
| _45_833 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(

let _45_846 = (decorated_pattern_as_typ p)
in (match (_45_846) with
| (vars, t) -> begin
(vars, FStar_Util.Inl (t))
end))
end
| _45_848 -> begin
(

let _45_851 = (decorated_pattern_as_exp p)
in (match (_45_851) with
| (vars, e) -> begin
(vars, FStar_Util.Inr (e))
end))
end))


let mk_basic_dtuple_type : FStar_Tc_Env.env  ->  Prims.int  ->  FStar_Absyn_Syntax.typ = (fun env n -> (

let r = (FStar_Tc_Env.get_range env)
in (

let l = (FStar_Absyn_Util.mk_dtuple_lid n r)
in (

let k = (FStar_Tc_Env.lookup_typ_lid env l)
in (

let t = (FStar_Absyn_Util.ftv l k)
in (

let vars = (FStar_Tc_Env.binders env)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _45_867; FStar_Absyn_Syntax.pos = _45_865; FStar_Absyn_Syntax.fvs = _45_863; FStar_Absyn_Syntax.uvs = _45_861}) -> begin
(

let _45_897 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _45_874 _45_878 -> (match ((_45_874, _45_878)) with
| ((out, subst), (b, _45_877)) -> begin
(match (b) with
| FStar_Util.Inr (_45_880) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _134_385 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _134_385 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _134_388 = (let _134_387 = (let _134_386 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _134_386 Prims.fst))
in (bs, _134_387))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_388 (Some (k)) r))
end
| _45_891 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, arg)))::subst
in (let _134_390 = (let _134_389 = (FStar_Absyn_Syntax.targ arg)
in (_134_389)::out)
in (_134_390, subst)))))
end)
end)) ([], [])))
in (match (_45_897) with
| (args, _45_896) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (t, (FStar_List.rev args)) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _45_899 -> begin
(FStar_All.failwith "Impossible")
end)))))))


let extract_lb_annotation : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * Prims.bool) = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(

let r = (FStar_Tc_Env.get_range env)
in (

let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(

let k = (let _134_401 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _134_401 Prims.fst))
in ((

let _45_910 = a
in {FStar_Absyn_Syntax.v = _45_910.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _45_910.FStar_Absyn_Syntax.p}), false))
end
| _45_913 -> begin
(a, true)
end))
in (

let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(

let t = (let _134_406 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _134_406 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _45_922) -> begin
(x, false)
end
| _45_925 -> begin
(FStar_All.failwith "impos")
end))
end
| _45_927 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _45_931) -> begin
(x, true)
end
| _45_934 -> begin
(FStar_All.failwith "impos")
end)
end))
in (

let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _45_940)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _45_947) -> begin
(e, t, true)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let _45_976 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _45_957 b -> (match (_45_957) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(

let _45_963 = (mk_t_binder scope a)
in (match (_45_963) with
| (tb, c) -> begin
(

let b = (FStar_Util.Inl (tb), (Prims.snd b))
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _45_971 = (mk_v_binder scope x)
in (match (_45_971) with
| (vb, c) -> begin
(

let b = (FStar_Util.Inr (vb), (Prims.snd b))
in (scope, (FStar_List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_45_976) with
| (scope, bs, check) -> begin
(

let _45_980 = (aux scope body)
in (match (_45_980) with
| (body, res, check_res) -> begin
(

let c = (FStar_Absyn_Util.ml_comp res r)
in (

let t = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (

let _45_983 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _134_414 = (FStar_Range.string_of_range r)
in (let _134_413 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _134_414 _134_413)))
end else begin
()
end
in (

let e = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _45_987 -> begin
(let _134_416 = (let _134_415 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _134_415 Prims.fst))
in (e, _134_416, false))
end))
in (let _134_417 = (FStar_Tc_Env.t_binders env)
in (aux _134_417 e))))))
end
| _45_989 -> begin
(e, t, false)
end))


let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (

let _45_1006 = (match (c.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _45_999)::(FStar_Util.Inl (wlp), _45_994)::[] -> begin
(wp, wlp)
end
| _45_1003 -> begin
(let _134_422 = (let _134_421 = (let _134_420 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _134_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _134_421))
in (FStar_All.failwith _134_422))
end)
in (match (_45_1006) with
| (wp, wlp) -> begin
(c.FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))


let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (

let _45_1014 = (destruct_comp c)
in (match (_45_1014) with
| (_45_1011, wp, wlp) -> begin
(let _134_444 = (let _134_443 = (let _134_439 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _134_439))
in (let _134_442 = (let _134_441 = (let _134_440 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _134_440))
in (_134_441)::[])
in (_134_443)::_134_442))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _134_444; FStar_Absyn_Syntax.flags = []})
end)))


let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
in (fun env l -> (

let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_45_1022, c) -> begin
(

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

let _45_1036 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _45_1047 = (let _134_458 = (norm_eff_name env l1)
in (let _134_457 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _134_458 _134_457)))
in (match (_45_1047) with
| (m, _45_1044, _45_1046) -> begin
m
end)))


let join_lcomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lident = (fun env c1 c2 -> if ((FStar_Ident.lid_equals c1.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) && (FStar_Ident.lid_equals c2.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid)) then begin
FStar_Absyn_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Absyn_Syntax.eff_name c2.FStar_Absyn_Syntax.eff_name)
end)


let lift_and_destruct : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  ((FStar_Absyn_Syntax.eff_decl * FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ)) = (fun env c1 c2 -> (

let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (

let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (

let _45_1059 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_45_1059) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_Tc_Env.get_effect_decl env m)
in (

let _45_1065 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_45_1065) with
| (a, kwp) -> begin
(let _134_472 = (destruct_comp m1)
in (let _134_471 = (destruct_comp m2)
in ((md, a, kwp), _134_472, _134_471)))
end)))))
end)))))


let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))


let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun md result wp wlp flags -> (let _134_495 = (let _134_494 = (let _134_493 = (FStar_Absyn_Syntax.targ wp)
in (let _134_492 = (let _134_491 = (FStar_Absyn_Syntax.targ wlp)
in (_134_491)::[])
in (_134_493)::_134_492))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _134_494; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _134_495)))


let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (

let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _45_1079 -> (match (()) with
| () -> begin
c0
end))}))


let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (

let _45_1082 = lc
in (let _134_505 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _45_1082.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _134_505; FStar_Absyn_Syntax.cflags = _45_1082.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _45_1084 -> (match (()) with
| () -> begin
(let _134_504 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _134_504))
end))})))


let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _134_508 = (FStar_Absyn_Util.compress_typ t)
in _134_508.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_45_1087) -> begin
true
end
| _45_1090 -> begin
false
end))


let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp = (fun env t v -> (

let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(

let _45_1099 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_45_1099) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (

let wp = (let _134_520 = (let _134_519 = (let _134_518 = (let _134_517 = (FStar_Absyn_Syntax.targ t)
in (let _134_516 = (let _134_515 = (FStar_Absyn_Syntax.varg v)
in (_134_515)::[])
in (_134_517)::_134_516))
in (m.FStar_Absyn_Syntax.ret, _134_518))
in (FStar_Absyn_Syntax.mk_Typ_app _134_519 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _134_520))
in (

let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (

let _45_1104 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _134_523 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _134_522 = (FStar_Absyn_Print.exp_to_string v)
in (let _134_521 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _134_523 _134_522 _134_521))))
end else begin
()
end
in c)))


let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _45_1111 -> (match (_45_1111) with
| (b, lc2) -> begin
(

let _45_1122 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(

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
in (let _134_533 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _134_532 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _134_533 bstr _134_532))))
end else begin
()
end
in (

let bind_it = (fun _45_1125 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (

let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (

let try_simplify = (fun _45_1129 -> (match (()) with
| () -> begin
(

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
in (match ((e1opt, b)) with
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _45_1147))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _134_541 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr ((x, e)))::[]) c2)
in (FStar_All.pipe_left (fun _134_540 -> Some (_134_540)) _134_541))
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

let _45_1171 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _134_545 = (match (b) with
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
in (let _134_544 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _134_543 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _134_542 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _134_545 _134_544 _134_543 _134_542)))))
end else begin
()
end
in c)
end
| None -> begin
(

let _45_1186 = (lift_and_destruct env c1 c2)
in (match (_45_1186) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _134_546 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_134_546)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _134_547 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_134_547)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _134_548 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_134_548)::[])
end
| _45_1199 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (

let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos))
in (

let wp_args = (let _134_563 = (FStar_Absyn_Syntax.targ t1)
in (let _134_562 = (let _134_561 = (FStar_Absyn_Syntax.targ t2)
in (let _134_560 = (let _134_559 = (FStar_Absyn_Syntax.targ wp1)
in (let _134_558 = (let _134_557 = (FStar_Absyn_Syntax.targ wlp1)
in (let _134_556 = (let _134_555 = (let _134_551 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _134_551))
in (let _134_554 = (let _134_553 = (let _134_552 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _134_552))
in (_134_553)::[])
in (_134_555)::_134_554))
in (_134_557)::_134_556))
in (_134_559)::_134_558))
in (_134_561)::_134_560))
in (_134_563)::_134_562))
in (

let wlp_args = (let _134_571 = (FStar_Absyn_Syntax.targ t1)
in (let _134_570 = (let _134_569 = (FStar_Absyn_Syntax.targ t2)
in (let _134_568 = (let _134_567 = (FStar_Absyn_Syntax.targ wlp1)
in (let _134_566 = (let _134_565 = (let _134_564 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _134_564))
in (_134_565)::[])
in (_134_567)::_134_566))
in (_134_569)::_134_568))
in (_134_571)::_134_570))
in (

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wp, wp_args) None t2.FStar_Absyn_Syntax.pos)
in (

let wlp = (FStar_Absyn_Syntax.mk_Typ_app (md.FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.FStar_Absyn_Syntax.pos)
in (

let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _134_572 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _134_572; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))


let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env t mk_wp mk_wlp f -> (

let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (

let _45_1217 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_45_1217) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (

let wp = (let _134_587 = (let _134_586 = (let _134_585 = (FStar_Absyn_Syntax.targ t)
in (let _134_584 = (let _134_583 = (FStar_Absyn_Syntax.targ f)
in (_134_583)::[])
in (_134_585)::_134_584))
in (mk_wp, _134_586))
in (FStar_Absyn_Syntax.mk_Typ_app _134_587 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _134_592 = (let _134_591 = (let _134_590 = (FStar_Absyn_Syntax.targ t)
in (let _134_589 = (let _134_588 = (FStar_Absyn_Syntax.targ f)
in (_134_588)::[])
in (_134_590)::_134_589))
in (mk_wlp, _134_591))
in (FStar_Absyn_Syntax.mk_Typ_app _134_592 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))


let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.FStar_Absyn_Syntax.pos)))))


let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (

let refresh = (fun _45_1226 -> (match (()) with
| () -> begin
(

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

let _45_1233 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _134_604 = (let _134_603 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _134_603))
in (FStar_Util.print1 "Refreshing label at %s\n" _134_604))
end else begin
()
end
in (

let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _45_1236 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _134_607 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _134_606 = (let _134_605 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _134_605))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _134_607 _134_606)))
end else begin
()
end
in (

let _45_1241 = (destruct_comp c')
in (match (_45_1241) with
| (t, wp, wlp) -> begin
(

let wp = (let _134_610 = (let _134_609 = (let _134_608 = (FStar_Tc_Env.get_range env)
in (wp, Some (b), _134_608))
in FStar_Absyn_Syntax.Meta_refresh_label (_134_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _134_610))
in (

let wlp = (let _134_613 = (let _134_612 = (let _134_611 = (FStar_Tc_Env.get_range env)
in (wlp, Some (b), _134_611))
in FStar_Absyn_Syntax.Meta_refresh_label (_134_612))
in (FStar_Absyn_Syntax.mk_Typ_meta _134_613))
in (let _134_618 = (

let _45_1244 = c'
in (let _134_617 = (let _134_616 = (FStar_Absyn_Syntax.targ wp)
in (let _134_615 = (let _134_614 = (FStar_Absyn_Syntax.targ wlp)
in (_134_614)::[])
in (_134_616)::_134_615))
in {FStar_Absyn_Syntax.effect_name = _45_1244.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _45_1244.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _134_617; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _134_618))))
end)))))
end)
end)
end))
in (

let _45_1246 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1246.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1246.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _45_1246.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))


let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _134_642 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _134_642)) then begin
f
end else begin
(let _134_643 = (reason ())
in (label _134_643 r f))
end
end))


let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _134_650 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_134_650))
end))


let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(

let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _45_1273 -> begin
g2
end))


let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _45_1278 -> (match (()) with
| () -> begin
(

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

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _45_1287 = (destruct_comp c)
in (match (_45_1287) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (let _134_669 = (let _134_668 = (let _134_667 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_666 = (let _134_665 = (FStar_Absyn_Syntax.targ f)
in (let _134_664 = (let _134_663 = (FStar_Absyn_Syntax.targ wp)
in (_134_663)::[])
in (_134_665)::_134_664))
in (_134_667)::_134_666))
in (md.FStar_Absyn_Syntax.assume_p, _134_668))
in (FStar_Absyn_Syntax.mk_Typ_app _134_669 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _134_676 = (let _134_675 = (let _134_674 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_673 = (let _134_672 = (FStar_Absyn_Syntax.targ f)
in (let _134_671 = (let _134_670 = (FStar_Absyn_Syntax.targ wlp)
in (_134_670)::[])
in (_134_672)::_134_671))
in (_134_674)::_134_673))
in (md.FStar_Absyn_Syntax.assume_p, _134_675))
in (FStar_Absyn_Syntax.mk_Typ_app _134_676 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (

let _45_1291 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1291.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1291.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _45_1291.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(

let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _45_8 -> (match (_45_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _45_1302 -> begin
[]
end))))
in (

let strengthen = (fun _45_1305 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let g0 = (FStar_Tc_Rel.simplify_guard env g0)
in (match ((FStar_Tc_Rel.guard_form g0)) with
| FStar_Tc_Rel.Trivial -> begin
c
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(

let c = if (((FStar_Absyn_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Absyn_Util.comp_result c))))) && (not ((FStar_Absyn_Util.is_partial_return c)))) then begin
(

let x = (FStar_Absyn_Util.gen_bvar (FStar_Absyn_Util.comp_result c))
in (

let xret = (let _134_698 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _134_698))
in (

let xbinding = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (

let lc = (let _134_701 = (lcomp_of_comp c)
in (let _134_700 = (let _134_699 = (lcomp_of_comp xret)
in (Some (xbinding), _134_699))
in (bind env (Some (e)) _134_701 _134_700)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _45_1320 = (destruct_comp c)
in (match (_45_1320) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (let _134_710 = (let _134_709 = (let _134_708 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_707 = (let _134_706 = (let _134_703 = (let _134_702 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _134_702 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _134_703))
in (let _134_705 = (let _134_704 = (FStar_Absyn_Syntax.targ wp)
in (_134_704)::[])
in (_134_706)::_134_705))
in (_134_708)::_134_707))
in (md.FStar_Absyn_Syntax.assert_p, _134_709))
in (FStar_Absyn_Syntax.mk_Typ_app _134_710 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _134_717 = (let _134_716 = (let _134_715 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_714 = (let _134_713 = (FStar_Absyn_Syntax.targ f)
in (let _134_712 = (let _134_711 = (FStar_Absyn_Syntax.targ wlp)
in (_134_711)::[])
in (_134_713)::_134_712))
in (_134_715)::_134_714))
in (md.FStar_Absyn_Syntax.assume_p, _134_716))
in (FStar_Absyn_Syntax.mk_Typ_app _134_717 None wlp.FStar_Absyn_Syntax.pos))
in (

let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _134_721 = (

let _45_1325 = lc
in (let _134_720 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _134_719 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _134_718 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _134_718))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _134_720; FStar_Absyn_Syntax.res_typ = _45_1325.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _134_719; FStar_Absyn_Syntax.comp = strengthen})))
in (_134_721, (

let _45_1327 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _45_1327.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _45_1327.FStar_Tc_Rel.implicits})))))
end)


let add_equality_to_post_condition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (

let x = (FStar_Absyn_Util.gen_bvar res_t)
in (

let y = (FStar_Absyn_Util.gen_bvar res_t)
in (

let _45_1337 = (let _134_729 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _134_728 = (FStar_Absyn_Util.bvar_to_exp y)
in (_134_729, _134_728)))
in (match (_45_1337) with
| (xexp, yexp) -> begin
(

let yret = (let _134_734 = (let _134_733 = (let _134_732 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_731 = (let _134_730 = (FStar_Absyn_Syntax.varg yexp)
in (_134_730)::[])
in (_134_732)::_134_731))
in (md_pure.FStar_Absyn_Syntax.ret, _134_733))
in (FStar_Absyn_Syntax.mk_Typ_app _134_734 None res_t.FStar_Absyn_Syntax.pos))
in (

let x_eq_y_yret = (let _134_742 = (let _134_741 = (let _134_740 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_739 = (let _134_738 = (let _134_735 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _134_735))
in (let _134_737 = (let _134_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_134_736)::[])
in (_134_738)::_134_737))
in (_134_740)::_134_739))
in (md_pure.FStar_Absyn_Syntax.assume_p, _134_741))
in (FStar_Absyn_Syntax.mk_Typ_app _134_742 None res_t.FStar_Absyn_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (let _134_753 = (let _134_752 = (let _134_751 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_750 = (let _134_749 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_748 = (let _134_747 = (let _134_746 = (let _134_745 = (let _134_744 = (let _134_743 = (FStar_Absyn_Syntax.v_binder y)
in (_134_743)::[])
in (_134_744, x_eq_y_yret))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_745 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _134_746))
in (_134_747)::[])
in (_134_749)::_134_748))
in (_134_751)::_134_750))
in (md_pure.FStar_Absyn_Syntax.close_wp, _134_752))
in (FStar_Absyn_Syntax.mk_Typ_app _134_753 None res_t.FStar_Absyn_Syntax.pos))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (

let lc = (let _134_756 = (lcomp_of_comp comp)
in (let _134_755 = (let _134_754 = (lcomp_of_comp lc2)
in (Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))), _134_754))
in (bind env None _134_756 _134_755)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))


let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _45_1348 -> (match (()) with
| () -> begin
(

let _45_1364 = (let _134_768 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _134_767 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _134_768 _134_767)))
in (match (_45_1364) with
| ((md, _45_1351, _45_1353), (res_t, wp_then, wlp_then), (_45_1360, wp_else, wlp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _134_788 = (let _134_786 = (let _134_785 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_784 = (let _134_783 = (FStar_Absyn_Syntax.targ g)
in (let _134_782 = (let _134_781 = (FStar_Absyn_Syntax.targ wp_t)
in (let _134_780 = (let _134_779 = (FStar_Absyn_Syntax.targ wp_e)
in (_134_779)::[])
in (_134_781)::_134_780))
in (_134_783)::_134_782))
in (_134_785)::_134_784))
in (md.FStar_Absyn_Syntax.if_then_else, _134_786))
in (let _134_787 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _134_788 None _134_787))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(

let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _134_795 = (let _134_794 = (let _134_793 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_792 = (let _134_791 = (FStar_Absyn_Syntax.targ wlp)
in (let _134_790 = (let _134_789 = (FStar_Absyn_Syntax.targ wp)
in (_134_789)::[])
in (_134_791)::_134_790))
in (_134_793)::_134_792))
in (md.FStar_Absyn_Syntax.ite_wp, _134_794))
in (FStar_Absyn_Syntax.mk_Typ_app _134_795 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _134_800 = (let _134_799 = (let _134_798 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_797 = (let _134_796 = (FStar_Absyn_Syntax.targ wlp)
in (_134_796)::[])
in (_134_798)::_134_797))
in (md.FStar_Absyn_Syntax.ite_wlp, _134_799))
in (FStar_Absyn_Syntax.mk_Typ_app _134_800 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _134_801 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _134_801; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))


let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| hd::tl -> begin
(FStar_List.fold_left (fun eff _45_1387 -> (match (_45_1387) with
| (_45_1385, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (

let bind_cases = (fun _45_1390 -> (match (()) with
| () -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _134_831 = (let _134_829 = (let _134_828 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_827 = (let _134_826 = (FStar_Absyn_Syntax.targ g)
in (let _134_825 = (let _134_824 = (FStar_Absyn_Syntax.targ wp_t)
in (let _134_823 = (let _134_822 = (FStar_Absyn_Syntax.targ wp_e)
in (_134_822)::[])
in (_134_824)::_134_823))
in (_134_826)::_134_825))
in (_134_828)::_134_827))
in (md.FStar_Absyn_Syntax.if_then_else, _134_829))
in (let _134_830 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _134_831 None _134_830))))
in (

let default_case = (

let post_k = (let _134_834 = (let _134_833 = (let _134_832 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_134_832)::[])
in (_134_833, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_834 res_t.FStar_Absyn_Syntax.pos))
in (

let kwp = (let _134_837 = (let _134_836 = (let _134_835 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_134_835)::[])
in (_134_836, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_837 res_t.FStar_Absyn_Syntax.pos))
in (

let post = (let _134_838 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _134_838 post_k))
in (

let wp = (let _134_845 = (let _134_844 = (let _134_839 = (FStar_Absyn_Syntax.t_binder post)
in (_134_839)::[])
in (let _134_843 = (let _134_842 = (let _134_840 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _134_840))
in (let _134_841 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _134_842 _134_841)))
in (_134_844, _134_843)))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_845 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _134_849 = (let _134_848 = (let _134_846 = (FStar_Absyn_Syntax.t_binder post)
in (_134_846)::[])
in (let _134_847 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_134_848, _134_847)))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_849 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (

let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (

let comp = (FStar_List.fold_right (fun _45_1406 celse -> (match (_45_1406) with
| (g, cthen) -> begin
(

let _45_1424 = (let _134_852 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _134_852 celse))
in (match (_45_1424) with
| ((md, _45_1410, _45_1412), (_45_1415, wp_then, wlp_then), (_45_1420, wp_else, wlp_else)) -> begin
(let _134_854 = (ifthenelse md res_t g wp_then wp_else)
in (let _134_853 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _134_854 _134_853 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(

let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (

let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (

let _45_1432 = (destruct_comp comp)
in (match (_45_1432) with
| (_45_1429, wp, wlp) -> begin
(

let wp = (let _134_861 = (let _134_860 = (let _134_859 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_858 = (let _134_857 = (FStar_Absyn_Syntax.targ wlp)
in (let _134_856 = (let _134_855 = (FStar_Absyn_Syntax.targ wp)
in (_134_855)::[])
in (_134_857)::_134_856))
in (_134_859)::_134_858))
in (md.FStar_Absyn_Syntax.ite_wp, _134_860))
in (FStar_Absyn_Syntax.mk_Typ_app _134_861 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _134_866 = (let _134_865 = (let _134_864 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_863 = (let _134_862 = (FStar_Absyn_Syntax.targ wlp)
in (_134_862)::[])
in (_134_864)::_134_863))
in (md.FStar_Absyn_Syntax.ite_wlp, _134_865))
in (FStar_Absyn_Syntax.mk_Typ_app _134_866 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))


let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (

let close = (fun _45_1439 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun md res_t bindings wp0 -> (FStar_List.fold_right (fun b wp -> (match (b) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(

let bs = (let _134_885 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_134_885)::[])
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _134_892 = (let _134_891 = (let _134_890 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_889 = (let _134_888 = (FStar_Absyn_Syntax.targ t)
in (let _134_887 = (let _134_886 = (FStar_Absyn_Syntax.targ wp)
in (_134_886)::[])
in (_134_888)::_134_887))
in (_134_890)::_134_889))
in (md.FStar_Absyn_Syntax.close_wp, _134_891))
in (FStar_Absyn_Syntax.mk_Typ_app _134_892 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let bs = (let _134_893 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_134_893)::[])
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.FStar_Absyn_Syntax.pos)
in (let _134_898 = (let _134_897 = (let _134_896 = (FStar_Absyn_Syntax.targ res_t)
in (let _134_895 = (let _134_894 = (FStar_Absyn_Syntax.targ wp)
in (_134_894)::[])
in (_134_896)::_134_895))
in (md.FStar_Absyn_Syntax.close_wp_t, _134_897))
in (FStar_Absyn_Syntax.mk_Typ_app _134_898 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_lid (l, t) -> begin
wp
end
| FStar_Tc_Env.Binding_sig (s) -> begin
(FStar_All.failwith "impos")
end)) bindings wp0))
in (

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _45_1470 = (destruct_comp c)
in (match (_45_1470) with
| (t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wp)
in (

let wlp = (close_wp md c.FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.FStar_Absyn_Syntax.result_typ wp wlp c.FStar_Absyn_Syntax.flags))))
end))))
end)
end))
in (

let _45_1474 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1474.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1474.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _45_1474.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _45_1480 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Absyn_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Absyn_Util.is_partial_return c) then begin
c
end else begin
(

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let t = c.FStar_Absyn_Syntax.result_typ
in (

let c = (FStar_Absyn_Syntax.mk_Comp c)
in (

let x = (FStar_Absyn_Util.new_bvd None)
in (

let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (

let ret = (let _134_907 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _134_907))
in (

let eq_ret = (let _134_909 = (let _134_908 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_134_908))
in (weaken_precondition env ret _134_909))
in (let _134_912 = (let _134_911 = (let _134_910 = (lcomp_of_comp c)
in (bind env None _134_910 (Some (FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_134_911.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _134_912 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
end
end)
end))
in (

let flags = if (((not ((FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Absyn_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.FStar_Absyn_Syntax.cflags
end else begin
lc.FStar_Absyn_Syntax.cflags
end
in (

let _45_1490 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1490.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _45_1490.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))


let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _134_924 = (let _134_923 = (let _134_922 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _134_921 = (FStar_Tc_Env.get_range env)
in (_134_922, _134_921)))
in FStar_Absyn_Syntax.Error (_134_923))
in (Prims.raise _134_924))
end
| Some (g) -> begin
(e, c', g)
end))


let maybe_instantiate_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.implicits) = (fun env t k -> (

let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(t, k, [])
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let rec aux = (fun subst _45_9 -> (match (_45_9) with
| (FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_45_1514)))::rest -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _45_1522 = (new_implicit_tvar env k)
in (match (_45_1522) with
| (t, u) -> begin
(

let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (

let _45_1528 = (aux subst rest)
in (match (_45_1528) with
| (args, bs, subst, us) -> begin
(let _134_938 = (let _134_937 = (let _134_936 = (FStar_All.pipe_left (fun _134_935 -> Some (_134_935)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _134_936))
in (_134_937)::args)
in (_134_938, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_45_1533)))::rest -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _45_1541 = (new_implicit_evar env t)
in (match (_45_1541) with
| (v, u) -> begin
(

let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (

let _45_1547 = (aux subst rest)
in (match (_45_1547) with
| (args, bs, subst, us) -> begin
(let _134_942 = (let _134_941 = (let _134_940 = (FStar_All.pipe_left (fun _134_939 -> Some (_134_939)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _134_940))
in (_134_941)::args)
in (_134_942, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (

let _45_1553 = (aux [] bs)
in (match (_45_1553) with
| (args, bs, subst, implicits) -> begin
(

let k = (FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.FStar_Absyn_Syntax.pos)
in (

let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _134_943 = (FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.FStar_Absyn_Syntax.pos)
in (_134_943, k, implicits))))
end)))
end
| _45_1557 -> begin
(t, k, [])
end)
end))


let maybe_instantiate : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.implicits) = (fun env e t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
(e, t, [])
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let rec aux = (fun subst _45_10 -> (match (_45_10) with
| (FStar_Util.Inl (a), _45_1573)::rest -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _45_1579 = (new_implicit_tvar env k)
in (match (_45_1579) with
| (t, u) -> begin
(

let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (

let _45_1585 = (aux subst rest)
in (match (_45_1585) with
| (args, bs, subst, us) -> begin
(let _134_957 = (let _134_956 = (let _134_955 = (FStar_All.pipe_left (fun _134_954 -> Some (_134_954)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _134_955))
in (_134_956)::args)
in (_134_957, bs, subst, (FStar_Util.Inl (u))::us))
end)))
end)))
end
| (FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_45_1590)))::rest -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _45_1598 = (new_implicit_evar env t)
in (match (_45_1598) with
| (v, u) -> begin
(

let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v)))::subst
in (

let _45_1604 = (aux subst rest)
in (match (_45_1604) with
| (args, bs, subst, us) -> begin
(let _134_961 = (let _134_960 = (let _134_959 = (FStar_All.pipe_left (fun _134_958 -> Some (_134_958)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (v), _134_959))
in (_134_960)::args)
in (_134_961, bs, subst, (FStar_Util.Inr (u))::us))
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (

let _45_1610 = (aux [] bs)
in (match (_45_1610) with
| (args, bs, subst, implicits) -> begin
(

let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _45_1617 -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(

let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _134_968 = (mk_exp_app e args (Some (t)))
in (_134_968, t, implicits)))
end else begin
(e, t, [])
end
end
| _45_1621 -> begin
(

let t = (let _134_969 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _134_969 (FStar_Absyn_Util.subst_typ subst)))
in (let _134_970 = (mk_exp_app e args (Some (t)))
in (_134_970, t, implicits)))
end))
end)))
end
| _45_1624 -> begin
(e, t, [])
end)
end))


let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _134_979 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in (_134_979, false))
end else begin
(let _134_980 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in (_134_980, true))
end
in (match (gopt) with
| (None, _45_1632) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(

let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(

let lc = (

let _45_1640 = lc
in {FStar_Absyn_Syntax.eff_name = _45_1640.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _45_1640.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _45_1640.FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(

let g = (

let _45_1645 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _45_1645.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _45_1645.FStar_Tc_Rel.implicits})
in (

let strengthen = (fun _45_1649 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let _45_1651 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _134_984 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _134_983 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _134_984 _134_983)))
end else begin
()
end
in (

let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _45_1656 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_45_1656) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (

let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (

let x = (FStar_Absyn_Util.new_bvd None)
in (

let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (

let wp = (let _134_989 = (let _134_988 = (let _134_987 = (FStar_Absyn_Syntax.targ t)
in (let _134_986 = (let _134_985 = (FStar_Absyn_Syntax.varg xexp)
in (_134_985)::[])
in (_134_987)::_134_986))
in (md.FStar_Absyn_Syntax.ret, _134_988))
in (FStar_Absyn_Syntax.mk_Typ_app _134_989 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (

let cret = (let _134_990 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _134_990))
in (

let guard = if apply_guard then begin
(let _134_993 = (let _134_992 = (let _134_991 = (FStar_Absyn_Syntax.varg xexp)
in (_134_991)::[])
in (f, _134_992))
in (FStar_Absyn_Syntax.mk_Typ_app _134_993 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (

let _45_1666 = (let _134_1001 = (FStar_All.pipe_left (fun _134_998 -> Some (_134_998)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _134_1000 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _134_999 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _134_1001 _134_1000 e cret _134_999))))
in (match (_45_1666) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let c = (let _134_1003 = (let _134_1002 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _134_1002))
in (bind env (Some (e)) _134_1003 (Some (FStar_Tc_Env.Binding_var ((x, lc.FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (

let c = (c.FStar_Absyn_Syntax.comp ())
in (

let _45_1669 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _134_1004 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _134_1004))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (

let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _45_11 -> (match (_45_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _45_1675 -> begin
[]
end))))
in (

let lc = (

let _45_1677 = lc
in (let _134_1006 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _134_1006; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if (((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + ((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k))) > 0) then begin
(

let ue = (let _134_1011 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _134_1011))
in (

let ut = (let _134_1012 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _134_1012))
in (

let uk = (let _134_1013 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _134_1013))
in (

let union = (FStar_String.concat "," (FStar_List.append (FStar_List.append ue ut) uk))
in (

let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (

let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (

let _45_1689 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (

let _45_1691 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (

let _45_1693 = (let _134_1015 = (let _134_1014 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _134_1014))
in (FStar_Tc_Errors.report r _134_1015))
in (

let _45_1695 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved)))))))))))
end else begin
()
end))


let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _134_1023 = (FStar_Util.for_all (fun _45_1703 -> (match (_45_1703) with
| (_45_1701, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _134_1023)) then begin
None
end else begin
(

let norm = (fun c -> (

let _45_1706 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _134_1026 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _134_1026))
end else begin
()
end
in (

let steps = (FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
in (

let c = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.norm_comp steps env c)
end else begin
(FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::[]) env c)
end
in (

let _45_1710 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _134_1027 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _134_1027))
end else begin
()
end
in c)))))
in (

let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _134_1030 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _134_1030 FStar_Util.set_elements)))
in (

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

let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _45_1735 -> (match (_45_1735) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _134_1035 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _134_1035)) then begin
([], e, c)
end else begin
(

let c = (norm c)
in (

let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (

let t = ct.FStar_Absyn_Syntax.result_typ
in (

let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in (

let uvs = (gen_uvars uvt.FStar_Absyn_Syntax.uvars_t)
in (

let _45_1751 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _134_1036 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _134_1036))) then begin
(

let _45_1747 = (destruct_comp ct)
in (match (_45_1747) with
| (_45_1743, wp, _45_1746) -> begin
(

let binder = (let _134_1037 = (FStar_Absyn_Syntax.null_v_binder t)
in (_134_1037)::[])
in (

let post = (let _134_1041 = (let _134_1038 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (binder, _134_1038))
in (let _134_1040 = (let _134_1039 = (FStar_Absyn_Syntax.mk_Kind_arrow (binder, FStar_Absyn_Syntax.ktype) t.FStar_Absyn_Syntax.pos)
in Some (_134_1039))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_1041 _134_1040 t.FStar_Absyn_Syntax.pos)))
in (

let vc = (let _134_1048 = (let _134_1047 = (let _134_1046 = (let _134_1045 = (let _134_1044 = (FStar_Absyn_Syntax.targ post)
in (_134_1044)::[])
in (wp, _134_1045))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1046))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _134_1047))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _134_1048))
in (let _134_1049 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _134_1049)))))
end))
end else begin
()
end
in (uvs, e, c)))))))
end)
end))))
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _45_1757 -> (match (_45_1757) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _45_1760 -> (match (_45_1760) with
| (u, k) -> begin
(

let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_45_1798) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _45_1801 -> begin
(

let a = (let _134_1054 = (let _134_1053 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _134_1052 -> Some (_134_1052)) _134_1053))
in (FStar_Absyn_Util.new_bvd _134_1054))
in (

let t = (let _134_1055 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _134_1055 k))
in (

let _45_1804 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _134_1057 = (FStar_All.pipe_left (fun _134_1056 -> Some (_134_1056)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (a), _134_1057)))
end))))
in (

let t = (match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.function_formals)) with
| Some (bs, cod) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.append tvars bs), cod) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(FStar_Absyn_Util.comp_result c)
end
| _45_1815 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (

let e = (match (tvars) with
| [] -> begin
e
end
| _45_1819 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _134_1058 = (FStar_Absyn_Syntax.mk_Total t)
in (e, _134_1058)))))
end))))
in Some (ecs)))))))
end)


let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (

let _45_1831 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _134_1067 = (let _134_1066 = (FStar_List.map (fun _45_1830 -> (match (_45_1830) with
| (lb, _45_1827, _45_1829) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _134_1066 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _134_1067))
end else begin
()
end
in (match ((let _134_1069 = (FStar_All.pipe_right lecs (FStar_List.map (fun _45_1837 -> (match (_45_1837) with
| (_45_1834, e, c) -> begin
(e, c)
end))))
in (gen verify env _134_1069))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _45_1846 _45_1849 -> (match ((_45_1846, _45_1849)) with
| ((l, _45_1843, _45_1845), (e, c)) -> begin
(

let _45_1850 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _134_1074 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _134_1073 = (FStar_Absyn_Print.lbname_to_string l)
in (let _134_1072 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _134_1074 _134_1073 _134_1072))))
end else begin
()
end
in (l, e, c))
end)) lecs ecs)
end)))


let check_unresolved_implicits : FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun g -> (

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
(Prims.raise (FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _45_1873 -> begin
()
end)))


let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _45_1879 = (FStar_Tc_Rel.try_discharge_guard env g)
in (

let _45_1881 = (check_unresolved_implicits g)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _134_1089 = (discharge g)
in (let _134_1088 = (lc.FStar_Absyn_Syntax.comp ())
in (_134_1089, _134_1088)))
end else begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (

let c = (let _134_1090 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _134_1090 FStar_Absyn_Util.comp_to_comp_typ))
in (

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let _45_1892 = (destruct_comp c)
in (match (_45_1892) with
| (t, wp, _45_1891) -> begin
(

let vc = (let _134_1096 = (let _134_1094 = (let _134_1093 = (FStar_Absyn_Syntax.targ t)
in (let _134_1092 = (let _134_1091 = (FStar_Absyn_Syntax.targ wp)
in (_134_1091)::[])
in (_134_1093)::_134_1092))
in (md.FStar_Absyn_Syntax.trivial, _134_1094))
in (let _134_1095 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _134_1096 (Some (FStar_Absyn_Syntax.ktype)) _134_1095)))
in (

let g = (let _134_1097 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _134_1097))
in (let _134_1099 = (discharge g)
in (let _134_1098 = (FStar_Absyn_Syntax.mk_Comp c)
in (_134_1099, _134_1098)))))
end))))))
end)))


let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (

let short_bin_op_e = (fun f _45_14 -> (match (_45_14) with
| [] -> begin
None
end
| (FStar_Util.Inr (fst), _45_1904)::[] -> begin
(let _134_1118 = (f fst)
in (FStar_All.pipe_right _134_1118 (fun _134_1117 -> Some (_134_1117))))
end
| _45_1908 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let table = (

let op_and_e = (fun e -> (let _134_1124 = (FStar_Absyn_Util.b2t e)
in (_134_1124, FStar_Absyn_Const.exp_false_bool)))
in (

let op_or_e = (fun e -> (let _134_1128 = (let _134_1127 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _134_1127))
in (_134_1128, FStar_Absyn_Const.exp_true_bool)))
in ((FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _45_1916) -> begin
(

let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _45_1922 -> (match (_45_1922) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _134_1146 = (mk seen_args)
in Some (_134_1146))
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


let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (

let short_bin_op_t = (fun f _45_15 -> (match (_45_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (fst), _45_1937)::[] -> begin
(f fst)
end
| _45_1941 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_t = (fun t -> (let _134_1167 = (unlabel t)
in (FStar_All.pipe_right _134_1167 (fun _134_1166 -> FStar_Tc_Rel.NonTrivial (_134_1166)))))
in (

let op_or_t = (fun t -> (let _134_1172 = (let _134_1170 = (unlabel t)
in (FStar_All.pipe_right _134_1170 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _134_1172 (fun _134_1171 -> FStar_Tc_Rel.NonTrivial (_134_1171)))))
in (

let op_imp_t = (fun t -> (let _134_1176 = (unlabel t)
in (FStar_All.pipe_right _134_1176 (fun _134_1175 -> FStar_Tc_Rel.NonTrivial (_134_1175)))))
in (

let short_op_ite = (fun _45_16 -> (match (_45_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| (FStar_Util.Inl (guard), _45_1953)::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(FStar_Util.Inl (guard), _45_1959)::[] -> begin
(let _134_1180 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _134_1180 (fun _134_1179 -> FStar_Tc_Rel.NonTrivial (_134_1179))))
end
| _45_1964 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = ((FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((FStar_Absyn_Const.ite_lid, short_op_ite))::[]
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

let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _45_1990 -> (match (_45_1990) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _134_1207 = (mk seen_args)
in Some (_134_1207))
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


let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _134_1221 = (let _134_1220 = (let _134_1219 = (let _134_1218 = (let _134_1217 = (let _134_1216 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _134_1216))
in (_134_1217)::[])
in (ens, _134_1218))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1219 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in (x, _134_1220))
in (FStar_Absyn_Syntax.mk_Typ_refine _134_1221 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (

let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Absyn_Util.comp_result comp))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_45_2005) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (req), _45_2020)::(FStar_Util.Inl (ens), _45_2014)::_45_2010 -> begin
(let _134_1227 = (let _134_1224 = (norm req)
in Some (_134_1224))
in (let _134_1226 = (let _134_1225 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _134_1225))
in (_134_1227, _134_1226)))
end
| _45_2024 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_45_2027) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp), _45_2042)::(FStar_Util.Inl (wlp), _45_2036)::_45_2032 -> begin
(

let _45_2054 = (match ((let _134_1229 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _134_1228 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in (_134_1229, _134_1228)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _45_2051 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_45_2054) with
| (as_req, as_ens) -> begin
(

let req = (let _134_1236 = (let _134_1235 = (let _134_1234 = (let _134_1231 = (FStar_All.pipe_left (fun _134_1230 -> Some (_134_1230)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _134_1231))
in (let _134_1233 = (let _134_1232 = (FStar_Absyn_Syntax.targ wp)
in (_134_1232)::[])
in (_134_1234)::_134_1233))
in (as_req, _134_1235))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1236 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (

let ens = (let _134_1243 = (let _134_1242 = (let _134_1241 = (let _134_1238 = (FStar_All.pipe_left (fun _134_1237 -> Some (_134_1237)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ), _134_1238))
in (let _134_1240 = (let _134_1239 = (FStar_Absyn_Syntax.targ wlp)
in (_134_1239)::[])
in (_134_1241)::_134_1240))
in (as_ens, _134_1242))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1243 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _134_1247 = (let _134_1244 = (norm req)
in Some (_134_1244))
in (let _134_1246 = (let _134_1245 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _134_1245))
in (_134_1247, _134_1246)))))
end))
end
| _45_2058 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




