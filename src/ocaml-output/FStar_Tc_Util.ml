
open Prims

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)


let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))


let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _145_10 = (FStar_Tc_Env.get_range env)
in (let _145_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Tc_Errors.report _145_10 _145_9))))


let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))


let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))


let syn' = (fun env k -> (let _145_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _145_29 k)))


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
(let _145_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _145_52 -> Some (_145_52)) _145_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _145_57 = (let _145_56 = (let _145_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _145_54 = (FStar_Tc_Env.get_range env)
in ((_145_55), (_145_54))))
in FStar_Absyn_Syntax.Error (_145_56))
in (Prims.raise _145_57))
end
| Some (g) -> begin
((e), (g))
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _145_61 = (let _145_60 = (let _145_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _145_58 = (FStar_Tc_Env.get_range env)
in ((_145_59), (_145_58))))
in FStar_Absyn_Syntax.Error (_145_60))
in (Prims.raise _145_61))
end
| Some (g) -> begin
(

let _47_53 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _145_62))
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
| _47_59 -> begin
(

let _47_60 = e
in (let _145_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _47_60.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _145_63; FStar_Absyn_Syntax.pos = _47_60.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _47_60.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _47_60.FStar_Absyn_Syntax.uvs}))
end)
in ((e), (g)))))
end)
end)))


let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_Options.full_context_dependency ()) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)


let as_uvar_e = (fun _47_1 -> (match (_47_1) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _47_75); FStar_Absyn_Syntax.tk = _47_72; FStar_Absyn_Syntax.pos = _47_70; FStar_Absyn_Syntax.fvs = _47_68; FStar_Absyn_Syntax.uvs = _47_66} -> begin
uv
end
| _47_80 -> begin
(FStar_All.failwith "Impossible")
end))


let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _47_92); FStar_Absyn_Syntax.tk = _47_89; FStar_Absyn_Syntax.pos = _47_87; FStar_Absyn_Syntax.fvs = _47_85; FStar_Absyn_Syntax.uvs = _47_83} -> begin
uv
end
| _47_97 -> begin
(FStar_All.failwith "Impossible")
end))


let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _145_73 = (let _145_72 = (FStar_Tc_Env.get_range env)
in (let _145_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _145_72 _145_71)))
in (FStar_All.pipe_right _145_73 Prims.fst)))


let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _145_80 = (let _145_79 = (FStar_Tc_Env.get_range env)
in (let _145_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _145_79 _145_78 k)))
in (FStar_All.pipe_right _145_80 Prims.fst)))


let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _145_87 = (let _145_86 = (FStar_Tc_Env.get_range env)
in (let _145_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _145_86 _145_85 t)))
in (FStar_All.pipe_right _145_87 Prims.fst)))


let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (

let _47_107 = (let _145_93 = (FStar_Tc_Env.get_range env)
in (let _145_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _145_93 _145_92 k)))
in (match (_47_107) with
| (t, u) -> begin
(let _145_95 = (let _145_94 = (as_uvar_t u)
in ((_145_94), (u.FStar_Absyn_Syntax.pos)))
in ((t), (_145_95)))
end)))


let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (

let _47_112 = (let _145_101 = (FStar_Tc_Env.get_range env)
in (let _145_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _145_101 _145_100 t)))
in (match (_47_112) with
| (e, u) -> begin
(let _145_103 = (let _145_102 = (as_uvar_e u)
in ((_145_102), (u.FStar_Absyn_Syntax.pos)))
in ((e), (_145_103)))
end)))


let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _145_106 = (let _145_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _145_105))
in (FStar_All.failwith _145_106))
end
| Some (tk) -> begin
tk
end))


let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _47_2 -> (match (_47_2) with
| (FStar_Util.Inl (t), imp) -> begin
(let _145_111 = (let _145_110 = (force_tk t)
in FStar_Util.Inl (_145_110))
in ((_145_111), (imp)))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _145_113 = (let _145_112 = (force_tk v)
in FStar_Util.Inr (_145_112))
in ((_145_113), (imp)))
end)))))


let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _47_3 -> (match (_47_3) with
| Some (FStar_Absyn_Syntax.Implicit (_47_129)) -> begin
true
end
| _47_133 -> begin
false
end))


let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (

let ktop = (let _145_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _145_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (

let r = (FStar_Tc_Env.get_range env)
in (

let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(

let imp_follows = (match (args) with
| ((_47_149, qual))::_47_147 -> begin
(is_implicit qual)
end
| _47_154 -> begin
false
end)
in (

let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| (b)::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(

let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _145_137 = (let _145_134 = (let _145_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _145_133))
in (FStar_All.pipe_right _145_134 Prims.fst))
in (FStar_All.pipe_right _145_137 (fun x -> (let _145_136 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inl (x)), (_145_136))))))
end
| FStar_Util.Inr (x) -> begin
(let _145_142 = (let _145_139 = (let _145_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _145_138))
in (FStar_All.pipe_right _145_139 Prims.fst))
in (FStar_All.pipe_right _145_142 (fun x -> (let _145_141 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inr (x)), (_145_141))))))
end)
in (

let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _145_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_145_143)::subst)
end
in (

let _47_173 = (mk_implicits vars subst brest)
in (match (_47_173) with
| (imp_args, bs) -> begin
(((imp_arg)::imp_args), (bs))
end))))
end else begin
(let _145_144 = (FStar_Absyn_Util.subst_binders subst bs)
in (([]), (_145_144)))
end
end
| _47_175 -> begin
(let _145_145 = (FStar_Absyn_Util.subst_binders subst bs)
in (([]), (_145_145)))
end))
in if imp_follows then begin
(([]), (bs), (k'))
end else begin
(

let _47_178 = (let _145_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _145_146 [] bs))
in (match (_47_178) with
| (imps, bs) -> begin
((imps), (bs), (k'))
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_47_180, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_47_185) -> begin
(

let fvs = (FStar_Absyn_Util.freevars_kind k)
in (

let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (

let kres = (let _145_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _145_147 Prims.fst))
in (

let bs = (let _145_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _145_148))
in (

let kar = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (kres)) r)
in (

let _47_192 = (let _145_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _145_149))
in (([]), (bs), (kres))))))))
end
| _47_195 -> begin
(let _145_152 = (let _145_151 = (let _145_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in ((_145_150), (r)))
in FStar_Absyn_Syntax.Error (_145_151))
in (Prims.raise _145_152))
end))
in (aux ktop)))))


let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _47_4 -> (match (_47_4) with
| Some (FStar_Absyn_Syntax.Implicit (_47_198)) -> begin
true
end
| _47_202 -> begin
false
end))


let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (

let pvar_eq = (fun x y -> (match (((x), (y))) with
| (FStar_Tc_Env.Binding_var (x, _47_211), FStar_Tc_Env.Binding_var (y, _47_216)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _47_222), FStar_Tc_Env.Binding_typ (y, _47_227)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _47_232 -> begin
false
end))
in (

let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _47_5 -> (match (_47_5) with
| FStar_Tc_Env.Binding_var (x, _47_238) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _47_243) -> begin
FStar_Util.Inl (x)
end
| _47_247 -> begin
(FStar_All.failwith "impos")
end)))))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _47_254) -> begin
(

let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (

let _47_260 = (let _145_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p _145_174 t))
in (match (_47_260) with
| (e, u) -> begin
(

let p = (

let _47_261 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term (((x), (e))); FStar_Absyn_Syntax.sort = _47_261.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _47_261.FStar_Absyn_Syntax.p})
in (([]), ([]), ([]), (env), (FStar_Util.Inr (e)), (p)))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _47_266) -> begin
(

let k = (new_kvar env)
in (

let _47_272 = (let _145_175 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _145_175 k))
in (match (_47_272) with
| (t, u) -> begin
(

let p = (

let _47_273 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ (((a), (t))); FStar_Absyn_Syntax.sort = _47_273.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _47_273.FStar_Absyn_Syntax.p})
in (([]), ([]), ([]), (env), (FStar_Util.Inl (t)), (p)))
end)))
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(

let e = (FStar_Absyn_Syntax.mk_Exp_constant c None p.FStar_Absyn_Syntax.p)
in (([]), ([]), ([]), (env), (FStar_Util.Inr (e)), (p)))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(

let w = (let _145_177 = (let _145_176 = (new_tvar env FStar_Absyn_Syntax.ktype)
in ((x.FStar_Absyn_Syntax.v), (_145_176)))
in FStar_Tc_Env.Binding_var (_145_177))
in (

let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in (((w)::[]), ([]), ((w)::[]), (env), (FStar_Util.Inr (e)), (p)))))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(

let b = (let _145_179 = (let _145_178 = (new_tvar env FStar_Absyn_Syntax.ktype)
in ((x.FStar_Absyn_Syntax.v), (_145_178)))
in FStar_Tc_Env.Binding_var (_145_179))
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in (((b)::[]), ((b)::[]), ([]), (env), (FStar_Util.Inr (e)), (p)))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(

let w = (let _145_181 = (let _145_180 = (new_kvar env)
in ((a.FStar_Absyn_Syntax.v), (_145_180)))
in FStar_Tc_Env.Binding_typ (_145_181))
in (

let env = if allow_wc_dependence then begin
(FStar_Tc_Env.push_local_binding env w)
end else begin
env
end
in (

let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in (((w)::[]), ([]), ((w)::[]), (env), (FStar_Util.Inl (t)), (p)))))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(

let b = (let _145_183 = (let _145_182 = (new_kvar env)
in ((a.FStar_Absyn_Syntax.v), (_145_182)))
in FStar_Tc_Env.Binding_typ (_145_183))
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (

let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in (((b)::[]), ((b)::[]), ([]), (env), (FStar_Util.Inl (t)), (p)))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let _47_332 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _47_310 _47_313 -> (match (((_47_310), (_47_313))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _47_320 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_47_320) with
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
in (((b')::b), ((a')::a), ((w')::w), (env), ((arg)::args), ((((pat), (imp)))::pats)))
end))
end)) (([]), ([]), ([]), (env), ([]), ([]))))
in (match (_47_332) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _145_191 = (let _145_190 = (let _145_189 = (let _145_188 = (let _145_187 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _145_186 = (FStar_All.pipe_right args FStar_List.rev)
in ((_145_187), (_145_186))))
in (FStar_Absyn_Syntax.mk_Exp_app' _145_188 None p.FStar_Absyn_Syntax.p))
in ((_145_189), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_145_190))
in (FStar_Absyn_Syntax.mk_Exp_meta _145_191))
in (let _145_194 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _145_193 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _145_192 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_145_194), (_145_193), (_145_192), (env), (FStar_Util.Inr (e)), ((

let _47_334 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons (((fv), (q), ((FStar_List.rev pats)))); FStar_Absyn_Syntax.sort = _47_334.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _47_334.FStar_Absyn_Syntax.p})))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_47_337) -> begin
(FStar_All.failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let pats = (FStar_List.map (fun _47_349 -> (match (_47_349) with
| (p, imp) -> begin
(let _145_200 = (elaborate_pat env p)
in ((_145_200), (imp)))
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
| _47_355 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))))
end)
end
| Some (f, _47_358) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_47_371)::_47_369) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))))
end
| ((_47_377)::_47_375, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(

let a = (let _145_206 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _145_206 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _145_208 = (let _145_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((a), (FStar_Absyn_Syntax.tun)))) None _145_207))
in ((_145_208), ((as_imp imp))))
end else begin
(let _145_210 = (let _145_209 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _145_209))
in ((_145_210), ((as_imp imp))))
end)
end
| (FStar_Util.Inr (_47_388), Some (FStar_Absyn_Syntax.Implicit (dot))) -> begin
(

let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in if (allow_implicits && dot) then begin
(let _145_215 = (let _145_214 = (let _145_212 = (let _145_211 = (FStar_Absyn_Util.bvar_to_exp a)
in ((a), (_145_211)))
in FStar_Absyn_Syntax.Pat_dot_term (_145_212))
in (let _145_213 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _145_214 None _145_213)))
in ((_145_215), (true)))
end else begin
(let _145_217 = (let _145_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _145_216))
in ((_145_217), (true)))
end)
end
| _47_396 -> begin
(let _145_221 = (let _145_220 = (let _145_219 = (let _145_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _145_218))
in ((_145_219), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))
in FStar_Absyn_Syntax.Error (_145_220))
in (Prims.raise _145_221))
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (((f), (p.FStar_Absyn_Syntax.v))) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _145_222 = (aux formals' pats')
in (((p), ((as_imp imp))))::_145_222)
end
| ((FStar_Util.Inl (_47_424), imp), FStar_Absyn_Syntax.Pat_dot_typ (_47_429)) when allow_implicits -> begin
(let _145_223 = (aux formals' pats')
in (((p), ((as_imp imp))))::_145_223)
end
| ((FStar_Util.Inl (_47_433), imp), _47_438) -> begin
(

let a = (let _145_224 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _145_224 FStar_Absyn_Syntax.kun))
in (

let p1 = if allow_implicits then begin
(let _145_225 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((a), (FStar_Absyn_Syntax.tun)))) None _145_225))
end else begin
(let _145_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _145_226))
end
in (

let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_47_443) -> begin
pats'
end
| _47_446 -> begin
pats
end)
in (let _145_227 = (aux formals' pats')
in (((p1), ((as_imp imp))))::_145_227))))
end
| ((FStar_Util.Inr (_47_449), Some (FStar_Absyn_Syntax.Implicit (false))), _47_456) when p_imp -> begin
(let _145_228 = (aux formals' pats')
in (((p), (true)))::_145_228)
end
| ((FStar_Util.Inr (_47_459), Some (FStar_Absyn_Syntax.Implicit (dot))), _47_466) -> begin
(

let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let p = if (allow_implicits && dot) then begin
(let _145_232 = (let _145_230 = (let _145_229 = (FStar_Absyn_Util.bvar_to_exp a)
in ((a), (_145_229)))
in FStar_Absyn_Syntax.Pat_dot_term (_145_230))
in (let _145_231 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _145_232 None _145_231)))
end else begin
(let _145_233 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _145_233))
end
in (let _145_234 = (aux formals' pats)
in (((p), (true)))::_145_234)))
end
| ((FStar_Util.Inr (_47_471), imp), _47_476) -> begin
(let _145_235 = (aux formals' pats')
in (((p), ((as_imp imp))))::_145_235)
end)
end))
in (aux f pats))
end)
in (

let _47_479 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons (((fv), (q), (pats))); FStar_Absyn_Syntax.sort = _47_479.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _47_479.FStar_Absyn_Syntax.p}))))
end
| _47_482 -> begin
p
end))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _47_494 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_47_494) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _47_497)) -> begin
(let _145_244 = (let _145_243 = (let _145_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in ((_145_242), (p.FStar_Absyn_Syntax.p)))
in FStar_Absyn_Syntax.Error (_145_243))
in (Prims.raise _145_244))
end
| Some (FStar_Tc_Env.Binding_typ (x, _47_503)) -> begin
(let _145_247 = (let _145_246 = (let _145_245 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in ((_145_245), (p.FStar_Absyn_Syntax.p)))
in FStar_Absyn_Syntax.Error (_145_246))
in (Prims.raise _145_247))
end
| _47_508 -> begin
((b), (a), (w), (arg), (p))
end)
end))))
in (

let as_arg = (fun _47_6 -> (match (_47_6) with
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
| FStar_Absyn_Syntax.Pat_disj ((q)::pats) -> begin
(

let _47_530 = (one_pat false env q)
in (match (_47_530) with
| (b, a, _47_527, te, q) -> begin
(

let _47_545 = (FStar_List.fold_right (fun p _47_535 -> (match (_47_535) with
| (w, args, pats) -> begin
(

let _47_541 = (one_pat false env p)
in (match (_47_541) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _145_261 = (let _145_260 = (let _145_259 = (let _145_257 = (vars_of_bindings a)
in (let _145_256 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _145_257 _145_256)))
in (let _145_258 = (FStar_Tc_Env.get_range env)
in ((_145_259), (_145_258))))
in FStar_Absyn_Syntax.Error (_145_260))
in (Prims.raise _145_261))
end else begin
(let _145_263 = (let _145_262 = (as_arg arg)
in (_145_262)::args)
in (((FStar_List.append w' w)), (_145_263), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_47_545) with
| (w, args, pats) -> begin
(let _145_265 = (let _145_264 = (as_arg te)
in (_145_264)::args)
in (((FStar_List.append b w)), (_145_265), ((

let _47_546 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _47_546.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _47_546.FStar_Absyn_Syntax.p}))))
end))
end))
end
| _47_549 -> begin
(

let _47_557 = (one_pat true env p)
in (match (_47_557) with
| (b, _47_552, _47_554, arg, p) -> begin
(let _145_267 = (let _145_266 = (as_arg arg)
in (_145_266)::[])
in ((b), (_145_267), (p)))
end))
end))
in (

let _47_561 = (top_level_pat_as_args env p)
in (match (_47_561) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map (fun _47_7 -> (match (_47_7) with
| (FStar_Util.Inl (_47_564), _47_567) -> begin
(FStar_All.failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _47_572) -> begin
e
end))))
in ((b), (exps), (p)))
end))))))))))


let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (let _145_286 = (FStar_All.pipe_left (fun _145_285 -> Some (_145_285)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _145_286 p.FStar_Absyn_Syntax.p)))
in (

let e = (FStar_Absyn_Util.unmeta_exp e)
in (match (((p.FStar_Absyn_Syntax.v), (e.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Pat_constant (_47_588), FStar_Absyn_Syntax.Exp_constant (_47_591)) -> begin
(let _145_287 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _145_287))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(

let _47_599 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _145_290 = (let _145_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _145_288 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_289 _145_288)))
in (FStar_All.failwith _145_290))
end else begin
()
end
in (

let _47_601 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _145_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _145_291 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _145_292 _145_291)))
end else begin
()
end
in (

let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (

let x = (

let _47_604 = x
in {FStar_Absyn_Syntax.v = _47_604.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _47_604.FStar_Absyn_Syntax.p})
in (let _145_293 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _145_293))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(

let _47_612 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _145_296 = (let _145_295 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _145_294 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_295 _145_294)))
in (FStar_All.failwith _145_296))
end else begin
()
end
in (

let x = (

let _47_614 = x
in (let _145_297 = (force_tk e)
in {FStar_Absyn_Syntax.v = _47_614.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _145_297; FStar_Absyn_Syntax.p = _47_614.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _47_619), _47_623) -> begin
(

let x = (

let _47_625 = x
in (let _145_298 = (force_tk e)
in {FStar_Absyn_Syntax.v = _47_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _145_298; FStar_Absyn_Syntax.p = _47_625.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _47_635)) -> begin
(

let _47_639 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _145_299 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _145_299))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons (((fv'), (q), ([])))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _47_656); FStar_Absyn_Syntax.tk = _47_653; FStar_Absyn_Syntax.pos = _47_651; FStar_Absyn_Syntax.fvs = _47_649; FStar_Absyn_Syntax.uvs = _47_647}, args)) -> begin
(

let _47_664 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _145_300 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _145_300))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _145_307 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons (((fv), (q), ((FStar_List.rev matched_pats))))) _145_307))
end
| ((arg)::args, ((argpat, _47_680))::argpats) -> begin
(match (((arg), (argpat.FStar_Absyn_Syntax.v))) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_47_687))), FStar_Absyn_Syntax.Pat_dot_typ (_47_692)) -> begin
(

let x = (let _145_308 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _145_308))
in (

let q = (let _145_310 = (FStar_All.pipe_left (fun _145_309 -> Some (_145_309)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((x), (t)))) _145_310 p.FStar_Absyn_Syntax.p))
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_47_700))), FStar_Absyn_Syntax.Pat_dot_term (_47_705)) -> begin
(

let x = (let _145_311 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _145_311))
in (

let q = (let _145_313 = (FStar_All.pipe_left (fun _145_312 -> Some (_145_312)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term (((x), (e)))) _145_313 p.FStar_Absyn_Syntax.p))
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _47_715) -> begin
(

let pat = (aux_t argpat t)
in (match_args ((((pat), ((as_imp imp))))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _47_723) -> begin
(

let pat = (let _145_314 = (aux argpat e)
in ((_145_314), ((as_imp imp))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _47_727 -> begin
(let _145_317 = (let _145_316 = (FStar_Absyn_Print.pat_to_string p)
in (let _145_315 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _145_316 _145_315)))
in (FStar_All.failwith _145_317))
end))
in (match_args [] args argpats))))
end
| _47_729 -> begin
(let _145_322 = (let _145_321 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _145_320 = (FStar_Absyn_Print.pat_to_string qq)
in (let _145_319 = (let _145_318 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _145_318 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _145_321 _145_320 _145_319))))
in (FStar_All.failwith _145_322))
end))))
and aux_t = (fun p t0 -> (

let pkg = (fun q k -> (let _145_330 = (FStar_All.pipe_left (fun _145_329 -> Some (_145_329)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _145_330 p.FStar_Absyn_Syntax.p)))
in (

let t = (FStar_Absyn_Util.compress_typ t0)
in (match (((p.FStar_Absyn_Syntax.v), (t.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(

let _47_741 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _145_333 = (let _145_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _145_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_332 _145_331)))
in (FStar_All.failwith _145_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(

let _47_748 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _145_336 = (let _145_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _145_334 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_335 _145_334)))
in (FStar_All.failwith _145_336))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _47_752), _47_756) -> begin
(

let k0 = (force_tk t0)
in (

let a = (

let _47_759 = a
in {FStar_Absyn_Syntax.v = _47_759.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _47_759.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ (((a), (t)))) a.FStar_Absyn_Syntax.sort)))
end
| _47_763 -> begin
(let _145_340 = (let _145_339 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _145_338 = (FStar_Absyn_Print.pat_to_string p)
in (let _145_337 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _145_339 _145_338 _145_337))))
in (FStar_All.failwith _145_340))
end))))
in (match (((p.FStar_Absyn_Syntax.v), (exps))) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _47_767) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (let _145_342 = (FStar_All.pipe_left (fun _145_341 -> Some (_145_341)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _145_342 p.FStar_Absyn_Syntax.p)))
end
| (_47_771, (e)::[]) -> begin
(aux p e)
end
| _47_776 -> begin
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
| _47_783 -> begin
(FStar_All.failwith "top-level pattern should be decorated with a type")
end)
in (

let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (

let pat_as_arg = (fun _47_790 -> (match (_47_790) with
| (p, i) -> begin
(

let _47_793 = (decorated_pattern_as_either p)
in (match (_47_793) with
| (vars, te) -> begin
(let _145_362 = (let _145_361 = (FStar_Absyn_Syntax.as_implicit i)
in ((te), (_145_361)))
in ((vars), (_145_362)))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_47_795) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _145_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in (([]), (_145_365)))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _145_368 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in (((FStar_Util.Inr (x))::[]), (_145_368)))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let _47_809 = (let _145_369 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _145_369 FStar_List.unzip))
in (match (_47_809) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _145_375 = (let _145_374 = (let _145_373 = (let _145_372 = (FStar_Absyn_Syntax.mk_Exp_fvar ((fv), (q)) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in ((_145_372), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app' _145_373))
in (FStar_All.pipe_right _145_374 pkg))
in ((vars), (_145_375))))
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
(let _145_377 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in (((FStar_Util.Inl (a))::[]), (_145_377)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(([]), (t))
end
| _47_833 -> begin
(FStar_All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(

let _47_846 = (decorated_pattern_as_typ p)
in (match (_47_846) with
| (vars, t) -> begin
((vars), (FStar_Util.Inl (t)))
end))
end
| _47_848 -> begin
(

let _47_851 = (decorated_pattern_as_exp p)
in (match (_47_851) with
| (vars, e) -> begin
((vars), (FStar_Util.Inr (e)))
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
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _47_867; FStar_Absyn_Syntax.pos = _47_865; FStar_Absyn_Syntax.fvs = _47_863; FStar_Absyn_Syntax.uvs = _47_861}) -> begin
(

let _47_897 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _47_874 _47_878 -> (match (((_47_874), (_47_878))) with
| ((out, subst), (b, _47_877)) -> begin
(match (b) with
| FStar_Util.Inr (_47_880) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _145_385 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_385 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _145_388 = (let _145_387 = (let _145_386 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_386 Prims.fst))
in ((bs), (_145_387)))
in (FStar_Absyn_Syntax.mk_Typ_lam _145_388 (Some (k)) r))
end
| _47_891 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (arg))))::subst
in (let _145_390 = (let _145_389 = (FStar_Absyn_Syntax.targ arg)
in (_145_389)::out)
in ((_145_390), (subst))))))
end)
end)) (([]), ([]))))
in (match (_47_897) with
| (args, _47_896) -> begin
(FStar_Absyn_Syntax.mk_Typ_app ((t), ((FStar_List.rev args))) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _47_899 -> begin
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

let k = (let _145_401 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _145_401 Prims.fst))
in (((

let _47_910 = a
in {FStar_Absyn_Syntax.v = _47_910.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _47_910.FStar_Absyn_Syntax.p})), (false)))
end
| _47_913 -> begin
((a), (true))
end))
in (

let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(

let t = (let _145_406 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_406 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _47_922) -> begin
((x), (false))
end
| _47_925 -> begin
(FStar_All.failwith "impos")
end))
end
| _47_927 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _47_931) -> begin
((x), (true))
end
| _47_934 -> begin
(FStar_All.failwith "impos")
end)
end))
in (

let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _47_940)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _47_947) -> begin
((e), (t), (true))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let _47_976 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _47_957 b -> (match (_47_957) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(

let _47_963 = (mk_t_binder scope a)
in (match (_47_963) with
| (tb, c) -> begin
(

let b = ((FStar_Util.Inl (tb)), ((Prims.snd b)))
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in ((scope), (bs), ((c || check))))))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _47_971 = (mk_v_binder scope x)
in (match (_47_971) with
| (vb, c) -> begin
(

let b = ((FStar_Util.Inr (vb)), ((Prims.snd b)))
in ((scope), ((FStar_List.append bs ((b)::[]))), ((c || check))))
end))
end)
end)) ((vars), ([]), (false))))
in (match (_47_976) with
| (scope, bs, check) -> begin
(

let _47_980 = (aux scope body)
in (match (_47_980) with
| (body, res, check_res) -> begin
(

let c = (FStar_Absyn_Util.ml_comp res r)
in (

let t = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (

let _47_983 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_414 = (FStar_Range.string_of_range r)
in (let _145_413 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _145_414 _145_413)))
end else begin
()
end
in (

let e = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) None e.FStar_Absyn_Syntax.pos)
in ((e), (t), ((check_res || check)))))))
end))
end))
end
| _47_987 -> begin
(let _145_416 = (let _145_415 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_415 Prims.fst))
in ((e), (_145_416), (false)))
end))
in (let _145_417 = (FStar_Tc_Env.t_binders env)
in (aux _145_417 e))))))
end
| _47_989 -> begin
((e), (t), (false))
end))


let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (

let _47_1006 = (match (c.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp), _47_999))::((FStar_Util.Inl (wlp), _47_994))::[] -> begin
((wp), (wlp))
end
| _47_1003 -> begin
(let _145_422 = (let _145_421 = (let _145_420 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _145_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _145_421))
in (FStar_All.failwith _145_422))
end)
in (match (_47_1006) with
| (wp, wlp) -> begin
((c.FStar_Absyn_Syntax.result_typ), (wp), (wlp))
end)))


let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (

let _47_1014 = (destruct_comp c)
in (match (_47_1014) with
| (_47_1011, wp, wlp) -> begin
(let _145_444 = (let _145_443 = (let _145_439 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _145_439))
in (let _145_442 = (let _145_441 = (let _145_440 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _145_440))
in (_145_441)::[])
in (_145_443)::_145_442))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _145_444; FStar_Absyn_Syntax.flags = []})
end)))


let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_47_1022, c) -> begin
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

let _47_1036 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _47_1047 = (let _145_458 = (norm_eff_name env l1)
in (let _145_457 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _145_458 _145_457)))
in (match (_47_1047) with
| (m, _47_1044, _47_1046) -> begin
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

let _47_1059 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_47_1059) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_Tc_Env.get_effect_decl env m)
in (

let _47_1065 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_47_1065) with
| (a, kwp) -> begin
(let _145_472 = (destruct_comp m1)
in (let _145_471 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_145_472), (_145_471))))
end)))))
end)))))


let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))


let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun md result wp wlp flags -> (let _145_495 = (let _145_494 = (let _145_493 = (FStar_Absyn_Syntax.targ wp)
in (let _145_492 = (let _145_491 = (FStar_Absyn_Syntax.targ wlp)
in (_145_491)::[])
in (_145_493)::_145_492))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _145_494; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _145_495)))


let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (

let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _47_1079 -> (match (()) with
| () -> begin
c0
end))}))


let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (

let _47_1082 = lc
in (let _145_505 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _47_1082.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _145_505; FStar_Absyn_Syntax.cflags = _47_1082.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _47_1084 -> (match (()) with
| () -> begin
(let _145_504 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _145_504))
end))})))


let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _145_508 = (FStar_Absyn_Util.compress_typ t)
in _145_508.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_47_1087) -> begin
true
end
| _47_1090 -> begin
false
end))


let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp = (fun env t v -> (

let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(

let _47_1099 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_47_1099) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (

let wp = (let _145_520 = (let _145_519 = (let _145_518 = (let _145_517 = (FStar_Absyn_Syntax.targ t)
in (let _145_516 = (let _145_515 = (FStar_Absyn_Syntax.varg v)
in (_145_515)::[])
in (_145_517)::_145_516))
in ((m.FStar_Absyn_Syntax.ret), (_145_518)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_519 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _145_520))
in (

let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (

let _47_1104 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_523 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _145_522 = (FStar_Absyn_Print.exp_to_string v)
in (let _145_521 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _145_523 _145_522 _145_521))))
end else begin
()
end
in c)))


let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _47_1111 -> (match (_47_1111) with
| (b, lc2) -> begin
(

let _47_1122 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _47_1115)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _47_1120 -> begin
"??"
end)
in (let _145_533 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _145_532 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _145_533 bstr _145_532))))
end else begin
()
end
in (

let bind_it = (fun _47_1125 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (

let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (

let try_simplify = (fun _47_1129 -> (match (()) with
| () -> begin
(

let aux = (fun _47_1131 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_47_1134)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_47_1138)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _47_1142 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _47_1147))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _145_541 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr (((x), (e))))::[]) c2)
in (FStar_All.pipe_left (fun _145_540 -> Some (_145_540)) _145_541))
end else begin
(aux ())
end
end
| _47_1153 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(

let _47_1171 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _145_545 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _47_1159)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _47_1165)) -> begin
(FStar_Absyn_Print.sli l)
end
| _47_1170 -> begin
"Something else"
end)
in (let _145_544 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _145_543 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _145_542 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _145_545 _145_544 _145_543 _145_542)))))
end else begin
()
end
in c)
end
| None -> begin
(

let _47_1186 = (lift_and_destruct env c1 c2)
in (match (_47_1186) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _145_546 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_145_546)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _145_547 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_145_547)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _145_548 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_145_548)::[])
end
| _47_1199 -> begin
(FStar_All.failwith "Unexpected type-variable binding")
end)
in (

let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos))
in (

let wp_args = (let _145_563 = (FStar_Absyn_Syntax.targ t1)
in (let _145_562 = (let _145_561 = (FStar_Absyn_Syntax.targ t2)
in (let _145_560 = (let _145_559 = (FStar_Absyn_Syntax.targ wp1)
in (let _145_558 = (let _145_557 = (FStar_Absyn_Syntax.targ wlp1)
in (let _145_556 = (let _145_555 = (let _145_551 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _145_551))
in (let _145_554 = (let _145_553 = (let _145_552 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _145_552))
in (_145_553)::[])
in (_145_555)::_145_554))
in (_145_557)::_145_556))
in (_145_559)::_145_558))
in (_145_561)::_145_560))
in (_145_563)::_145_562))
in (

let wlp_args = (let _145_571 = (FStar_Absyn_Syntax.targ t1)
in (let _145_570 = (let _145_569 = (FStar_Absyn_Syntax.targ t2)
in (let _145_568 = (let _145_567 = (FStar_Absyn_Syntax.targ wlp1)
in (let _145_566 = (let _145_565 = (let _145_564 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _145_564))
in (_145_565)::[])
in (_145_567)::_145_566))
in (_145_569)::_145_568))
in (_145_571)::_145_570))
in (

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t2))))::[]) kwp)
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_app ((md.FStar_Absyn_Syntax.bind_wp), (wp_args)) None t2.FStar_Absyn_Syntax.pos)
in (

let wlp = (FStar_Absyn_Syntax.mk_Typ_app ((md.FStar_Absyn_Syntax.bind_wlp), (wlp_args)) None t2.FStar_Absyn_Syntax.pos)
in (

let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _145_572 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _145_572; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))


let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env t mk_wp mk_wlp f -> (

let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (

let _47_1217 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_47_1217) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (

let wp = (let _145_587 = (let _145_586 = (let _145_585 = (FStar_Absyn_Syntax.targ t)
in (let _145_584 = (let _145_583 = (FStar_Absyn_Syntax.targ f)
in (_145_583)::[])
in (_145_585)::_145_584))
in ((mk_wp), (_145_586)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_587 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _145_592 = (let _145_591 = (let _145_590 = (FStar_Absyn_Syntax.targ t)
in (let _145_589 = (let _145_588 = (FStar_Absyn_Syntax.targ f)
in (_145_588)::[])
in (_145_590)::_145_589))
in ((mk_wlp), (_145_591)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_592 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))


let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (((t), (None), (t.FStar_Absyn_Syntax.pos))))))


let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (

let refresh = (fun _47_1226 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_47_1229) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _47_1233 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_604 = (let _145_603 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _145_603))
in (FStar_Util.print1 "Refreshing label at %s\n" _145_604))
end else begin
()
end
in (

let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _47_1236 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _145_607 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _145_606 = (let _145_605 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _145_605))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _145_607 _145_606)))
end else begin
()
end
in (

let _47_1241 = (destruct_comp c')
in (match (_47_1241) with
| (t, wp, wlp) -> begin
(

let wp = (let _145_610 = (let _145_609 = (let _145_608 = (FStar_Tc_Env.get_range env)
in ((wp), (Some (b)), (_145_608)))
in FStar_Absyn_Syntax.Meta_refresh_label (_145_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _145_610))
in (

let wlp = (let _145_613 = (let _145_612 = (let _145_611 = (FStar_Tc_Env.get_range env)
in ((wlp), (Some (b)), (_145_611)))
in FStar_Absyn_Syntax.Meta_refresh_label (_145_612))
in (FStar_Absyn_Syntax.mk_Typ_meta _145_613))
in (let _145_618 = (

let _47_1244 = c'
in (let _145_617 = (let _145_616 = (FStar_Absyn_Syntax.targ wp)
in (let _145_615 = (let _145_614 = (FStar_Absyn_Syntax.targ wlp)
in (_145_614)::[])
in (_145_616)::_145_615))
in {FStar_Absyn_Syntax.effect_name = _47_1244.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _47_1244.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _145_617; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _145_618))))
end)))))
end)
end)
end))
in (

let _47_1246 = lc
in {FStar_Absyn_Syntax.eff_name = _47_1246.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _47_1246.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _47_1246.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (reason), (r), (true))))))


let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _145_642 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _145_642)) then begin
f
end else begin
(let _145_643 = (reason ())
in (label _145_643 r f))
end
end))


let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _145_650 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_145_650))
end))


let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(

let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _47_1273 -> begin
g2
end))


let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _47_1278 -> (match (()) with
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

let _47_1287 = (destruct_comp c)
in (match (_47_1287) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (let _145_669 = (let _145_668 = (let _145_667 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_666 = (let _145_665 = (FStar_Absyn_Syntax.targ f)
in (let _145_664 = (let _145_663 = (FStar_Absyn_Syntax.targ wp)
in (_145_663)::[])
in (_145_665)::_145_664))
in (_145_667)::_145_666))
in ((md.FStar_Absyn_Syntax.assume_p), (_145_668)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_669 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _145_676 = (let _145_675 = (let _145_674 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_673 = (let _145_672 = (FStar_Absyn_Syntax.targ f)
in (let _145_671 = (let _145_670 = (FStar_Absyn_Syntax.targ wlp)
in (_145_670)::[])
in (_145_672)::_145_671))
in (_145_674)::_145_673))
in ((md.FStar_Absyn_Syntax.assume_p), (_145_675)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_676 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (

let _47_1291 = lc
in {FStar_Absyn_Syntax.eff_name = _47_1291.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _47_1291.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _47_1291.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _47_8 -> (match (_47_8) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _47_1302 -> begin
[]
end))))
in (

let strengthen = (fun _47_1305 -> (match (()) with
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

let xret = (let _145_698 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _145_698))
in (

let xbinding = FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))
in (

let lc = (let _145_701 = (lcomp_of_comp c)
in (let _145_700 = (let _145_699 = (lcomp_of_comp xret)
in ((Some (xbinding)), (_145_699)))
in (bind env (Some (e)) _145_701 _145_700)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _47_1320 = (destruct_comp c)
in (match (_47_1320) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (let _145_710 = (let _145_709 = (let _145_708 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_707 = (let _145_706 = (let _145_703 = (let _145_702 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _145_702 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _145_703))
in (let _145_705 = (let _145_704 = (FStar_Absyn_Syntax.targ wp)
in (_145_704)::[])
in (_145_706)::_145_705))
in (_145_708)::_145_707))
in ((md.FStar_Absyn_Syntax.assert_p), (_145_709)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_710 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _145_717 = (let _145_716 = (let _145_715 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_714 = (let _145_713 = (FStar_Absyn_Syntax.targ f)
in (let _145_712 = (let _145_711 = (FStar_Absyn_Syntax.targ wlp)
in (_145_711)::[])
in (_145_713)::_145_712))
in (_145_715)::_145_714))
in ((md.FStar_Absyn_Syntax.assume_p), (_145_716)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_717 None wlp.FStar_Absyn_Syntax.pos))
in (

let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _145_721 = (

let _47_1325 = lc
in (let _145_720 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _145_719 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _145_718 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _145_718))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _145_720; FStar_Absyn_Syntax.res_typ = _47_1325.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _145_719; FStar_Absyn_Syntax.comp = strengthen})))
in ((_145_721), ((

let _47_1327 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _47_1327.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _47_1327.FStar_Tc_Rel.implicits}))))))
end)


let add_equality_to_post_condition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (

let x = (FStar_Absyn_Util.gen_bvar res_t)
in (

let y = (FStar_Absyn_Util.gen_bvar res_t)
in (

let _47_1337 = (let _145_729 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _145_728 = (FStar_Absyn_Util.bvar_to_exp y)
in ((_145_729), (_145_728))))
in (match (_47_1337) with
| (xexp, yexp) -> begin
(

let yret = (let _145_734 = (let _145_733 = (let _145_732 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_731 = (let _145_730 = (FStar_Absyn_Syntax.varg yexp)
in (_145_730)::[])
in (_145_732)::_145_731))
in ((md_pure.FStar_Absyn_Syntax.ret), (_145_733)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_734 None res_t.FStar_Absyn_Syntax.pos))
in (

let x_eq_y_yret = (let _145_742 = (let _145_741 = (let _145_740 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_739 = (let _145_738 = (let _145_735 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _145_735))
in (let _145_737 = (let _145_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_145_736)::[])
in (_145_738)::_145_737))
in (_145_740)::_145_739))
in ((md_pure.FStar_Absyn_Syntax.assume_p), (_145_741)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_742 None res_t.FStar_Absyn_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (let _145_753 = (let _145_752 = (let _145_751 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_750 = (let _145_749 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_748 = (let _145_747 = (let _145_746 = (let _145_745 = (let _145_744 = (let _145_743 = (FStar_Absyn_Syntax.v_binder y)
in (_145_743)::[])
in ((_145_744), (x_eq_y_yret)))
in (FStar_Absyn_Syntax.mk_Typ_lam _145_745 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _145_746))
in (_145_747)::[])
in (_145_749)::_145_748))
in (_145_751)::_145_750))
in ((md_pure.FStar_Absyn_Syntax.close_wp), (_145_752)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_753 None res_t.FStar_Absyn_Syntax.pos))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (

let lc = (let _145_756 = (lcomp_of_comp comp)
in (let _145_755 = (let _145_754 = (lcomp_of_comp lc2)
in ((Some (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort))))), (_145_754)))
in (bind env None _145_756 _145_755)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))


let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _47_1348 -> (match (()) with
| () -> begin
(

let _47_1364 = (let _145_768 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _145_767 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _145_768 _145_767)))
in (match (_47_1364) with
| ((md, _47_1351, _47_1353), (res_t, wp_then, wlp_then), (_47_1360, wp_else, wlp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _145_788 = (let _145_786 = (let _145_785 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_784 = (let _145_783 = (FStar_Absyn_Syntax.targ g)
in (let _145_782 = (let _145_781 = (FStar_Absyn_Syntax.targ wp_t)
in (let _145_780 = (let _145_779 = (FStar_Absyn_Syntax.targ wp_e)
in (_145_779)::[])
in (_145_781)::_145_780))
in (_145_783)::_145_782))
in (_145_785)::_145_784))
in ((md.FStar_Absyn_Syntax.if_then_else), (_145_786)))
in (let _145_787 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _145_788 None _145_787))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _145_795 = (let _145_794 = (let _145_793 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_792 = (let _145_791 = (FStar_Absyn_Syntax.targ wlp)
in (let _145_790 = (let _145_789 = (FStar_Absyn_Syntax.targ wp)
in (_145_789)::[])
in (_145_791)::_145_790))
in (_145_793)::_145_792))
in ((md.FStar_Absyn_Syntax.ite_wp), (_145_794)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_795 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _145_800 = (let _145_799 = (let _145_798 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_797 = (let _145_796 = (FStar_Absyn_Syntax.targ wlp)
in (_145_796)::[])
in (_145_798)::_145_797))
in ((md.FStar_Absyn_Syntax.ite_wlp), (_145_799)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_800 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _145_801 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _145_801; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))


let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (match (lcases) with
| [] -> begin
(FStar_All.failwith "Empty cases!")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun eff _47_1387 -> (match (_47_1387) with
| (_47_1385, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (

let bind_cases = (fun _47_1390 -> (match (()) with
| () -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _145_831 = (let _145_829 = (let _145_828 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_827 = (let _145_826 = (FStar_Absyn_Syntax.targ g)
in (let _145_825 = (let _145_824 = (FStar_Absyn_Syntax.targ wp_t)
in (let _145_823 = (let _145_822 = (FStar_Absyn_Syntax.targ wp_e)
in (_145_822)::[])
in (_145_824)::_145_823))
in (_145_826)::_145_825))
in (_145_828)::_145_827))
in ((md.FStar_Absyn_Syntax.if_then_else), (_145_829)))
in (let _145_830 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _145_831 None _145_830))))
in (

let default_case = (

let post_k = (let _145_834 = (let _145_833 = (let _145_832 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_145_832)::[])
in ((_145_833), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _145_834 res_t.FStar_Absyn_Syntax.pos))
in (

let kwp = (let _145_837 = (let _145_836 = (let _145_835 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_145_835)::[])
in ((_145_836), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _145_837 res_t.FStar_Absyn_Syntax.pos))
in (

let post = (let _145_838 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _145_838 post_k))
in (

let wp = (let _145_845 = (let _145_844 = (let _145_839 = (FStar_Absyn_Syntax.t_binder post)
in (_145_839)::[])
in (let _145_843 = (let _145_842 = (let _145_840 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _145_840))
in (let _145_841 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _145_842 _145_841)))
in ((_145_844), (_145_843))))
in (FStar_Absyn_Syntax.mk_Typ_lam _145_845 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _145_849 = (let _145_848 = (let _145_846 = (FStar_Absyn_Syntax.t_binder post)
in (_145_846)::[])
in (let _145_847 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((_145_848), (_145_847))))
in (FStar_Absyn_Syntax.mk_Typ_lam _145_849 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (

let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (

let comp = (FStar_List.fold_right (fun _47_1406 celse -> (match (_47_1406) with
| (g, cthen) -> begin
(

let _47_1424 = (let _145_852 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _145_852 celse))
in (match (_47_1424) with
| ((md, _47_1410, _47_1412), (_47_1415, wp_then, wlp_then), (_47_1420, wp_else, wlp_else)) -> begin
(let _145_854 = (ifthenelse md res_t g wp_then wp_else)
in (let _145_853 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _145_854 _145_853 [])))
end))
end)) lcases default_case)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(

let comp = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (

let md = (FStar_Tc_Env.get_effect_decl env comp.FStar_Absyn_Syntax.effect_name)
in (

let _47_1432 = (destruct_comp comp)
in (match (_47_1432) with
| (_47_1429, wp, wlp) -> begin
(

let wp = (let _145_861 = (let _145_860 = (let _145_859 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_858 = (let _145_857 = (FStar_Absyn_Syntax.targ wlp)
in (let _145_856 = (let _145_855 = (FStar_Absyn_Syntax.targ wp)
in (_145_855)::[])
in (_145_857)::_145_856))
in (_145_859)::_145_858))
in ((md.FStar_Absyn_Syntax.ite_wp), (_145_860)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_861 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _145_866 = (let _145_865 = (let _145_864 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_863 = (let _145_862 = (FStar_Absyn_Syntax.targ wlp)
in (_145_862)::[])
in (_145_864)::_145_863))
in ((md.FStar_Absyn_Syntax.ite_wlp), (_145_865)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_866 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))


let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (

let close = (fun _47_1439 -> (match (()) with
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

let bs = (let _145_885 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_145_885)::[])
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos)
in (let _145_892 = (let _145_891 = (let _145_890 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_889 = (let _145_888 = (FStar_Absyn_Syntax.targ t)
in (let _145_887 = (let _145_886 = (FStar_Absyn_Syntax.targ wp)
in (_145_886)::[])
in (_145_888)::_145_887))
in (_145_890)::_145_889))
in ((md.FStar_Absyn_Syntax.close_wp), (_145_891)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_892 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let bs = (let _145_893 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_145_893)::[])
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos)
in (let _145_898 = (let _145_897 = (let _145_896 = (FStar_Absyn_Syntax.targ res_t)
in (let _145_895 = (let _145_894 = (FStar_Absyn_Syntax.targ wp)
in (_145_894)::[])
in (_145_896)::_145_895))
in ((md.FStar_Absyn_Syntax.close_wp_t), (_145_897)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_898 None wp0.FStar_Absyn_Syntax.pos))))
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

let _47_1470 = (destruct_comp c)
in (match (_47_1470) with
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

let _47_1474 = lc
in {FStar_Absyn_Syntax.eff_name = _47_1474.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _47_1474.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _47_1474.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _47_1480 -> (match (()) with
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

let ret = (let _145_907 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _145_907))
in (

let eq_ret = (let _145_909 = (let _145_908 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_145_908))
in (weaken_precondition env ret _145_909))
in (let _145_912 = (let _145_911 = (let _145_910 = (lcomp_of_comp c)
in (bind env None _145_910 ((Some (FStar_Tc_Env.Binding_var (((x), (t))))), (eq_ret))))
in (_145_911.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _145_912 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
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

let _47_1490 = lc
in {FStar_Absyn_Syntax.eff_name = _47_1490.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _47_1490.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))


let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _145_924 = (let _145_923 = (let _145_922 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _145_921 = (FStar_Tc_Env.get_range env)
in ((_145_922), (_145_921))))
in FStar_Absyn_Syntax.Error (_145_923))
in (Prims.raise _145_924))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_instantiate_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.implicits) = (fun env t k -> (

let k = (FStar_Absyn_Util.compress_kind k)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
((t), (k), ([]))
end else begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let rec aux = (fun subst _47_9 -> (match (_47_9) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_47_1514))))::rest -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _47_1522 = (new_implicit_tvar env k)
in (match (_47_1522) with
| (t, u) -> begin
(

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (

let _47_1528 = (aux subst rest)
in (match (_47_1528) with
| (args, bs, subst, us) -> begin
(let _145_938 = (let _145_937 = (let _145_936 = (FStar_All.pipe_left (fun _145_935 -> Some (_145_935)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_145_936)))
in (_145_937)::args)
in ((_145_938), (bs), (subst), ((FStar_Util.Inl (u))::us)))
end)))
end)))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_47_1533))))::rest -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _47_1541 = (new_implicit_evar env t)
in (match (_47_1541) with
| (v, u) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v))))::subst
in (

let _47_1547 = (aux subst rest)
in (match (_47_1547) with
| (args, bs, subst, us) -> begin
(let _145_942 = (let _145_941 = (let _145_940 = (FStar_All.pipe_left (fun _145_939 -> Some (_145_939)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (v)), (_145_940)))
in (_145_941)::args)
in ((_145_942), (bs), (subst), ((FStar_Util.Inr (u))::us)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), ([]))
end))
in (

let _47_1553 = (aux [] bs)
in (match (_47_1553) with
| (args, bs, subst, implicits) -> begin
(

let k = (FStar_Absyn_Syntax.mk_Kind_arrow' ((bs), (k)) t.FStar_Absyn_Syntax.pos)
in (

let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _145_943 = (FStar_Absyn_Syntax.mk_Typ_app' ((t), (args)) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((_145_943), (k), (implicits)))))
end)))
end
| _47_1557 -> begin
((t), (k), ([]))
end)
end))


let maybe_instantiate : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.implicits) = (fun env e t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in if (not ((env.FStar_Tc_Env.instantiate_targs && env.FStar_Tc_Env.instantiate_vargs))) then begin
((e), (t), ([]))
end else begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let rec aux = (fun subst _47_10 -> (match (_47_10) with
| ((FStar_Util.Inl (a), _47_1573))::rest -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _47_1579 = (new_implicit_tvar env k)
in (match (_47_1579) with
| (t, u) -> begin
(

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (

let _47_1585 = (aux subst rest)
in (match (_47_1585) with
| (args, bs, subst, us) -> begin
(let _145_957 = (let _145_956 = (let _145_955 = (FStar_All.pipe_left (fun _145_954 -> Some (_145_954)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_145_955)))
in (_145_956)::args)
in ((_145_957), (bs), (subst), ((FStar_Util.Inl (u))::us)))
end)))
end)))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_47_1590))))::rest -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _47_1598 = (new_implicit_evar env t)
in (match (_47_1598) with
| (v, u) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v))))::subst
in (

let _47_1604 = (aux subst rest)
in (match (_47_1604) with
| (args, bs, subst, us) -> begin
(let _145_961 = (let _145_960 = (let _145_959 = (FStar_All.pipe_left (fun _145_958 -> Some (_145_958)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (v)), (_145_959)))
in (_145_960)::args)
in ((_145_961), (bs), (subst), ((FStar_Util.Inr (u))::us)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), ([]))
end))
in (

let _47_1610 = (aux [] bs)
in (match (_47_1610) with
| (args, bs, subst, implicits) -> begin
(

let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _47_1617 -> begin
(FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(

let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _145_968 = (mk_exp_app e args (Some (t)))
in ((_145_968), (t), (implicits))))
end else begin
((e), (t), ([]))
end
end
| _47_1621 -> begin
(

let t = (let _145_969 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _145_969 (FStar_Absyn_Util.subst_typ subst)))
in (let _145_970 = (mk_exp_app e args (Some (t)))
in ((_145_970), (t), (implicits))))
end))
end)))
end
| _47_1624 -> begin
((e), (t), ([]))
end)
end))


let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _145_979 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in ((_145_979), (false)))
end else begin
(let _145_980 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in ((_145_980), (true)))
end
in (match (gopt) with
| (None, _47_1632) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(

let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(

let lc = (

let _47_1640 = lc
in {FStar_Absyn_Syntax.eff_name = _47_1640.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _47_1640.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _47_1640.FStar_Absyn_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(

let g = (

let _47_1645 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _47_1645.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _47_1645.FStar_Tc_Rel.implicits})
in (

let strengthen = (fun _47_1649 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let _47_1651 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _145_984 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _145_983 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _145_984 _145_983)))
end else begin
()
end
in (

let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _47_1656 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_47_1656) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (

let md = (FStar_Tc_Env.get_effect_decl env ct.FStar_Absyn_Syntax.effect_name)
in (

let x = (FStar_Absyn_Util.new_bvd None)
in (

let xexp = (FStar_Absyn_Util.bvd_to_exp x t)
in (

let wp = (let _145_989 = (let _145_988 = (let _145_987 = (FStar_Absyn_Syntax.targ t)
in (let _145_986 = (let _145_985 = (FStar_Absyn_Syntax.varg xexp)
in (_145_985)::[])
in (_145_987)::_145_986))
in ((md.FStar_Absyn_Syntax.ret), (_145_988)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_989 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (

let cret = (let _145_990 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _145_990))
in (

let guard = if apply_guard then begin
(let _145_993 = (let _145_992 = (let _145_991 = (FStar_Absyn_Syntax.varg xexp)
in (_145_991)::[])
in ((f), (_145_992)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_993 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (

let _47_1666 = (let _145_1001 = (FStar_All.pipe_left (fun _145_998 -> Some (_145_998)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _145_1000 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _145_999 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _145_1001 _145_1000 e cret _145_999))))
in (match (_47_1666) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let c = (let _145_1003 = (let _145_1002 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _145_1002))
in (bind env (Some (e)) _145_1003 ((Some (FStar_Tc_Env.Binding_var (((x), (lc.FStar_Absyn_Syntax.res_typ))))), (eq_ret))))
in (

let c = (c.FStar_Absyn_Syntax.comp ())
in (

let _47_1669 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _145_1004 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _145_1004))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (

let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun _47_11 -> (match (_47_11) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _47_1675 -> begin
[]
end))))
in (

let lc = (

let _47_1677 = lc
in (let _145_1006 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _145_1006; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in ((e), (lc), (g))))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if ((((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t)) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k)) > (Prims.parse_int "0")) then begin
(

let ue = (let _145_1011 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _145_1011))
in (

let ut = (let _145_1012 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _145_1012))
in (

let uk = (let _145_1013 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _145_1013))
in (

let union = (FStar_String.concat "," (FStar_List.append ue (FStar_List.append ut uk)))
in (

let hide_uvar_nums_saved = (FStar_Options.hide_uvar_nums ())
in (

let print_implicits_saved = (FStar_Options.print_implicits ())
in (

let _47_1689 = (FStar_Options.push ())
in (

let _47_1691 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _47_1693 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _47_1695 = (let _145_1015 = (let _145_1014 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _145_1014))
in (FStar_Tc_Errors.report r _145_1015))
in (FStar_Options.pop ())))))))))))
end else begin
()
end))


let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _145_1023 = (FStar_Util.for_all (fun _47_1703 -> (match (_47_1703) with
| (_47_1701, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _145_1023)) then begin
None
end else begin
(

let norm = (fun c -> (

let _47_1706 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_1026 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _145_1026))
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

let _47_1710 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_1027 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _145_1027))
end else begin
()
end
in c)))))
in (

let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _145_1030 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _145_1030 FStar_Util.set_elements)))
in (

let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _47_1719) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun _47_12 -> (match (_47_12) with
| (FStar_Util.Inl (_47_1724), _47_1727) -> begin
true
end
| _47_1730 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _47_1732 -> begin
true
end))
in (

let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _47_1735 -> (match (_47_1735) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _145_1035 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _145_1035)) then begin
(([]), (e), (c))
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

let _47_1751 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _145_1036 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _145_1036))) then begin
(

let _47_1747 = (destruct_comp ct)
in (match (_47_1747) with
| (_47_1743, wp, _47_1746) -> begin
(

let binder = (let _145_1037 = (FStar_Absyn_Syntax.null_v_binder t)
in (_145_1037)::[])
in (

let post = (let _145_1041 = (let _145_1038 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((binder), (_145_1038)))
in (let _145_1040 = (let _145_1039 = (FStar_Absyn_Syntax.mk_Kind_arrow ((binder), (FStar_Absyn_Syntax.ktype)) t.FStar_Absyn_Syntax.pos)
in Some (_145_1039))
in (FStar_Absyn_Syntax.mk_Typ_lam _145_1041 _145_1040 t.FStar_Absyn_Syntax.pos)))
in (

let vc = (let _145_1048 = (let _145_1047 = (let _145_1046 = (let _145_1045 = (let _145_1044 = (FStar_Absyn_Syntax.targ post)
in (_145_1044)::[])
in ((wp), (_145_1045)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_1046))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _145_1047))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _145_1048))
in (let _145_1049 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _145_1049)))))
end))
end else begin
()
end
in ((uvs), (e), (c))))))))
end)
end))))
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _47_1757 -> (match (_47_1757) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _47_1760 -> (match (_47_1760) with
| (u, k) -> begin
(

let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_47_1798) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _47_1801 -> begin
(

let a = (let _145_1054 = (let _145_1053 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _145_1052 -> Some (_145_1052)) _145_1053))
in (FStar_Absyn_Util.new_bvd _145_1054))
in (

let t = (let _145_1055 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _145_1055 k))
in (

let _47_1804 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _145_1057 = (FStar_All.pipe_left (fun _145_1056 -> Some (_145_1056)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (a)), (_145_1057))))
end))))
in (

let t = (match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.function_formals)) with
| Some (bs, cod) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (((FStar_List.append tvars bs)), (cod)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(FStar_Absyn_Util.comp_result c)
end
| _47_1815 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((tvars), (c)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (

let e = (match (tvars) with
| [] -> begin
e
end
| _47_1819 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' ((tvars), (e)) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _145_1058 = (FStar_Absyn_Syntax.mk_Total t)
in ((e), (_145_1058))))))
end))))
in Some (ecs)))))))
end)


let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (

let _47_1831 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_1067 = (let _145_1066 = (FStar_List.map (fun _47_1830 -> (match (_47_1830) with
| (lb, _47_1827, _47_1829) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _145_1066 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _145_1067))
end else begin
()
end
in (match ((let _145_1069 = (FStar_All.pipe_right lecs (FStar_List.map (fun _47_1837 -> (match (_47_1837) with
| (_47_1834, e, c) -> begin
((e), (c))
end))))
in (gen verify env _145_1069))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _47_1846 _47_1849 -> (match (((_47_1846), (_47_1849))) with
| ((l, _47_1843, _47_1845), (e, c)) -> begin
(

let _47_1850 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_1074 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _145_1073 = (FStar_Absyn_Print.lbname_to_string l)
in (let _145_1072 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _145_1074 _145_1073 _145_1072))))
end else begin
()
end
in ((l), (e), (c)))
end)) lecs ecs)
end)))


let check_unresolved_implicits : FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Uvar -> begin
true
end
| _47_1857 -> begin
false
end))
in (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun _47_13 -> (match (_47_13) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _47_1863) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_47_1867, r)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unresolved implicit argument"), (r)))))
end
| _47_1873 -> begin
()
end)))


let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _47_1879 = (FStar_Tc_Rel.try_discharge_guard env g)
in (

let _47_1881 = (check_unresolved_implicits g)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _145_1089 = (discharge g)
in (let _145_1088 = (lc.FStar_Absyn_Syntax.comp ())
in ((_145_1089), (_145_1088))))
end else begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (

let c = (let _145_1090 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _145_1090 FStar_Absyn_Util.comp_to_comp_typ))
in (

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let _47_1892 = (destruct_comp c)
in (match (_47_1892) with
| (t, wp, _47_1891) -> begin
(

let vc = (let _145_1096 = (let _145_1094 = (let _145_1093 = (FStar_Absyn_Syntax.targ t)
in (let _145_1092 = (let _145_1091 = (FStar_Absyn_Syntax.targ wp)
in (_145_1091)::[])
in (_145_1093)::_145_1092))
in ((md.FStar_Absyn_Syntax.trivial), (_145_1094)))
in (let _145_1095 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _145_1096 (Some (FStar_Absyn_Syntax.ktype)) _145_1095)))
in (

let g = (let _145_1097 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _145_1097))
in (let _145_1099 = (discharge g)
in (let _145_1098 = (FStar_Absyn_Syntax.mk_Comp c)
in ((_145_1099), (_145_1098))))))
end))))))
end)))


let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (

let short_bin_op_e = (fun f _47_14 -> (match (_47_14) with
| [] -> begin
None
end
| ((FStar_Util.Inr (fst), _47_1904))::[] -> begin
(let _145_1118 = (f fst)
in (FStar_All.pipe_right _145_1118 (fun _145_1117 -> Some (_145_1117))))
end
| _47_1908 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let table = (

let op_and_e = (fun e -> (let _145_1124 = (FStar_Absyn_Util.b2t e)
in ((_145_1124), (FStar_Absyn_Const.exp_false_bool))))
in (

let op_or_e = (fun e -> (let _145_1128 = (let _145_1127 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _145_1127))
in ((_145_1128), (FStar_Absyn_Const.exp_true_bool))))
in (((FStar_Absyn_Const.op_And), ((short_bin_op_e op_and_e))))::(((FStar_Absyn_Const.op_Or), ((short_bin_op_e op_or_e))))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _47_1916) -> begin
(

let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _47_1922 -> (match (_47_1922) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _145_1146 = (mk seen_args)
in Some (_145_1146))
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
| _47_1927 -> begin
None
end))))


let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (

let short_bin_op_t = (fun f _47_15 -> (match (_47_15) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| ((FStar_Util.Inl (fst), _47_1937))::[] -> begin
(f fst)
end
| _47_1941 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_t = (fun t -> (let _145_1167 = (unlabel t)
in (FStar_All.pipe_right _145_1167 (fun _145_1166 -> FStar_Tc_Rel.NonTrivial (_145_1166)))))
in (

let op_or_t = (fun t -> (let _145_1172 = (let _145_1170 = (unlabel t)
in (FStar_All.pipe_right _145_1170 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _145_1172 (fun _145_1171 -> FStar_Tc_Rel.NonTrivial (_145_1171)))))
in (

let op_imp_t = (fun t -> (let _145_1176 = (unlabel t)
in (FStar_All.pipe_right _145_1176 (fun _145_1175 -> FStar_Tc_Rel.NonTrivial (_145_1175)))))
in (

let short_op_ite = (fun _47_16 -> (match (_47_16) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| ((FStar_Util.Inl (guard), _47_1953))::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| (_then)::((FStar_Util.Inl (guard), _47_1959))::[] -> begin
(let _145_1180 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _145_1180 (fun _145_1179 -> FStar_Tc_Rel.NonTrivial (_145_1179))))
end
| _47_1964 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Absyn_Const.and_lid), ((short_bin_op_t op_and_t))))::(((FStar_Absyn_Const.or_lid), ((short_bin_op_t op_or_t))))::(((FStar_Absyn_Const.imp_lid), ((short_bin_op_t op_imp_t))))::(((FStar_Absyn_Const.ite_lid), (short_op_ite)))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _47_1972) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _47_1982; FStar_Absyn_Syntax.pos = _47_1980; FStar_Absyn_Syntax.fvs = _47_1978; FStar_Absyn_Syntax.uvs = _47_1976}) -> begin
(

let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _47_1990 -> (match (_47_1990) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _145_1207 = (mk seen_args)
in Some (_145_1207))
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
| _47_1995 -> begin
FStar_Tc_Rel.Trivial
end))))))))


let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _145_1221 = (let _145_1220 = (let _145_1219 = (let _145_1218 = (let _145_1217 = (let _145_1216 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _145_1216))
in (_145_1217)::[])
in ((ens), (_145_1218)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_1219 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in ((x), (_145_1220)))
in (FStar_Absyn_Syntax.mk_Typ_refine _145_1221 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (

let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
((None), ((FStar_Absyn_Util.comp_result comp)))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_47_2005) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (req), _47_2020))::((FStar_Util.Inl (ens), _47_2014))::_47_2010 -> begin
(let _145_1227 = (let _145_1224 = (norm req)
in Some (_145_1224))
in (let _145_1226 = (let _145_1225 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _145_1225))
in ((_145_1227), (_145_1226))))
end
| _47_2024 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_47_2027) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp), _47_2042))::((FStar_Util.Inl (wlp), _47_2036))::_47_2032 -> begin
(

let _47_2054 = (match ((let _145_1229 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _145_1228 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in ((_145_1229), (_145_1228))))) with
| (Some (x), Some (y)) -> begin
((x), (y))
end
| _47_2051 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_47_2054) with
| (as_req, as_ens) -> begin
(

let req = (let _145_1236 = (let _145_1235 = (let _145_1234 = (let _145_1231 = (FStar_All.pipe_left (fun _145_1230 -> Some (_145_1230)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ)), (_145_1231)))
in (let _145_1233 = (let _145_1232 = (FStar_Absyn_Syntax.targ wp)
in (_145_1232)::[])
in (_145_1234)::_145_1233))
in ((as_req), (_145_1235)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_1236 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (

let ens = (let _145_1243 = (let _145_1242 = (let _145_1241 = (let _145_1238 = (FStar_All.pipe_left (fun _145_1237 -> Some (_145_1237)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ)), (_145_1238)))
in (let _145_1240 = (let _145_1239 = (FStar_Absyn_Syntax.targ wlp)
in (_145_1239)::[])
in (_145_1241)::_145_1240))
in ((as_ens), (_145_1242)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_1243 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _145_1247 = (let _145_1244 = (norm req)
in Some (_145_1244))
in (let _145_1246 = (let _145_1245 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _145_1245))
in ((_145_1247), (_145_1246))))))
end))
end
| _47_2058 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end
end)
end)))




