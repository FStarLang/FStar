
open Prims

type lcomp_with_binder =
(FStar_Tc_Env.binding Prims.option * FStar_Absyn_Syntax.lcomp)


let try_solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun env f -> (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env f))


let report : FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _149_10 = (FStar_Tc_Env.get_range env)
in (let _149_9 = (FStar_Tc_Errors.failed_to_prove_specification errs)
in (FStar_Errors.report _149_10 _149_9))))


let discharge_guard : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (FStar_Tc_Rel.try_discharge_guard env g))


let force_trivial : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  Prims.unit = (fun env g -> (discharge_guard env g))


let syn' = (fun env k -> (let _149_29 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _149_29 k)))


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
(let _149_53 = (FStar_Tc_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _149_52 -> Some (_149_52)) _149_53))
end)
end)
in if (env.FStar_Tc_Env.is_pattern && false) then begin
(match ((FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _149_57 = (let _149_56 = (let _149_55 = (FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _149_54 = (FStar_Tc_Env.get_range env)
in ((_149_55), (_149_54))))
in FStar_Errors.Error (_149_56))
in (Prims.raise _149_57))
end
| Some (g) -> begin
((e), (g))
end)
end else begin
(match ((check env t1 t2)) with
| None -> begin
(let _149_61 = (let _149_60 = (let _149_59 = (FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _149_58 = (FStar_Tc_Env.get_range env)
in ((_149_59), (_149_58))))
in FStar_Errors.Error (_149_60))
in (Prims.raise _149_61))
end
| Some (g) -> begin
(

let _48_37 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_62 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _149_62))
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
| _48_43 -> begin
(

let _48_44 = e
in (let _149_63 = (FStar_Util.mk_ref (Some (t2)))
in {FStar_Absyn_Syntax.n = _48_44.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _149_63; FStar_Absyn_Syntax.pos = _48_44.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _48_44.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _48_44.FStar_Absyn_Syntax.uvs}))
end)
in ((e), (g)))))
end)
end)))


let env_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders = (fun env -> if (FStar_Options.full_context_dependency ()) then begin
(FStar_Tc_Env.binders env)
end else begin
(FStar_Tc_Env.t_binders env)
end)


let as_uvar_e = (fun uu___161 -> (match (uu___161) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _48_59); FStar_Absyn_Syntax.tk = _48_56; FStar_Absyn_Syntax.pos = _48_54; FStar_Absyn_Syntax.fvs = _48_52; FStar_Absyn_Syntax.uvs = _48_50} -> begin
uv
end
| _48_64 -> begin
(failwith "Impossible")
end))


let as_uvar_t : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.uvar_t = (fun t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _48_76); FStar_Absyn_Syntax.tk = _48_73; FStar_Absyn_Syntax.pos = _48_71; FStar_Absyn_Syntax.fvs = _48_69; FStar_Absyn_Syntax.uvs = _48_67} -> begin
uv
end
| _48_81 -> begin
(failwith "Impossible")
end))


let new_kvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd = (fun env -> (let _149_73 = (let _149_72 = (FStar_Tc_Env.get_range env)
in (let _149_71 = (env_binders env)
in (FStar_Tc_Rel.new_kvar _149_72 _149_71)))
in (FStar_All.pipe_right _149_73 Prims.fst)))


let new_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env k -> (let _149_80 = (let _149_79 = (FStar_Tc_Env.get_range env)
in (let _149_78 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _149_79 _149_78 k)))
in (FStar_All.pipe_right _149_80 Prims.fst)))


let new_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp = (fun env t -> (let _149_87 = (let _149_86 = (FStar_Tc_Env.get_range env)
in (let _149_85 = (env_binders env)
in (FStar_Tc_Rel.new_evar _149_86 _149_85 t)))
in (FStar_All.pipe_right _149_87 Prims.fst)))


let new_implicit_tvar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * (FStar_Absyn_Syntax.uvar_t * FStar_Range.range)) = (fun env k -> (

let _48_91 = (let _149_93 = (FStar_Tc_Env.get_range env)
in (let _149_92 = (env_binders env)
in (FStar_Tc_Rel.new_tvar _149_93 _149_92 k)))
in (match (_48_91) with
| (t, u) -> begin
(let _149_95 = (let _149_94 = (as_uvar_t u)
in ((_149_94), (u.FStar_Absyn_Syntax.pos)))
in ((t), (_149_95)))
end)))


let new_implicit_evar : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) = (fun env t -> (

let _48_96 = (let _149_101 = (FStar_Tc_Env.get_range env)
in (let _149_100 = (env_binders env)
in (FStar_Tc_Rel.new_evar _149_101 _149_100 t)))
in (match (_48_96) with
| (e, u) -> begin
(let _149_103 = (let _149_102 = (as_uvar_e u)
in ((_149_102), (u.FStar_Absyn_Syntax.pos)))
in ((e), (_149_103)))
end)))


let force_tk = (fun s -> (match ((FStar_ST.read s.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _149_106 = (let _149_105 = (FStar_Range.string_of_range s.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "Impossible: Forced tk not present (%s)" _149_105))
in (failwith _149_106))
end
| Some (tk) -> begin
tk
end))


let tks_of_args : FStar_Absyn_Syntax.args  ->  ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu___162 -> (match (uu___162) with
| (FStar_Util.Inl (t), imp) -> begin
(let _149_111 = (let _149_110 = (force_tk t)
in FStar_Util.Inl (_149_110))
in ((_149_111), (imp)))
end
| (FStar_Util.Inr (v), imp) -> begin
(let _149_113 = (let _149_112 = (force_tk v)
in FStar_Util.Inr (_149_112))
in ((_149_113), (imp)))
end)))))


let is_implicit : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___163 -> (match (uu___163) with
| Some (FStar_Absyn_Syntax.Implicit (_48_113)) -> begin
true
end
| _48_117 -> begin
false
end))


let destruct_arrow_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.args * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env tt k args -> (

let ktop = (let _149_124 = (FStar_Absyn_Util.compress_kind k)
in (FStar_All.pipe_right _149_124 (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env)))
in (

let r = (FStar_Tc_Env.get_range env)
in (

let rec aux = (fun k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs, k') -> begin
(

let imp_follows = (match (args) with
| ((_48_133, qual))::_48_131 -> begin
(is_implicit qual)
end
| _48_138 -> begin
false
end)
in (

let rec mk_implicits = (fun vars subst bs -> (match (bs) with
| (b)::brest -> begin
if (FStar_All.pipe_right (Prims.snd b) is_implicit) then begin
(

let imp_arg = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _149_137 = (let _149_134 = (let _149_133 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_tvar r vars _149_133))
in (FStar_All.pipe_right _149_134 Prims.fst))
in (FStar_All.pipe_right _149_137 (fun x -> (let _149_136 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inl (x)), (_149_136))))))
end
| FStar_Util.Inr (x) -> begin
(let _149_142 = (let _149_139 = (let _149_138 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Rel.new_evar r vars _149_138))
in (FStar_All.pipe_right _149_139 Prims.fst))
in (FStar_All.pipe_right _149_142 (fun x -> (let _149_141 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inr (x)), (_149_141))))))
end)
in (

let subst = if (FStar_Absyn_Syntax.is_null_binder b) then begin
subst
end else begin
(let _149_143 = (FStar_Absyn_Util.subst_formal b imp_arg)
in (_149_143)::subst)
end
in (

let _48_157 = (mk_implicits vars subst brest)
in (match (_48_157) with
| (imp_args, bs) -> begin
(((imp_arg)::imp_args), (bs))
end))))
end else begin
(let _149_144 = (FStar_Absyn_Util.subst_binders subst bs)
in (([]), (_149_144)))
end
end
| _48_159 -> begin
(let _149_145 = (FStar_Absyn_Util.subst_binders subst bs)
in (([]), (_149_145)))
end))
in if imp_follows then begin
(([]), (bs), (k'))
end else begin
(

let _48_162 = (let _149_146 = (FStar_Tc_Env.binders env)
in (mk_implicits _149_146 [] bs))
in (match (_48_162) with
| (imps, bs) -> begin
((imps), (bs), (k'))
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_48_164, k) -> begin
(aux k)
end
| FStar_Absyn_Syntax.Kind_uvar (_48_169) -> begin
(

let fvs = (FStar_Absyn_Util.freevars_kind k)
in (

let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (

let kres = (let _149_147 = (FStar_Tc_Rel.new_kvar r binders)
in (FStar_All.pipe_right _149_147 Prims.fst))
in (

let bs = (let _149_148 = (tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _149_148))
in (

let kar = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (kres)) r)
in (

let _48_176 = (let _149_149 = (FStar_Tc_Rel.keq env None k kar)
in (FStar_All.pipe_left (force_trivial env) _149_149))
in (([]), (bs), (kres))))))))
end
| _48_179 -> begin
(let _149_152 = (let _149_151 = (let _149_150 = (FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in ((_149_150), (r)))
in FStar_Errors.Error (_149_151))
in (Prims.raise _149_152))
end))
in (aux ktop)))))


let as_imp : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___164 -> (match (uu___164) with
| Some (FStar_Absyn_Syntax.Implicit (_48_182)) -> begin
true
end
| _48_186 -> begin
false
end))


let pat_as_exps : Prims.bool  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  (FStar_Tc_Env.binding Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.pat) = (fun allow_implicits env p -> (

let pvar_eq = (fun x y -> (match (((x), (y))) with
| (FStar_Tc_Env.Binding_var (x, _48_195), FStar_Tc_Env.Binding_var (y, _48_200)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| (FStar_Tc_Env.Binding_typ (x, _48_206), FStar_Tc_Env.Binding_typ (y, _48_211)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _48_216 -> begin
false
end))
in (

let vars_of_bindings = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu___165 -> (match (uu___165) with
| FStar_Tc_Env.Binding_var (x, _48_222) -> begin
FStar_Util.Inr (x)
end
| FStar_Tc_Env.Binding_typ (x, _48_227) -> begin
FStar_Util.Inl (x)
end
| _48_231 -> begin
(failwith "impos")
end)))))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_term (x, _48_238) -> begin
(

let t = (new_tvar env FStar_Absyn_Syntax.ktype)
in (

let _48_244 = (let _149_174 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_evar p.FStar_Absyn_Syntax.p _149_174 t))
in (match (_48_244) with
| (e, u) -> begin
(

let p = (

let _48_245 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_term (((x), (e))); FStar_Absyn_Syntax.sort = _48_245.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _48_245.FStar_Absyn_Syntax.p})
in (([]), ([]), ([]), (env), (FStar_Util.Inr (e)), (p)))
end)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, _48_250) -> begin
(

let k = (new_kvar env)
in (

let _48_256 = (let _149_175 = (FStar_Tc_Env.binders env)
in (FStar_Tc_Rel.new_tvar p.FStar_Absyn_Syntax.p _149_175 k))
in (match (_48_256) with
| (t, u) -> begin
(

let p = (

let _48_257 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_dot_typ (((a), (t))); FStar_Absyn_Syntax.sort = _48_257.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _48_257.FStar_Absyn_Syntax.p})
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

let w = (let _149_177 = (let _149_176 = (new_tvar env FStar_Absyn_Syntax.ktype)
in ((x.FStar_Absyn_Syntax.v), (_149_176)))
in FStar_Tc_Env.Binding_var (_149_177))
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

let b = (let _149_179 = (let _149_178 = (new_tvar env FStar_Absyn_Syntax.ktype)
in ((x.FStar_Absyn_Syntax.v), (_149_178)))
in FStar_Tc_Env.Binding_var (_149_179))
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar x None p.FStar_Absyn_Syntax.p)
in (((b)::[]), ((b)::[]), ([]), (env), (FStar_Util.Inr (e)), (p)))))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(

let w = (let _149_181 = (let _149_180 = (new_kvar env)
in ((a.FStar_Absyn_Syntax.v), (_149_180)))
in FStar_Tc_Env.Binding_typ (_149_181))
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

let b = (let _149_183 = (let _149_182 = (new_kvar env)
in ((a.FStar_Absyn_Syntax.v), (_149_182)))
in FStar_Tc_Env.Binding_typ (_149_183))
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (

let t = (FStar_Absyn_Syntax.mk_Typ_btvar a None p.FStar_Absyn_Syntax.p)
in (((b)::[]), ((b)::[]), ([]), (env), (FStar_Util.Inl (t)), (p)))))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let _48_316 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _48_294 _48_297 -> (match (((_48_294), (_48_297))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _48_304 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_48_304) with
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
in (match (_48_316) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _149_191 = (let _149_190 = (let _149_189 = (let _149_188 = (let _149_187 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) fv.FStar_Absyn_Syntax.v fv.FStar_Absyn_Syntax.p)
in (let _149_186 = (FStar_All.pipe_right args FStar_List.rev)
in ((_149_187), (_149_186))))
in (FStar_Absyn_Syntax.mk_Exp_app' _149_188 None p.FStar_Absyn_Syntax.p))
in ((_149_189), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_149_190))
in (FStar_Absyn_Syntax.mk_Exp_meta _149_191))
in (let _149_194 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _149_193 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _149_192 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_149_194), (_149_193), (_149_192), (env), (FStar_Util.Inr (e)), ((

let _48_318 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons (((fv), (q), ((FStar_List.rev pats)))); FStar_Absyn_Syntax.sort = _48_318.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _48_318.FStar_Absyn_Syntax.p})))))))
end))
end
| FStar_Absyn_Syntax.Pat_disj (_48_321) -> begin
(failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let pats = (FStar_List.map (fun _48_333 -> (match (_48_333) with
| (p, imp) -> begin
(let _149_200 = (elaborate_pat env p)
in ((_149_200), (imp)))
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
| _48_339 -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))))
end)
end
| Some (f, _48_342) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_48_355)::_48_353) -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))))
end
| ((_48_361)::_48_359, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun f -> (match (f) with
| (FStar_Util.Inl (t), imp) -> begin
(

let a = (let _149_206 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _149_206 FStar_Absyn_Syntax.kun))
in if allow_implicits then begin
(let _149_208 = (let _149_207 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((a), (FStar_Absyn_Syntax.tun)))) None _149_207))
in ((_149_208), ((as_imp imp))))
end else begin
(let _149_210 = (let _149_209 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _149_209))
in ((_149_210), ((as_imp imp))))
end)
end
| (FStar_Util.Inr (_48_372), Some (FStar_Absyn_Syntax.Implicit (dot))) -> begin
(

let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in if (allow_implicits && dot) then begin
(let _149_215 = (let _149_214 = (let _149_212 = (let _149_211 = (FStar_Absyn_Util.bvar_to_exp a)
in ((a), (_149_211)))
in FStar_Absyn_Syntax.Pat_dot_term (_149_212))
in (let _149_213 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _149_214 None _149_213)))
in ((_149_215), (true)))
end else begin
(let _149_217 = (let _149_216 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _149_216))
in ((_149_217), (true)))
end)
end
| _48_380 -> begin
(let _149_221 = (let _149_220 = (let _149_219 = (let _149_218 = (FStar_Absyn_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _149_218))
in ((_149_219), ((FStar_Ident.range_of_lid fv.FStar_Absyn_Syntax.v))))
in FStar_Errors.Error (_149_220))
in (Prims.raise _149_221))
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (((f), (p.FStar_Absyn_Syntax.v))) with
| (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_tvar (_))) | (((FStar_Util.Inl (_), imp), FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _149_222 = (aux formals' pats')
in (((p), ((as_imp imp))))::_149_222)
end
| ((FStar_Util.Inl (_48_408), imp), FStar_Absyn_Syntax.Pat_dot_typ (_48_413)) when allow_implicits -> begin
(let _149_223 = (aux formals' pats')
in (((p), ((as_imp imp))))::_149_223)
end
| ((FStar_Util.Inl (_48_417), imp), _48_422) -> begin
(

let a = (let _149_224 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _149_224 FStar_Absyn_Syntax.kun))
in (

let p1 = if allow_implicits then begin
(let _149_225 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((a), (FStar_Absyn_Syntax.tun)))) None _149_225))
end else begin
(let _149_226 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_tvar (a)) None _149_226))
end
in (

let pats' = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_dot_typ (_48_427) -> begin
pats'
end
| _48_430 -> begin
pats
end)
in (let _149_227 = (aux formals' pats')
in (((p1), ((as_imp imp))))::_149_227))))
end
| ((FStar_Util.Inr (_48_433), Some (FStar_Absyn_Syntax.Implicit (false))), _48_440) when p_imp -> begin
(let _149_228 = (aux formals' pats')
in (((p), (true)))::_149_228)
end
| ((FStar_Util.Inr (_48_443), Some (FStar_Absyn_Syntax.Implicit (dot))), _48_450) -> begin
(

let a = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let p = if (allow_implicits && dot) then begin
(let _149_232 = (let _149_230 = (let _149_229 = (FStar_Absyn_Util.bvar_to_exp a)
in ((a), (_149_229)))
in FStar_Absyn_Syntax.Pat_dot_term (_149_230))
in (let _149_231 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo _149_232 None _149_231)))
end else begin
(let _149_233 = (FStar_Absyn_Syntax.range_of_lid fv.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_var (a)) None _149_233))
end
in (let _149_234 = (aux formals' pats)
in (((p), (true)))::_149_234)))
end
| ((FStar_Util.Inr (_48_455), imp), _48_460) -> begin
(let _149_235 = (aux formals' pats')
in (((p), ((as_imp imp))))::_149_235)
end)
end))
in (aux f pats))
end)
in (

let _48_463 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_cons (((fv), (q), (pats))); FStar_Absyn_Syntax.sort = _48_463.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _48_463.FStar_Absyn_Syntax.p}))))
end
| _48_466 -> begin
p
end))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _48_478 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_48_478) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup pvar_eq))) with
| Some (FStar_Tc_Env.Binding_var (x, _48_481)) -> begin
(let _149_244 = (let _149_243 = (let _149_242 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inr (x)))
in ((_149_242), (p.FStar_Absyn_Syntax.p)))
in FStar_Errors.Error (_149_243))
in (Prims.raise _149_244))
end
| Some (FStar_Tc_Env.Binding_typ (x, _48_487)) -> begin
(let _149_247 = (let _149_246 = (let _149_245 = (FStar_Tc_Errors.nonlinear_pattern_variable (FStar_Util.Inl (x)))
in ((_149_245), (p.FStar_Absyn_Syntax.p)))
in FStar_Errors.Error (_149_246))
in (Prims.raise _149_247))
end
| _48_492 -> begin
((b), (a), (w), (arg), (p))
end)
end))))
in (

let as_arg = (fun uu___166 -> (match (uu___166) with
| FStar_Util.Inl (t) -> begin
(failwith "Impossible")
end
| FStar_Util.Inr (e) -> begin
(FStar_Absyn_Syntax.varg e)
end))
in (

let top_level_pat_as_args = (fun env p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Pat_disj ((q)::pats) -> begin
(

let _48_514 = (one_pat false env q)
in (match (_48_514) with
| (b, a, _48_511, te, q) -> begin
(

let _48_529 = (FStar_List.fold_right (fun p _48_519 -> (match (_48_519) with
| (w, args, pats) -> begin
(

let _48_525 = (one_pat false env p)
in (match (_48_525) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv pvar_eq a a'))) then begin
(let _149_261 = (let _149_260 = (let _149_259 = (let _149_257 = (vars_of_bindings a)
in (let _149_256 = (vars_of_bindings a')
in (FStar_Tc_Errors.disjunctive_pattern_vars _149_257 _149_256)))
in (let _149_258 = (FStar_Tc_Env.get_range env)
in ((_149_259), (_149_258))))
in FStar_Errors.Error (_149_260))
in (Prims.raise _149_261))
end else begin
(let _149_263 = (let _149_262 = (as_arg arg)
in (_149_262)::args)
in (((FStar_List.append w' w)), (_149_263), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_48_529) with
| (w, args, pats) -> begin
(let _149_265 = (let _149_264 = (as_arg te)
in (_149_264)::args)
in (((FStar_List.append b w)), (_149_265), ((

let _48_530 = p
in {FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_disj ((q)::pats); FStar_Absyn_Syntax.sort = _48_530.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _48_530.FStar_Absyn_Syntax.p}))))
end))
end))
end
| _48_533 -> begin
(

let _48_541 = (one_pat true env p)
in (match (_48_541) with
| (b, _48_536, _48_538, arg, p) -> begin
(let _149_267 = (let _149_266 = (as_arg arg)
in (_149_266)::[])
in ((b), (_149_267), (p)))
end))
end))
in (

let _48_545 = (top_level_pat_as_args env p)
in (match (_48_545) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map (fun uu___167 -> (match (uu___167) with
| (FStar_Util.Inl (_48_548), _48_551) -> begin
(failwith "Impossible: top-level pattern must be an expression")
end
| (FStar_Util.Inr (e), _48_556) -> begin
e
end))))
in ((b), (exps), (p)))
end))))))))))


let decorate_pattern : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.pat  ->  FStar_Absyn_Syntax.exp Prims.list  ->  FStar_Absyn_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (let _149_286 = (FStar_All.pipe_left (fun _149_285 -> Some (_149_285)) (FStar_Util.Inr (t)))
in (FStar_Absyn_Syntax.withinfo q _149_286 p.FStar_Absyn_Syntax.p)))
in (

let e = (FStar_Absyn_Util.unmeta_exp e)
in (match (((p.FStar_Absyn_Syntax.v), (e.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Pat_constant (_48_572), FStar_Absyn_Syntax.Exp_constant (_48_575)) -> begin
(let _149_287 = (force_tk e)
in (pkg p.FStar_Absyn_Syntax.v _149_287))
end
| (FStar_Absyn_Syntax.Pat_var (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(

let _48_583 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _149_290 = (let _149_289 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _149_288 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _149_289 _149_288)))
in (failwith _149_290))
end else begin
()
end
in (

let _48_585 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _149_292 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _149_291 = (FStar_Tc_Normalize.typ_norm_to_string env y.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _149_292 _149_291)))
end else begin
()
end
in (

let s = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env y.FStar_Absyn_Syntax.sort)
in (

let x = (

let _48_588 = x
in {FStar_Absyn_Syntax.v = _48_588.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = _48_588.FStar_Absyn_Syntax.p})
in (let _149_293 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_var (x)) _149_293))))))
end
| (FStar_Absyn_Syntax.Pat_wild (x), FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(

let _48_596 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq x y) Prims.op_Negation) then begin
(let _149_296 = (let _149_295 = (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)
in (let _149_294 = (FStar_Absyn_Print.strBvd y.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _149_295 _149_294)))
in (failwith _149_296))
end else begin
()
end
in (

let x = (

let _48_598 = x
in (let _149_297 = (force_tk e)
in {FStar_Absyn_Syntax.v = _48_598.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _149_297; FStar_Absyn_Syntax.p = _48_598.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_wild (x)) x.FStar_Absyn_Syntax.sort)))
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _48_603), _48_607) -> begin
(

let x = (

let _48_609 = x
in (let _149_298 = (force_tk e)
in {FStar_Absyn_Syntax.v = _48_609.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _149_298; FStar_Absyn_Syntax.p = _48_609.FStar_Absyn_Syntax.p}))
in (pkg (FStar_Absyn_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, []), FStar_Absyn_Syntax.Exp_fvar (fv', _48_619)) -> begin
(

let _48_623 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _149_299 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (failwith _149_299))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_cons (((fv'), (q), ([])))) fv'.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_cons (fv, q, argpats), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv', _48_640); FStar_Absyn_Syntax.tk = _48_637; FStar_Absyn_Syntax.pos = _48_635; FStar_Absyn_Syntax.fvs = _48_633; FStar_Absyn_Syntax.uvs = _48_631}, args)) -> begin
(

let _48_648 = if (FStar_All.pipe_right (FStar_Absyn_Util.fvar_eq fv fv') Prims.op_Negation) then begin
(let _149_300 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Absyn_Syntax.v.FStar_Ident.str fv'.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (failwith _149_300))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _149_307 = (force_tk e)
in (pkg (FStar_Absyn_Syntax.Pat_cons (((fv), (q), ((FStar_List.rev matched_pats))))) _149_307))
end
| ((arg)::args, ((argpat, _48_664))::argpats) -> begin
(match (((arg), (argpat.FStar_Absyn_Syntax.v))) with
| ((FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit (_48_671))), FStar_Absyn_Syntax.Pat_dot_typ (_48_676)) -> begin
(

let x = (let _149_308 = (force_tk t)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _149_308))
in (

let q = (let _149_310 = (FStar_All.pipe_left (fun _149_309 -> Some (_149_309)) (FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_typ (((x), (t)))) _149_310 p.FStar_Absyn_Syntax.p))
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit (_48_684))), FStar_Absyn_Syntax.Pat_dot_term (_48_689)) -> begin
(

let x = (let _149_311 = (force_tk e)
in (FStar_Absyn_Util.gen_bvar_p p.FStar_Absyn_Syntax.p _149_311))
in (

let q = (let _149_313 = (FStar_All.pipe_left (fun _149_312 -> Some (_149_312)) (FStar_Util.Inr (x.FStar_Absyn_Syntax.sort)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_dot_term (((x), (e)))) _149_313 p.FStar_Absyn_Syntax.p))
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((FStar_Util.Inl (t), imp), _48_699) -> begin
(

let pat = (aux_t argpat t)
in (match_args ((((pat), ((as_imp imp))))::matched_pats) args argpats))
end
| ((FStar_Util.Inr (e), imp), _48_707) -> begin
(

let pat = (let _149_314 = (aux argpat e)
in ((_149_314), ((as_imp imp))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _48_711 -> begin
(let _149_317 = (let _149_316 = (FStar_Absyn_Print.pat_to_string p)
in (let _149_315 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _149_316 _149_315)))
in (failwith _149_317))
end))
in (match_args [] args argpats))))
end
| _48_713 -> begin
(let _149_322 = (let _149_321 = (FStar_Range.string_of_range qq.FStar_Absyn_Syntax.p)
in (let _149_320 = (FStar_Absyn_Print.pat_to_string qq)
in (let _149_319 = (let _149_318 = (FStar_All.pipe_right exps (FStar_List.map FStar_Absyn_Print.exp_to_string))
in (FStar_All.pipe_right _149_318 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _149_321 _149_320 _149_319))))
in (failwith _149_322))
end))))
and aux_t = (fun p t0 -> (

let pkg = (fun q k -> (let _149_330 = (FStar_All.pipe_left (fun _149_329 -> Some (_149_329)) (FStar_Util.Inl (k)))
in (FStar_Absyn_Syntax.withinfo q _149_330 p.FStar_Absyn_Syntax.p)))
in (

let t = (FStar_Absyn_Util.compress_typ t0)
in (match (((p.FStar_Absyn_Syntax.v), (t.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Pat_twild (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(

let _48_725 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _149_333 = (let _149_332 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _149_331 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _149_332 _149_331)))
in (failwith _149_333))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_twild (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_tvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(

let _48_732 = if (FStar_All.pipe_right (FStar_Absyn_Util.bvar_eq a b) Prims.op_Negation) then begin
(let _149_336 = (let _149_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _149_334 = (FStar_Absyn_Print.strBvd b.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _149_335 _149_334)))
in (failwith _149_336))
end else begin
()
end
in (pkg (FStar_Absyn_Syntax.Pat_tvar (b)) b.FStar_Absyn_Syntax.sort))
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _48_736), _48_740) -> begin
(

let k0 = (force_tk t0)
in (

let a = (

let _48_743 = a
in {FStar_Absyn_Syntax.v = _48_743.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k0; FStar_Absyn_Syntax.p = _48_743.FStar_Absyn_Syntax.p})
in (pkg (FStar_Absyn_Syntax.Pat_dot_typ (((a), (t)))) a.FStar_Absyn_Syntax.sort)))
end
| _48_747 -> begin
(let _149_340 = (let _149_339 = (FStar_Range.string_of_range p.FStar_Absyn_Syntax.p)
in (let _149_338 = (FStar_Absyn_Print.pat_to_string p)
in (let _149_337 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _149_339 _149_338 _149_337))))
in (failwith _149_340))
end))))
in (match (((p.FStar_Absyn_Syntax.v), (exps))) with
| (FStar_Absyn_Syntax.Pat_disj (ps), _48_751) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (let _149_342 = (FStar_All.pipe_left (fun _149_341 -> Some (_149_341)) (FStar_Util.Inr (FStar_Absyn_Syntax.tun)))
in (FStar_Absyn_Syntax.withinfo (FStar_Absyn_Syntax.Pat_disj (ps)) _149_342 p.FStar_Absyn_Syntax.p)))
end
| (_48_755, (e)::[]) -> begin
(aux p e)
end
| _48_760 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_exp : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.exp) = (fun pat -> (

let topt = (match (pat.FStar_Absyn_Syntax.sort) with
| Some (FStar_Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _48_767 -> begin
(failwith "top-level pattern should be decorated with a type")
end)
in (

let pkg = (fun f -> (f topt pat.FStar_Absyn_Syntax.p))
in (

let pat_as_arg = (fun _48_774 -> (match (_48_774) with
| (p, i) -> begin
(

let _48_777 = (decorated_pattern_as_either p)
in (match (_48_777) with
| (vars, te) -> begin
(let _149_362 = (let _149_361 = (FStar_Absyn_Syntax.as_implicit i)
in ((te), (_149_361)))
in ((vars), (_149_362)))
end))
end))
in (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_48_779) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _149_365 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in (([]), (_149_365)))
end
| (FStar_Absyn_Syntax.Pat_wild (x)) | (FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _149_368 = (FStar_All.pipe_right (FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in (((FStar_Util.Inr (x))::[]), (_149_368)))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(

let _48_793 = (let _149_369 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _149_369 FStar_List.unzip))
in (match (_48_793) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _149_375 = (let _149_374 = (let _149_373 = (let _149_372 = (FStar_Absyn_Syntax.mk_Exp_fvar ((fv), (q)) (Some (fv.FStar_Absyn_Syntax.sort)) fv.FStar_Absyn_Syntax.p)
in ((_149_372), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app' _149_373))
in (FStar_All.pipe_right _149_374 pkg))
in ((vars), (_149_375))))
end))
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * FStar_Absyn_Syntax.typ) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (a)) | (FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _149_377 = (FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.FStar_Absyn_Syntax.sort)) p.FStar_Absyn_Syntax.p)
in (((FStar_Util.Inl (a))::[]), (_149_377)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(([]), (t))
end
| _48_817 -> begin
(failwith "Expected a type pattern")
end))
and decorated_pattern_as_either : FStar_Absyn_Syntax.pat  ->  (FStar_Absyn_Syntax.either_var Prims.list * (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either) = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(

let _48_830 = (decorated_pattern_as_typ p)
in (match (_48_830) with
| (vars, t) -> begin
((vars), (FStar_Util.Inl (t)))
end))
end
| _48_832 -> begin
(

let _48_835 = (decorated_pattern_as_exp p)
in (match (_48_835) with
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
| FStar_Absyn_Syntax.Kind_arrow (bs, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _48_851; FStar_Absyn_Syntax.pos = _48_849; FStar_Absyn_Syntax.fvs = _48_847; FStar_Absyn_Syntax.uvs = _48_845}) -> begin
(

let _48_881 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _48_858 _48_862 -> (match (((_48_858), (_48_862))) with
| ((out, subst), (b, _48_861)) -> begin
(match (b) with
| FStar_Util.Inr (_48_864) -> begin
(failwith "impossible")
end
| FStar_Util.Inl (a) -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let arg = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let _149_385 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _149_385 Prims.fst))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _149_388 = (let _149_387 = (let _149_386 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _149_386 Prims.fst))
in ((bs), (_149_387)))
in (FStar_Absyn_Syntax.mk_Typ_lam _149_388 (Some (k)) r))
end
| _48_875 -> begin
(failwith "Impossible")
end)
in (

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (arg))))::subst
in (let _149_390 = (let _149_389 = (FStar_Absyn_Syntax.targ arg)
in (_149_389)::out)
in ((_149_390), (subst))))))
end)
end)) (([]), ([]))))
in (match (_48_881) with
| (args, _48_880) -> begin
(FStar_Absyn_Syntax.mk_Typ_app ((t), ((FStar_List.rev args))) (Some (FStar_Absyn_Syntax.ktype)) r)
end))
end
| _48_883 -> begin
(failwith "Impossible")
end)))))))


let extract_lb_annotation : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * Prims.bool) = (fun env t e -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(

let r = (FStar_Tc_Env.get_range env)
in (

let mk_t_binder = (fun scope a -> (match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(

let k = (let _149_401 = (FStar_Tc_Rel.new_kvar e.FStar_Absyn_Syntax.pos scope)
in (FStar_All.pipe_right _149_401 Prims.fst))
in (((

let _48_894 = a
in {FStar_Absyn_Syntax.v = _48_894.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _48_894.FStar_Absyn_Syntax.p})), (false)))
end
| _48_897 -> begin
((a), (true))
end))
in (

let mk_v_binder = (fun scope x -> (match (x.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(

let t = (let _149_406 = (FStar_Tc_Rel.new_tvar e.FStar_Absyn_Syntax.pos scope FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _149_406 Prims.fst))
in (match ((FStar_Absyn_Syntax.null_v_binder t)) with
| (FStar_Util.Inr (x), _48_906) -> begin
((x), (false))
end
| _48_909 -> begin
(failwith "impos")
end))
end
| _48_911 -> begin
(match ((FStar_Absyn_Syntax.null_v_binder x.FStar_Absyn_Syntax.sort)) with
| (FStar_Util.Inr (x), _48_915) -> begin
((x), (true))
end
| _48_918 -> begin
(failwith "impos")
end)
end))
in (

let rec aux = (fun vars e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _48_924)) -> begin
(aux vars e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _48_931) -> begin
((e), (t), (true))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let _48_960 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _48_941 b -> (match (_48_941) with
| (scope, bs, check) -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(

let _48_947 = (mk_t_binder scope a)
in (match (_48_947) with
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

let _48_955 = (mk_v_binder scope x)
in (match (_48_955) with
| (vb, c) -> begin
(

let b = ((FStar_Util.Inr (vb)), ((Prims.snd b)))
in ((scope), ((FStar_List.append bs ((b)::[]))), ((c || check))))
end))
end)
end)) ((vars), ([]), (false))))
in (match (_48_960) with
| (scope, bs, check) -> begin
(

let _48_964 = (aux scope body)
in (match (_48_964) with
| (body, res, check_res) -> begin
(

let c = (FStar_Absyn_Util.ml_comp res r)
in (

let t = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (

let _48_967 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _149_414 = (FStar_Range.string_of_range r)
in (let _149_413 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _149_414 _149_413)))
end else begin
()
end
in (

let e = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) None e.FStar_Absyn_Syntax.pos)
in ((e), (t), ((check_res || check)))))))
end))
end))
end
| _48_971 -> begin
(let _149_416 = (let _149_415 = (FStar_Tc_Rel.new_tvar r vars FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _149_415 Prims.fst))
in ((e), (_149_416), (false)))
end))
in (let _149_417 = (FStar_Tc_Env.t_binders env)
in (aux _149_417 e))))))
end
| _48_973 -> begin
((e), (t), (false))
end))


let destruct_comp : FStar_Absyn_Syntax.comp_typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun c -> (

let _48_990 = (match (c.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp), _48_983))::((FStar_Util.Inl (wlp), _48_978))::[] -> begin
((wp), (wlp))
end
| _48_987 -> begin
(let _149_422 = (let _149_421 = (let _149_420 = (FStar_List.map FStar_Absyn_Print.arg_to_string c.FStar_Absyn_Syntax.effect_args)
in (FStar_All.pipe_right _149_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Absyn_Syntax.effect_name.FStar_Ident.str _149_421))
in (failwith _149_422))
end)
in (match (_48_990) with
| (wp, wlp) -> begin
((c.FStar_Absyn_Syntax.result_typ), (wp), (wlp))
end)))


let lift_comp : FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.lident  ->  (FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ)  ->  FStar_Absyn_Syntax.comp_typ = (fun c m lift -> (

let _48_998 = (destruct_comp c)
in (match (_48_998) with
| (_48_995, wp, wlp) -> begin
(let _149_444 = (let _149_443 = (let _149_439 = (lift c.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _149_439))
in (let _149_442 = (let _149_441 = (let _149_440 = (lift c.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _149_440))
in (_149_441)::[])
in (_149_443)::_149_442))
in {FStar_Absyn_Syntax.effect_name = m; FStar_Absyn_Syntax.result_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _149_444; FStar_Absyn_Syntax.flags = []})
end)))


let norm_eff_name : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (match ((FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_48_1006, c) -> begin
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

let _48_1020 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))


let join_effects : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _48_1031 = (let _149_458 = (norm_eff_name env l1)
in (let _149_457 = (norm_eff_name env l2)
in (FStar_Tc_Env.join env _149_458 _149_457)))
in (match (_48_1031) with
| (m, _48_1028, _48_1030) -> begin
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

let _48_1043 = (FStar_Tc_Env.join env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)
in (match (_48_1043) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_Tc_Env.get_effect_decl env m)
in (

let _48_1049 = (FStar_Tc_Env.wp_signature env md.FStar_Absyn_Syntax.mname)
in (match (_48_1049) with
| (a, kwp) -> begin
(let _149_472 = (destruct_comp m1)
in (let _149_471 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_149_472), (_149_471))))
end)))))
end)))))


let is_pure_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid))))


let mk_comp : FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun md result wp wlp flags -> (let _149_495 = (let _149_494 = (let _149_493 = (FStar_Absyn_Syntax.targ wp)
in (let _149_492 = (let _149_491 = (FStar_Absyn_Syntax.targ wlp)
in (_149_491)::[])
in (_149_493)::_149_492))
in {FStar_Absyn_Syntax.effect_name = md.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.result_typ = result; FStar_Absyn_Syntax.effect_args = _149_494; FStar_Absyn_Syntax.flags = flags})
in (FStar_Absyn_Syntax.mk_Comp _149_495)))


let lcomp_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.lcomp = (fun c0 -> (

let c = (FStar_Absyn_Util.comp_to_comp_typ c0)
in {FStar_Absyn_Syntax.eff_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.res_typ = c.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.cflags = c.FStar_Absyn_Syntax.flags; FStar_Absyn_Syntax.comp = (fun _48_1063 -> (match (()) with
| () -> begin
c0
end))}))


let subst_lcomp : FStar_Absyn_Syntax.subst  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun subst lc -> (

let _48_1066 = lc
in (let _149_505 = (FStar_Absyn_Util.subst_typ subst lc.FStar_Absyn_Syntax.res_typ)
in {FStar_Absyn_Syntax.eff_name = _48_1066.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _149_505; FStar_Absyn_Syntax.cflags = _48_1066.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _48_1068 -> (match (()) with
| () -> begin
(let _149_504 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.subst_comp subst _149_504))
end))})))


let is_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _149_508 = (FStar_Absyn_Util.compress_typ t)
in _149_508.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_48_1071) -> begin
true
end
| _48_1074 -> begin
false
end))


let return_value : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp = (fun env t v -> (

let c = (match ((FStar_Tc_Env.effect_decl_opt env FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(

let _48_1083 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_48_1083) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (

let wp = (let _149_520 = (let _149_519 = (let _149_518 = (let _149_517 = (FStar_Absyn_Syntax.targ t)
in (let _149_516 = (let _149_515 = (FStar_Absyn_Syntax.varg v)
in (_149_515)::[])
in (_149_517)::_149_516))
in ((m.FStar_Absyn_Syntax.ret), (_149_518)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_519 (Some (k)) v.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env) _149_520))
in (

let wlp = wp
in (mk_comp m t wp wlp ((FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (

let _48_1088 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _149_523 = (FStar_Range.string_of_range v.FStar_Absyn_Syntax.pos)
in (let _149_522 = (FStar_Absyn_Print.exp_to_string v)
in (let _149_521 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _149_523 _149_522 _149_521))))
end else begin
()
end
in c)))


let bind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Absyn_Syntax.lcomp = (fun env e1opt lc1 _48_1095 -> (match (_48_1095) with
| (b, lc2) -> begin
(

let _48_1106 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (FStar_Tc_Env.Binding_var (x, _48_1099)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| _48_1104 -> begin
"??"
end)
in (let _149_533 = (FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _149_532 = (FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (FStar_Util.print3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _149_533 bstr _149_532))))
end else begin
()
end
in (

let bind_it = (fun _48_1109 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Absyn_Syntax.comp ())
in (

let c2 = (lc2.FStar_Absyn_Syntax.comp ())
in (

let try_simplify = (fun _48_1113 -> (match (()) with
| () -> begin
(

let aux = (fun _48_1115 -> (match (()) with
| () -> begin
if (FStar_Absyn_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_lid (_48_1118)) -> begin
Some (c2)
end
| Some (FStar_Tc_Env.Binding_var (_48_1122)) -> begin
if (FStar_Absyn_Util.is_ml_comp c2) then begin
Some (c2)
end else begin
None
end
end
| _48_1126 -> begin
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
| (Some (e), Some (FStar_Tc_Env.Binding_var (x, _48_1131))) -> begin
if ((FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((FStar_Absyn_Syntax.is_null_bvd x)))) then begin
(let _149_541 = (FStar_Absyn_Util.subst_comp ((FStar_Util.Inr (((x), (e))))::[]) c2)
in (FStar_All.pipe_left (fun _149_540 -> Some (_149_540)) _149_541))
end else begin
(aux ())
end
end
| _48_1137 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(

let _48_1155 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("bind"))) then begin
(let _149_545 = (match (b) with
| None -> begin
"None"
end
| Some (FStar_Tc_Env.Binding_var (x, _48_1143)) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Some (FStar_Tc_Env.Binding_lid (l, _48_1149)) -> begin
(FStar_Absyn_Print.sli l)
end
| _48_1154 -> begin
"Something else"
end)
in (let _149_544 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _149_543 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (let _149_542 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print4 "bind (%s) %s and %s simplified to %s\n" _149_545 _149_544 _149_543 _149_542)))))
end else begin
()
end
in c)
end
| None -> begin
(

let _48_1170 = (lift_and_destruct env c1 c2)
in (match (_48_1170) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _149_546 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_149_546)::[])
end
| Some (FStar_Tc_Env.Binding_var (x, t1)) -> begin
(let _149_547 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_149_547)::[])
end
| Some (FStar_Tc_Env.Binding_lid (l, t1)) -> begin
(let _149_548 = (FStar_Absyn_Syntax.null_v_binder t1)
in (_149_548)::[])
end
| _48_1183 -> begin
(failwith "Unexpected type-variable binding")
end)
in (

let mk_lam = (fun wp -> (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos))
in (

let wp_args = (let _149_563 = (FStar_Absyn_Syntax.targ t1)
in (let _149_562 = (let _149_561 = (FStar_Absyn_Syntax.targ t2)
in (let _149_560 = (let _149_559 = (FStar_Absyn_Syntax.targ wp1)
in (let _149_558 = (let _149_557 = (FStar_Absyn_Syntax.targ wlp1)
in (let _149_556 = (let _149_555 = (let _149_551 = (mk_lam wp2)
in (FStar_Absyn_Syntax.targ _149_551))
in (let _149_554 = (let _149_553 = (let _149_552 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _149_552))
in (_149_553)::[])
in (_149_555)::_149_554))
in (_149_557)::_149_556))
in (_149_559)::_149_558))
in (_149_561)::_149_560))
in (_149_563)::_149_562))
in (

let wlp_args = (let _149_571 = (FStar_Absyn_Syntax.targ t1)
in (let _149_570 = (let _149_569 = (FStar_Absyn_Syntax.targ t2)
in (let _149_568 = (let _149_567 = (FStar_Absyn_Syntax.targ wlp1)
in (let _149_566 = (let _149_565 = (let _149_564 = (mk_lam wlp2)
in (FStar_Absyn_Syntax.targ _149_564))
in (_149_565)::[])
in (_149_567)::_149_566))
in (_149_569)::_149_568))
in (_149_571)::_149_570))
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
in (let _149_572 = (join_lcomp env lc1 lc2)
in {FStar_Absyn_Syntax.eff_name = _149_572; FStar_Absyn_Syntax.res_typ = lc2.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_it})))
end))


let lift_formula : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env t mk_wp mk_wlp f -> (

let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (

let _48_1201 = (FStar_Tc_Env.wp_signature env md_pure.FStar_Absyn_Syntax.mname)
in (match (_48_1201) with
| (a, kwp) -> begin
(

let k = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::[]) kwp)
in (

let wp = (let _149_587 = (let _149_586 = (let _149_585 = (FStar_Absyn_Syntax.targ t)
in (let _149_584 = (let _149_583 = (FStar_Absyn_Syntax.targ f)
in (_149_583)::[])
in (_149_585)::_149_584))
in ((mk_wp), (_149_586)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_587 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _149_592 = (let _149_591 = (let _149_590 = (FStar_Absyn_Syntax.targ t)
in (let _149_589 = (let _149_588 = (FStar_Absyn_Syntax.targ f)
in (_149_588)::[])
in (_149_590)::_149_589))
in ((mk_wlp), (_149_591)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_592 (Some (k)) f.FStar_Absyn_Syntax.pos))
in (mk_comp md_pure FStar_Tc_Recheck.t_unit wp wlp []))))
end))))


let unlabel : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (((t), (None), (t.FStar_Absyn_Syntax.pos))))))


let refresh_comp_label : FStar_Tc_Env.env  ->  Prims.bool  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env b lc -> (

let refresh = (fun _48_1210 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in if (FStar_Absyn_Util.is_ml_comp c) then begin
c
end else begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_48_1213) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _48_1217 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _149_604 = (let _149_603 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _149_603))
in (FStar_Util.print1 "Refreshing label at %s\n" _149_604))
end else begin
()
end
in (

let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _48_1220 = if ((FStar_All.pipe_left Prims.op_Negation (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name c'.FStar_Absyn_Syntax.effect_name)) && (FStar_Tc_Env.debug env FStar_Options.Low)) then begin
(let _149_607 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _149_606 = (let _149_605 = (FStar_Absyn_Syntax.mk_Comp c')
in (FStar_All.pipe_left FStar_Absyn_Print.comp_typ_to_string _149_605))
in (FStar_Util.print2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _149_607 _149_606)))
end else begin
()
end
in (

let _48_1225 = (destruct_comp c')
in (match (_48_1225) with
| (t, wp, wlp) -> begin
(

let wp = (let _149_610 = (let _149_609 = (let _149_608 = (FStar_Tc_Env.get_range env)
in ((wp), (Some (b)), (_149_608)))
in FStar_Absyn_Syntax.Meta_refresh_label (_149_609))
in (FStar_Absyn_Syntax.mk_Typ_meta _149_610))
in (

let wlp = (let _149_613 = (let _149_612 = (let _149_611 = (FStar_Tc_Env.get_range env)
in ((wlp), (Some (b)), (_149_611)))
in FStar_Absyn_Syntax.Meta_refresh_label (_149_612))
in (FStar_Absyn_Syntax.mk_Typ_meta _149_613))
in (let _149_618 = (

let _48_1228 = c'
in (let _149_617 = (let _149_616 = (FStar_Absyn_Syntax.targ wp)
in (let _149_615 = (let _149_614 = (FStar_Absyn_Syntax.targ wlp)
in (_149_614)::[])
in (_149_616)::_149_615))
in {FStar_Absyn_Syntax.effect_name = _48_1228.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _48_1228.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _149_617; FStar_Absyn_Syntax.flags = c'.FStar_Absyn_Syntax.flags}))
in (FStar_Absyn_Syntax.mk_Comp _149_618))))
end)))))
end)
end)
end))
in (

let _48_1230 = lc
in {FStar_Absyn_Syntax.eff_name = _48_1230.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _48_1230.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _48_1230.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = refresh})))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun reason r f -> (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (reason), (r), (true))))))


let label_opt : FStar_Tc_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _149_642 = (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _149_642)) then begin
f
end else begin
(let _149_643 = (reason ())
in (label _149_643 r f))
end
end))


let label_guard : Prims.string  ->  FStar_Range.range  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun reason r g -> (match (g) with
| FStar_Tc_Rel.Trivial -> begin
g
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _149_650 = (label reason r f)
in FStar_Tc_Rel.NonTrivial (_149_650))
end))


let weaken_guard : FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Tc_Rel.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_Tc_Rel.NonTrivial (f1), FStar_Tc_Rel.NonTrivial (f2)) -> begin
(

let g = (FStar_Absyn_Util.mk_imp f1 f2)
in FStar_Tc_Rel.NonTrivial (g))
end
| _48_1257 -> begin
g2
end))


let weaken_precondition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_formula  ->  FStar_Absyn_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _48_1262 -> (match (()) with
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

let _48_1271 = (destruct_comp c)
in (match (_48_1271) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (let _149_669 = (let _149_668 = (let _149_667 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_666 = (let _149_665 = (FStar_Absyn_Syntax.targ f)
in (let _149_664 = (let _149_663 = (FStar_Absyn_Syntax.targ wp)
in (_149_663)::[])
in (_149_665)::_149_664))
in (_149_667)::_149_666))
in ((md.FStar_Absyn_Syntax.assume_p), (_149_668)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_669 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _149_676 = (let _149_675 = (let _149_674 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_673 = (let _149_672 = (FStar_Absyn_Syntax.targ f)
in (let _149_671 = (let _149_670 = (FStar_Absyn_Syntax.targ wlp)
in (_149_670)::[])
in (_149_672)::_149_671))
in (_149_674)::_149_673))
in ((md.FStar_Absyn_Syntax.assume_p), (_149_675)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_676 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Absyn_Syntax.flags))))
end)))
end
end))
end))
in (

let _48_1275 = lc
in {FStar_Absyn_Syntax.eff_name = _48_1275.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _48_1275.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _48_1275.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Tc_Rel.guard_t  ->  (FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun reason env e lc g0 -> if (FStar_Tc_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun uu___168 -> (match (uu___168) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _48_1286 -> begin
[]
end))))
in (

let strengthen = (fun _48_1289 -> (match (()) with
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

let xret = (let _149_698 = (FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.FStar_Absyn_Syntax.sort _149_698))
in (

let xbinding = FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))
in (

let lc = (let _149_701 = (lcomp_of_comp c)
in (let _149_700 = (let _149_699 = (lcomp_of_comp xret)
in ((Some (xbinding)), (_149_699)))
in (bind env (Some (e)) _149_701 _149_700)))
in (lc.FStar_Absyn_Syntax.comp ())))))
end else begin
c
end
in (

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _48_1304 = (destruct_comp c)
in (match (_48_1304) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let wp = (let _149_710 = (let _149_709 = (let _149_708 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_707 = (let _149_706 = (let _149_703 = (let _149_702 = (FStar_Tc_Env.get_range env)
in (label_opt env reason _149_702 f))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _149_703))
in (let _149_705 = (let _149_704 = (FStar_Absyn_Syntax.targ wp)
in (_149_704)::[])
in (_149_706)::_149_705))
in (_149_708)::_149_707))
in ((md.FStar_Absyn_Syntax.assert_p), (_149_709)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_710 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _149_717 = (let _149_716 = (let _149_715 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_714 = (let _149_713 = (FStar_Absyn_Syntax.targ f)
in (let _149_712 = (let _149_711 = (FStar_Absyn_Syntax.targ wlp)
in (_149_711)::[])
in (_149_713)::_149_712))
in (_149_715)::_149_714))
in ((md.FStar_Absyn_Syntax.assume_p), (_149_716)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_717 None wlp.FStar_Absyn_Syntax.pos))
in (

let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _149_721 = (

let _48_1309 = lc
in (let _149_720 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in (let _149_719 = if ((FStar_Absyn_Util.is_pure_lcomp lc) && (let _149_718 = (FStar_Absyn_Util.is_function_typ lc.FStar_Absyn_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _149_718))) then begin
flags
end else begin
[]
end
in {FStar_Absyn_Syntax.eff_name = _149_720; FStar_Absyn_Syntax.res_typ = _48_1309.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _149_719; FStar_Absyn_Syntax.comp = strengthen})))
in ((_149_721), ((

let _48_1311 = g0
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _48_1311.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _48_1311.FStar_Tc_Rel.implicits}))))))
end)


let add_equality_to_post_condition : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (

let x = (FStar_Absyn_Util.gen_bvar res_t)
in (

let y = (FStar_Absyn_Util.gen_bvar res_t)
in (

let _48_1321 = (let _149_729 = (FStar_Absyn_Util.bvar_to_exp x)
in (let _149_728 = (FStar_Absyn_Util.bvar_to_exp y)
in ((_149_729), (_149_728))))
in (match (_48_1321) with
| (xexp, yexp) -> begin
(

let yret = (let _149_734 = (let _149_733 = (let _149_732 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_731 = (let _149_730 = (FStar_Absyn_Syntax.varg yexp)
in (_149_730)::[])
in (_149_732)::_149_731))
in ((md_pure.FStar_Absyn_Syntax.ret), (_149_733)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_734 None res_t.FStar_Absyn_Syntax.pos))
in (

let x_eq_y_yret = (let _149_742 = (let _149_741 = (let _149_740 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_739 = (let _149_738 = (let _149_735 = (FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _149_735))
in (let _149_737 = (let _149_736 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ yret)
in (_149_736)::[])
in (_149_738)::_149_737))
in (_149_740)::_149_739))
in ((md_pure.FStar_Absyn_Syntax.assume_p), (_149_741)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_742 None res_t.FStar_Absyn_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (let _149_753 = (let _149_752 = (let _149_751 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_750 = (let _149_749 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_748 = (let _149_747 = (let _149_746 = (let _149_745 = (let _149_744 = (let _149_743 = (FStar_Absyn_Syntax.v_binder y)
in (_149_743)::[])
in ((_149_744), (x_eq_y_yret)))
in (FStar_Absyn_Syntax.mk_Typ_lam _149_745 None res_t.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _149_746))
in (_149_747)::[])
in (_149_749)::_149_748))
in (_149_751)::_149_750))
in ((md_pure.FStar_Absyn_Syntax.close_wp), (_149_752)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_753 None res_t.FStar_Absyn_Syntax.pos))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Absyn_Syntax.RETURN)::[]))
in (

let lc = (let _149_756 = (lcomp_of_comp comp)
in (let _149_755 = (let _149_754 = (lcomp_of_comp lc2)
in ((Some (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort))))), (_149_754)))
in (bind env None _149_756 _149_755)))
in (lc.FStar_Absyn_Syntax.comp ()))))))
end))))))


let ite : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.formula  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _48_1332 -> (match (()) with
| () -> begin
(

let _48_1348 = (let _149_768 = (lcomp_then.FStar_Absyn_Syntax.comp ())
in (let _149_767 = (lcomp_else.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _149_768 _149_767)))
in (match (_48_1348) with
| ((md, _48_1335, _48_1337), (res_t, wp_then, wlp_then), (_48_1344, wp_else, wlp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _149_788 = (let _149_786 = (let _149_785 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_784 = (let _149_783 = (FStar_Absyn_Syntax.targ g)
in (let _149_782 = (let _149_781 = (FStar_Absyn_Syntax.targ wp_t)
in (let _149_780 = (let _149_779 = (FStar_Absyn_Syntax.targ wp_e)
in (_149_779)::[])
in (_149_781)::_149_780))
in (_149_783)::_149_782))
in (_149_785)::_149_784))
in ((md.FStar_Absyn_Syntax.if_then_else), (_149_786)))
in (let _149_787 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _149_788 None _149_787))))
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

let wp = (let _149_795 = (let _149_794 = (let _149_793 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_792 = (let _149_791 = (FStar_Absyn_Syntax.targ wlp)
in (let _149_790 = (let _149_789 = (FStar_Absyn_Syntax.targ wp)
in (_149_789)::[])
in (_149_791)::_149_790))
in (_149_793)::_149_792))
in ((md.FStar_Absyn_Syntax.ite_wp), (_149_794)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_795 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _149_800 = (let _149_799 = (let _149_798 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_797 = (let _149_796 = (FStar_Absyn_Syntax.targ wlp)
in (_149_796)::[])
in (_149_798)::_149_797))
in ((md.FStar_Absyn_Syntax.ite_wlp), (_149_799)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_800 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _149_801 = (join_effects env lcomp_then.FStar_Absyn_Syntax.eff_name lcomp_else.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _149_801; FStar_Absyn_Syntax.res_typ = lcomp_then.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = comp})))


let bind_cases : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp) Prims.list  ->  FStar_Absyn_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (match (lcases) with
| [] -> begin
(failwith "Empty cases!")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun eff _48_1371 -> (match (_48_1371) with
| (_48_1369, lc) -> begin
(join_effects env eff lc.FStar_Absyn_Syntax.eff_name)
end)) (Prims.snd hd).FStar_Absyn_Syntax.eff_name tl)
end)
in (

let bind_cases = (fun _48_1374 -> (match (()) with
| () -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _149_831 = (let _149_829 = (let _149_828 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_827 = (let _149_826 = (FStar_Absyn_Syntax.targ g)
in (let _149_825 = (let _149_824 = (FStar_Absyn_Syntax.targ wp_t)
in (let _149_823 = (let _149_822 = (FStar_Absyn_Syntax.targ wp_e)
in (_149_822)::[])
in (_149_824)::_149_823))
in (_149_826)::_149_825))
in (_149_828)::_149_827))
in ((md.FStar_Absyn_Syntax.if_then_else), (_149_829)))
in (let _149_830 = (FStar_Range.union_ranges wp_t.FStar_Absyn_Syntax.pos wp_e.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _149_831 None _149_830))))
in (

let default_case = (

let post_k = (let _149_834 = (let _149_833 = (let _149_832 = (FStar_Absyn_Syntax.null_v_binder res_t)
in (_149_832)::[])
in ((_149_833), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _149_834 res_t.FStar_Absyn_Syntax.pos))
in (

let kwp = (let _149_837 = (let _149_836 = (let _149_835 = (FStar_Absyn_Syntax.null_t_binder post_k)
in (_149_835)::[])
in ((_149_836), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _149_837 res_t.FStar_Absyn_Syntax.pos))
in (

let post = (let _149_838 = (FStar_Absyn_Util.new_bvd None)
in (FStar_Absyn_Util.bvd_to_bvar_s _149_838 post_k))
in (

let wp = (let _149_845 = (let _149_844 = (let _149_839 = (FStar_Absyn_Syntax.t_binder post)
in (_149_839)::[])
in (let _149_843 = (let _149_842 = (let _149_840 = (FStar_Tc_Env.get_range env)
in (label FStar_Tc_Errors.exhaustiveness_check _149_840))
in (let _149_841 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left _149_842 _149_841)))
in ((_149_844), (_149_843))))
in (FStar_Absyn_Syntax.mk_Typ_lam _149_845 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _149_849 = (let _149_848 = (let _149_846 = (FStar_Absyn_Syntax.t_binder post)
in (_149_846)::[])
in (let _149_847 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((_149_848), (_149_847))))
in (FStar_Absyn_Syntax.mk_Typ_lam _149_849 (Some (kwp)) res_t.FStar_Absyn_Syntax.pos))
in (

let md = (FStar_Tc_Env.get_effect_decl env FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (

let comp = (FStar_List.fold_right (fun _48_1390 celse -> (match (_48_1390) with
| (g, cthen) -> begin
(

let _48_1408 = (let _149_852 = (cthen.FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _149_852 celse))
in (match (_48_1408) with
| ((md, _48_1394, _48_1396), (_48_1399, wp_then, wlp_then), (_48_1404, wp_else, wlp_else)) -> begin
(let _149_854 = (ifthenelse md res_t g wp_then wp_else)
in (let _149_853 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _149_854 _149_853 [])))
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

let _48_1416 = (destruct_comp comp)
in (match (_48_1416) with
| (_48_1413, wp, wlp) -> begin
(

let wp = (let _149_861 = (let _149_860 = (let _149_859 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_858 = (let _149_857 = (FStar_Absyn_Syntax.targ wlp)
in (let _149_856 = (let _149_855 = (FStar_Absyn_Syntax.targ wp)
in (_149_855)::[])
in (_149_857)::_149_856))
in (_149_859)::_149_858))
in ((md.FStar_Absyn_Syntax.ite_wp), (_149_860)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_861 None wp.FStar_Absyn_Syntax.pos))
in (

let wlp = (let _149_866 = (let _149_865 = (let _149_864 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_863 = (let _149_862 = (FStar_Absyn_Syntax.targ wlp)
in (_149_862)::[])
in (_149_864)::_149_863))
in ((md.FStar_Absyn_Syntax.ite_wlp), (_149_865)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_866 None wlp.FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Absyn_Syntax.eff_name = eff; FStar_Absyn_Syntax.res_typ = res_t; FStar_Absyn_Syntax.cflags = []; FStar_Absyn_Syntax.comp = bind_cases})))


let close_comp : FStar_Tc_Env.env  ->  FStar_Tc_Env.binding Prims.list  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env bindings lc -> (

let close = (fun _48_1423 -> (match (()) with
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

let bs = (let _149_885 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_149_885)::[])
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos)
in (let _149_892 = (let _149_891 = (let _149_890 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_889 = (let _149_888 = (FStar_Absyn_Syntax.targ t)
in (let _149_887 = (let _149_886 = (FStar_Absyn_Syntax.targ wp)
in (_149_886)::[])
in (_149_888)::_149_887))
in (_149_890)::_149_889))
in ((md.FStar_Absyn_Syntax.close_wp), (_149_891)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_892 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let bs = (let _149_893 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_149_893)::[])
in (

let wp = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (wp)) None wp.FStar_Absyn_Syntax.pos)
in (let _149_898 = (let _149_897 = (let _149_896 = (FStar_Absyn_Syntax.targ res_t)
in (let _149_895 = (let _149_894 = (FStar_Absyn_Syntax.targ wp)
in (_149_894)::[])
in (_149_896)::_149_895))
in ((md.FStar_Absyn_Syntax.close_wp_t), (_149_897)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_898 None wp0.FStar_Absyn_Syntax.pos))))
end
| FStar_Tc_Env.Binding_lid (l, t) -> begin
wp
end
| FStar_Tc_Env.Binding_sig (s) -> begin
(failwith "impos")
end)) bindings wp0))
in (

let c = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _48_1454 = (destruct_comp c)
in (match (_48_1454) with
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

let _48_1458 = lc
in {FStar_Absyn_Syntax.eff_name = _48_1458.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _48_1458.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = _48_1458.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _48_1464 -> (match (()) with
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

let ret = (let _149_907 = (return_value env t xexp)
in (FStar_All.pipe_left lcomp_of_comp _149_907))
in (

let eq_ret = (let _149_909 = (let _149_908 = (FStar_Absyn_Util.mk_eq t t xexp e)
in FStar_Tc_Rel.NonTrivial (_149_908))
in (weaken_precondition env ret _149_909))
in (let _149_912 = (let _149_911 = (let _149_910 = (lcomp_of_comp c)
in (bind env None _149_910 ((Some (FStar_Tc_Env.Binding_var (((x), (t))))), (eq_ret))))
in (_149_911.FStar_Absyn_Syntax.comp ()))
in (FStar_Absyn_Util.comp_set_flags _149_912 ((FStar_Absyn_Syntax.PARTIAL_RETURN)::(FStar_Absyn_Util.comp_flags c)))))))))))
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

let _48_1474 = lc
in {FStar_Absyn_Syntax.eff_name = _48_1474.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = _48_1474.FStar_Absyn_Syntax.res_typ; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = refine}))))


let check_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env e c c' -> (match ((FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _149_924 = (let _149_923 = (let _149_922 = (FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _149_921 = (FStar_Tc_Env.get_range env)
in ((_149_922), (_149_921))))
in FStar_Errors.Error (_149_923))
in (Prims.raise _149_924))
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

let rec aux = (fun subst uu___169 -> (match (uu___169) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_48_1498))))::rest -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _48_1506 = (new_implicit_tvar env k)
in (match (_48_1506) with
| (t, u) -> begin
(

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (

let _48_1512 = (aux subst rest)
in (match (_48_1512) with
| (args, bs, subst, us) -> begin
(let _149_938 = (let _149_937 = (let _149_936 = (FStar_All.pipe_left (fun _149_935 -> Some (_149_935)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_149_936)))
in (_149_937)::args)
in ((_149_938), (bs), (subst), ((FStar_Util.Inl (u))::us)))
end)))
end)))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_48_1517))))::rest -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _48_1525 = (new_implicit_evar env t)
in (match (_48_1525) with
| (v, u) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v))))::subst
in (

let _48_1531 = (aux subst rest)
in (match (_48_1531) with
| (args, bs, subst, us) -> begin
(let _149_942 = (let _149_941 = (let _149_940 = (FStar_All.pipe_left (fun _149_939 -> Some (_149_939)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (v)), (_149_940)))
in (_149_941)::args)
in ((_149_942), (bs), (subst), ((FStar_Util.Inr (u))::us)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), ([]))
end))
in (

let _48_1537 = (aux [] bs)
in (match (_48_1537) with
| (args, bs, subst, implicits) -> begin
(

let k = (FStar_Absyn_Syntax.mk_Kind_arrow' ((bs), (k)) t.FStar_Absyn_Syntax.pos)
in (

let k = (FStar_Absyn_Util.subst_kind subst k)
in (let _149_943 = (FStar_Absyn_Syntax.mk_Typ_app' ((t), (args)) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((_149_943), (k), (implicits)))))
end)))
end
| _48_1541 -> begin
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

let rec aux = (fun subst uu___170 -> (match (uu___170) with
| ((FStar_Util.Inl (a), _48_1557))::rest -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _48_1563 = (new_implicit_tvar env k)
in (match (_48_1563) with
| (t, u) -> begin
(

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (

let _48_1569 = (aux subst rest)
in (match (_48_1569) with
| (args, bs, subst, us) -> begin
(let _149_957 = (let _149_956 = (let _149_955 = (FStar_All.pipe_left (fun _149_954 -> Some (_149_954)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_149_955)))
in (_149_956)::args)
in ((_149_957), (bs), (subst), ((FStar_Util.Inl (u))::us)))
end)))
end)))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_48_1574))))::rest -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _48_1582 = (new_implicit_evar env t)
in (match (_48_1582) with
| (v, u) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v))))::subst
in (

let _48_1588 = (aux subst rest)
in (match (_48_1588) with
| (args, bs, subst, us) -> begin
(let _149_961 = (let _149_960 = (let _149_959 = (FStar_All.pipe_left (fun _149_958 -> Some (_149_958)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (v)), (_149_959)))
in (_149_960)::args)
in ((_149_961), (bs), (subst), ((FStar_Util.Inr (u))::us)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), ([]))
end))
in (

let _48_1594 = (aux [] bs)
in (match (_48_1594) with
| (args, bs, subst, implicits) -> begin
(

let mk_exp_app = (fun e args t -> (match (args) with
| [] -> begin
e
end
| _48_1601 -> begin
(FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) t e.FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(

let t = (FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
in (let _149_968 = (mk_exp_app e args (Some (t)))
in ((_149_968), (t), (implicits))))
end else begin
((e), (t), ([]))
end
end
| _48_1605 -> begin
(

let t = (let _149_969 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) (Some (FStar_Absyn_Syntax.ktype)) e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _149_969 (FStar_Absyn_Util.subst_typ subst)))
in (let _149_970 = (mk_exp_app e args (Some (t)))
in ((_149_970), (t), (implicits))))
end))
end)))
end
| _48_1608 -> begin
((e), (t), ([]))
end)
end))


let weaken_result_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_Tc_Env.use_eq then begin
(let _149_979 = (FStar_Tc_Rel.try_teq env lc.FStar_Absyn_Syntax.res_typ t)
in ((_149_979), (false)))
end else begin
(let _149_980 = (FStar_Tc_Rel.try_subtype env lc.FStar_Absyn_Syntax.res_typ t)
in ((_149_980), (true)))
end
in (match (gopt) with
| (None, _48_1616) -> begin
(FStar_Tc_Rel.subtype_fail env lc.FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(

let g = (FStar_Tc_Rel.simplify_guard env g)
in (match ((FStar_Tc_Rel.guard_form g)) with
| FStar_Tc_Rel.Trivial -> begin
(

let lc = (

let _48_1624 = lc
in {FStar_Absyn_Syntax.eff_name = _48_1624.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _48_1624.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _48_1624.FStar_Absyn_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(

let g = (

let _48_1629 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _48_1629.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _48_1629.FStar_Tc_Rel.implicits})
in (

let strengthen = (fun _48_1633 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let _48_1635 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _149_984 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _149_983 = (FStar_Tc_Normalize.typ_norm_to_string env f)
in (FStar_Util.print2 "Strengthening %s with guard %s\n" _149_984 _149_983)))
end else begin
()
end
in (

let ct = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let _48_1640 = (FStar_Tc_Env.wp_signature env FStar_Absyn_Const.effect_PURE_lid)
in (match (_48_1640) with
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

let wp = (let _149_989 = (let _149_988 = (let _149_987 = (FStar_Absyn_Syntax.targ t)
in (let _149_986 = (let _149_985 = (FStar_Absyn_Syntax.varg xexp)
in (_149_985)::[])
in (_149_987)::_149_986))
in ((md.FStar_Absyn_Syntax.ret), (_149_988)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_989 (Some (k)) xexp.FStar_Absyn_Syntax.pos))
in (

let cret = (let _149_990 = (mk_comp md t wp wp ((FStar_Absyn_Syntax.RETURN)::[]))
in (FStar_All.pipe_left lcomp_of_comp _149_990))
in (

let guard = if apply_guard then begin
(let _149_993 = (let _149_992 = (let _149_991 = (FStar_Absyn_Syntax.varg xexp)
in (_149_991)::[])
in ((f), (_149_992)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_993 (Some (FStar_Absyn_Syntax.ktype)) f.FStar_Absyn_Syntax.pos))
end else begin
f
end
in (

let _48_1650 = (let _149_1001 = (FStar_All.pipe_left (fun _149_998 -> Some (_149_998)) (FStar_Tc_Errors.subtyping_failed env lc.FStar_Absyn_Syntax.res_typ t))
in (let _149_1000 = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let _149_999 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _149_1001 _149_1000 e cret _149_999))))
in (match (_48_1650) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let c = (let _149_1003 = (let _149_1002 = (FStar_Absyn_Syntax.mk_Comp ct)
in (FStar_All.pipe_left lcomp_of_comp _149_1002))
in (bind env (Some (e)) _149_1003 ((Some (FStar_Tc_Env.Binding_var (((x), (lc.FStar_Absyn_Syntax.res_typ))))), (eq_ret))))
in (

let c = (c.FStar_Absyn_Syntax.comp ())
in (

let _48_1653 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.Extreme) then begin
(let _149_1004 = (FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _149_1004))
end else begin
()
end
in c)))
end)))))))))
end)))))
end))
in (

let flags = (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_List.collect (fun uu___171 -> (match (uu___171) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _48_1659 -> begin
[]
end))))
in (

let lc = (

let _48_1661 = lc
in (let _149_1006 = (norm_eff_name env lc.FStar_Absyn_Syntax.eff_name)
in {FStar_Absyn_Syntax.eff_name = _149_1006; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = flags; FStar_Absyn_Syntax.comp = strengthen}))
in ((e), (lc), (g))))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvt = (FStar_Absyn_Util.uvars_in_typ t)
in if ((((FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_e) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_t)) + (FStar_Util.set_count uvt.FStar_Absyn_Syntax.uvars_k)) > (Prims.parse_int "0")) then begin
(

let ue = (let _149_1011 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_e)
in (FStar_List.map FStar_Absyn_Print.uvar_e_to_string _149_1011))
in (

let ut = (let _149_1012 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_t)
in (FStar_List.map FStar_Absyn_Print.uvar_t_to_string _149_1012))
in (

let uk = (let _149_1013 = (FStar_Util.set_elements uvt.FStar_Absyn_Syntax.uvars_k)
in (FStar_List.map FStar_Absyn_Print.uvar_k_to_string _149_1013))
in (

let union = (FStar_String.concat "," (FStar_List.append ue (FStar_List.append ut uk)))
in (

let hide_uvar_nums_saved = (FStar_Options.hide_uvar_nums ())
in (

let print_implicits_saved = (FStar_Options.print_implicits ())
in (

let _48_1673 = (FStar_Options.push ())
in (

let _48_1675 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _48_1677 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _48_1679 = (let _149_1015 = (let _149_1014 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _149_1014))
in (FStar_Errors.report r _149_1015))
in (FStar_Options.pop ())))))))))))
end else begin
()
end))


let gen : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list Prims.option = (fun verify env ecs -> if (let _149_1023 = (FStar_Util.for_all (fun _48_1687 -> (match (_48_1687) with
| (_48_1685, c) -> begin
(FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _149_1023)) then begin
None
end else begin
(

let norm = (fun c -> (

let _48_1690 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _149_1026 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s" _149_1026))
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

let _48_1694 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _149_1027 = (FStar_Absyn_Print.comp_typ_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s" _149_1027))
end else begin
()
end
in c)))))
in (

let env_uvars = (FStar_Tc_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _149_1030 = (FStar_Util.set_difference uvs env_uvars.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _149_1030 FStar_Util.set_elements)))
in (

let should_gen = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, _48_1703) -> begin
if (FStar_All.pipe_right bs (FStar_Util.for_some (fun uu___172 -> (match (uu___172) with
| (FStar_Util.Inl (_48_1708), _48_1711) -> begin
true
end
| _48_1714 -> begin
false
end)))) then begin
false
end else begin
true
end
end
| _48_1716 -> begin
true
end))
in (

let uvars = (FStar_All.pipe_right ecs (FStar_List.map (fun _48_1719 -> (match (_48_1719) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) FStar_Absyn_Util.compress_typ)
in if (let _149_1035 = (should_gen t)
in (FStar_All.pipe_left Prims.op_Negation _149_1035)) then begin
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

let _48_1735 = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && verify) && (let _149_1036 = (FStar_Absyn_Util.is_total_comp c)
in (FStar_All.pipe_left Prims.op_Negation _149_1036))) then begin
(

let _48_1731 = (destruct_comp ct)
in (match (_48_1731) with
| (_48_1727, wp, _48_1730) -> begin
(

let binder = (let _149_1037 = (FStar_Absyn_Syntax.null_v_binder t)
in (_149_1037)::[])
in (

let post = (let _149_1041 = (let _149_1038 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((binder), (_149_1038)))
in (let _149_1040 = (let _149_1039 = (FStar_Absyn_Syntax.mk_Kind_arrow ((binder), (FStar_Absyn_Syntax.ktype)) t.FStar_Absyn_Syntax.pos)
in Some (_149_1039))
in (FStar_Absyn_Syntax.mk_Typ_lam _149_1041 _149_1040 t.FStar_Absyn_Syntax.pos)))
in (

let vc = (let _149_1048 = (let _149_1047 = (let _149_1046 = (let _149_1045 = (let _149_1044 = (FStar_Absyn_Syntax.targ post)
in (_149_1044)::[])
in ((wp), (_149_1045)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_1046))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn wp.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _149_1047))
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Beta)::[]) env _149_1048))
in (let _149_1049 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _149_1049)))))
end))
end else begin
()
end
in ((uvs), (e), (c))))))))
end)
end))))
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _48_1741 -> (match (_48_1741) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _48_1744 -> (match (_48_1744) with
| (u, k) -> begin
(

let a = (match ((FStar_Unionfind.find u)) with
| (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) | (FStar_Absyn_Syntax.Fixed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _})) -> begin
(FStar_Absyn_Util.bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)
end
| FStar_Absyn_Syntax.Fixed (_48_1782) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| _48_1785 -> begin
(

let a = (let _149_1054 = (let _149_1053 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left (fun _149_1052 -> Some (_149_1052)) _149_1053))
in (FStar_Absyn_Util.new_bvd _149_1054))
in (

let t = (let _149_1055 = (FStar_Absyn_Util.bvd_to_typ a FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.close_for_kind _149_1055 k))
in (

let _48_1788 = (FStar_Absyn_Util.unchecked_unify u t)
in (FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.ktype))))
end)
in (let _149_1057 = (FStar_All.pipe_left (fun _149_1056 -> Some (_149_1056)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (a)), (_149_1057))))
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
| _48_1799 -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((tvars), (c)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
end)
end)
in (

let e = (match (tvars) with
| [] -> begin
e
end
| _48_1803 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs' ((tvars), (e)) (Some (t)) e.FStar_Absyn_Syntax.pos)
end)
in (let _149_1058 = (FStar_Absyn_Syntax.mk_Total t)
in ((e), (_149_1058))))))
end))))
in Some (ecs)))))))
end)


let generalize : Prims.bool  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list  ->  (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp) Prims.list = (fun verify env lecs -> (

let _48_1815 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _149_1067 = (let _149_1066 = (FStar_List.map (fun _48_1814 -> (match (_48_1814) with
| (lb, _48_1811, _48_1813) -> begin
(FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _149_1066 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s" _149_1067))
end else begin
()
end
in (match ((let _149_1069 = (FStar_All.pipe_right lecs (FStar_List.map (fun _48_1821 -> (match (_48_1821) with
| (_48_1818, e, c) -> begin
((e), (c))
end))))
in (gen verify env _149_1069))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _48_1830 _48_1833 -> (match (((_48_1830), (_48_1833))) with
| ((l, _48_1827, _48_1829), (e, c)) -> begin
(

let _48_1834 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _149_1074 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _149_1073 = (FStar_Absyn_Print.lbname_to_string l)
in (let _149_1072 = (FStar_Absyn_Print.typ_to_string (FStar_Absyn_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s" _149_1074 _149_1073 _149_1072))))
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
| _48_1841 -> begin
false
end))
in (match ((FStar_All.pipe_right g.FStar_Tc_Rel.implicits (FStar_List.tryFind (fun uu___173 -> (match (uu___173) with
| FStar_Util.Inl (u) -> begin
false
end
| FStar_Util.Inr (u, _48_1847) -> begin
(unresolved u)
end))))) with
| Some (FStar_Util.Inr (_48_1851, r)) -> begin
(Prims.raise (FStar_Errors.Error ((("Unresolved implicit argument"), (r)))))
end
| _48_1857 -> begin
()
end)))


let check_top_level : FStar_Tc_Env.env  ->  FStar_Tc_Rel.guard_t  ->  FStar_Absyn_Syntax.lcomp  ->  (Prims.bool * FStar_Absyn_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _48_1863 = (FStar_Tc_Rel.try_discharge_guard env g)
in (

let _48_1865 = (check_unresolved_implicits g)
in (FStar_Absyn_Util.is_pure_lcomp lc))))
in (

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in if (FStar_Absyn_Util.is_total_lcomp lc) then begin
(let _149_1089 = (discharge g)
in (let _149_1088 = (lc.FStar_Absyn_Syntax.comp ())
in ((_149_1089), (_149_1088))))
end else begin
(

let c = (lc.FStar_Absyn_Syntax.comp ())
in (

let steps = (FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.DeltaComp)::[]
in (

let c = (let _149_1090 = (FStar_Tc_Normalize.norm_comp steps env c)
in (FStar_All.pipe_right _149_1090 FStar_Absyn_Util.comp_to_comp_typ))
in (

let md = (FStar_Tc_Env.get_effect_decl env c.FStar_Absyn_Syntax.effect_name)
in (

let _48_1876 = (destruct_comp c)
in (match (_48_1876) with
| (t, wp, _48_1875) -> begin
(

let vc = (let _149_1096 = (let _149_1094 = (let _149_1093 = (FStar_Absyn_Syntax.targ t)
in (let _149_1092 = (let _149_1091 = (FStar_Absyn_Syntax.targ wp)
in (_149_1091)::[])
in (_149_1093)::_149_1092))
in ((md.FStar_Absyn_Syntax.trivial), (_149_1094)))
in (let _149_1095 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.mk_Typ_app _149_1096 (Some (FStar_Absyn_Syntax.ktype)) _149_1095)))
in (

let g = (let _149_1097 = (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula (FStar_Tc_Rel.NonTrivial (vc)))
in (FStar_Tc_Rel.conj_guard g _149_1097))
in (let _149_1099 = (discharge g)
in (let _149_1098 = (FStar_Absyn_Syntax.mk_Comp c)
in ((_149_1099), (_149_1098))))))
end))))))
end)))


let short_circuit_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.args  ->  (FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.exp) Prims.option = (fun head seen_args -> (

let short_bin_op_e = (fun f uu___174 -> (match (uu___174) with
| [] -> begin
None
end
| ((FStar_Util.Inr (fst), _48_1888))::[] -> begin
(let _149_1118 = (f fst)
in (FStar_All.pipe_right _149_1118 (fun _149_1117 -> Some (_149_1117))))
end
| _48_1892 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let table = (

let op_and_e = (fun e -> (let _149_1124 = (FStar_Absyn_Util.b2t e)
in ((_149_1124), (FStar_Absyn_Const.exp_false_bool))))
in (

let op_or_e = (fun e -> (let _149_1128 = (let _149_1127 = (FStar_Absyn_Util.b2t e)
in (FStar_Absyn_Util.mk_neg _149_1127))
in ((_149_1128), (FStar_Absyn_Const.exp_true_bool))))
in (((FStar_Absyn_Const.op_And), ((short_bin_op_e op_and_e))))::(((FStar_Absyn_Const.op_Or), ((short_bin_op_e op_or_e))))::[]))
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _48_1900) -> begin
(

let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _48_1906 -> (match (_48_1906) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _149_1146 = (mk seen_args)
in Some (_149_1146))
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
| _48_1911 -> begin
None
end))))


let short_circuit_typ : (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either  ->  FStar_Absyn_Syntax.args  ->  FStar_Tc_Rel.guard_formula = (fun head seen_args -> (

let short_bin_op_t = (fun f uu___175 -> (match (uu___175) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| ((FStar_Util.Inl (fst), _48_1921))::[] -> begin
(f fst)
end
| _48_1925 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_t = (fun t -> (let _149_1167 = (unlabel t)
in (FStar_All.pipe_right _149_1167 (fun _149_1166 -> FStar_Tc_Rel.NonTrivial (_149_1166)))))
in (

let op_or_t = (fun t -> (let _149_1172 = (let _149_1170 = (unlabel t)
in (FStar_All.pipe_right _149_1170 FStar_Absyn_Util.mk_neg))
in (FStar_All.pipe_right _149_1172 (fun _149_1171 -> FStar_Tc_Rel.NonTrivial (_149_1171)))))
in (

let op_imp_t = (fun t -> (let _149_1176 = (unlabel t)
in (FStar_All.pipe_right _149_1176 (fun _149_1175 -> FStar_Tc_Rel.NonTrivial (_149_1175)))))
in (

let short_op_ite = (fun uu___176 -> (match (uu___176) with
| [] -> begin
FStar_Tc_Rel.Trivial
end
| ((FStar_Util.Inl (guard), _48_1937))::[] -> begin
FStar_Tc_Rel.NonTrivial (guard)
end
| (_then)::((FStar_Util.Inl (guard), _48_1943))::[] -> begin
(let _149_1180 = (FStar_Absyn_Util.mk_neg guard)
in (FStar_All.pipe_right _149_1180 (fun _149_1179 -> FStar_Tc_Rel.NonTrivial (_149_1179))))
end
| _48_1948 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Absyn_Const.and_lid), ((short_bin_op_t op_and_t))))::(((FStar_Absyn_Const.or_lid), ((short_bin_op_t op_or_t))))::(((FStar_Absyn_Const.imp_lid), ((short_bin_op_t op_imp_t))))::(((FStar_Absyn_Const.ite_lid), (short_op_ite)))::[]
in (match (head) with
| FStar_Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
FStar_Tc_Rel.Trivial
end
| Some (g, _48_1956) -> begin
FStar_Tc_Rel.NonTrivial (g)
end)
end
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _48_1966; FStar_Absyn_Syntax.pos = _48_1964; FStar_Absyn_Syntax.fvs = _48_1962; FStar_Absyn_Syntax.uvs = _48_1960}) -> begin
(

let lid = fv.FStar_Absyn_Syntax.v
in (match ((FStar_Util.find_map table (fun _48_1974 -> (match (_48_1974) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _149_1207 = (mk seen_args)
in Some (_149_1207))
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
| _48_1979 -> begin
FStar_Tc_Rel.Trivial
end))))))))


let pure_or_ghost_pre_and_post : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Absyn_Syntax.typ Prims.option * FStar_Absyn_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Absyn_Util.gen_bvar res_t)
in (let _149_1221 = (let _149_1220 = (let _149_1219 = (let _149_1218 = (let _149_1217 = (let _149_1216 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_Absyn_Syntax.varg _149_1216))
in (_149_1217)::[])
in ((ens), (_149_1218)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_1219 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))
in ((x), (_149_1220)))
in (FStar_Absyn_Syntax.mk_Typ_refine _149_1221 (Some (FStar_Absyn_Syntax.mk_Kind_type)) res_t.FStar_Absyn_Syntax.pos))))
in (

let norm = (fun t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Delta)::(FStar_Tc_Normalize.Unlabel)::[]) env t))
in if (FStar_Absyn_Util.is_tot_or_gtot_comp comp) then begin
((None), ((FStar_Absyn_Util.comp_result comp)))
end else begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_48_1989) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (req), _48_2004))::((FStar_Util.Inl (ens), _48_1998))::_48_1994 -> begin
(let _149_1227 = (let _149_1224 = (norm req)
in Some (_149_1224))
in (let _149_1226 = (let _149_1225 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _149_1225))
in ((_149_1227), (_149_1226))))
end
| _48_2008 -> begin
(failwith "Impossible")
end)
end else begin
(

let comp = (FStar_Tc_Normalize.norm_comp ((FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_48_2011) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp), _48_2026))::((FStar_Util.Inl (wlp), _48_2020))::_48_2016 -> begin
(

let _48_2038 = (match ((let _149_1229 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_requires)
in (let _149_1228 = (FStar_Tc_Env.lookup_typ_abbrev env FStar_Absyn_Const.as_ensures)
in ((_149_1229), (_149_1228))))) with
| (Some (x), Some (y)) -> begin
((x), (y))
end
| _48_2035 -> begin
(failwith "Impossible")
end)
in (match (_48_2038) with
| (as_req, as_ens) -> begin
(

let req = (let _149_1236 = (let _149_1235 = (let _149_1234 = (let _149_1231 = (FStar_All.pipe_left (fun _149_1230 -> Some (_149_1230)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ)), (_149_1231)))
in (let _149_1233 = (let _149_1232 = (FStar_Absyn_Syntax.targ wp)
in (_149_1232)::[])
in (_149_1234)::_149_1233))
in ((as_req), (_149_1235)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_1236 (Some (FStar_Absyn_Syntax.mk_Kind_type)) ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (

let ens = (let _149_1243 = (let _149_1242 = (let _149_1241 = (let _149_1238 = (FStar_All.pipe_left (fun _149_1237 -> Some (_149_1237)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (ct.FStar_Absyn_Syntax.result_typ)), (_149_1238)))
in (let _149_1240 = (let _149_1239 = (FStar_Absyn_Syntax.targ wlp)
in (_149_1239)::[])
in (_149_1241)::_149_1240))
in ((as_ens), (_149_1242)))
in (FStar_Absyn_Syntax.mk_Typ_app _149_1243 None ct.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _149_1247 = (let _149_1244 = (norm req)
in Some (_149_1244))
in (let _149_1246 = (let _149_1245 = (mk_post_type ct.FStar_Absyn_Syntax.result_typ ens)
in (norm _149_1245))
in ((_149_1247), (_149_1246))))))
end))
end
| _48_2042 -> begin
(failwith "Impossible")
end)
end))
end
end)
end)))




