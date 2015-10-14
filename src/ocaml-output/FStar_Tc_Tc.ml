
open Prims
let syn' = (fun env k -> (let _104_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _104_11 (Some (k)))))

let log = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _104_14 = (FStar_Tc_Env.current_module env)
in (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.prims_lid _104_14))))))

let rng = (fun env -> (FStar_Tc_Env.get_range env))

let instantiate_both = (fun env -> (let _39_24 = env
in {FStar_Tc_Env.solver = _39_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _39_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_24.FStar_Tc_Env.default_effects}))

let no_inst = (fun env -> (let _39_27 = env
in {FStar_Tc_Env.solver = _39_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _39_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_27.FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = (match ((tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
v.FStar_Absyn_Syntax.pos
end
| false -> begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end)
in (let _104_34 = (let _104_33 = (let _104_32 = (let _104_27 = (let _104_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _104_25 -> FStar_Util.Inl (_104_25)) _104_26))
in (_104_27, Some (FStar_Absyn_Syntax.Implicit)))
in (let _104_31 = (let _104_30 = (FStar_Absyn_Syntax.varg v)
in (let _104_29 = (let _104_28 = (FStar_Absyn_Syntax.varg tl)
in (_104_28)::[])
in (_104_30)::_104_29))
in (_104_32)::_104_31))
in (FStar_Absyn_Util.lex_pair, _104_33))
in (FStar_Absyn_Syntax.mk_Exp_app _104_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

let is_eq = (fun _39_1 -> (match (_39_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _39_37 -> begin
false
end))

let steps = (fun env -> (match ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) with
| true -> begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end
| false -> begin
(FStar_Tc_Normalize.Beta)::[]
end))

let whnf = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))

let norm_t = (fun env t -> (let _104_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _104_47 env t)))

let norm_k = (fun env k -> (let _104_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _104_52 env k)))

let norm_c = (fun env c -> (let _104_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _104_57 env c)))

let fxv_check = (fun head env kt fvs -> (let rec aux = (fun norm kt -> (match ((FStar_Util.set_is_empty fvs)) with
| true -> begin
()
end
| false -> begin
(let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _104_76 = (match (norm) with
| true -> begin
(norm_k env k)
end
| false -> begin
k
end)
in (FStar_Absyn_Util.freevars_kind _104_76))
end
| FStar_Util.Inr (t) -> begin
(let _104_77 = (match (norm) with
| true -> begin
(norm_t env t)
end
| false -> begin
t
end)
in (FStar_Absyn_Util.freevars_typ _104_77))
end)
in (let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in (match ((FStar_Util.set_is_empty a)) with
| true -> begin
()
end
| false -> begin
(match ((not (norm))) with
| true -> begin
(aux true kt)
end
| false -> begin
(let fail = (fun _39_61 -> (match (()) with
| () -> begin
(let escaping = (let _104_82 = (let _104_81 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _104_81 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _104_82 (FStar_String.concat ", ")))
in (let msg = (match (((FStar_Util.set_count a) > 1)) with
| true -> begin
(let _104_83 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _104_83))
end
| false -> begin
(let _104_84 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _104_84))
end)
in (let _104_87 = (let _104_86 = (let _104_85 = (FStar_Tc_Env.get_range env)
in (msg, _104_85))
in FStar_Absyn_Syntax.Error (_104_86))
in (Prims.raise _104_87))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _39_71 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _39_78 -> begin
(fail ())
end))
end))
end)
end)))
end))
in (aux false kt)))

let maybe_push_binding = (fun env b -> (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
env
end
| false -> begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let b = FStar_Tc_Env.Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
in (FStar_Tc_Env.push_local_binding env b))
end
| FStar_Util.Inr (x) -> begin
(let b = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (FStar_Tc_Env.push_local_binding env b))
end)
end))

let maybe_make_subst = (fun _39_2 -> (match (_39_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _39_99 -> begin
[]
end))

let maybe_alpha_subst = (fun s b1 b2 -> (match ((FStar_Absyn_Syntax.is_null_binder b1)) with
| true -> begin
s
end
| false -> begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(match ((FStar_Absyn_Util.bvar_eq a b)) with
| true -> begin
s
end
| false -> begin
(let _104_98 = (let _104_97 = (let _104_96 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _104_96))
in FStar_Util.Inl (_104_97))
in (_104_98)::s)
end)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(match ((FStar_Absyn_Util.bvar_eq x y)) with
| true -> begin
s
end
| false -> begin
(let _104_101 = (let _104_100 = (let _104_99 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _104_99))
in FStar_Util.Inr (_104_100))
in (_104_101)::s)
end)
end
| _39_114 -> begin
(FStar_All.failwith "impossible")
end)
end))

let maybe_extend_subst = (fun s b v -> (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
s
end
| false -> begin
(match (((Prims.fst b), (Prims.fst v))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::s
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::s
end
| _39_129 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let set_lcomp_result = (fun lc t -> (let _39_132 = lc
in {FStar_Absyn_Syntax.eff_name = _39_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _39_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _39_134 -> (match (()) with
| () -> begin
(let _104_110 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _104_110 t))
end))}))

let value_check_expected_typ = (fun env e tlc -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _104_117 = (match ((not ((FStar_Absyn_Util.is_pure_or_ghost_function t)))) with
| true -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| false -> begin
(FStar_Tc_Util.return_value env t e)
end)
in (FStar_Tc_Util.lcomp_of_comp _104_117))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Absyn_Syntax.res_typ
in (let _39_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _39_147 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_119 = (FStar_Absyn_Print.typ_to_string t)
in (let _104_118 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.fprint2 "Computed return type %s; expected type %s\n" _104_119 _104_118)))
end
| false -> begin
()
end)
in (let _39_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_39_151) with
| (e, g) -> begin
(let _39_154 = (let _104_125 = (FStar_All.pipe_left (fun _104_124 -> Some (_104_124)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _104_125 env e lc g))
in (match (_39_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_39_158) with
| (e, lc, g) -> begin
(let _39_159 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_126 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.fprint1 "Return comp type is %s\n" _104_126))
end
| false -> begin
()
end)
in (e, lc, g))
end)))))

let comp_check_expected_typ = (fun env e lc -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t) -> begin
(FStar_Tc_Util.weaken_result_typ env e lc t)
end))

let check_expected_effect = (fun env copt _39_171 -> (match (_39_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_39_173) -> begin
copt
end
| None -> begin
(let c1 = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let md = (FStar_Tc_Env.get_effect_decl env c1.FStar_Absyn_Syntax.effect_name)
in (match ((FStar_Tc_Env.default_effect env md.FStar_Absyn_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(let flags = (match ((FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_ML_lid)) with
| true -> begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end
| false -> begin
[]
end)
end)
in (let def = (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = flags})
in Some (def)))
end)))
end)
in (match (expected_c_opt) with
| None -> begin
(let _104_139 = (norm_c env c)
in (e, _104_139, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _39_187 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_142 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _104_141 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _104_140 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.fprint3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _104_142 _104_141 _104_140))))
end
| false -> begin
()
end)
in (let c = (norm_c env c)
in (let expected_c' = (let _104_143 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _104_143))
in (let _39_195 = (let _104_144 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _104_144))
in (match (_39_195) with
| (e, _39_193, g) -> begin
(let _39_196 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_146 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _104_145 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.fprint2 "(%s) DONE check_expected_effect; guard is: %s\n" _104_146 _104_145)))
end
| false -> begin
()
end)
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun env _39_202 -> (match (_39_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _104_152 = (let _104_151 = (let _104_150 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _104_149 = (FStar_Tc_Env.get_range env)
in (_104_150, _104_149)))
in FStar_Absyn_Syntax.Error (_104_151))
in (Prims.raise _104_152))
end)
end))

let binding_of_lb = (fun x t -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
FStar_Tc_Env.Binding_var ((bvd, t))
end
| FStar_Util.Inr (lid) -> begin
FStar_Tc_Env.Binding_lid ((lid, t))
end))

let print_expected_ty = (fun env -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _104_159 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint1 "Expected type is %s" _104_159))
end))

let with_implicits = (fun imps _39_220 -> (match (_39_220) with
| (e, l, g) -> begin
(e, l, (let _39_221 = g
in {FStar_Tc_Rel.guard_f = _39_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _39_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun u g -> (let _39_225 = g
in {FStar_Tc_Rel.guard_f = _39_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _39_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

let rec tc_kind = (fun env k -> (let k = (FStar_Absyn_Util.compress_kind k)
in (let w = (fun f -> (f k.FStar_Absyn_Syntax.pos))
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(k, FStar_Tc_Rel.trivial_guard)
end
| FStar_Absyn_Syntax.Kind_uvar (u, args) -> begin
(let _39_244 = (match ((FStar_Tc_Env.debug env FStar_Options.Medium)) with
| true -> begin
(let _104_210 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _104_209 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint2 "(%s) - Checking kind %s" _104_210 _104_209)))
end
| false -> begin
()
end)
in (let _39_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_249) with
| (env, _39_248) -> begin
(let _39_252 = (tc_args env args)
in (match (_39_252) with
| (args, g) -> begin
(let _104_212 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_104_212, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _39_263; FStar_Absyn_Syntax.pos = _39_261; FStar_Absyn_Syntax.fvs = _39_259; FStar_Absyn_Syntax.uvs = _39_257}) -> begin
(let _39_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_39_272) with
| (_39_269, binders, body) -> begin
(let _39_275 = (tc_args env args)
in (match (_39_275) with
| (args, g) -> begin
(match (((FStar_List.length binders) <> (FStar_List.length args))) with
| true -> begin
(let _104_216 = (let _104_215 = (let _104_214 = (let _104_213 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _104_213))
in (_104_214, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_215))
in (Prims.raise _104_216))
end
| false -> begin
(let _39_308 = (FStar_List.fold_left2 (fun _39_279 b a -> (match (_39_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(let _39_289 = (let _104_220 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _104_220))
in (match (_39_289) with
| (t, g) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _104_222 = (let _104_221 = (FStar_Absyn_Syntax.targ t)
in (_104_221)::args)
in (subst, _104_222, (g)::guards)))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(let env = (let _104_223 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _104_223))
in (let _39_301 = (tc_ghost_exp env e)
in (match (_39_301) with
| (e, _39_299, g) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (let _104_225 = (let _104_224 = (FStar_Absyn_Syntax.varg e)
in (_104_224)::args)
in (subst, _104_225, (g)::guards)))
end)))
end
| _39_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_39_308) with
| (subst, args, guards) -> begin
(let args = (FStar_List.rev args)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _104_228 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _104_228))))))
end))
end)
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _39_319 = (tc_kind env k)
in (match (_39_319) with
| (k, f) -> begin
(let _39_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_39_322) with
| (args, g) -> begin
(let kabr = ((Prims.fst kabr), args)
in (let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _104_230 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _104_230))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _39_332 = (tc_binders env bs)
in (match (_39_332) with
| (bs, env, g) -> begin
(let _39_335 = (tc_kind env k)
in (match (_39_335) with
| (k, f) -> begin
(let f = (FStar_Tc_Rel.close_guard bs f)
in (let _104_233 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _104_232 = (FStar_Tc_Rel.conj_guard g f)
in (_104_233, _104_232))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _104_234 = (FStar_Tc_Util.new_kvar env)
in (_104_234, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun env x -> (let _39_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_39_342) with
| (t, g) -> begin
(let x = (let _39_343 = x
in {FStar_Absyn_Syntax.v = _39_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_343.FStar_Absyn_Syntax.p})
in (let env' = (let _104_237 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _104_237))
in (x, env', g)))
end)))
and tc_binders = (fun env bs -> (let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _39_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_39_362) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _39_363 = a
in {FStar_Absyn_Syntax.v = _39_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_363.FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _39_370 = (aux env' bs)
in (match (_39_370) with
| (bs, env', g') -> begin
(let _104_245 = (let _104_244 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _104_244))
in ((b)::bs, env', _104_245))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _39_376 = (tc_vbinder env x)
in (match (_39_376) with
| (x, env', g) -> begin
(let b = (FStar_Util.Inr (x), imp)
in (let _39_381 = (aux env' bs)
in (match (_39_381) with
| (bs, env', g') -> begin
(let _104_247 = (let _104_246 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _104_246))
in ((b)::bs, env', _104_247))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun env args -> (FStar_List.fold_right (fun _39_386 _39_389 -> (match ((_39_386, _39_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _39_396 = (tc_typ env t)
in (match (_39_396) with
| (t, _39_394, g') -> begin
(let _104_252 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _104_252))
end))
end
| FStar_Util.Inr (e) -> begin
(let _39_403 = (tc_ghost_exp env e)
in (match (_39_403) with
| (e, _39_401, g') -> begin
(let _104_253 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _104_253))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _39_410 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_39_410) with
| (t, g) -> begin
(let _104_256 = (FStar_Absyn_Syntax.mk_Total t)
in (_104_256, g))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (let tc = (let _104_259 = (let _104_258 = (let _104_257 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_104_257)::c.FStar_Absyn_Syntax.effect_args)
in (head, _104_258))
in (FStar_Absyn_Syntax.mk_Typ_app _104_259 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _39_418 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_39_418) with
| (tc, f) -> begin
(let _39_422 = (FStar_Absyn_Util.head_and_args tc)
in (match (_39_422) with
| (_39_420, args) -> begin
(let _39_434 = (match (args) with
| (FStar_Util.Inl (res), _39_427)::args -> begin
(res, args)
end
| _39_431 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_39_434) with
| (res, args) -> begin
(let _39_450 = (let _104_261 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _39_3 -> (match (_39_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _39_441 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_441) with
| (env, _39_440) -> begin
(let _39_446 = (tc_ghost_exp env e)
in (match (_39_446) with
| (e, _39_444, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _104_261 FStar_List.unzip))
in (match (_39_450) with
| (flags, guards) -> begin
(let _104_263 = (FStar_Absyn_Syntax.mk_Comp (let _39_451 = c
in {FStar_Absyn_Syntax.effect_name = _39_451.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _39_451.FStar_Absyn_Syntax.flags}))
in (let _104_262 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_104_263, _104_262)))
end))
end))
end))
end)))))
end))
and tc_typ = (fun env t -> (let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (let w = (fun k -> (FStar_Absyn_Syntax.syn t.FStar_Absyn_Syntax.pos (Some (k))))
in (let t = (FStar_Absyn_Util.compress_typ t)
in (let top = t
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let k = (FStar_Tc_Env.lookup_btvar env a)
in (let a = (let _39_463 = a
in {FStar_Absyn_Syntax.v = _39_463.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_463.FStar_Absyn_Syntax.p})
in (let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _39_470 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_39_470) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Absyn_Syntax.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.eqT_k k)
in (let i = (let _39_475 = i
in {FStar_Absyn_Syntax.v = _39_475.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _39_475.FStar_Absyn_Syntax.p})
in (let _104_286 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_104_286, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Absyn_Syntax.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Absyn_Syntax.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.allT_k k)
in (let i = (let _39_482 = i
in {FStar_Absyn_Syntax.v = _39_482.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _39_482.FStar_Absyn_Syntax.p})
in (let _104_287 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_104_287, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _39_490 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (let i = (let _39_492 = i
in {FStar_Absyn_Syntax.v = _39_492.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_492.FStar_Absyn_Syntax.p})
in (let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (let _39_499 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_39_499) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(let _39_507 = (tc_binders env bs)
in (match (_39_507) with
| (bs, env, g) -> begin
(let _39_510 = (tc_comp env cod)
in (match (_39_510) with
| (cod, f) -> begin
(let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _39_595 = (match ((FStar_Absyn_Util.is_smt_lemma t)) with
| true -> begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _39_533; FStar_Absyn_Syntax.result_typ = _39_531; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _39_527)::(FStar_Util.Inl (post), _39_522)::(FStar_Util.Inr (pats), _39_517)::[]; FStar_Absyn_Syntax.flags = _39_513}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _104_292 = (FStar_Absyn_Util.compress_exp pats)
in _104_292.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _39_548); FStar_Absyn_Syntax.tk = _39_545; FStar_Absyn_Syntax.pos = _39_543; FStar_Absyn_Syntax.fvs = _39_541; FStar_Absyn_Syntax.uvs = _39_539}, _39_563::(FStar_Util.Inr (hd), _39_560)::(FStar_Util.Inr (tl), _39_555)::[]) when (FStar_Absyn_Syntax.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _39_569 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_39_569) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _39_576 -> begin
[]
end)
in (let _104_293 = (extract_pats tl)
in (FStar_List.append pat _104_293)))
end))
end
| _39_579 -> begin
[]
end))
in (let pats = (let _104_294 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _104_294))
in (let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _39_585 -> (match (_39_585) with
| (b, _39_584) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(not ((FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)))
end
| FStar_Util.Inr (x) -> begin
(not ((FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)))
end)
end))))) with
| None -> begin
()
end
| Some (b) -> begin
(let _104_297 = (let _104_296 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _104_296))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _104_297))
end))))
end
| _39_594 -> begin
(FStar_All.failwith "Impossible")
end)
end
| false -> begin
()
end)
in (let _104_299 = (let _104_298 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _104_298))
in (t, FStar_Absyn_Syntax.ktype, _104_299))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _39_604 = (tc_binders env bs)
in (match (_39_604) with
| (bs, env, g) -> begin
(let _39_608 = (tc_typ env t)
in (match (_39_608) with
| (t, k, f) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _104_304 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _104_303 = (let _104_302 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _104_302))
in (_104_304, k, _104_303))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let _39_617 = (tc_vbinder env x)
in (match (_39_617) with
| (x, env, f1) -> begin
(let _39_621 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_307 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_306 = (FStar_Absyn_Print.typ_to_string phi)
in (let _104_305 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.fprint3 "(%s) Checking refinement formula %s; env expects type %s\n" _104_307 _104_306 _104_305))))
end
| false -> begin
()
end)
in (let _39_625 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_39_625) with
| (phi, f2) -> begin
(let _104_314 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _104_313 = (let _104_312 = (let _104_311 = (let _104_310 = (FStar_Absyn_Syntax.v_binder x)
in (_104_310)::[])
in (FStar_Tc_Rel.close_guard _104_311 f2))
in (FStar_Tc_Rel.conj_guard f1 _104_312))
in (_104_314, FStar_Absyn_Syntax.ktype, _104_313)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _39_630 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_317 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_316 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _104_315 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.fprint3 "(%s) Checking type application (%s): %s\n" _104_317 _104_316 _104_315))))
end
| false -> begin
()
end)
in (let _39_635 = (tc_typ (no_inst env) head)
in (match (_39_635) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _39_638 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_321 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _104_320 = (FStar_Absyn_Print.typ_to_string head)
in (let _104_319 = (FStar_Absyn_Print.kind_to_string k1')
in (let _104_318 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.fprint4 "(%s) head %s has kind %s ... after norm %s\n" _104_321 _104_320 _104_319 _104_318)))))
end
| false -> begin
()
end)
in (let check_app = (fun _39_641 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_39_643) -> begin
(let _39_647 = (tc_args env args)
in (match (_39_647) with
| (args, g) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _104_324 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _104_324 Prims.fst))
in (let bs = (let _104_325 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _104_325))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (let _39_653 = (let _104_326 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _104_326))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _104_337 = (FStar_Absyn_Util.subst_kind subst kres)
in (_104_337, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _104_341 = (let _104_340 = (let _104_339 = (let _104_338 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_338))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _104_339))
in FStar_Absyn_Syntax.Error (_104_340))
in (Prims.raise _104_341))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _39_726 = (let _104_342 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _104_342))
in (match (_39_726) with
| (t, u) -> begin
(let targ = (FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (FStar_Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _39_755 = (let _104_343 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _104_343))
in (match (_39_755) with
| (e, u) -> begin
(let varg = (FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (FStar_Util.Inr (u)) g)
in (let subst = (maybe_extend_subst subst formal varg)
in (check_args ((varg)::outargs) subst g rest args))))
end)))
end
| (formal::formals, actual::actuals) -> begin
(match ((formal, actual)) with
| ((FStar_Util.Inl (a), aqual), (FStar_Util.Inl (t), imp)) -> begin
(let formal_k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_776 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_345 = (FStar_Absyn_Print.arg_to_string actual)
in (let _104_344 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.fprint2 "Checking argument %s against expected kind %s\n" _104_345 _104_344)))
end
| false -> begin
()
end)
in (let _39_782 = (tc_typ_check (let _39_778 = env
in {FStar_Tc_Env.solver = _39_778.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_778.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_778.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_778.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_778.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_778.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_778.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_778.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_778.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_778.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_778.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_778.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_778.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_778.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_778.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_778.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_778.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_778.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_778.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_39_782) with
| (t, g') -> begin
(let _39_783 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_346 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.fprint1 ">>>Got guard %s\n" _104_346))
end
| false -> begin
()
end)
in (let actual = (FStar_Util.Inl (t), imp)
in (let g' = (let _104_348 = (let _104_347 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _104_347))
in (FStar_Tc_Rel.imp_guard _104_348 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _104_349 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _104_349 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _39_799 = env'
in {FStar_Tc_Env.solver = _39_799.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_799.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_799.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_799.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_799.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_799.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_799.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_799.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_799.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_799.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_799.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_799.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_799.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_799.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_799.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_799.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_799.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_799.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_799.FStar_Tc_Env.default_effects})
in (let _39_802 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_351 = (FStar_Absyn_Print.arg_to_string actual)
in (let _104_350 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.fprint2 "Checking argument %s against expected type %s\n" _104_351 _104_350)))
end
| false -> begin
()
end)
in (let _39_808 = (tc_ghost_exp env' v)
in (match (_39_808) with
| (v, _39_806, g') -> begin
(let actual = (FStar_Util.Inr (v), imp)
in (let g' = (let _104_353 = (let _104_352 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _104_352))
in (FStar_Tc_Rel.imp_guard _104_353 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _104_354 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _104_354 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _39_815), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (FStar_Absyn_Util.b2t v)
in (let _104_356 = (let _104_355 = (FStar_Absyn_Syntax.targ tv)
in (_104_355)::actuals)
in (check_args outargs subst g ((formal)::formals) _104_356)))
end
| _39_825 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_39_827), _39_830), (FStar_Util.Inl (_39_833), _39_836)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_39_840, []) -> begin
(let _104_358 = (let _104_357 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _104_357))
in (_104_358, (FStar_List.rev outargs), g))
end
| ([], _39_845) -> begin
(let _104_366 = (let _104_365 = (let _104_364 = (let _104_363 = (let _104_361 = (let _104_360 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _39_4 -> (match (_39_4) with
| (_39_849, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _39_854 -> begin
true
end))))
in (FStar_List.length _104_360))
in (FStar_All.pipe_right _104_361 FStar_Util.string_of_int))
in (let _104_362 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _104_363 _104_362)))
in (_104_364, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_365))
in (Prims.raise _104_366))
end))
in (check_args [] [] f1 formals args))
end
| _39_856 -> begin
(let _104_369 = (let _104_368 = (let _104_367 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_104_367, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_368))
in (Prims.raise _104_369))
end)
end))
in (match ((let _104_373 = (let _104_370 = (FStar_Absyn_Util.compress_typ head)
in _104_370.FStar_Absyn_Syntax.n)
in (let _104_372 = (let _104_371 = (FStar_Absyn_Util.compress_kind k1)
in _104_371.FStar_Absyn_Syntax.n)
in (_104_373, _104_372)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_39_858), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(let result_k = (let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in (t, result_k, FStar_Tc_Rel.trivial_guard)))
end
| _39_869 -> begin
(let _39_873 = (check_app ())
in (match (_39_873) with
| (k, args, g) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(let _39_881 = (tc_kind env k1)
in (match (_39_881) with
| (k1, f1) -> begin
(let _39_884 = (tc_typ_check env t1 k1)
in (match (_39_884) with
| (t1, f2) -> begin
(let _104_377 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _104_376 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_104_377, k1, _104_376)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (u, k1) when env.FStar_Tc_Env.check_uvars -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _39_896 = (tc_kind env k1)
in (match (_39_896) with
| (k1, g) -> begin
(let _39_900 = (FStar_Tc_Rel.new_tvar s.FStar_Absyn_Syntax.pos [] k1)
in (match (_39_900) with
| (_39_898, u') -> begin
(let _39_901 = (FStar_Absyn_Util.unchecked_unify u u')
in (u', k1, g))
end))
end))
end
| _39_904 -> begin
(tc_typ env s)
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_39_906, k1) -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _39_915 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High)) with
| true -> begin
(let _104_379 = (FStar_Absyn_Print.typ_to_string s)
in (let _104_378 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.fprint2 "Admitting un-instantiated uvar %s at kind %s\n" _104_379 _104_378)))
end
| false -> begin
()
end)
in (let _104_382 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_104_382, k1, FStar_Tc_Rel.trivial_guard)))
end
| _39_918 -> begin
(let _39_919 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High)) with
| true -> begin
(let _104_384 = (FStar_Absyn_Print.typ_to_string s)
in (let _104_383 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.fprint2 "Admitting instantiated uvar %s at kind %s\n" _104_384 _104_383)))
end
| false -> begin
()
end)
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(let _39_930 = (tc_typ env t)
in (match (_39_930) with
| (t, k, f) -> begin
(let _104_385 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_104_385, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(let _39_941 = (tc_typ env t)
in (match (_39_941) with
| (t, k, f) -> begin
(let _104_386 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_104_386, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(let _39_950 = (tc_typ env t)
in (match (_39_950) with
| (t, k, f) -> begin
(let _104_387 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_104_387, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(let _39_958 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_39_958) with
| (quant, f) -> begin
(let _39_961 = (tc_args env pats)
in (match (_39_961) with
| (pats, g) -> begin
(let g = (let _39_962 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _39_962.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _39_962.FStar_Tc_Rel.implicits})
in (let _104_390 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _104_389 = (FStar_Tc_Util.force_tk quant)
in (let _104_388 = (FStar_Tc_Rel.conj_guard f g)
in (_104_390, _104_389, _104_388)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let t = (FStar_Tc_Util.new_tvar env k)
in (t, k, FStar_Tc_Rel.trivial_guard)))
end
| _39_969 -> begin
(let _104_392 = (let _104_391 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _104_391))
in (FStar_All.failwith _104_392))
end))))))
and tc_typ_check = (fun env t k -> (let _39_976 = (tc_typ env t)
in (match (_39_976) with
| (t, k', f) -> begin
(let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (let f' = (match (env.FStar_Tc_Env.use_eq) with
| true -> begin
(FStar_Tc_Rel.keq env (Some (t)) k' k)
end
| false -> begin
(FStar_Tc_Rel.subkind env k' k)
end)
in (let f = (FStar_Tc_Rel.conj_guard f f')
in (t, f))))
end)))
and tc_value = (fun env e -> (let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (_39_985, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (FStar_Tc_Env.lookup_bvar env x)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar (let _39_992 = x
in {FStar_Absyn_Syntax.v = _39_992.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_992.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _39_998 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_39_998) with
| (e, t, implicits) -> begin
(let tc = (match ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) with
| true -> begin
FStar_Util.Inl (t)
end
| false -> begin
(let _104_399 = (let _104_398 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_398))
in FStar_Util.Inr (_104_399))
end)
in (let _104_400 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _104_400)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (let e = (FStar_Absyn_Syntax.mk_Exp_fvar ((let _39_1005 = v
in {FStar_Absyn_Syntax.v = _39_1005.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_1005.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _39_1011 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_39_1011) with
| (e, t, implicits) -> begin
(let tc = (match ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) with
| true -> begin
FStar_Util.Inl (t)
end
| false -> begin
(let _104_402 = (let _104_401 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_401))
in FStar_Util.Inr (_104_402))
end)
in (let is_data_ctor = (fun _39_5 -> (match (_39_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _39_1021 -> begin
false
end))
in (match (((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v))))) with
| true -> begin
(let _104_408 = (let _104_407 = (let _104_406 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
in (let _104_405 = (FStar_Tc_Env.get_range env)
in (_104_406, _104_405)))
in FStar_Absyn_Syntax.Error (_104_407))
in (Prims.raise _104_408))
end
| false -> begin
(let _104_409 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _104_409))
end)))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fail = (fun msg t -> (let _104_414 = (let _104_413 = (let _104_412 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_104_412, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_413))
in (Prims.raise _104_414)))
in (let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(let _39_1042 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _39_1041 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _39_1047 = (tc_binders env bs)
in (match (_39_1047) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun norm t -> (match ((let _104_423 = (FStar_Absyn_Util.compress_typ t)
in _104_423.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _39_1076 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _39_1075 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _39_1081 = (tc_binders env bs)
in (match (_39_1081) with
| (bs, envbody, g) -> begin
(let _39_1085 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_39_1085) with
| (envbody, _39_1084) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let rec tc_binders = (fun _39_1095 bs_annot c bs -> (match (_39_1095) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _104_432 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _104_432))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_39_1110), _39_1113), (FStar_Util.Inr (_39_1116), _39_1119)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _39_1126), (FStar_Util.Inl (b), imp)) -> begin
(let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_1144 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _39_1136 -> begin
(let _39_1139 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_39_1139) with
| (k, g1) -> begin
(let g2 = (FStar_Tc_Rel.keq env None ka k)
in (let g = (let _104_433 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _104_433))
in (k, g)))
end))
end)
in (match (_39_1144) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _39_1145 = b
in {FStar_Absyn_Syntax.v = _39_1145.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_1145.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _39_1153), (FStar_Util.Inr (y), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _39_1175 = (match ((let _104_434 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _104_434.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _39_1163 -> begin
(let _39_1164 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_435 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.fprint1 "Checking binder %s\n" _104_435))
end
| false -> begin
()
end)
in (let _39_1170 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_39_1170) with
| (t, _39_1168, g1) -> begin
(let g2 = (FStar_Tc_Rel.teq env tx t)
in (let g = (let _104_436 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _104_436))
in (t, g)))
end)))
end)
in (match (_39_1175) with
| (t, g) -> begin
(let b = (FStar_Util.Inr ((let _39_1176 = y
in {FStar_Absyn_Syntax.v = _39_1176.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_1176.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _39_1182 -> begin
(let _104_439 = (let _104_438 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _104_437 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _104_438 _104_437)))
in (fail _104_439 t))
end)
end
| ([], _39_1185) -> begin
(match ((FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _39_1194; FStar_Absyn_Syntax.pos = _39_1192; FStar_Absyn_Syntax.fvs = _39_1190; FStar_Absyn_Syntax.uvs = _39_1188} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _104_441 = (let _104_440 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _104_440))
in (fail _104_441 t))
end)
end
| false -> begin
(fail "Curried function, but not total" t)
end)
end
| (_39_1202, []) -> begin
(let c = (let _104_442 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _104_442 c.FStar_Absyn_Syntax.pos))
in (let _104_443 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _104_443)))
end)
end))
in (let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _39_1211 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_448 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint1 "Building let-rec environment... type of this abstraction is %s\n" _104_448))
end
| false -> begin
()
end)
in (let r = (FStar_Tc_Env.get_range env)
in (let env = (let _39_1214 = env
in {FStar_Tc_Env.solver = _39_1214.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1214.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1214.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1214.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1214.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1214.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1214.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1214.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1214.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1214.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1214.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1214.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1214.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _39_1214.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1214.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_1214.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_1214.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1214.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1214.FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_39_1221), _39_1224) -> begin
[]
end
| (FStar_Util.Inr (x), _39_1229) -> begin
(match ((let _104_454 = (let _104_453 = (let _104_452 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _104_452))
in (FStar_Absyn_Util.unrefine _104_453))
in _104_454.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_39_1232) -> begin
[]
end
| _39_1235 -> begin
(let _104_455 = (FStar_Absyn_Util.bvar_to_exp x)
in (_104_455)::[])
end)
end)))))
in (let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun dec -> (let _39_1242 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_39_1242) with
| (head, _39_1241) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _39_1245) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _39_1249 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _39_6 -> (match (_39_6) with
| FStar_Absyn_Syntax.DECREASES (_39_1253) -> begin
true
end
| _39_1256 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _39_1260 = (match (((FStar_List.length bs') <> (FStar_List.length actuals))) with
| true -> begin
(let _104_464 = (let _104_463 = (let _104_462 = (let _104_460 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _104_459 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _104_460 _104_459)))
in (let _104_461 = (FStar_Tc_Env.get_range env)
in (_104_462, _104_461)))
in FStar_Absyn_Syntax.Error (_104_463))
in (Prims.raise _104_464))
end
| false -> begin
()
end)
in (let dec = (as_lex_list dec)
in (let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _39_1268), (FStar_Util.Inl (actual), _39_1273)) -> begin
(let _104_468 = (let _104_467 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _104_467))
in FStar_Util.Inl (_104_468))
end
| ((FStar_Util.Inr (formal), _39_1279), (FStar_Util.Inr (actual), _39_1284)) -> begin
(let _104_470 = (let _104_469 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _104_469))
in FStar_Util.Inr (_104_470))
end
| _39_1288 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _39_1291 -> begin
(let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _39_1296 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _39_1300 -> (match (_39_1300) with
| (l, t0) -> begin
(let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _104_472 = (FStar_Absyn_Util.compress_typ t)
in _104_472.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _39_7 -> (match (_39_7) with
| FStar_Absyn_Syntax.DECREASES (_39_1316) -> begin
true
end
| _39_1319 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _104_476 = (let _104_475 = (let _104_474 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _104_474))
in FStar_Util.Inr (_104_475))
in (_104_476)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _104_481 = (let _104_480 = (let _104_479 = (FStar_Absyn_Syntax.varg dec)
in (let _104_478 = (let _104_477 = (FStar_Absyn_Syntax.varg prev_dec)
in (_104_477)::[])
in (_104_479)::_104_478))
in (precedes, _104_480))
in (FStar_Absyn_Syntax.mk_Typ_app _104_481 None r))))
end
| _39_1327 -> begin
(let formal_args = (let _104_484 = (let _104_483 = (let _104_482 = (FStar_Absyn_Syntax.v_binder y)
in (_104_482)::[])
in (FStar_List.append bs _104_483))
in (FStar_All.pipe_right _104_484 filter_types_and_functions))
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _39_1332 -> begin
(mk_lex_list formal_args)
end)
in (let _104_489 = (let _104_488 = (let _104_487 = (FStar_Absyn_Syntax.varg lhs)
in (let _104_486 = (let _104_485 = (FStar_Absyn_Syntax.varg prev_dec)
in (_104_485)::[])
in (_104_487)::_104_486))
in (precedes, _104_488))
in (FStar_Absyn_Syntax.mk_Typ_app _104_489 None r))))
end)
in (let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (FStar_List.append bs (((FStar_Util.Inr ((let _39_1336 = x
in {FStar_Absyn_Syntax.v = _39_1336.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _39_1336.FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _39_1340 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_492 = (FStar_Absyn_Print.lbname_to_string l)
in (let _104_491 = (FStar_Absyn_Print.typ_to_string t)
in (let _104_490 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.fprint3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _104_492 _104_491 _104_490))))
end
| false -> begin
()
end)
in (let _39_1347 = (let _104_494 = (let _104_493 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _104_493 Prims.fst))
in (tc_typ _104_494 t'))
in (match (_39_1347) with
| (t', _39_1344, _39_1346) -> begin
(l, t')
end)))))))))
end
| _39_1349 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _39_1351 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _104_500 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _39_1356 -> (match (_39_1356) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _104_499 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _39_8 -> (match (_39_8) with
| (FStar_Util.Inl (x), t) -> begin
(let _104_498 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_104_498)::[])
end
| _39_1363 -> begin
[]
end))))
in (_104_500, _104_499)))))))))))
end))
in (let _39_1368 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_39_1368) with
| (bs, envbody, g, c) -> begin
(let _39_1371 = (match ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) with
| true -> begin
(mk_letrec_environment bs envbody)
end
| false -> begin
(envbody, [])
end)
in (match (_39_1371) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _39_1375) -> begin
(let _39_1385 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_39_1385) with
| (_39_1379, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _39_1387 -> begin
(match ((not (norm))) with
| true -> begin
(let _104_501 = (whnf env t)
in (as_function_typ true _104_501))
end
| false -> begin
(let _39_1396 = (expected_function_typ env None)
in (match (_39_1396) with
| (_39_1389, bs, _39_1392, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end)
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_Tc_Env.use_eq
in (let _39_1400 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_1400) with
| (env, topt) -> begin
(let _39_1407 = (expected_function_typ env topt)
in (match (_39_1407) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _39_1413 = (tc_exp (let _39_1408 = envbody
in {FStar_Tc_Env.solver = _39_1408.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1408.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1408.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1408.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1408.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1408.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1408.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1408.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1408.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1408.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1408.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1408.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1408.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1408.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _39_1408.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _39_1408.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1408.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1408.FStar_Tc_Env.default_effects}) body)
in (match (_39_1413) with
| (body, cbody, guard_body) -> begin
(let _39_1414 = (match ((FStar_Tc_Env.debug env FStar_Options.Medium)) with
| true -> begin
(let _104_504 = (FStar_Absyn_Print.exp_to_string body)
in (let _104_503 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _104_502 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.fprint3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _104_504 _104_503 _104_502))))
end
| false -> begin
()
end)
in (let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _39_1417 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _104_505 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.fprint1 "Introduced %s implicits in body of abstraction\n" _104_505))
end
| false -> begin
()
end)
in (let _39_1424 = (let _104_507 = (let _104_506 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _104_506))
in (check_expected_effect (let _39_1419 = envbody
in {FStar_Tc_Env.solver = _39_1419.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1419.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1419.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1419.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1419.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1419.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1419.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1419.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1419.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1419.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1419.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1419.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1419.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1419.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_1419.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1419.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _39_1419.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1419.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1419.FStar_Tc_Env.default_effects}) c_opt _104_507))
in (match (_39_1424) with
| (body, cbody, guard) -> begin
(let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = (match ((env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str))))) with
| true -> begin
(let _39_1426 = (let _104_508 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _104_508))
in (let _39_1428 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _39_1428.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _39_1428.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end
| false -> begin
(let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end)
in (let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (let e = (let _104_510 = (let _104_509 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_104_509, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _104_510 None top.FStar_Absyn_Syntax.pos))
in (let _39_1451 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_39_1440) -> begin
(let _104_513 = (let _104_512 = (let _104_511 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_104_511, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _104_512 None top.FStar_Absyn_Syntax.pos))
in (_104_513, t, guard))
end
| _39_1443 -> begin
(let _39_1446 = (match (use_teq) with
| true -> begin
(let _104_514 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _104_514))
end
| false -> begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (_39_1446) with
| (e, guard') -> begin
(let _104_516 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _104_515 = (FStar_Tc_Rel.conj_guard guard guard')
in (_104_516, t, _104_515)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_39_1451) with
| (e, tfun, guard) -> begin
(let _39_1452 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_519 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _104_518 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _104_517 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.fprint3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _104_519 _104_518 _104_517))))
end
| false -> begin
()
end)
in (let c = (match (env.FStar_Tc_Env.top_level) with
| true -> begin
(FStar_Absyn_Syntax.mk_Total tfun)
end
| false -> begin
(FStar_Tc_Util.return_value env tfun e)
end)
in (let _39_1457 = (let _104_521 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _104_521 guard))
in (match (_39_1457) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _39_1459 -> begin
(let _104_523 = (let _104_522 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _104_522))
in (FStar_All.failwith _104_523))
end))))
and tc_exp = (fun env e -> (let env = (match ((e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
env
end
| false -> begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end)
in (let _39_1463 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_528 = (let _104_526 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _104_526))
in (let _104_527 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.fprint2 "%s (%s)\n" _104_528 _104_527)))
end
| false -> begin
()
end)
in (let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_39_1469) -> begin
(let _104_552 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _104_552))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _39_1489) -> begin
(let _39_1494 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_39_1494) with
| (t1, f) -> begin
(let _39_1498 = (let _104_553 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _104_553 e1))
in (match (_39_1498) with
| (e1, c, g) -> begin
(let _39_1502 = (let _104_557 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _39_1499 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _104_557 e1 c f))
in (match (_39_1502) with
| (c, f) -> begin
(let _39_1506 = (let _104_561 = (let _104_560 = (w c)
in (FStar_All.pipe_left _104_560 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _104_561 c))
in (match (_39_1506) with
| (e, c, f2) -> begin
(let _104_563 = (let _104_562 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _104_562))
in (e, c, _104_563))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(let pats_t = (let _104_569 = (let _104_568 = (let _104_564 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _104_564))
in (let _104_567 = (let _104_566 = (let _104_565 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _104_565))
in (_104_566)::[])
in (_104_568, _104_567)))
in (FStar_Absyn_Syntax.mk_Typ_app _104_569 None FStar_Absyn_Syntax.dummyRange))
in (let _39_1516 = (let _104_570 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _104_570 e))
in (match (_39_1516) with
| (e, t, g) -> begin
(let g = (let _39_1517 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _39_1517.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _39_1517.FStar_Tc_Rel.implicits})
in (let c = (let _104_571 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _104_571 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _104_572 = (FStar_Absyn_Util.compress_exp e)
in _104_572.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_39_1527, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _39_1532; FStar_Absyn_Syntax.lbeff = _39_1530; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _39_1543 = (let _104_573 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _104_573 e1))
in (match (_39_1543) with
| (e1, c1, g1) -> begin
(let _39_1547 = (tc_exp env e2)
in (match (_39_1547) with
| (e2, c2, g2) -> begin
(let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _104_586 = (let _104_584 = (let _104_583 = (let _104_582 = (let _104_581 = (w c)
in (let _104_580 = (let _104_579 = (let _104_578 = (let _104_577 = (let _104_576 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1))
in (_104_576)::[])
in (false, _104_577))
in (_104_578, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _104_579))
in (FStar_All.pipe_left _104_581 _104_580)))
in (_104_582, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_104_583))
in (FStar_Absyn_Syntax.mk_Exp_meta _104_584))
in (let _104_585 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_104_586, c, _104_585))))
end))
end))
end
| _39_1550 -> begin
(let _39_1554 = (tc_exp env e)
in (match (_39_1554) with
| (e, c, g) -> begin
(let _104_587 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_104_587, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(let _39_1563 = (tc_exp env e)
in (match (_39_1563) with
| (e, c, g) -> begin
(let _104_588 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_104_588, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let env0 = env
in (let env = (let _104_590 = (let _104_589 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _104_589 Prims.fst))
in (FStar_All.pipe_right _104_590 instantiate_both))
in (let _39_1570 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_592 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_591 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.fprint2 "(%s) Checking app %s\n" _104_592 _104_591)))
end
| false -> begin
()
end)
in (let _39_1575 = (tc_exp (no_inst env) head)
in (match (_39_1575) with
| (head, chead, g_head) -> begin
(let aux = (fun _39_1577 -> (match (()) with
| () -> begin
(let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _39_1581) when (((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _39_1593)::(FStar_Util.Inr (e2), _39_1588)::[] -> begin
(let _39_1599 = (tc_exp env e1)
in (match (_39_1599) with
| (e1, c1, g1) -> begin
(let _39_1603 = (tc_exp env e2)
in (match (_39_1603) with
| (e2, c2, g2) -> begin
(let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = (match ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And)) with
| true -> begin
(let _104_598 = (let _104_595 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _104_595))
in (let _104_597 = (let _104_596 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _104_596 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _104_598 c2 _104_597)))
end
| false -> begin
(let _104_602 = (let _104_599 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _104_599))
in (let _104_601 = (let _104_600 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _104_600 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _104_602 _104_601 c2)))
end)
in (let c = (let _104_605 = (let _104_604 = (FStar_All.pipe_left (fun _104_603 -> Some (_104_603)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_104_604, c2))
in (FStar_Tc_Util.bind env None c1 _104_605))
in (let e = (let _104_610 = (let _104_609 = (let _104_608 = (FStar_Absyn_Syntax.varg e1)
in (let _104_607 = (let _104_606 = (FStar_Absyn_Syntax.varg e2)
in (_104_606)::[])
in (_104_608)::_104_607))
in (head, _104_609))
in (FStar_Absyn_Syntax.mk_Exp_app _104_610 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _104_612 = (let _104_611 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _104_611))
in (e, c, _104_612)))))))
end))
end))
end
| _39_1610 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _39_1612 -> begin
(let thead = chead.FStar_Absyn_Syntax.res_typ
in (let _39_1614 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_614 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _104_613 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.fprint2 "(%s) Type of head is %s\n" _104_614 _104_613)))
end
| false -> begin
()
end)
in (let rec check_function_app = (fun norm tf -> (match ((let _104_619 = (FStar_Absyn_Util.unrefine tf)
in _104_619.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _39_1647)::_39_1643 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(let _39_1659 = (tc_exp env e)
in (match (_39_1659) with
| (e, c, g_e) -> begin
(let _39_1663 = (tc_args env tl)
in (match (_39_1663) with
| (args, comps, g_rest) -> begin
(let _104_624 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _104_624))
end))
end))
end))
in (let _39_1667 = (tc_args env args)
in (match (_39_1667) with
| (args, comps, g_args) -> begin
(let bs = (let _104_625 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _104_625))
in (let cres = (let _104_626 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _104_626 top.FStar_Absyn_Syntax.pos))
in (let _39_1670 = (let _104_628 = (let _104_627 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _104_627))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _104_628))
in (let comp = (let _104_631 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _104_631))
in (let _104_633 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _104_632 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_104_633, comp, _104_632)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let vars = (FStar_Tc_Env.binders env)
in (let rec tc_args = (fun _39_1687 bs cres args -> (match (_39_1687) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_39_1701, None)::_39_1699) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_1707 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _39_1711 = (let _104_669 = (let _104_668 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_668))
in (FStar_Tc_Rel.new_tvar _104_669 vars k))
in (match (_39_1711) with
| (targ, u) -> begin
(let _39_1712 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_671 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _104_670 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint2 "Instantiating %s to %s" _104_671 _104_670)))
end
| false -> begin
()
end)
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (let _104_672 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (targ), _104_672))
in (let _104_681 = (let _104_680 = (let _104_679 = (let _104_678 = (let _104_677 = (FStar_Tc_Util.as_uvar_t u)
in (_104_677, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_104_678))
in (add_implicit _104_679 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _104_680, fvs))
in (tc_args _104_681 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_39_1726, None)::_39_1724) -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _39_1732 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (let _39_1736 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_39_1736) with
| (varg, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (let _104_682 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (varg), _104_682))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(let _39_1752 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_688 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _104_687 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "\tGot a type arg for %s = %s\n" _104_688 _104_687)))
end
| false -> begin
()
end)
in (let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_1755 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _39_1761 = (tc_typ_check (let _39_1757 = env
in {FStar_Tc_Env.solver = _39_1757.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1757.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1757.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1757.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1757.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1757.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1757.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1757.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1757.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1757.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1757.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1757.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1757.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1757.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_1757.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1757.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_1757.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1757.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1757.FStar_Tc_Env.default_effects}) t k)
in (match (_39_1761) with
| (t, g') -> begin
(let f = (let _104_689 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _104_689))
in (let g' = (let _39_1763 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _39_1763.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _39_1763.FStar_Tc_Rel.implicits})
in (let arg = (FStar_Util.Inl (t), aq)
in (let subst = (let _104_690 = (FStar_List.hd bs)
in (maybe_extend_subst subst _104_690 arg))
in (let _104_696 = (let _104_695 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _104_695, fvs))
in (tc_args _104_696 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(let _39_1781 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_698 = (FStar_Absyn_Print.subst_to_string subst)
in (let _104_697 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.fprint2 "\tType of arg (before subst (%s)) = %s\n" _104_698 _104_697)))
end
| false -> begin
()
end)
in (let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _39_1784 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_699 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint1 "\tType of arg (after subst) = %s\n" _104_699))
end
| false -> begin
()
end)
in (let _39_1786 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (let env = (FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _39_1789 = env
in {FStar_Tc_Env.solver = _39_1789.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1789.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1789.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1789.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1789.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1789.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1789.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1789.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1789.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1789.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1789.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1789.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1789.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1789.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_1789.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1789.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_1789.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1789.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1789.FStar_Tc_Env.default_effects})
in (let _39_1792 = (match (((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq)) with
| true -> begin
(let _104_701 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_700 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint2 "Checking arg %s at type %s with an equality constraint!\n" _104_701 _104_700)))
end
| false -> begin
()
end)
in (let _39_1794 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_704 = (FStar_Absyn_Print.tag_of_exp e)
in (let _104_703 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_702 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint3 "Checking arg (%s) %s at type %s\n" _104_704 _104_703 _104_702))))
end
| false -> begin
()
end)
in (let _39_1799 = (tc_exp env e)
in (match (_39_1799) with
| (e, c, g_e) -> begin
(let g = (FStar_Tc_Rel.conj_guard g g_e)
in (let _39_1801 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_706 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _104_705 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.fprint2 "Guard on this arg is %s;\naccumulated guard is %s\n" _104_706 _104_705)))
end
| false -> begin
()
end)
in (let arg = (FStar_Util.Inr (e), aq)
in (match ((FStar_Absyn_Util.is_tot_or_gtot_lcomp c)) with
| true -> begin
(let subst = (let _104_707 = (FStar_List.hd bs)
in (maybe_extend_subst subst _104_707 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end
| false -> begin
(match ((FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name)) with
| true -> begin
(let subst = (let _104_712 = (FStar_List.hd bs)
in (maybe_extend_subst subst _104_712 arg))
in (let _39_1808 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_39_1808) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end
| false -> begin
(match ((let _104_717 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _104_717))) with
| true -> begin
(let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _104_718 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _104_718))
in (let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end
| false -> begin
(let _104_731 = (let _104_730 = (let _104_724 = (let _104_723 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _104_723))
in (_104_724)::arg_rets)
in (let _104_729 = (let _104_727 = (let _104_726 = (FStar_All.pipe_left (fun _104_725 -> Some (_104_725)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_104_726, c))
in (_104_727)::comps)
in (let _104_728 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _104_730, _104_729, g, _104_728))))
in (tc_args _104_731 rest cres rest'))
end)
end)
end))))
end))))))))))
end
| ((FStar_Util.Inr (_39_1815), _39_1818)::_39_1813, (FStar_Util.Inl (_39_1824), _39_1827)::_39_1822) -> begin
(let _104_735 = (let _104_734 = (let _104_733 = (let _104_732 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_732))
in ("Expected an expression; got a type", _104_733))
in FStar_Absyn_Syntax.Error (_104_734))
in (Prims.raise _104_735))
end
| ((FStar_Util.Inl (_39_1834), _39_1837)::_39_1832, (FStar_Util.Inr (_39_1843), _39_1846)::_39_1841) -> begin
(let _104_739 = (let _104_738 = (let _104_737 = (let _104_736 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_736))
in ("Expected a type; got an expression", _104_737))
in FStar_Absyn_Syntax.Error (_104_738))
in (Prims.raise _104_739))
end
| (_39_1851, []) -> begin
(let _39_1854 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (let _39_1872 = (match (bs) with
| [] -> begin
(let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _39_1862 -> (match (_39_1862) with
| (_39_1860, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = (match (refine_with_equality) with
| true -> begin
(let _104_741 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _104_741 cres))
end
| false -> begin
(let _39_1864 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_744 = (FStar_Absyn_Print.exp_to_string head)
in (let _104_743 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _104_742 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.fprint3 "Not refining result: f=%s; cres=%s; guard=%s\n" _104_744 _104_743 _104_742))))
end
| false -> begin
()
end)
in cres)
end)
in (let _104_745 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_104_745, g))))))
end
| _39_1868 -> begin
(let g = (let _104_746 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _104_746 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _104_752 = (let _104_751 = (let _104_750 = (let _104_749 = (let _104_748 = (let _104_747 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _104_747))
in (FStar_Absyn_Syntax.mk_Typ_fun _104_748 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _104_749))
in (FStar_Absyn_Syntax.mk_Total _104_750))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_751))
in (_104_752, g)))
end)
in (match (_39_1872) with
| (cres, g) -> begin
(let _39_1873 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_753 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.fprint1 "\t Type of result cres is %s\n" _104_753))
end
| false -> begin
()
end)
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev outargs)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _39_1882 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_39_1882) with
| (comp, g) -> begin
(let _39_1883 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_759 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _104_758 = (let _104_757 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _104_757))
in (FStar_Util.fprint2 "\t Type of app term %s is %s\n" _104_759 _104_758)))
end
| false -> begin
()
end)
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_39_1887) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _104_764 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _104_764 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(let _39_1899 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_765 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.fprint1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _104_765))
end
| false -> begin
()
end)
in (let _104_770 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _104_770 args)))
end
| _39_1902 when (not (norm)) -> begin
(let _104_771 = (whnf env tres)
in (aux true _104_771))
end
| _39_1904 -> begin
(let _104_777 = (let _104_776 = (let _104_775 = (let _104_773 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _104_772 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _104_773 _104_772)))
in (let _104_774 = (FStar_Absyn_Syntax.argpos arg)
in (_104_775, _104_774)))
in FStar_Absyn_Syntax.Error (_104_776))
in (Prims.raise _104_777))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _104_778 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _104_778 args))))
end
| _39_1906 -> begin
(match ((not (norm))) with
| true -> begin
(let _104_779 = (whnf env tf)
in (check_function_app true _104_779))
end
| false -> begin
(let _104_782 = (let _104_781 = (let _104_780 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_104_780, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_781))
in (Prims.raise _104_782))
end)
end))
in (let _104_783 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _104_783)))))
end))
end))
in (let _39_1910 = (aux ())
in (match (_39_1910) with
| (e, c, g) -> begin
(let _39_1911 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _104_784 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.fprint1 "Introduced %s implicits in application\n" _104_784))
end
| false -> begin
()
end)
in (let c = (match ((((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c))) with
| true -> begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end
| false -> begin
c
end)
in (let _39_1918 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_789 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _104_788 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _104_787 = (let _104_786 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _104_786 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.fprint3 "(%s) About to check %s against expected typ %s\n" _104_789 _104_788 _104_787))))
end
| false -> begin
()
end)
in (let _39_1923 = (comp_check_expected_typ env0 e c)
in (match (_39_1923) with
| (e, c, g') -> begin
(let _104_790 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _104_790))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let _39_1930 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_1930) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _39_1935 = (tc_exp env1 e1)
in (match (_39_1935) with
| (e1, c1, g1) -> begin
(let _39_1942 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _104_791 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_104_791, res_t)))
end)
in (match (_39_1942) with
| (env_branches, res_t) -> begin
(let guard_x = (let _104_793 = (FStar_All.pipe_left (fun _104_792 -> Some (_104_792)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _104_793))
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (let _39_1959 = (let _39_1956 = (FStar_List.fold_right (fun _39_1950 _39_1953 -> (match ((_39_1950, _39_1953)) with
| ((_39_1946, f, c, g), (caccum, gaccum)) -> begin
(let _104_796 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _104_796))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_39_1956) with
| (cases, g) -> begin
(let _104_797 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_104_797, g))
end))
in (match (_39_1959) with
| (c_branches, g_branches) -> begin
(let _39_1960 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_801 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_800 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _104_799 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _104_798 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.fprint4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _104_801 _104_800 _104_799 _104_798)))))
end
| false -> begin
()
end)
in (let cres = (let _104_804 = (let _104_803 = (FStar_All.pipe_left (fun _104_802 -> Some (_104_802)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_104_803, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _104_804))
in (let e = (let _104_811 = (w cres)
in (let _104_810 = (let _104_809 = (let _104_808 = (FStar_List.map (fun _39_1970 -> (match (_39_1970) with
| (f, _39_1965, _39_1967, _39_1969) -> begin
f
end)) t_eqns)
in (e1, _104_808))
in (FStar_Absyn_Syntax.mk_Exp_match _104_809))
in (FStar_All.pipe_left _104_811 _104_810)))
in (let _104_813 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _104_812 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_104_813, cres, _104_812))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_1975; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| FStar_Util.Inr (_39_1988) -> begin
true
end
| _39_1991 -> begin
false
end)
in (let _39_1996 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_1996) with
| (env1, _39_1995) -> begin
(let _39_2009 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _39_1999 -> begin
(match ((top_level && (not (env.FStar_Tc_Env.generalize)))) with
| true -> begin
(let _104_814 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _104_814))
end
| false -> begin
(let _39_2002 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_39_2002) with
| (t, f) -> begin
(let _39_2003 = (match ((FStar_Tc_Env.debug env FStar_Options.Medium)) with
| true -> begin
(let _104_816 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_815 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "(%s) Checked type annotation %s\n" _104_816 _104_815)))
end
| false -> begin
()
end)
in (let t = (norm_t env1 t)
in (let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end)
end)
in (match (_39_2009) with
| (f, env1) -> begin
(let _39_2015 = (tc_exp (let _39_2010 = env1
in {FStar_Tc_Env.solver = _39_2010.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2010.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2010.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2010.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2010.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2010.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2010.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2010.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2010.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2010.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2010.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2010.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2010.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2010.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _39_2010.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2010.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2010.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2010.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2010.FStar_Tc_Env.default_effects}) e1)
in (match (_39_2015) with
| (e1, c1, g1) -> begin
(let _39_2019 = (let _104_820 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _39_2016 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _104_820 e1 c1 f))
in (match (_39_2019) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_39_2021) -> begin
(let _39_2032 = (match ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) with
| true -> begin
(let _39_2025 = (let _104_821 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _104_821 c1))
in (match (_39_2025) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
(e2, c1)
end
| false -> begin
(let _39_2026 = (match ((FStar_ST.read FStar_Options.warn_top_level_effects)) with
| true -> begin
(let _104_822 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _104_822 FStar_Tc_Errors.top_level_effect))
end
| false -> begin
()
end)
in (let _104_823 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_104_823, c1)))
end)
end))
end
| false -> begin
(let _39_2028 = (let _104_824 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.discharge_guard env _104_824))
in (let _104_825 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _104_825)))
end)
in (match (_39_2032) with
| (e2, c1) -> begin
(let _39_2037 = (match (env.FStar_Tc_Env.generalize) with
| true -> begin
(let _104_826 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _104_826))
end
| false -> begin
(x, e1, c1)
end)
in (match (_39_2037) with
| (_39_2034, e1, c1) -> begin
(let cres = (let _104_827 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_827))
in (let cres = (match ((FStar_Absyn_Util.is_total_comp c1)) with
| true -> begin
cres
end
| false -> begin
(let _104_828 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _104_828 (None, cres)))
end)
in (let _39_2040 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _104_837 = (let _104_836 = (w cres)
in (let _104_835 = (let _104_834 = (let _104_833 = (let _104_832 = (let _104_831 = (FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1))
in (_104_831)::[])
in (false, _104_832))
in (_104_833, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _104_834))
in (FStar_All.pipe_left _104_836 _104_835)))
in (_104_837, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (let _39_2048 = (let _104_838 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _104_838 e2))
in (match (_39_2048) with
| (e2, c2, g2) -> begin
(let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _104_846 = (w cres)
in (let _104_845 = (let _104_844 = (let _104_843 = (let _104_842 = (let _104_841 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1))
in (_104_841)::[])
in (false, _104_842))
in (_104_843, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _104_844))
in (FStar_All.pipe_left _104_846 _104_845)))
in (let g2 = (let _104_855 = (let _104_848 = (let _104_847 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_104_847)::[])
in (FStar_Tc_Rel.close_guard _104_848))
in (let _104_854 = (let _104_853 = (let _104_852 = (let _104_851 = (let _104_850 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _104_850 e1))
in (FStar_All.pipe_left (fun _104_849 -> FStar_Tc_Rel.NonTrivial (_104_849)) _104_851))
in (FStar_Tc_Rel.guard_of_guard_formula _104_852))
in (FStar_Tc_Rel.imp_guard _104_853 g2))
in (FStar_All.pipe_left _104_855 _104_854)))
in (let guard = (let _104_856 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _104_856))
in (match (topt) with
| None -> begin
(let tres = cres.FStar_Absyn_Syntax.res_typ
in (let fvs = (FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs)) with
| true -> begin
(let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _39_2057 = (let _104_857 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _104_857))
in (e, cres, guard)))
end
| false -> begin
(e, cres, guard)
end)))
end
| _39_2060 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _39_2063), _39_2066) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(let env = (instantiate_both env)
in (let _39_2078 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_2078) with
| (env0, topt) -> begin
(let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _39_9 -> (match (_39_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_39_2087); FStar_Absyn_Syntax.lbtyp = _39_2085; FStar_Absyn_Syntax.lbeff = _39_2083; FStar_Absyn_Syntax.lbdef = _39_2081} -> begin
true
end
| _39_2091 -> begin
false
end))))
in (let _39_2118 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _39_2095 _39_2101 -> (match ((_39_2095, _39_2101)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_2098; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _39_2106 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_39_2106) with
| (_39_2103, t, check_t) -> begin
(let e = (FStar_Absyn_Util.unascribe e)
in (let t = (match ((not (check_t))) with
| true -> begin
t
end
| false -> begin
(match (((not (is_inner_let)) && (not (env.FStar_Tc_Env.generalize)))) with
| true -> begin
(let _39_2108 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High)) with
| true -> begin
(let _104_861 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint1 "Type %s is marked as no-generalize\n" _104_861))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _104_862 = (tc_typ_check_trivial (let _39_2110 = env0
in {FStar_Tc_Env.solver = _39_2110.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2110.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2110.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2110.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2110.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2110.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2110.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2110.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2110.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2110.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2110.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2110.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2110.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2110.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2110.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _39_2110.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2110.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2110.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2110.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _104_862 (norm_t env)))
end)
end)
in (let env = (match (((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str))) with
| true -> begin
(let _39_2113 = env
in {FStar_Tc_Env.solver = _39_2113.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2113.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2113.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2113.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2113.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2113.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2113.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2113.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2113.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2113.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2113.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2113.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2113.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2113.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2113.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2113.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2113.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2113.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2113.FStar_Tc_Env.default_effects})
end
| false -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_39_2118) with
| (lbs, env') -> begin
(let _39_2133 = (let _104_868 = (let _104_867 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _104_867 (FStar_List.map (fun _39_2122 -> (match (_39_2122) with
| (x, t, e) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (let _39_2124 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_866 = (FStar_Absyn_Print.lbname_to_string x)
in (let _104_865 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_864 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint3 "Checking %s = %s against type %s\n" _104_866 _104_865 _104_864))))
end
| false -> begin
()
end)
in (let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (let _39_2130 = (tc_total_exp env' e)
in (match (_39_2130) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _104_868 FStar_List.unzip))
in (match (_39_2133) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (let _39_2152 = (match (((not (env.FStar_Tc_Env.generalize)) || is_inner_let)) with
| true -> begin
(let _104_870 = (FStar_List.map (fun _39_2138 -> (match (_39_2138) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_104_870, g_lbs))
end
| false -> begin
(let _39_2139 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _104_874 = (FStar_All.pipe_right lbs (FStar_List.map (fun _39_2144 -> (match (_39_2144) with
| (x, t, e) -> begin
(let _104_873 = (let _104_872 = (FStar_Absyn_Util.range_of_lb (x, t, e))
in (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) _104_872))
in (x, e, _104_873))
end))))
in (FStar_Tc_Util.generalize true env _104_874))
in (let _104_876 = (FStar_List.map (fun _39_2149 -> (match (_39_2149) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_104_876, FStar_Tc_Rel.trivial_guard))))
end)
in (match (_39_2152) with
| (lbs, g_lbs) -> begin
(match ((not (is_inner_let))) with
| true -> begin
(let cres = (let _104_877 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_877))
in (let _39_2154 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let _39_2156 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _104_881 = (let _104_880 = (w cres)
in (FStar_All.pipe_left _104_880 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_104_881, cres, FStar_Tc_Rel.trivial_guard)))))
end
| false -> begin
(let _39_2172 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _39_2160 _39_2167 -> (match ((_39_2160, _39_2167)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_2164; FStar_Absyn_Syntax.lbdef = _39_2162}) -> begin
(let b = (binding_of_lb x t)
in (let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_39_2172) with
| (bindings, env) -> begin
(let _39_2176 = (tc_exp env e1)
in (match (_39_2176) with
| (e1, cres, g1) -> begin
(let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (let cres = (let _39_2180 = cres
in {FStar_Absyn_Syntax.eff_name = _39_2180.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _39_2180.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _39_2180.FStar_Absyn_Syntax.comp})
in (let e = (let _104_886 = (w cres)
in (FStar_All.pipe_left _104_886 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_39_2185) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _39_10 -> (match (_39_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_39_2197); FStar_Absyn_Syntax.lbtyp = _39_2195; FStar_Absyn_Syntax.lbeff = _39_2193; FStar_Absyn_Syntax.lbdef = _39_2191} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _39_2205; FStar_Absyn_Syntax.lbeff = _39_2203; FStar_Absyn_Syntax.lbdef = _39_2201} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _39_2214; FStar_Absyn_Syntax.lbeff = _39_2212; FStar_Absyn_Syntax.lbdef = _39_2210}) -> begin
(let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _39_2220 = (let _104_888 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _104_888))
in (e, cres, guard)))
end
| _39_2223 -> begin
(e, cres, guard)
end))
end))))))
end))
end))
end)
end)))
end))
end)))
end)))
end))))))
and tc_eqn = (fun scrutinee_x pat_t env _39_2230 -> (match (_39_2230) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _39_2238 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_39_2238) with
| (bindings, exps, p) -> begin
(let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (let _39_2247 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat")))) with
| true -> begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _39_11 -> (match (_39_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _104_901 = (FStar_Absyn_Print.strBvd x)
in (let _104_900 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.fprint2 "Before tc ... pattern var %s  : %s\n" _104_901 _104_900)))
end
| _39_2246 -> begin
()
end))))
end
| false -> begin
()
end)
in (let _39_2252 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_39_2252) with
| (env1, _39_2251) -> begin
(let env1 = (let _39_2253 = env1
in {FStar_Tc_Env.solver = _39_2253.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2253.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2253.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2253.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2253.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2253.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2253.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2253.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _39_2253.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2253.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2253.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2253.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2253.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2253.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2253.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2253.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2253.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2253.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2253.FStar_Tc_Env.default_effects})
in (let expected_pat_t = (FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _39_2258 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_904 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_903 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.fprint2 "Checking pattern expression %s against expected type %s\n" _104_904 _104_903)))
end
| false -> begin
()
end)
in (let _39_2263 = (tc_exp env1 e)
in (match (_39_2263) with
| (e, lc, g) -> begin
(let _39_2264 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_906 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _104_905 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.fprint2 "Pre-checked pattern expression %s at type %s\n" _104_906 _104_905)))
end
| false -> begin
()
end)
in (let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (FStar_Tc_Rel.conj_guard g g')
in (let _39_2268 = (let _104_907 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _104_907))
in (let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (let _39_2271 = (match ((let _104_910 = (let _104_909 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _104_908 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _104_909 _104_908)))
in (FStar_All.pipe_left Prims.op_Negation _104_910))) with
| true -> begin
(let _104_915 = (let _104_914 = (let _104_913 = (let _104_912 = (FStar_Absyn_Print.exp_to_string e')
in (let _104_911 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _104_912 _104_911)))
in (_104_913, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_104_914))
in (Prims.raise _104_915))
end
| false -> begin
()
end)
in (let _39_2273 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_916 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.fprint1 "Done checking pattern expression %s\n" _104_916))
end
| false -> begin
()
end)
in e)))))))
end))))))
in (let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (let _39_2284 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat")))) with
| true -> begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _39_12 -> (match (_39_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _104_919 = (FStar_Absyn_Print.strBvd x)
in (let _104_918 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "Pattern var %s  : %s\n" _104_919 _104_918)))
end
| _39_2283 -> begin
()
end))))
end
| false -> begin
()
end)
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _39_2291 = (tc_pat true pat_t pattern)
in (match (_39_2291) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _39_2301 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
(match ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) with
| true -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end
| false -> begin
(let _39_2298 = (let _104_920 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _104_920 e))
in (match (_39_2298) with
| (e, c, g) -> begin
(Some (e), g)
end))
end)
end)
in (match (_39_2301) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _104_922 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _104_921 -> Some (_104_921)) _104_922))
end)
in (let _39_2309 = (tc_exp pat_env branch)
in (match (_39_2309) with
| (branch, c, g_branch) -> begin
(let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _39_2314 = (let _104_923 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _104_923 FStar_Tc_Env.clear_expected_typ))
in (match (_39_2314) with
| (scrutinee_env, _39_2313) -> begin
(let c = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _39_2328 -> begin
(let clause = (let _104_927 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _104_926 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _104_927 _104_926 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _104_929 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _104_928 -> Some (_104_928)) _104_929))
end))
end))) None))
in (let c = (match ((eqs, when_condition)) with
| (None, None) -> begin
c
end
| (Some (f), None) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (f)))
end
| (Some (f), Some (w)) -> begin
(let _104_932 = (let _104_931 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _104_930 -> FStar_Tc_Rel.NonTrivial (_104_930)) _104_931))
in (FStar_Tc_Util.weaken_precondition env c _104_932))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun scrutinee f -> (let disc = (let _104_939 = (let _104_937 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _104_937))
in (let _104_938 = (FStar_Absyn_Syntax.range_of_lid f.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_left _104_939 _104_938)))
in (let disc = (let _104_942 = (let _104_941 = (let _104_940 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_104_940)::[])
in (disc, _104_941))
in (FStar_Absyn_Syntax.mk_Exp_app _104_942 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun scrutinee pat_exp -> (let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Absyn_Syntax.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_39_2386) -> begin
(let _104_951 = (let _104_950 = (let _104_949 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _104_948 = (let _104_947 = (FStar_Absyn_Syntax.varg pat_exp)
in (_104_947)::[])
in (_104_949)::_104_948))
in (FStar_Absyn_Util.teq, _104_950))
in (FStar_Absyn_Syntax.mk_Typ_app _104_951 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _39_2390) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _39_2403); FStar_Absyn_Syntax.tk = _39_2400; FStar_Absyn_Syntax.pos = _39_2398; FStar_Absyn_Syntax.fvs = _39_2396; FStar_Absyn_Syntax.uvs = _39_2394}, args) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _104_959 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_39_2414) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in (let sub_term = (let _104_957 = (let _104_956 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _104_955 = (let _104_954 = (FStar_Absyn_Syntax.varg scrutinee)
in (_104_954)::[])
in (_104_956, _104_955)))
in (FStar_Absyn_Syntax.mk_Exp_app _104_957 None f.FStar_Absyn_Syntax.p))
in (let _104_958 = (mk_guard sub_term ei)
in (_104_958)::[])))
end))))
in (FStar_All.pipe_right _104_959 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _39_2422 -> begin
(let _104_962 = (let _104_961 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _104_960 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _104_961 _104_960)))
in (FStar_All.failwith _104_962))
end)))
in (let mk_guard = (fun s tsc pat -> (match ((not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)))) with
| true -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| false -> begin
(let t = (mk_guard s pat)
in (let _39_2431 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_39_2431) with
| (t, _39_2430) -> begin
t
end)))
end))
in (let path_guard = (let _104_971 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _104_970 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _104_970)))))
in (FStar_All.pipe_right _104_971 FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _104_972 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _104_972))
in (let _39_2439 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _104_973 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.fprint1 "Carrying guard from match: %s\n") _104_973))
end
| false -> begin
()
end)
in (let _104_975 = (let _104_974 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _104_974))
in ((pattern, when_clause, branch), path_guard, c, _104_975))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun env k -> (let _39_2445 = (tc_kind env k)
in (match (_39_2445) with
| (k, g) -> begin
(let _39_2446 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun env t -> (let _39_2453 = (tc_typ env t)
in (match (_39_2453) with
| (t, k, g) -> begin
(let _39_2454 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun env t k -> (let _39_2461 = (tc_typ_check env t k)
in (match (_39_2461) with
| (t, f) -> begin
(let _39_2462 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun env e -> (let _39_2469 = (tc_exp env e)
in (match (_39_2469) with
| (e, c, g) -> begin
(match ((FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _104_985 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _104_985 (norm_c env)))
in (match ((let _104_987 = (let _104_986 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _104_986))
in (FStar_Tc_Rel.sub_comp env c _104_987))) with
| Some (g') -> begin
(let _104_988 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _104_988))
end
| _39_2475 -> begin
(let _104_991 = (let _104_990 = (let _104_989 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_104_989, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_990))
in (Prims.raise _104_991))
end)))
end)
end)))
and tc_ghost_exp = (fun env e -> (let _39_2481 = (tc_exp env e)
in (match (_39_2481) with
| (e, c, g) -> begin
(match ((FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let c = (let _104_994 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _104_994 (norm_c env)))
in (let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (let _39_2485 = env
in {FStar_Tc_Env.solver = _39_2485.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2485.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2485.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2485.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2485.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2485.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2485.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2485.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2485.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2485.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2485.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2485.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2485.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2485.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2485.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2485.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _39_2485.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2485.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2485.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _104_995 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _104_995))
end
| _39_2490 -> begin
(let _104_998 = (let _104_997 = (let _104_996 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_104_996, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_997))
in (Prims.raise _104_998))
end))))
end)
end)))

let tc_tparams = (fun env tps -> (let _39_2496 = (tc_binders env tps)
in (match (_39_2496) with
| (tps, env, g) -> begin
(let _39_2497 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _39_2516)::(FStar_Util.Inl (wp), _39_2511)::(FStar_Util.Inl (_39_2503), _39_2506)::[], _39_2520) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _39_2524 -> begin
(let _104_1012 = (let _104_1011 = (let _104_1010 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (let _104_1009 = (FStar_Absyn_Syntax.range_of_lid m)
in (_104_1010, _104_1009)))
in FStar_Absyn_Syntax.Error (_104_1011))
in (Prims.raise _104_1012))
end))

let rec tc_eff_decl = (fun env m -> (let _39_2530 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_39_2530) with
| (binders, env, g) -> begin
(let _39_2531 = (FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (let _39_2536 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_39_2536) with
| (a, kwp_a) -> begin
(let a_typ = (FStar_Absyn_Util.btvar_to_typ a)
in (let b = (let _104_1026 = (FStar_Absyn_Syntax.range_of_lid m.FStar_Absyn_Syntax.mname)
in (FStar_Absyn_Util.gen_bvar_p _104_1026 FStar_Absyn_Syntax.ktype))
in (let b_typ = (FStar_Absyn_Util.btvar_to_typ b)
in (let kwp_b = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (let kwlp_a = kwp_a
in (let kwlp_b = kwp_b
in (let a_kwp_b = (let _104_1029 = (let _104_1028 = (let _104_1027 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_104_1027)::[])
in (_104_1028, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1029 a_typ.FStar_Absyn_Syntax.pos))
in (let a_kwlp_b = a_kwp_b
in (let w = (fun k -> (let _104_1037 = (FStar_Absyn_Syntax.range_of_lid m.FStar_Absyn_Syntax.mname)
in (k _104_1037)))
in (let ret = (let expected_k = (let _104_1044 = (let _104_1043 = (let _104_1042 = (let _104_1041 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1040 = (let _104_1039 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_104_1039)::[])
in (_104_1041)::_104_1040))
in (_104_1042, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1043))
in (FStar_All.pipe_left w _104_1044))
in (let _104_1045 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _104_1045 (norm_t env))))
in (let bind_wp = (let expected_k = (let _104_1060 = (let _104_1059 = (let _104_1058 = (let _104_1057 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1056 = (let _104_1055 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1054 = (let _104_1053 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _104_1052 = (let _104_1051 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _104_1050 = (let _104_1049 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _104_1048 = (let _104_1047 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_104_1047)::[])
in (_104_1049)::_104_1048))
in (_104_1051)::_104_1050))
in (_104_1053)::_104_1052))
in (_104_1055)::_104_1054))
in (_104_1057)::_104_1056))
in (_104_1058, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1059))
in (FStar_All.pipe_left w _104_1060))
in (let _104_1061 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _104_1061 (norm_t env))))
in (let bind_wlp = (let expected_k = (let _104_1072 = (let _104_1071 = (let _104_1070 = (let _104_1069 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1068 = (let _104_1067 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1066 = (let _104_1065 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _104_1064 = (let _104_1063 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_104_1063)::[])
in (_104_1065)::_104_1064))
in (_104_1067)::_104_1066))
in (_104_1069)::_104_1068))
in (_104_1070, kwlp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1071))
in (FStar_All.pipe_left w _104_1072))
in (let _104_1073 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _104_1073 (norm_t env))))
in (let if_then_else = (let expected_k = (let _104_1084 = (let _104_1083 = (let _104_1082 = (let _104_1081 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1080 = (let _104_1079 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1078 = (let _104_1077 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _104_1076 = (let _104_1075 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1075)::[])
in (_104_1077)::_104_1076))
in (_104_1079)::_104_1078))
in (_104_1081)::_104_1080))
in (_104_1082, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1083))
in (FStar_All.pipe_left w _104_1084))
in (let _104_1085 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _104_1085 (norm_t env))))
in (let ite_wp = (let expected_k = (let _104_1094 = (let _104_1093 = (let _104_1092 = (let _104_1091 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1090 = (let _104_1089 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _104_1088 = (let _104_1087 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1087)::[])
in (_104_1089)::_104_1088))
in (_104_1091)::_104_1090))
in (_104_1092, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1093))
in (FStar_All.pipe_left w _104_1094))
in (let _104_1095 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _104_1095 (norm_t env))))
in (let ite_wlp = (let expected_k = (let _104_1102 = (let _104_1101 = (let _104_1100 = (let _104_1099 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1098 = (let _104_1097 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_104_1097)::[])
in (_104_1099)::_104_1098))
in (_104_1100, kwlp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1101))
in (FStar_All.pipe_left w _104_1102))
in (let _104_1103 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _104_1103 (norm_t env))))
in (let wp_binop = (let expected_k = (let _104_1115 = (let _104_1114 = (let _104_1113 = (let _104_1112 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1111 = (let _104_1110 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _104_1109 = (let _104_1108 = (let _104_1105 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _104_1105))
in (let _104_1107 = (let _104_1106 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1106)::[])
in (_104_1108)::_104_1107))
in (_104_1110)::_104_1109))
in (_104_1112)::_104_1111))
in (_104_1113, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1114))
in (FStar_All.pipe_left w _104_1115))
in (let _104_1116 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _104_1116 (norm_t env))))
in (let wp_as_type = (let expected_k = (let _104_1123 = (let _104_1122 = (let _104_1121 = (let _104_1120 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1119 = (let _104_1118 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1118)::[])
in (_104_1120)::_104_1119))
in (_104_1121, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1122))
in (FStar_All.pipe_left w _104_1123))
in (let _104_1124 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _104_1124 (norm_t env))))
in (let close_wp = (let expected_k = (let _104_1133 = (let _104_1132 = (let _104_1131 = (let _104_1130 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1129 = (let _104_1128 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1127 = (let _104_1126 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_104_1126)::[])
in (_104_1128)::_104_1127))
in (_104_1130)::_104_1129))
in (_104_1131, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1132))
in (FStar_All.pipe_left w _104_1133))
in (let _104_1134 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _104_1134 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _104_1147 = (let _104_1146 = (let _104_1145 = (let _104_1144 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1143 = (let _104_1142 = (let _104_1141 = (let _104_1140 = (let _104_1139 = (let _104_1138 = (let _104_1137 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_104_1137)::[])
in (_104_1138, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1139))
in (FStar_All.pipe_left w _104_1140))
in (FStar_Absyn_Syntax.null_t_binder _104_1141))
in (_104_1142)::[])
in (_104_1144)::_104_1143))
in (_104_1145, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1146))
in (FStar_All.pipe_left w _104_1147))
in (let _104_1148 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _104_1148 (norm_t env))))
in (let _39_2570 = (let expected_k = (let _104_1157 = (let _104_1156 = (let _104_1155 = (let _104_1154 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1153 = (let _104_1152 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _104_1151 = (let _104_1150 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1150)::[])
in (_104_1152)::_104_1151))
in (_104_1154)::_104_1153))
in (_104_1155, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1156))
in (FStar_All.pipe_left w _104_1157))
in (let _104_1161 = (let _104_1158 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _104_1158 (norm_t env)))
in (let _104_1160 = (let _104_1159 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _104_1159 (norm_t env)))
in (_104_1161, _104_1160))))
in (match (_39_2570) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (let _104_1166 = (let _104_1165 = (let _104_1164 = (let _104_1163 = (FStar_Absyn_Syntax.t_binder a)
in (_104_1163)::[])
in (_104_1164, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1165))
in (FStar_All.pipe_left w _104_1166))
in (let _104_1167 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _104_1167 (norm_t env))))
in (let trivial_wp = (let expected_k = (let _104_1174 = (let _104_1173 = (let _104_1172 = (let _104_1171 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1170 = (let _104_1169 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1169)::[])
in (_104_1171)::_104_1170))
in (_104_1172, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1173))
in (FStar_All.pipe_left w _104_1174))
in (let _104_1175 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _104_1175 (norm_t env))))
in {FStar_Absyn_Syntax.mname = m.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = m.FStar_Absyn_Syntax.qualifiers; FStar_Absyn_Syntax.signature = mk; FStar_Absyn_Syntax.ret = ret; FStar_Absyn_Syntax.bind_wp = bind_wp; FStar_Absyn_Syntax.bind_wlp = bind_wlp; FStar_Absyn_Syntax.if_then_else = if_then_else; FStar_Absyn_Syntax.ite_wp = ite_wp; FStar_Absyn_Syntax.ite_wlp = ite_wlp; FStar_Absyn_Syntax.wp_binop = wp_binop; FStar_Absyn_Syntax.wp_as_type = wp_as_type; FStar_Absyn_Syntax.close_wp = close_wp; FStar_Absyn_Syntax.close_wp_t = close_wp_t; FStar_Absyn_Syntax.assert_p = assert_p; FStar_Absyn_Syntax.assume_p = assume_p; FStar_Absyn_Syntax.null_wp = null_wp; FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl = (fun env se deserialized -> (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (p, r) -> begin
(match (p) with
| FStar_Absyn_Syntax.SetOptions (o) -> begin
(match ((FStar_Options.set_options o)) with
| FStar_Getopt.GoOn -> begin
(se, env)
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end)
end
| FStar_Absyn_Syntax.ResetOptions -> begin
(let _39_2589 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _39_2591 = (let _104_1179 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _104_1179 Prims.ignore))
in (se, env)))
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, r) -> begin
(let ne = (tc_eff_decl env ne)
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ne, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, r) -> begin
(let _39_2606 = (let _104_1180 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _104_1180))
in (match (_39_2606) with
| (a, kwp_a_src) -> begin
(let _39_2609 = (let _104_1181 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _104_1181))
in (match (_39_2609) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _104_1185 = (let _104_1184 = (let _104_1183 = (let _104_1182 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _104_1182))
in FStar_Util.Inl (_104_1183))
in (_104_1184)::[])
in (FStar_Absyn_Util.subst_kind _104_1185 kwp_b_tgt))
in (let expected_k = (let _104_1191 = (let _104_1190 = (let _104_1189 = (let _104_1188 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1187 = (let _104_1186 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_104_1186)::[])
in (_104_1188)::_104_1187))
in (_104_1189, kwp_a_tgt))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1190))
in (FStar_All.pipe_right r _104_1191))
in (let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _39_2613 = sub
in {FStar_Absyn_Syntax.source = _39_2613.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _39_2613.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_2630 = (tc_tparams env tps)
in (match (_39_2630) with
| (tps, env) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _39_2633 -> begin
(tc_kind_trivial env k)
end)
in (let _39_2635 = (match ((FStar_Tc_Env.debug env FStar_Options.Extreme)) with
| true -> begin
(let _104_1194 = (FStar_Absyn_Print.sli lid)
in (let _104_1193 = (let _104_1192 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _104_1192))
in (FStar_Util.fprint2 "Checked %s at kind %s\n" _104_1194 _104_1193)))
end
| false -> begin
()
end)
in (let k = (norm_k env k)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _39_2653 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_39_2648); FStar_Absyn_Syntax.tk = _39_2646; FStar_Absyn_Syntax.pos = _39_2644; FStar_Absyn_Syntax.fvs = _39_2642; FStar_Absyn_Syntax.uvs = _39_2640} -> begin
(let _104_1195 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _104_1195))
end
| _39_2652 -> begin
()
end)
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _39_2666 = (tc_tparams env tps)
in (match (_39_2666) with
| (tps, env) -> begin
(let k = (tc_kind_trivial env k)
in (let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r))
in (let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, tps, c, tags, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _39_2681 = (tc_tparams env tps)
in (match (_39_2681) with
| (tps, env) -> begin
(let _39_2684 = (tc_comp env c)
in (match (_39_2684) with
| (c, g) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _39_13 -> (match (_39_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _104_1198 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _104_1197 -> Some (_104_1197)))
in FStar_Absyn_Syntax.DefaultEffect (_104_1198)))
end
| t -> begin
t
end))))
in (let se = FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, tps, c, tags, r))
in (let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))
end))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_2704 = (tc_tparams env tps)
in (match (_39_2704) with
| (tps, env') -> begin
(let _39_2710 = (let _104_1202 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _104_1202 (fun _39_2707 -> (match (_39_2707) with
| (t, k) -> begin
(let _104_1201 = (norm_t env' t)
in (let _104_1200 = (norm_k env' k)
in (_104_1201, _104_1200)))
end))))
in (match (_39_2710) with
| (t, k1) -> begin
(let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _39_2713 -> begin
(let k2 = (let _104_1203 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _104_1203 (norm_k env)))
in (let _39_2715 = (let _104_1204 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _104_1204))
in k2))
end)
in (let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k2, t, tags, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end))
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, (tname, tps, k), quals, mutuals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_2735 = (tc_binders env tps)
in (match (_39_2735) with
| (tps, env, g) -> begin
(let tycon = (tname, tps, k)
in (let _39_2737 = (FStar_Tc_Util.discharge_guard env g)
in (let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _39_2749 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _39_2746 -> begin
([], t)
end)
in (match (_39_2749) with
| (formals, result_t) -> begin
(let cardinality_and_positivity_check = (fun formal -> (let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _39_2757 -> (match (_39_2757) with
| (a, _39_2756) -> begin
(match (a) with
| FStar_Util.Inl (_39_2759) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _104_1212 = (FStar_Absyn_Util.compress_typ t)
in _104_1212.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Absyn_Syntax.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _104_1218 = (let _104_1217 = (let _104_1216 = (let _104_1214 = (let _104_1213 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid _104_1213))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _104_1214 tname))
in (let _104_1215 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_104_1216, _104_1215)))
in FStar_Absyn_Syntax.Error (_104_1217))
in (Prims.raise _104_1218))
end)
end
| _39_2772 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(let _39_2775 = (match ((FStar_Options.warn_cardinality ())) with
| true -> begin
(let _104_1219 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _104_1219))
end
| false -> begin
(match ((FStar_Options.check_cardinality ())) with
| true -> begin
(let _104_1222 = (let _104_1221 = (let _104_1220 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_104_1220, r))
in FStar_Absyn_Syntax.Error (_104_1221))
in (Prims.raise _104_1222))
end
| false -> begin
()
end)
end)
in (let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_39_2779) -> begin
(let _39_2784 = (FStar_Absyn_Util.kind_formals k)
in (match (_39_2784) with
| (formals, _39_2783) -> begin
(check_positivity formals)
end))
end
| _39_2786 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in (match (((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t))) with
| true -> begin
(let _39_2793 = (let _104_1223 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _104_1223 FStar_Util.must))
in (match (_39_2793) with
| (formals, _39_2792) -> begin
(check_positivity formals)
end))
end
| false -> begin
()
end))
end)))
in (let _39_2794 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (let _39_2848 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
(match ((not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _104_1227 = (let _104_1226 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _104_1226 Prims.fst))
in (FStar_List.forall2 (fun _39_2801 _39_2805 -> (match ((_39_2801, _39_2805)) with
| ((a, _39_2800), (b, _39_2804)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _39_2813; FStar_Absyn_Syntax.pos = _39_2811; FStar_Absyn_Syntax.fvs = _39_2809; FStar_Absyn_Syntax.uvs = _39_2807}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _39_2828; FStar_Absyn_Syntax.pos = _39_2826; FStar_Absyn_Syntax.fvs = _39_2824; FStar_Absyn_Syntax.uvs = _39_2822}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _39_2837 -> begin
false
end)
end)) _104_1227 tps)))))) with
| true -> begin
(let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _39_2840 -> begin
(let _39_2844 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_39_2844) with
| (_39_2842, expected_args) -> begin
(let _104_1228 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _104_1228 expected_args))
end))
end)
in (let _104_1234 = (let _104_1233 = (let _104_1232 = (let _104_1230 = (let _104_1229 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid _104_1229))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _104_1230 result_t expected_t))
in (let _104_1231 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_104_1232, _104_1231)))
in FStar_Absyn_Syntax.Error (_104_1233))
in (Prims.raise _104_1234)))
end
| false -> begin
()
end)
end
| _39_2847 -> begin
(let _104_1241 = (let _104_1240 = (let _104_1239 = (let _104_1237 = (let _104_1235 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid _104_1235))
in (let _104_1236 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _104_1237 result_t _104_1236)))
in (let _104_1238 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_104_1239, _104_1238)))
in FStar_Absyn_Syntax.Error (_104_1240))
in (Prims.raise _104_1241))
end)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _39_2852 = (match ((log env)) with
| true -> begin
(let _104_1243 = (let _104_1242 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Absyn_Syntax.str _104_1242))
in (FStar_All.pipe_left FStar_Util.print_string _104_1243))
end
| false -> begin
()
end)
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let t = (let _104_1244 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _104_1244 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _39_2862 = (FStar_Tc_Util.check_uvars r t)
in (let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _39_2866 = (match ((log env)) with
| true -> begin
(let _104_1246 = (let _104_1245 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Absyn_Syntax.str _104_1245))
in (FStar_All.pipe_left FStar_Util.print_string _104_1246))
end
| false -> begin
()
end)
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let phi = (let _104_1247 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _104_1247 (norm_t env)))
in (let _39_2876 = (FStar_Tc_Util.check_uvars r phi)
in (let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_2929 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _39_2889 lb -> (match (_39_2889) with
| (gen, lbs) -> begin
(let _39_2926 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_39_2898); FStar_Absyn_Syntax.lbtyp = _39_2896; FStar_Absyn_Syntax.lbeff = _39_2894; FStar_Absyn_Syntax.lbdef = _39_2892} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_2903; FStar_Absyn_Syntax.lbdef = e} -> begin
(let _39_2923 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _39_2911) -> begin
(let _39_2914 = (match ((FStar_Tc_Env.debug env FStar_Options.Medium)) with
| true -> begin
(let _104_1250 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.fprint2 "Using annotation %s for let binding %s\n" _104_1250 l.FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _104_1251 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _104_1251))
end
| _39_2918 -> begin
(let _39_2919 = (match ((not (deserialized))) with
| true -> begin
(let _104_1253 = (let _104_1252 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _104_1252))
in (FStar_All.pipe_left FStar_Util.print_string _104_1253))
end
| false -> begin
()
end)
in (let _104_1254 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _104_1254)))
end))
end)
in (match (_39_2923) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_39_2926) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_39_2929) with
| (generalize, lbs') -> begin
(let lbs' = (FStar_List.rev lbs')
in (let e = (let _104_1259 = (let _104_1258 = (let _104_1257 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _104_1257 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit)))
in (((Prims.fst lbs), lbs'), _104_1258))
in (FStar_Absyn_Syntax.mk_Exp_let _104_1259 None r))
in (let _39_2964 = (match ((tc_exp (let _39_2932 = env
in {FStar_Tc_Env.solver = _39_2932.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2932.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2932.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2932.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2932.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2932.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2932.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2932.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2932.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2932.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2932.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2932.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _39_2932.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2932.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2932.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2932.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2932.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2932.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2932.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _39_2941; FStar_Absyn_Syntax.pos = _39_2939; FStar_Absyn_Syntax.fvs = _39_2937; FStar_Absyn_Syntax.uvs = _39_2935}, _39_2948, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_39_2952, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _39_2958 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _39_2961 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_2964) with
| (se, lbs) -> begin
(let _39_2970 = (match ((log env)) with
| true -> begin
(let _104_1265 = (let _104_1264 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _104_1261 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _104_1261))) with
| None -> begin
true
end
| _39_2968 -> begin
false
end)
in (match (should_log) with
| true -> begin
(let _104_1263 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _104_1262 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _104_1263 _104_1262)))
end
| false -> begin
""
end)))))
in (FStar_All.pipe_right _104_1264 (FStar_String.concat "\n")))
in (FStar_Util.fprint1 "%s\n" _104_1265))
end
| false -> begin
()
end)
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))
end))))
end)))
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let env = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (let _39_2982 = (tc_exp env e)
in (match (_39_2982) with
| (e, c, g1) -> begin
(let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _39_2988 = (let _104_1269 = (let _104_1266 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_104_1266))
in (let _104_1268 = (let _104_1267 = (c.FStar_Absyn_Syntax.comp ())
in (e, _104_1267))
in (check_expected_effect env _104_1269 _104_1268)))
in (match (_39_2988) with
| (e, _39_2986, g) -> begin
(let _39_2989 = (let _104_1270 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _104_1270))
in (let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_3008 = (FStar_All.pipe_right ses (FStar_List.partition (fun _39_14 -> (match (_39_14) with
| FStar_Absyn_Syntax.Sig_tycon (_39_3002) -> begin
true
end
| _39_3005 -> begin
false
end))))
in (match (_39_3008) with
| (tycons, rest) -> begin
(let _39_3017 = (FStar_All.pipe_right rest (FStar_List.partition (fun _39_15 -> (match (_39_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_39_3011) -> begin
true
end
| _39_3014 -> begin
false
end))))
in (match (_39_3017) with
| (abbrevs, rest) -> begin
(let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _39_16 -> (match (_39_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _104_1274 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _104_1274 Prims.fst))
end
| _39_3029 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _39_3032 -> begin
(FStar_All.failwith "impossible")
end))))
in (let _39_3036 = (FStar_List.split recs)
in (match (_39_3036) with
| (recs, abbrev_defs) -> begin
(let msg = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _104_1275 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _104_1275))
end
| false -> begin
""
end)
in (let _39_3038 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (let _39_3045 = (tc_decls false env tycons deserialized)
in (match (_39_3045) with
| (tycons, _39_3042, _39_3044) -> begin
(let _39_3051 = (tc_decls false env recs deserialized)
in (match (_39_3051) with
| (recs, _39_3048, _39_3050) -> begin
(let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (let _39_3058 = (tc_decls false env1 rest deserialized)
in (match (_39_3058) with
| (rest, _39_3055, _39_3057) -> begin
(let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(let tt = (let _104_1278 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _104_1278))
in (let _39_3074 = (tc_typ_trivial env1 tt)
in (match (_39_3074) with
| (tt, _39_3073) -> begin
(let _39_3083 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _39_3080 -> begin
([], tt)
end)
in (match (_39_3083) with
| (tps, t) -> begin
(let _104_1280 = (let _104_1279 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _104_1279, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_104_1280))
end))
end)))
end
| _39_3085 -> begin
(let _104_1282 = (let _104_1281 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _104_1281))
in (FStar_All.failwith _104_1282))
end)) recs abbrev_defs)
in (let _39_3087 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
in (let se = FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append (FStar_List.append tycons abbrevs) rest), quals, lids, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))
end)))
end))
end))))
end)))
end))
end)))
end))
and tc_decls = (fun for_export env ses deserialized -> (let _39_3111 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _39_3098 se -> (match (_39_3098) with
| (ses, all_non_private, env) -> begin
(let _39_3100 = (match ((FStar_Tc_Env.debug env FStar_Options.Low)) with
| true -> begin
(let _104_1290 = (let _104_1289 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _104_1289))
in (FStar_Util.print_string _104_1290))
end
| false -> begin
()
end)
in (let _39_3104 = (tc_decl env se deserialized)
in (match (_39_3104) with
| (se, env) -> begin
(let _39_3105 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in (let non_private_decls = (match (for_export) with
| true -> begin
(non_private env se)
end
| false -> begin
[]
end)
in ((se)::ses, (non_private_decls)::all_non_private, env)))
end)))
end)) ([], [], env)))
in (match (_39_3111) with
| (ses, all_non_private, env) -> begin
(let _104_1291 = (FStar_All.pipe_right (FStar_List.rev all_non_private) FStar_List.flatten)
in ((FStar_List.rev ses), _104_1291, env))
end)))
and non_private = (fun env se -> (let is_private = (fun quals -> (FStar_List.contains FStar_Absyn_Syntax.Private quals))
in (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _39_3119, _39_3121) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_tycon (_39_3125, _39_3127, _39_3129, _39_3131, _39_3133, quals, r) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, k, t, quals, r) -> begin
(match ((is_private quals)) with
| true -> begin
(FStar_Absyn_Syntax.Sig_tycon ((l, bs, k, [], [], (FStar_Absyn_Syntax.Assumption)::quals, r)))::[]
end
| false -> begin
(se)::[]
end)
end
| FStar_Absyn_Syntax.Sig_assume (_39_3147, _39_3149, quals, _39_3152) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| FStar_Absyn_Syntax.Sig_val_decl (_39_3156, _39_3158, quals, _39_3161) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| FStar_Absyn_Syntax.Sig_main (_39_3165) -> begin
[]
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_datacon (_39_3183) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, _39_3189) -> begin
(let check_priv = (fun lbs -> (let is_priv = (fun _39_17 -> (match (_39_17) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _39_3200; FStar_Absyn_Syntax.lbeff = _39_3198; FStar_Absyn_Syntax.lbdef = _39_3196} -> begin
(match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some (_39_3205, qs) -> begin
(FStar_List.contains FStar_Absyn_Syntax.Private qs)
end
| _39_3210 -> begin
false
end)
end
| _39_3212 -> begin
false
end))
in (let some_priv = (FStar_All.pipe_right lbs (FStar_Util.for_some is_priv))
in (match (some_priv) with
| true -> begin
(match ((FStar_All.pipe_right lbs (FStar_Util.for_some (fun x -> (let _104_1301 = (is_priv x)
in (FStar_All.pipe_right _104_1301 Prims.op_Negation)))))) with
| true -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Some but not all functions in this mutually recursive nest are marked private", r))))
end
| false -> begin
true
end)
end
| false -> begin
false
end))))
in (let _39_3219 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.partition (fun lb -> ((FStar_Absyn_Util.is_pure_or_ghost_function lb.FStar_Absyn_Syntax.lbtyp) && (let _104_1303 = (FStar_Absyn_Util.is_lemma lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_left Prims.op_Negation _104_1303))))))
in (match (_39_3219) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_39_3223::_39_3221, _39_3228::_39_3226) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_39_3234::_39_3232, []) -> begin
(match ((check_priv pure_funs)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| ([], _39_3242::_39_3240) -> begin
(match ((check_priv rest)) with
| true -> begin
[]
end
| false -> begin
(FStar_All.pipe_right rest (FStar_List.collect (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_39_3247) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (l) -> begin
(let _104_1307 = (let _104_1306 = (let _104_1305 = (FStar_Absyn_Syntax.range_of_lid l)
in (l, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::[], _104_1305))
in FStar_Absyn_Syntax.Sig_val_decl (_104_1306))
in (_104_1307)::[])
end))))
end)
end
| ([], []) -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end)))

let get_exports = (fun env modul non_private_decls -> (let assume_vals = (fun decls -> (FStar_All.pipe_right decls (FStar_List.map (fun _39_18 -> (match (_39_18) with
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((lid, t, (FStar_Absyn_Syntax.Assumption)::quals, r))
end
| s -> begin
s
end)))))
in (match (modul.FStar_Absyn_Syntax.is_interface) with
| true -> begin
non_private_decls
end
| false -> begin
(let exports = (let _104_1319 = (FStar_Tc_Env.modules env)
in (FStar_Util.find_map _104_1319 (fun m -> (match ((m.FStar_Absyn_Syntax.is_interface && (FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name m.FStar_Absyn_Syntax.name))) with
| true -> begin
(let _104_1318 = (FStar_All.pipe_right m.FStar_Absyn_Syntax.exports assume_vals)
in Some (_104_1318))
end
| false -> begin
None
end))))
in (match (exports) with
| None -> begin
non_private_decls
end
| Some (e) -> begin
e
end))
end)))

let tc_partial_modul = (fun env modul -> (let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let msg = (Prims.strcat "Internals for " name)
in (let env = (let _39_3276 = env
in (let _104_1324 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)))
in {FStar_Tc_Env.solver = _39_3276.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_3276.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_3276.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_3276.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_3276.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_3276.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_3276.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_3276.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_3276.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_3276.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_3276.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_3276.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_3276.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_3276.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_3276.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_3276.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_3276.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _104_1324; FStar_Tc_Env.default_effects = _39_3276.FStar_Tc_Env.default_effects}))
in (let _39_3279 = (match ((not ((FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end
| false -> begin
()
end)
in (let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (let _39_3285 = (tc_decls true env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_39_3285) with
| (ses, non_private_decls, env) -> begin
((let _39_3286 = modul
in {FStar_Absyn_Syntax.name = _39_3286.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _39_3286.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _39_3286.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _39_3286.FStar_Absyn_Syntax.is_deserialized}), non_private_decls, env)
end))))))))

let tc_more_partial_modul = (fun env modul decls -> (let _39_3294 = (tc_decls true env decls false)
in (match (_39_3294) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _39_3295 = modul
in {FStar_Absyn_Syntax.name = _39_3295.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _39_3295.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _39_3295.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _39_3295.FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun env modul npds -> (let exports = (get_exports env modul npds)
in (let modul = (let _39_3302 = modul
in {FStar_Absyn_Syntax.name = _39_3302.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _39_3302.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (let env = (FStar_Tc_Env.finish_module env modul)
in (let _39_3312 = (match ((not ((FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(let _39_3306 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str))
in (let _39_3308 = (match (((not (modul.FStar_Absyn_Syntax.is_interface)) || (let _104_1337 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str _104_1337)))) with
| true -> begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
end
| false -> begin
()
end)
in (let _39_3310 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _104_1338 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _104_1338 Prims.ignore)))))
end
| false -> begin
()
end)
in (modul, env))))))

let tc_modul = (fun env modul -> (let _39_3319 = (tc_partial_modul env modul)
in (match (_39_3319) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_Tc_Env.push_sigelt en elt)
in (let _39_3326 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _104_1351 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _104_1351 m)))))

let check_module = (fun env m -> (let _39_3331 = (match (((let _104_1356 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _104_1356)) <> 0)) with
| true -> begin
(let _104_1357 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.fprint2 "Checking %s: %s\n" (match (m.FStar_Absyn_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| false -> begin
"module"
end) _104_1357))
end
| false -> begin
()
end)
in (let _39_3344 = (match (m.FStar_Absyn_Syntax.is_deserialized) with
| true -> begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end
| false -> begin
(let _39_3336 = (tc_modul env m)
in (match (_39_3336) with
| (m, env) -> begin
(let _39_3340 = (match ((FStar_ST.read FStar_Options.serialize_mods)) with
| true -> begin
(let c_file_name = (let _104_1363 = (let _104_1362 = (let _104_1360 = (let _104_1359 = (let _104_1358 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _104_1358 "/"))
in (Prims.strcat _104_1359 FStar_Options.cache_dir))
in (Prims.strcat _104_1360 "/"))
in (let _104_1361 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (Prims.strcat _104_1362 _104_1361)))
in (Prims.strcat _104_1363 ".cache"))
in (let _39_3338 = (let _104_1366 = (let _104_1365 = (let _104_1364 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (Prims.strcat "Serializing module " _104_1364))
in (Prims.strcat _104_1365 "\n"))
in (FStar_Util.print_string _104_1366))
in (let _104_1367 = (FStar_Util.get_owriter c_file_name)
in (FStar_Absyn_SSyntax.serialize_modul _104_1367 m))))
end
| false -> begin
()
end)
in (m, env))
end))
end)
in (match (_39_3344) with
| (m, env) -> begin
(let _39_3345 = (match ((FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)) with
| true -> begin
(let _104_1368 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.fprint1 "%s\n" _104_1368))
end
| false -> begin
()
end)
in ((m)::[], env))
end))))
